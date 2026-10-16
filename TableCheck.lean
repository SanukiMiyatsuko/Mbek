import Mbek.TableAnalysis.Systems
import Mbek.TableAnalysis.Report

/-!
表解析の検査・推定ツール。

    lake exe tablecheck <表.csv> [--a mrf] [--b mbek2] [--n 6]
                        [--derived] [--loo] [--suggest "<A側の項>"]...

CSV は 1 列目 = A 側、2 列目 = B 側、3 列目 = 備考（空でなければ「予想」扱い）。
体系名: `mrf`（rasen の MRF）, `mbek0` … `mbek5`（Mbek を fund M で読む）。
-/

open TA OTSys

structure Opts where
  path : String := ""
  a : String := "mrf"
  b : String := "mbek2"
  n : Nat := 6
  derived : Bool := false
  loo : Bool := false
  suggest : Array String := #[]

def parseArgs : List String → Opts → Except String Opts
  | [], o => if o.path.isEmpty then .error "CSV のパスを指定してください" else .ok o
  | "--a" :: s :: rest, o => parseArgs rest { o with a := s }
  | "--b" :: s :: rest, o => parseArgs rest { o with b := s }
  | "--n" :: s :: rest, o => parseArgs rest { o with n := s.toNat?.getD o.n }
  | "--derived" :: rest, o => parseArgs rest { o with derived := true }
  | "--loo" :: rest, o => parseArgs rest { o with loo := true }
  | "--suggest" :: s :: rest, o => parseArgs rest { o with suggest := o.suggest.push s }
  | s :: rest, o =>
    if s.startsWith "--" then .error s!"不明なオプション {s}" else parseArgs rest { o with path := s }

def run (A B : Type) [OTSys A] [OTSys B] (o : Opts) : IO UInt32 := do
  let content ← IO.FS.readFile o.path
  let tbl : Table A B := loadTable content
  IO.println s!"# 表解析レポート\n"
  IO.println s!"- ファイル: {o.path}"
  IO.println s!"- A = {o.a}, B = {o.b}, 基本列は n = 0..{o.n - 1} まで計算"
  let nt := (tbl.rows.filter (·.trusted)).size
  IO.println s!"- 読み込んだ行: {tbl.rows.size}（確定 {nt}・予想 {tbl.rows.size - nt}）"
  for (l, s) in tbl.skipped do
    IO.println s!"- 読めなかった行 r{l}: {s}"
  IO.println ""
  let bad ← checkOrder tbl.rows
  checkStandard tbl.rows
  checkSync tbl.rows o.n
  let K ← checkClosure tbl.rows o.n o.derived
  checkConjectures tbl.rows K o.n
  if !o.suggest.isEmpty then
    IO.println "\n## 対応先の推定"
    let E := buildEdits K
    for s in o.suggest do
      match (parse? s : Option A) with
      | none => IO.println s!"- 読めない項: {s}"
      | some x =>
        IO.println s!"- {fmt x}"
        match lookA K x with
        | some y => IO.println s!"    既知: {fmt y}"
        | none => printSuggestion (suggest K E o.n x)
  if o.loo then leaveOneOut tbl.rows o.n
  return if bad == 0 then 0 else 1

def sysDispatch (o : Opts) : IO UInt32 :=
  let withB (A : Type) [OTSys A] : IO UInt32 :=
    match o.b with
    | "mrf" => run A MRF.T o
    | "mbek0" => run A (MbekT 0) o
    | "mbek1" => run A (MbekT 1) o
    | "mbek2" => run A (MbekT 2) o
    | "mbek3" => run A (MbekT 3) o
    | "mbek4" => run A (MbekT 4) o
    | "mbek5" => run A (MbekT 5) o
    | s => do IO.eprintln s!"不明な体系 {s}"; return 2
  match o.a with
  | "mrf" => withB MRF.T
  | "mbek0" => withB (MbekT 0)
  | "mbek1" => withB (MbekT 1)
  | "mbek2" => withB (MbekT 2)
  | "mbek3" => withB (MbekT 3)
  | "mbek4" => withB (MbekT 4)
  | "mbek5" => withB (MbekT 5)
  | s => do IO.eprintln s!"不明な体系 {s}"; return 2

def main (args : List String) : IO UInt32 :=
  match parseArgs args {} with
  | .error e => do IO.eprintln e; return 2
  | .ok o => sysDispatch o
