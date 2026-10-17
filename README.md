# Mbek

## 弱 hyper-Mahlo

`fund1`〜`fund5` を `K_{l+1} = P (l+1) Z Z` の次数を引数にした `fundM` にまとめ、`fundH := fundM .hyper`（解釈：弱 hyper-Mahlo 基数の崩壊まで）を定義した。

* 設計と検証：[docs/hyper-mahlo.md](docs/hyper-mahlo.md)
* 定義：[Mbek/two/hyper.lean](Mbek/two/hyper.lean)

## 表解析

OT 間の対応表（表解析）の方法論と、それを機械化した検査・推定ツールがある。

* 方法論：[docs/table-analysis.md](docs/table-analysis.md)
* 予想1 までの表解析：[docs/mrf_mbek2_to_conjecture1.md](docs/mrf_mbek2_to_conjecture1.md)
* ツール：`lake exe tablecheck <表.csv>`（例：`lake exe tablecheck data/mrf_mbek2.csv`）
