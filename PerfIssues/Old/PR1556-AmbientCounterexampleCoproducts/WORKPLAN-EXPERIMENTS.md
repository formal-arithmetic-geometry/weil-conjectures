# Workplan experiments: PR #1556

Case: `P1556-closing-proof`, declaration
`not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety`.

This is the positive B4/D4 control. The expensive site is the generated
`congr` proof-proposition domain: the exact `Eq` proposition conversion is
50.090 s. Its left `CategoryStruct.comp` contains a `NatTrans.app` with a
concrete `Iso.hom` major premise. Replacing only that major premise with the
definitionally equal left term changes the same comparison from 49.548 s to
0 ms; the checked result type is structurally preserved. The reverse control
is 50.585 s.

Probe retained under [`G3B-ClosingNatMajor.lean`](probes/wp/G3B-ClosingNatMajor.lean),
with the surrounding proof-domain probes copied under `probes/wp/`.
The enclosing `Exists.intro`, `id`, and `Eq.mp` domains are immediate; the
cost descends into the generated proposition. This is a validated accessor-
induced dependent-proposition conversion, not a repeated baseline.
