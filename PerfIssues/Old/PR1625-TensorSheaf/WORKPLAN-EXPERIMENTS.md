# Workplan experiments: PR #1625

Case: `P1625-result-lhs`, declaration
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison_app_app_fac`.

This is the positive D3 control. The stored value checks in 335 ms, while the
final inferred/declared type conversion takes 95.520 s. The exact pair is a
shared `Eq` whose left side contains `CategoryStruct.comp`; argument 5 is a
`NatTrans.app` pair and its argument 6 is the differing concrete major
premise. The type-preserving `NatTrans` major-premise alignment changes the
same conversion from 95.869 s to 0 ms; the reverse control is 93.567 s.
The retained before run used 188.18 s CPU, 189.31 s wall, and 8,245,292 KB
peak RSS.

Probe retained under [`G3B-NatTransMajor.lean`](probes/wp/G3B-NatTransMajor.lean).
The aligned term has a structurally identical checked result type, so the
theorem obligation is preserved. This confirms accessor major-premise
alignment as a recurring mechanism and is not a new baseline.
