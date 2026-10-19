## Worker report

The module defines and states `AlgebraicGeometry.exists_valuation_marked_strictification` in
`Sheaf.AlgebraicGeometry.Curve.ValuationMarkedStrictification`.  It uses the landed
`AlgebraicGeometry.MultipointedCurve`, `MultipointedCurve.IsSemistable`,
`MultipointedCurve.Hom.IsEtaModification`, and
`MultipointedCurve.Hom.curveBaseChange`/`markingBaseChange`, together with
`AlgebraicGeometry.IsStrictlySemistableCurve`.

The hypotheses are rendered as follows.  The separably closed field is
`(K : Type u) [Field K] [IsSepClosed K]`.  The valuation ring and finite chain condition
are `(V : ValuationSubring K) [Finite (PrimeSpectrum V)]`; `ValuationSubring` supplies the
valuation-ring inclusion into `K`, and finiteness of `PrimeSpectrum V` is the finite-chain
hypothesis recorded in the node.  The base curve and marking are
`Y : MultipointedCurve (Spec (.of V))`; semistability is `hY : Y.IsSemistable`.  The
smooth generic curve is
`hgeneric : Smooth (pullback.snd Y.x (Spec.map (CommRingCat.ofHom V.subtype)))`, and the
etale generic marking is the analogous `hmarking` for `Y.d`.

The conclusion is an existential strict model `Z : MultipointedCurve (Spec (.of V))` and a
compatible pair map `f : Z.Hom Y`.  Strict semistability is
`IsStrictlySemistableCurve Z.x`; semistability is `Z.IsSemistable`; and the pair map is an
eta-modification through
`f.IsEtaModification (Spec.map (CommRingCat.ofHom V.subtype))`.  The latter expands to
proper curve and marking maps, schematically dense isomorphism opens, and isomorphisms on
both generic base changes, so it records the node's generic-pair identity condition under
the canonical generic-fibre identifications.  The source and marking maps in
`MultipointedCurve.Hom` enforce compatibility with the base and the closed marking.

Dependency declarations used:

* `AlgebraicGeometry.MultipointedCurve` from
  `Sheaf.TraceFormula.MultipointedCurve`;
* `AlgebraicGeometry.MultipointedCurve.IsSemistable`,
  `AlgebraicGeometry.MultipointedCurve.Hom.IsEtaModification`,
  `MultipointedCurve.Hom.curveBaseChange`, and
  `MultipointedCurve.Hom.markingBaseChange` from
  `Sheaf.AlgebraicGeometry.MultipointedCurveModification`;
* `AlgebraicGeometry.IsStrictlySemistableCurve` from
  `Sheaf.AlgebraicGeometry.StrictlySemistableCurve`;
* `AlgebraicGeometry.Smooth` and `AlgebraicGeometry.Etale` from Mathlib's smooth and
  etale morphism modules;
* `ValuationSubring`, `IsSepClosed`, `Spec`, and `PrimeSpectrum` from Mathlib.

Searches made: `msearch.py Q26 lem-trf-valuation-marked-strictification leanfinder` for
strictification of a semistable marked curve (no matching declaration; only Weierstrass
curve results); `msearch.py ... leansearch` for a proper strict semistable modification
(no matching declaration); `msearch.py ... loogle '"semistable"'` (zero hits); and
`msearch.py ... grep 'semistable|multipointed|strictification' AlgebraicGeometry`
(zero hits in Mathlib).  Repository searches with `rg` found the existing project
interfaces listed above and no theorem with this item's conclusion.

Edge cases checked against the definitions and source: `MultipointedCurve` permits empty
marking and empty curve/fibres; no separatedness or properness is imposed on `Y`; the
finite spectrum condition includes a field valuation ring; `IsStrictlySemistableCurve`
allows empty fibres; and the generic smooth/etale hypotheses are stated independently.
The theorem proof is intentionally `sorry` as required for stage 2.

## Second reading by Q26

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
