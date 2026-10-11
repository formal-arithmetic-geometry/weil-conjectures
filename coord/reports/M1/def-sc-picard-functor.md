## Worker report

The module defines `AlgebraicGeometry.curvePicardFunctor`, the fppf sheafification
of the Picard presheaf for a smooth projective geometrically integral curve, by
using `AlgebraicGeometry.picardFunctor`. It also defines
`AlgebraicGeometry.curvePicardFunctorDegree`, the fppf sheafification of the
fibrewise degree-`d` subfunctor, using `AlgebraicGeometry.picardFunctorDegree`.

The field hypothesis is rendered by `[Field k]`. The curve hypothesis is the
explicit structure morphism `f : C ⟶ Spec (.of k)` with
`[f.IsSmoothProjectiveCurve]`, which supplies smoothness, projectivity, and the
curve conditions. Geometric integrality is rendered by `[GeometricallyIntegral f]`.
The Picard functor clause is exactly `picardFunctor f`, whose definition is the
fppf sheafification of `picardPresheaf f`. The degree clause is exactly
`picardFunctorDegree f d`, whose defining subfunctor requires fibrewise degree
identically `d` on every field-valued point. No representability, openness, or
closedness claim is introduced.

Dependencies used: `WeilConjectures.AlgebraicGeometry.Picard.Defs`, through the
recorded declaration `AlgebraicGeometry.picardFunctor`; and
`WeilConjectures.AlgebraicGeometry.Picard.Jacobian`, through
`AlgebraicGeometry.picardFunctorDegree`. The smooth-projective curve class is
`Sheaf.AlgebraicGeometry.SmoothProjectiveCurve`, declaration
`AlgebraicGeometry.Scheme.Hom.IsSmoothProjectiveCurve`. Geometric integrality is
Mathlib's `AlgebraicGeometry.GeometricallyIntegral`.

Edge cases checked: `d = 0` gives the degree-zero sheaf; an empty test scheme
makes the fibrewise condition vacuous, as in `picardSubfunctorDegree`; arbitrary
field extensions are covered by the field-valued-point quantifier in the
upstream degree subfunctor. Universe `u` is shared by `k`, `C`, and the site.

Searches: `rg -n 'Picard|picardFunctor'` in `WeilConjectures` and `lean/Sheaf`,
which found the generic `picardFunctor` and `picardFunctorDegree`; inspection of
their declarations showed that they provide the general constructions but not
this specialized curve statement. `msearch.py leanfinder`/`loogle` searches for
smooth-projective Picard functors found no declaration matching the specialized
notion. Mathlib grep found no specialized curve Picard functor.

## Earlier second reading (a previous round; superseded)

Reading the node and module together: the field, smooth-projective, and
geometrically-integral hypotheses are all present as explicit binders. The
Picard functor is the recorded fppf sheafification, and `Pic^d` is defined by
the recorded degree subfunctor sheafification. The module makes no
representability or geometric-subfunctor claim, so every clause of the node is
accounted for.

## Second reading by M1

I reread the node statement (source place: blueprint node `def-sc-picard-functor`,
order 447) as the following list.  It introduces a field `k`; a smooth projective
curve `C` over `k`; geometric integrality of `C` over `k`; the Picard functor
`Pic_{C/k}`; its fppf sheafification construction from the presheaf
`R ↦ Pic(C ×_k Spec R)`; the fibrewise degree on residue-field fibres; and, for
each integer `d`, the degree subfunctor `Pic^d_{C/k}`.  It concludes only these
definitions and explicitly makes no representability, openness, or closedness
claim.

The field is rendered by `[Field k]` in `PicardFunctor.lean`.  The curve and its
smooth/projective/curve hypotheses are rendered by the explicit morphism
`f : C ⟶ Spec (.of k)` and `[f.IsSmoothProjectiveCurve]`; this class extends
`IsCurveOverField`, `Smooth`, and `IsProjective` in
`Sheaf.AlgebraicGeometry.SmoothProjectiveCurve`.  Geometric integrality is the
Mathlib class `[GeometricallyIntegral f]`.  The Picard functor clause is rendered
by `curvePicardFunctor f := picardFunctor f`; the dependency declaration is the
fppf sheafification of `picardPresheaf f`.  The degree clause is rendered by
`curvePicardFunctorDegree f d := picardFunctorDegree f d`; the dependency's
`picardSubfunctorDegree` quantifies over every field-valued point and requires
the fibre degree to equal `d`.  Thus every object, hypothesis, and conclusion
clause is present with the same quantifier scope.  The Lean declarations are
definitions with concrete data and contain no `sorry`.

Edge cases checked: `d = 0` gives the degree-zero sheaf; on an empty test scheme
the fibrewise condition is vacuous, as in `picardSubfunctorDegree`; arbitrary
field extensions are included by its field-valued-point quantifier; the shared
universe `u` covers `k`, `C`, and the fppf site; no zero or characteristic
hypothesis is added.

Searches were repeated with `rg` over `WeilConjectures`, `lean/Sheaf`, and Mathlib,
and with `msearch.py` LeanFinder/Loogle queries for smooth-projective Picard
functors.  Only the generic `picardFunctor` and `picardFunctorDegree` declarations
were found; neither states this specialized curve definition, so the module is
needed.  No mismatch was found and no source or node field was changed.  The
module compiles cleanly with `scompile.py`.

## Reviewer fix (R-dpf1133, stage 2)

The delivered module `Sheaf.AlgebraicGeometry.PicardFunctor` only restated source definitions:
`curvePicardFunctor f := picardFunctor f` and `curvePicardFunctorDegree f d := picardFunctorDegree f d`,
with `[f.IsSmoothProjectiveCurve] [GeometricallyIntegral f]` binders the bodies never use. A second
name for an existing notion fails H4/H12, and every citer (`IsJacobian` of def-sc-jacobian,
`exists_jacobian_pullback`, `exists_commGrpObj_representableBy_picardFunctorDegree`) already writes
Pic^0_{C/k} as `picardFunctorDegree f 0`. The record is switched to `existing: true`:
Pic_{C/k} = `AlgebraicGeometry.picardFunctor f` (Picard.Defs, also the record of def-pc-picard-functor),
Pic^d_{C/k} = `AlgebraicGeometry.picardFunctorDegree f d` (Picard.Jacobian, the fppf sheafification of
the fibrewise-degree-d subpresheaf `picardSubfunctorDegree`). The module is left out.
