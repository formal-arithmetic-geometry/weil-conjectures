## Worker report

Item: `lem-sfb-normal-curve-separable-point-smooth`, group NE, 2026-10-22.

The module `Sheaf.AlgebraicGeometry.Curve.NormalSeparablePointSmooth` states
`AlgebraicGeometry.IsIntegralCurve.isDiscreteValuationRing_and_smoothAt_of_isIntegrallyClosed`.
Its only theorem has proof `sorry`; there are no new definitions or helper theorems.
The node changes only in `lean`. No statement correction or dispute is needed.

I read the node, all six statement dependencies and their recorded declarations/docstrings,
and all proof-dependency records. I read Stacks `varieties.tex`,
`lemma-regular-point-on-curve` (Tag 0B8Y), including its proof. The node is precisely
its implications (2) to (3) and (6), with the explicit finite-separable hypothesis.
The theorem's docstring carries the node's six proof steps and their dependency IDs.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| Arbitrary field k | `{k : Type u} [Field k]` |
| k-scheme with its structure map | `{X : Scheme.{u}} (f : X ⟶ Spec (.of k))` |
| X a curve: integral, separated, finite type, dimension exactly one | `[IsIntegralCurve f]`; its parent `IsVariety f` supplies `IsIntegral X`, `IsSeparated f`, `LocallyOfFiniteType f` and `QuasiCompact f`, and its dimension field says `topologicalKrullDim X = 1` |
| A point x | `(x : X)` |
| x closed | `(hx : IsClosed ({x} : Set X))` |
| Local ring at x | `X.presheaf.stalk x` |
| The local ring is an integrally closed domain | `[IsIntegrallyClosed (X.presheaf.stalk x)]`; `IsDomain` already follows from `IsIntegralCurve f` through `IsVariety.isIntegral` and Mathlib's integral-scheme stalk instance, so it is not an extra binder |
| Residue field κ(x) | `X.residueField x`, defined as `IsLocalRing.ResidueField (X.presheaf.stalk x)` |
| κ(x)/k is the extension induced by f | `(f.residueFieldAlgebraMap x).toAlgebra`, passed explicitly; no arbitrary algebra instance |
| This extension is finite | `(hfin : (f.residueFieldAlgebraMap x).Finite)`; `RingHom.Finite` means finite as a module for this exact map, hence finite-dimensional over k |
| This extension is separable | `(hsep : @Algebra.IsSeparable k (X.residueField x) _ _ (f.residueFieldAlgebraMap x).toAlgebra)` |
| Local ring is a discrete valuation ring | `IsDiscreteValuationRing (X.presheaf.stalk x)` |
| Structure morphism smooth on some open neighbourhood of x | `∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)` |
| Both conclusions | The outer conjunction `∧` |
| k need not be perfect | No `PerfectField`, algebraic-closedness, or characteristic assumption |

The common universe `u` is the project's scheme/base-field convention. It allows any
field and curve in a universe containing both. There is no quantified test category
or small auxiliary universe restricting the theorem's scope. `autoImplicit` is disabled.

Dependency declarations used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs` (available through the public imports).
- `def-pc-curve`: `AlgebraicGeometry.IsIntegralCurve` and its parent
  `AlgebraicGeometry.IsVariety`, imported from
  `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap`,
  `Mathlib.AlgebraicGeometry.ResidueField`.
  The existing canonical base-field embedding
  `AlgebraicGeometry.Scheme.Hom.residueFieldAlgebraMap`, from
  `WeilConjectures.ZetaSeries`, is the composite of the field-to-prime-residue map,
  `Scheme.Spec.residueFieldIso` inverse, and `f.residueFieldMap x`.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable`,
  `Mathlib.FieldTheory.Separable`; separability already implies algebraicity.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`.

The recorded modules of all thirteen proof dependencies are imported without `public`
(shared modules serve more than one dependency). These include the affine-chart, finite-type,
localization, dimension, normal-to-regular, separable-residue smoothness,
principal-open and affine smoothness-comparison inputs. The normal-dimension-one
node's recorded `WeilConjectures.AlgebraicGeometry.Regular` module is retained as
the DAG records it. None of these imports closes an import cycle.

Edge cases checked before writing:

- A rational closed point of A¹ has a DVR stalk and lies in a smooth open.
- A non-rational closed point with finite separable residue field is allowed:
  there is no equality κ(x) = k or rationality assumption.
- Imperfect fields are allowed. For example A¹ over F_p(t) still satisfies the
  conclusion at any separable closed point. Regular nonsmooth points with purely
  inseparable residue fields are excluded by the explicit separability hypothesis.
- The generic point is not closed on an integral one-dimensional curve, so its
  field stalk does not contradict the DVR conclusion.
- Empty schemes and dimension-zero schemes do not satisfy `IsIntegralCurve`;
  the definition requires integrality and dimension exactly one.
- A singular cusp does not satisfy the integrally closed stalk hypothesis.
- Normality is required only at x; no normality assumption on all of X is added.
- Characteristic zero and positive characteristic are both retained.

Searches (prescribed `msearch.py NE lem-sfb-normal-curve-separable-point-smooth`):

- `leanfinder`, query: "A normal integral curve over a field is smooth at a closed
  point with finite separable residue field and its stalk is a discrete valuation ring".
  Eight hits: Weierstrass minimal/good reduction and its integral instance,
  `Algebra.IsSmoothAt`, residue-field field instance, `Algebra.smoothLocus`,
  the DVR cotangent-space criterion, and the integral-scheme domain-stalk instance.
  None states the item.
- `loogle`, query: `AlgebraicGeometry.IsIntegralCurve, IsDiscreteValuationRing, AlgebraicGeometry.Smooth`.
  Zero hits; the service does not index the project's `IsIntegralCurve`.
- `grep`, query: `separable.*smooth|smooth.*separable|normal.*curve`, directory
  `AlgebraicGeometry`. Five hits, all about normal forms of Weierstrass equations;
  no match.
- `leansearch`, query: "A normal curve over a field is smooth at a closed point
  with separable residue field". Eight hits: separable residue fields for formally
  unramified local rings, their maximal-ideal criterion, smooth locus, formally
  unramified field criterion, formally smooth extensions of perfect fields,
  `IsSeparable`, separable-closure recursor, and a Weierstrass normal-form lemma.
  None is the item.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, same conceptual patterns,
  followed by reading candidate `WeilConjectures.AlgebraicGeometry.Curve.NormalSmooth`:
  its theorems require a perfect base and normality at every point and conclude
  global relative-dimension-one smoothness, so they are not this statement.
  `Sheaf.AlgebraicGeometry.Curve.NormalSmoothProjectiveCompactification` is also
  a different global compactification statement over a finite field.
  `Sheaf.AlgebraicGeometry.Curve.TameRadicalNormalization` uses this item in its
  proof plan but does not state it.
- Literal node-ID search in `lean/WeilConjectures`: no match. Search for the proposed
  full declaration name across Mathlib, upstream and Sheaf: no match.

Validation: the prescribed `scompile.py` succeeded for both the sandbox and final
module-name passes, with no warnings or errors (2.5 s and 2.6 s). No local/global
build was run and no shared source file was edited. `deliver2.py --no-push` also
reported OK: preflight and per-file compilation passed, with exactly the module,
node record and worker report staged.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
