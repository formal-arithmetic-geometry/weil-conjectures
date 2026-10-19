## Worker report

The module `lean/Sheaf/AlgebraicGeometry/AlterationRelativeCurvePreparation.lean`
states `AlgebraicGeometry.alteration_relative_curve_preparation` as a theorem with a
`sorry` proof.  It uses the corrected base alternative `IsField A ∨ ...`, where the
trait alternative binds `hD : IsDomain A`, a `Nonempty` discrete valuation ring
structure over that domain, and `IsExcellent A`.

The theorem renders the hypotheses as follows.

* `A : Type u` with `[CommRing A]` is the coefficient ring.  The base hypothesis is
  `IsField A ∨ ∃ hD : IsDomain A, Nonempty (@IsDiscreteValuationRing A inferInstance hD)
  ∧ IsExcellent A`.
* `S : Scheme.{u}`, `eS : S = Spec (.of A)`, `s : S`, and
  `hs : IsGenericPoint s Set.univ` encode the field spectrum or excellent integral
  trait and its generic point.
* `X : Scheme.{u}` and `p : X ⟶ S` carry `[IsIntegral X]`, `hp : IsProper p`,
  `hdom : DenseRange p.base`, and
  `hft : LocallyOfFiniteType p ∧ QuasiCompact p`, rendering integral, proper,
  dominant, finite type `X → S`.
* `d : ℕ`, `hd : topologicalKrullDim (p.fiber s) = (d : WithBot ℕ∞)`, and
  `hdpos : 1 ≤ d` render `d = dim X_s ≥ 1`.
* `Z : Scheme.{u}`, `i : Z ⟶ X`, `[IsClosedImmersion i]`, and
  `hZ : ∀ ξ : X, IsGenericPoint ξ Set.univ → ξ ∉ Set.range i.base` render the closed
  nowhere-dense boundary (the underlying closed set avoids every generic point).

The conclusion is the existential tuple
`∃ (X₁ Y : Scheme.{u}) (h : X₁ ⟶ X) (q : Y ⟶ S) (f : X₁ ⟶ Y), ...`.
Its clauses are rendered in order by:

* `IsIntegral X₁` and `∀ U : X₁.Opens, IsAffineOpen U → IsExcellent Γ(X₁, U)`;
* `IsIntegral Y` and the analogous affine-coordinate excellence predicate;
* `IsProper h`, `DenseRange h.base`, and
  `∃ U : X.Opens, Dense (U : Set X) ∧ IsFinite (h ∣_ U)`, expressing proper,
  dominant, generically finite `h` (finite over a dense open);
* `IsHProjective q`, `IsProper q`, `DenseRange q.base`, and
  `LocallyOfFiniteType q ∧ QuasiCompact q`, expressing projective, proper, dominant,
  finite type `Y → S`;
* `topologicalKrullDim (q.fiber s) = ((d - 1 : ℕ) : WithBot ℕ∞)`;
* `IsProper f ∧ DenseRange f.base`;
* `h ≫ p = f ≫ q`, the assertion that the structure map of `X₁` factors through
  `Y`;
* for every `y : Y` with `IsGenericPoint y Set.univ`,
  `SmoothOfRelativeDimension 1 (f.fiberToSpecResidueField y) ∧
  IsIntegral (f.fiber y)`, so the generic fibre is a smooth irreducible curve;
* the reduced inverse boundary is represented by
  `((Limits.pullback h i).nilradical.subschemeι ≫ Limits.pullback.fst h i) ≫ f`.
  Its fibre over `y` is required to satisfy `IsFinite` and `Etale` after
  `fiberToSpecResidueField`; this permits the empty finite étale fibre.

The declaration records the following dependency declarations.  Properness uses
`AlgebraicGeometry.IsProper` from `Mathlib.AlgebraicGeometry.Morphisms.Proper`;
finite type uses `AlgebraicGeometry.LocallyOfFiniteType` and
`AlgebraicGeometry.QuasiCompact` from the corresponding Mathlib modules;
integrality uses `AlgebraicGeometry.IsIntegral` from
`Mathlib.AlgebraicGeometry.Properties`; excellence uses
`IsExcellent` from `Sheaf.RingTheory.ExcellentRing`; discrete valuation rings use
`IsDiscreteValuationRing` from `Mathlib.RingTheory.DiscreteValuationRing.Basic`;
smoothness uses `AlgebraicGeometry.Smooth`/`SmoothOfRelativeDimension` from
`Mathlib.AlgebraicGeometry.Morphisms.Smooth`; étaleness uses
`AlgebraicGeometry.Etale`; reduction uses `Scheme.nilradical`,
`IdealSheafData.subscheme`, and `IdealSheafData.subschemeι`; fibres use
`Scheme.Hom.fiber` and `fiberToSpecResidueField`; dimension uses
`topologicalKrullDim`; closed immersions use `AlgebraicGeometry.IsClosedImmersion`;
finite morphisms use `AlgebraicGeometry.IsFinite`; projectivity uses the upstream
`AlgebraicGeometry.IsHProjective`; and generic points use `IsGenericPoint`.
The proof dependencies are the relative-curve factorization, generic smooth-boundary
preparation, projective-implies-proper, and closed-irreducible-dimension/trdeg nodes;
the statement module imports only the definition modules needed to elaborate its
signature, leaving the postponed proof imports to stage 3.

I checked the edge cases `d = 1` (the dimension expression becomes zero), an empty
boundary `Z`, both the field and trait base alternatives, and the possibility that the
finite étale generic boundary fibre is empty.  The explicit universe `u` is shared by
rings, schemes, and morphisms, and `set_option autoImplicit false` binds every symbol.

Searches made: `msearch.py ... grep 'alteration_relative_curve_preparation'
WeilConjectures/` returned zero hits; `msearch.py ... leanfinder 'Preparation of an
alteration problem as a relative curve'` returned only generic smoothness and rational
map declarations, with no matching alteration theorem.  I also searched the project
and source with `rg` for alteration, generic-smooth, and boundary-preparation names.
The existing reviewed project source was copied verbatim; no new node, dependency
repair, or statement correction was needed.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
