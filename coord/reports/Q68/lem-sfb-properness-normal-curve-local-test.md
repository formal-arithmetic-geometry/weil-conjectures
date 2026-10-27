## Worker report

The module `Sheaf.AlgebraicGeometry.PropernessNormalCurveLocalTest` states
`AlgebraicGeometry.isProper_iff_normal_curve_local_test`, with exactly one postponed
proof (`sorry`) and no new definitions. The item's statement and all other original
node fields are unchanged; only its `lean` record is supplied. No dependency repair,
new node, or statement correction is needed.

Source read: `literature/stacks-project/limits.tex`,
`lemma-essentially-finite-type-criterion-proper` (Tag 0GWX), including the two
diagrams and the dimension-one footnote. This specializes the Nagata base to a
field; it keeps the C,U,c diagrams, rather than quantifying over arbitrary
fraction-field maps. Also read the entire statement, docstring and signature of
`normal_curve_universal_closedness_test`, whose existing generic-map encoding is
used here without adding a new notion.

Hypothesis and clause correspondence:

- The arbitrary field k is `(k : Type u) [Field k]`.
- The given k-schemes X,Y are `(X Y : Scheme.{u})`, with explicitly supplied structure
  maps `p : X ⟶ Spec (CommRingCat.of k)` and `q : Y ⟶ Spec (CommRingCat.of k)`.
  Their local finite type assumptions are `[LocallyOfFiniteType p]` and
  `[LocallyOfFiniteType q]`. No global finite type or quasi-compactness is imposed
  on these structure maps.
- The quasi-compact k-morphism is `(f : X ⟶ Y) [QuasiCompact f]`, with
  `(hf : f ≫ q = p)` expressing that it is over k.
- The equivalence has left side `IsProper f` and right side the universal local
  extension condition. Properness uses the recorded Mathlib class; its universal
  closedness implies quasi-compactness, so it agrees with the node's definition.
- Every integral finite-type k-test scheme is quantified as `(C : Scheme.{u})`
  with structure morphism s, `[IsIntegral C] [LocallyOfFiniteType s]
  [QuasiCompact s]`. The last two instances together mean finite type.
- Normality is precisely the given stalk condition
  `∀ z : C, IsDomain (C.presheaf.stalk z) ∧ IsIntegrallyClosed (C.presheaf.stalk z)`.
  This uses the dependency's inline normal-domain interface, not a new predicate.
- The point c is universally quantified; closedness is `IsClosed ({c} : Set C)`;
  the local dimension is `ringKrullDim (C.presheaf.stalk c) = 1`.
- U is quantified as an open with `(U : Set C) = {c}ᶜ`. Closedness ensures that this
  open exists; quantifying over all representations adds no hypothesis.
- The two maps u,v are called `a : U.toScheme ⟶ X` and `b : C ⟶ Y`.
  Their base compatibility is `a ≫ p = U.ι ≫ s` and `b ≫ q = s`;
  the commuting diagram is `a ≫ f = U.ι ≫ b`.
- R is literally the structure-sheaf stalk `C.presheaf.stalk c`, not a chosen DVR.
  Its fraction field is `FractionRing (C.presheaf.stalk c)`, the localization at
  nonzero divisors (nonzero elements because the stalk is a domain).
- The lift and its uniqueness are `∃! h : Spec (C.presheaf.stalk c) ⟶ X` with the
  conjunction of all required conditions. Its being over k is
  `h ≫ p = C.fromSpecStalk c ≫ s`. Its composite with f is the required restriction
  `h ≫ f = C.fromSpecStalk c ≫ b`.
- For the last clause, let j denote, in this report only, the spectrum map of the
  canonical algebra map from R to FractionRing R. The final equality is
  `pullback.snd U.ι (j ≫ C.fromSpecStalk c) ≫ j ≫ h =
   pullback.fst U.ι (j ≫ C.fromSpecStalk c) ≫ a`.
  Thus the generic restrictions agree after the canonical pullback with U.
  This is the same encoding as the already stated universal-closedness criterion.
  It is equivalent to equality on Spec F: on an integral C the generic point
  of Spec R maps to the generic point of C; it cannot be c since dim R = 1.
  Therefore Spec F maps entirely into U, and the pullback projection to Spec F
  is an isomorphism. The pullback condition loses no part of the generic spectrum,
  introduces no arbitrary map, and has no extra assumption about a factorization.
- Neither X nor Y has an integral, normal, or reducedness hypothesis. All integral
  and normal hypotheses occur only inside the quantification over test curves.

Recorded statement-dependency declarations used, with their source signatures and
docstrings read:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs (imported transitively).
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  Mathlib.AlgebraicGeometry.Scheme; extends a locally ringed space with affine charts.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType` and `QuasiCompact`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and Morphisms.QuasiCompact.
- `def-weil-proper-morphism`: `IsProper`, Mathlib.AlgebraicGeometry.Morphisms.Proper;
  includes `IsSeparated`, `UniversallyClosed`, and `LocallyOfFiniteType`.
- `def-pc-integral-scheme`: `IsIntegral`, Mathlib.AlgebraicGeometry.Properties;
  nonempty with domain sections on nonempty opens.
- `def-weil-pbc-normal-ring`: `IsIntegrallyClosed` and `IsDomain`,
  Mathlib.RingTheory.IntegralClosure.IntegrallyClosed; the recorded normal-domain
  interface is their conjunction, used on every stalk as the item requests.
- `def-weil-pbc-krull-dimension-ring`: `ringKrullDim`,
  Mathlib.RingTheory.KrullDimension.Basic; dimension of the prime spectrum.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme.

Other canonical constructions reused: `Scheme.fromSpecStalk` (Mathlib's stalk
morphism, with recorded properties in
WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism), `FractionRing`
and its `algebraMap` (Mathlib.RingTheory.Localization.FractionRing), and
`pullback.fst`/`pullback.snd` (Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback).
The FunctionField import provides the established integral-scheme stalk-domain
instance. The explicitly imported proof-dependency modules follow all six steps
of the unchanged DAG proof; that proof is reproduced in the theorem docstring.
In particular the existing proof input is
`AlgebraicGeometry.normal_curve_universal_closedness_test` in
Sheaf.AlgebraicGeometry.NormalCurveUniversalClosednessTest; no copy is defined.

Edge cases checked before writing:

- Empty X and empty Y are allowed. No Nonempty constraint is introduced on either.
  Empty X yields no punctured-curve maps, consistent with its proper map to Y.
- Empty C is already excluded by the node's integral condition. A zero-dimensional
  integral C cannot supply a stalk of dimension one, so its test is vacuous, as
  required. The closed point in a dimension-one test differs from its generic point.
- Nonreduced X,Y and arbitrary positive characteristic are retained. No smoothness,
  perfectness, algebraic closedness, or separation assumption is added.
- Non-affine C and X,Y not quasi-compact over k remain covered.
- The single explicit universe u places the field, X,Y and test schemes together;
  it is the established scheme-universe convention, not an independent potentially
  smaller test universe. The theorem is polymorphic in u.
- Uniqueness is uniqueness of h satisfying the full conjunction. Proof fields are
  propositions, so no additional structure is being chosen for a k-morphism.

Searches actually run (msearch.py Q68 lem-sfb-properness-normal-curve-local-test):

- LeanFinder: "Properness of a quasi compact morphism between schemes locally of
  finite type over a field tested by unique lifts from local rings of normal
  integral finite type curves". Eight hits, including IsProper.of_valuativeCriterion,
  IsProper, isProper_eq, and normalization quasi-compactness; none is the restricted
  C,U,c criterion.
- Loogle: `"ValuativeCriterion", "IsProper"`. Two hits:
  IsProper.of_valuativeCriterion and IsProper.eq_valuativeCriterion. Both use the
  general valuative criterion, not this restricted family of diagrams.
- Mathlib grep via msearch: `normal.*curve.*proper|proper.*normal.*curve`, subdirectory
  AlgebraicGeometry: zero hits.
- Direct rg in lean/WeilConjectures and lean/Sheaf:
  `normal_curve|NormalCurve|properness_normal|proper.*normal.*curve|normal.*curve.*proper`.
  Found the related NormalCurveUniversalClosednessTest, proper-birational curve
  results, and the AffinePropernessFormalArcTest citer. None states this theorem.
- Direct grep of `lem-sfb-properness-normal-curve-local-test` in
  lean/WeilConjectures: no match.

Validation: scompile.py compiled the draft both as a sandbox and at its actual
library module path, cleanly (2.1s/2.2s). The final import list and delivery are
checked again by the required dry run. No statement dispute was found.

## Second reading by Q68

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
