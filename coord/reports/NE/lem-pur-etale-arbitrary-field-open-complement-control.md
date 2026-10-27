## Worker report

The module Sheaf.AlgebraicGeometry.ArbitraryFieldOpenComplementControl states
AlgebraicGeometry.Scheme.exists_uniform_dimension_bound_and_hasOpenComplementCondition.
Its sole theorem has proof `sorry`; there are no new definitions, helper theorems,
dependency repairs, or statement corrections. The original statement and split are unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Any field k is `(k : Type u) [Field k]`. There is no separable-closedness,
  algebraic-closedness, characteristic restriction beyond invertibility, or absolute
  cohomological-dimension assumption.
- A finite commutative ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  The coefficient universe is the recorded ordinary small-etale encoding, and imposes
  no mathematical restriction on finite rings.
- `N : ℕ`, `hN : 1 ≤ N`, and `hunit : IsUnit (N : k)` give precisely the positive
  invertible integer. `hkill : (N : A) = 0` means NA = 0: multiplication by the
  cast integer annihilates every element; conversely apply annihilation to 1.
- `aT : T ⟶ Spec (.of k)` and `[LocallyOfFiniteType aT] [QuasiCompact aT]`
  make T a finite-type k-scheme. `j : W ⟶ T`, `[IsOpenImmersion j]` and
  `[QuasiCompact j]` give the quasi-compact open k-immersion. W's structure morphism
  is `j ≫ aT`; choosing it this way encodes compatibility over k without extra data
  or an extra hypothesis. No separatedness is required.
- The first conjunct `∃ d : ℕ, ...` asserts the required existence of a nonnegative
  uniform field-extension dimension bound. The quantifiers over `(L : Type u)
  [Field L]`, every `s : Spec L ⟶ Spec k`, and every `IsPullback` square describe
  all field base changes W_L, independently of a chosen fibre-product representative.
  The conclusion is `topologicalKrullDim P ≤ (d : WithBot ℕ∞)`. This is the same
  universe and cartesian-square interface as the recorded dimension-bound theorem.
- The second conjunct quantifies over EVERY natural d satisfying this bound, rather
  than merely the witness of the first conjunct. Its conclusion is the recorded
  `HasOpenComplementCondition A j (2 * d)`, verbatim the equivalent formulation
  explicitly requested by the node.
- Unfolding that predicate gives (1) every module sheaf M on W.smallEtaleTopology,
  every integer q with `(2 * d : ℤ) < q`, and `IsZero` of its higher direct image;
  (2) every constructible F and every integer q, constructibility of its higher
  direct image. M has no constructibility hypothesis. Higher images are exactly
  `DerivedCategory.Plus.homologyFunctor` applied to `Etale.rightDerivedLowerStarPlus`
  of `DerivedCategory.Plus.singleFunctor` in degree zero, on ordinary constant-A
  module sheaves. The same constant 2d occurs in both clauses through this predicate.

Dependency declarations read and reused:

- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: AlgebraicGeometry.LocallyOfFiniteType;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: AlgebraicGeometry.QuasiCompact.
  The scheme-conventions node is a convention-only record, introducing no declaration.
- WeilConjectures.AlgebraicGeometry.DerivedCategories and its public import
  WeilConjectures.SixFunctors.Etale.Derived.Coefficients:
  AlgebraicGeometry.Etale.DerivedCategoryModule, with the ordinary sheaf category.
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs:
  AlgebraicGeometry.Etale.lowerStar; its extension module
  WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence:
  AlgebraicGeometry.Etale.rightDerivedLowerStarPlus. These are publicly imported by
  the open-complement condition module.
- WeilConjectures.Mathlib.Topology.KrullDimension: topologicalKrullDimAt and its
  public Mathlib.Topology.KrullDimension import: topologicalKrullDim. Only the global
  dimension is needed here.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: pullback and its
  projections, expressed invariantly by IsPullback as in the proof prerequisite.
- WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes:
  AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible, and the public
  sheaf predicate AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf from
  WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf.
- Sheaf.AlgebraicGeometry.OpenComplementCondition:
  AlgebraicGeometry.Scheme.HasOpenComplementCondition, whose full definition was read.

Every stated proof dependency is imported. The two Mathlib leaves for finite-type
open immersions and finite-type composition are already in the public finite-type
module. The remaining proof imports are BaseChangeDimension,
Sites.TorsionAbelianDirectImageVanishing,
SmoothBaseChange.HigherDirectImageForgetComparison, and
FiniteTypeDirectImageConstructibility. The docstring reproduces all four proof steps
with these node names, including the torsion argument and coefficient forgetting.

Sources read: current main-20261015 sk-prop-sf-rf-shriek-preservation proof's
closed-immersion paragraph, and Stacks etale-cohomology.tex lemma-finite-cd
(Tag 0F10), especially its arbitrary-field relative clause (1). The quantitative
2d bound comes from the existing torsion-abelian dimension-bound prerequisite,
not from a claim that Tag 0F10 itself states the numerical constant.

Edge cases checked: empty W has dimension bottom and only zero module sheaves;
empty T forces empty W, and neither is excluded by any binder. d = 0 yields
vanishing in positive degrees. The zero coefficient ring is allowed; N = 1
forces it, and no Nontrivial A instance is imposed. The identity open immersion
is allowed. Negative degrees are included in the constructibility clause. Larger
admissible bounds remain covered by the universal quantifier. Arbitrary fields
such as R and fields of unbounded absolute torsion cohomological dimension are
not excluded. All variables and the universe u are explicitly bound; autoImplicit
is false, and the signature contains no let/show bindings.

Searches executed with msearch.py for this group/item:

- leanfinder: "A quasi compact open immersion of finite type schemes over any field
  has constructible higher direct images of finite coefficient etale sheaves and
  vanishing above twice the geometric dimension". Eight results, including
  Scheme.Hom.isConstructible_image and isLocallyConstructible_image, concern
  constructible subsets or scheme morphisms, not this sheaf statement.
- loogle: "AlgebraicGeometry.IsOpenImmersion, AlgebraicGeometry.LocallyOfFiniteType".
  Six results; locallyOfFiniteType_of_isOpenImmersion supplies the geometric
  prerequisite, none states the required higher-direct-image theorem.
- grep: "higherDirectImage|HasOpenComplementCondition". Zero Mathlib hits.
- leansearch: "Uniform cohomological dimension bound and constructibility of higher
  direct images of finite coefficient etale sheaves for a quasi compact open
  immersion over an arbitrary field". Eight results concern open immersions,
  structure-sheaf modules and scheme morphisms, not the assertion here.
- rg in both lean/WeilConjectures and lean/Sheaf for
  HasOpenComplementCondition|openComplementCondition|forall_field_dimension_le and
  the item id found the predicate, the torsion-abelian bound, and narrower existing
  open-complement statements. OpenComplementKnown and OpenComplementUnconditional
  require separable closedness or different coefficient hypotheses. Upstream
  openComplementCondition_two_mul requires a dimension bound on T, whereas this
  item uses an arbitrary uniform bound on W_L and also asserts its existence.
  It is not an exact existing match. The proposed full theorem name was checked
  against both project roots, Mathlib, and dag/lean_names_upstream.json: no match.

No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by NE

This is the dispatcher's required author's self-check; independent maintainer review
follows delivery. No other agent was started, as instructed. Re-read the original
node and final signature together: k, A, N, finite-type aT, and quasi-compact open j
match all hypotheses. The composite structure map avoids adding a redundant
compatibility hypothesis. The first conjunct retains existence and emptiness; the
second retains every admissible d, not only a chosen witness. Re-opened the full
HasOpenComplementCondition definition to check arbitrary M, every constructible F,
all integer degrees, ordinary module coefficients and the bound 2d. All match.
No statement or dependency repair was necessary and nothing was weakened.
