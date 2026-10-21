## Worker report

The module `Sheaf.Paper.FiniteFieldClosedSupport` states
`AlgebraicGeometry.Scheme.finiteFieldClosedSupport_bounded_constructible`.
Its only theorem has proof `sorry`. There are no new definitions, dependency repairs,
statement corrections, or disputed statements. Only the item's `lean` field changes.

Source read: Bhatt--Scholze, *The pro-etale topology for schemes*, Lemma 6.7.11,
including its closed-immersion support-triangle proof, from the repository PDF
(`pdftotext` to stdout, lines 3757--3774). The finite-field specialization is R=A,
m=0. The declaration docstring contains all six DAG proof steps and their dependencies.

Clause-by-clause correspondence:

- The prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- The base field and its positive characteristic are `(k : Type u) [Field k]`,
  `(p : ℕ) [CharP k p]`, and `_hp : 0 < p`. The different characteristics are
  `_hpℓ : p ≠ ℓ`. No finiteness, perfection, algebraic-closure, or cohomological
  dimension assumption is placed on k.
- The finite coefficient field is `(A : Type u) [Field A] [Finite A] [CharP A ℓ]`.
- Z and T are arbitrary `Scheme.{u}` objects with their `Over (Spec (.of k))`
  instances. Each structure morphism has both `LocallyOfFiniteType` and
  `QuasiCompact`, exactly the recorded definition of finite type.
- The closed immersion is `(g : Z ⟶ T) [IsClosedImmersion g]`. The instance
  `[g.IsOver (Spec (.of k))]` says that g is a morphism of the stated k-schemes.
- The ambient ordinary category is `proEtaleDerivedCategory T A`, transparently
  `DerivedCategory (proEtaleRingModules T (proEtaleConstantRing T A))` with the
  standard localization instance. This is the uncompleted category of modules
  over the intrinsic constant ring sheaf on `T.ProEt`, not the category of
  fixed-scalar sheaves with an etale-origin condition.
- B_A(T) is rendered inline as the conjunction `_hK`. The set of integers q
  for which `DerivedCategory.homologyFunctor ... q` of K is not `IsZero` is
  `Set.Finite`, exactly vanishing outside a finite interval of integers. Every
  cohomology sheaf satisfies `IsConstructibleProEtaleModuleSheaf T A`.
  This reuses the dependency's positive finite constructible locally closed
  stratification, canonical restriction, local constant module models and finite
  geometric stalks. Over a finite field, finite stalks mean finite-dimensional
  module values. If one wants a common stratification for all nonzero
  cohomology, there are only finitely many of them, so their finite
  stratifications have a finite common refinement; zero cohomology adds no
  constraint.
- Rg! is `(sfIntrinsicClosedUpperShriek g j A).rightDerivedFunctor`, with j
  written as `Scheme.Opens.ι` of the open subset `(Set.range g)ᶜ`. Its openness
  is the actual closed-embedding proof from g. This is exactly the functor
  appearing in `sfIntrinsicClosedAmbientAdjunction`, not an unspecified functor
  or an additional adjoint assumption. Its right-derived construction uses
  ordinary unbounded categories. Finite type over the field implies that T is
  Noetherian, so the recorded ambient adjunction applies to this complement.
- The conclusion repeats precisely the same finite cohomological support and
  constructibility conjunction on Z for this Rg! applied to K. Thus it states
  Rg!(B_A(T)) is contained in B_A(Z), with no assertion of a uniform amplitude.

Statement dependencies read and used (including full signatures/docstrings):

- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.ProEt` and `Scheme.ProEt.topology`.
- `def-weil-pbc-constant-sheaf`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf`; instantiated by the recorded `proEtaleConstantRing`.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, used through `proEtaleRingModules`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `DerivedCategory` and `HasDerivedCategory.standard`, used through
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory` from
  `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`.
- `def-weil-proetale-constructible-sheaf`:
  `Sheaf.Paper.ProEtaleConstructibleSheaf`,
  `AlgebraicGeometry.Scheme.IsConstructibleProEtaleModuleSheaf`.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and its morphisms.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, together with `QuasiCompact` from
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion` and `Scheme.Hom.isClosedEmbedding`.
- `lem-exc-proetale-closed-support`:
  `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient`,
  `AlgebraicGeometry.Scheme.sfIntrinsicClosedAmbientAdjunction`, and its actual
  functor from `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedSupport`,
  `AlgebraicGeometry.Scheme.sfIntrinsicClosedUpperShriek`.

All recorded proof-dependency modules are imported, using private imports for
proof-only modules. Mathlib matches for finite type/base change, Noetherianity,
constructible preimages, and cohomology of exact functors are available through
the imported Mathlib modules. `lem-sfb-finite-field-proetale-direct-image` has no
recorded Lean module at this reading, so its proof import cannot yet be added;
its role remains explicitly in step 4 of the proof docstring. No import cycle
was introduced. No proof dependency is silently replaced by a new hypothesis.

Searches for existing declarations:

- `msearch.py ... leanfinder`: "Exceptional inverse image for a closed immersion
  preserves bounded constructible complexes of finite field coefficient sheaves
  on the pro etale site". Eight hits concern constructible subsets and scheme
  immersions; none states this preservation result.
- `msearch.py ... loogle`: `"SheafOfModules", "constructible"`; zero hits.
- `msearch.py ... leansearch`: "Closed immersion exceptional inverse image
  preserves bounded constructible complexes of finite coefficients". Eight hits
  concern closed immersions and constructible subsets, not this theorem.
- `msearch.py ... grep`: the regular expression matching closedUpperShriek,
  ClosedUpperShriek, closedSupport or ClosedSupport adjacent to constructible
  or bounded; zero Mathlib hits.
- `rg -n` on both `lean/WeilConjectures` and `lean/Sheaf` with that expression,
  and the literal node id: upstream
  `ProEtale.boundedConstructible_closedUpperShriek_rightDerivedFunctor_obj`
  in `FiniteCoefficient/Derived/LocalizeConstructible.lean` is related, but its
  ambient objects are fixed `ModuleCat`-valued sheaves and its constructibility
  predicate is defined by etale origin. It is not the intrinsic category and
  intrinsic stratification predicate recorded by this item's dependencies.
  Other hits concern condensed or adic coefficients or finite-Tor adic stages.
  No existing declaration exactly states the node. The proposed new declaration
  name was separately searched in the project and `dag/lean_names_upstream.json`;
  no collision was found.

Edge cases checked before writing: Z empty gives the zero object; g the identity
has empty complement and Rg! identifies with identity; T empty is allowed; K zero
has empty nonzero-cohomology support; arbitrary negative and positive degrees
are retained because q ranges over all integers. No chosen uniform interval or
nonempty scheme is required. The coefficient field is necessarily nonzero,
exactly as the node requires. There is no restriction on the cohomological
dimension of k. The universe u is explicit everywhere; the existing framework
retains site objects in u+1, morphisms in u, and module values in u+1. There are
no auto-bound implicit variables or file-local definitions/notation/instances.

Validation: prescribed `scompile.py NS lem-sfb-finite-field-closed-support` passed
both the sandbox check and the actual module check with no warnings or errors.
An initial compile exposed field-notation resolution on a literal open subset;
using the explicit `Scheme.Opens.ι` resolved it without changing the statement.

## Second reading by NS

Second pass with the JSON statement and the complete Lean file open: ell prime,
p positive, both characteristic conditions, p different from ell, both finite-type
k-schemes and the closed k-immersion are present. The input and output use the
same intrinsic cohomology predicate. Finite support of integer-indexed cohomology
is equivalent to the finite-interval wording, and constructibility is precisely
the dependency declaration, with no etale-descent or finite-Tor condition added.
The chosen complement is an actual open subscheme of T, and the displayed
right-derived kernel functor is exactly the recorded ambient Rg!, rather than
an arbitrary map or an assumption that it already preserves constructibility.
The explicit open-inclusion spelling is the only compile-driven repair. Checked
all Lean lines are at most 100 characters and the JSON signature matches the
file verbatim. No mathematical statement correction was needed. This second
pass is by the single dispatched worker; the maintainer's independent reading
is the delivery review required by the brief.
