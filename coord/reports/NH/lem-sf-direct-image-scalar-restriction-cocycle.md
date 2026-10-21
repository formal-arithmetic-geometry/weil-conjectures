## Worker report

The module `Sheaf.AlgebraicGeometry.DirectImageScalarRestrictionCocycle` states the
uniqueness and coefficient cocycle clauses of
`lem-sf-direct-image-scalar-restriction-cocycle`. Both theorem proofs are `sorry`.
No construction, dependency record, natural-language statement, or dependency list is
changed. No new node is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Finite commutative rings are `{A B C : Type (u + 1)}` with `[CommRing A]`,
  `[CommRing B]`, `[CommRing C]` and the three `[Finite ...]` instances.
  The uniqueness theorem needs just the two rings of one coefficient map.
- The two ring homomorphisms are `(φ : A →+* B)` and `(ψ : B →+* C)`;
  the composite χ is the actual ring homomorphism `ψ.comp φ`.
- The arbitrary scheme morphism p:Z→Y is `{X Y : Scheme.{u}} (f : X ⟶ Y)`;
  X here names the node's Z. There is no geometric property instance on f.
- The small pro-etale sites are `Scheme.ProEt.topology X` and
  `Scheme.ProEt.topology Y` on the recorded Mathlib `Scheme.ProEt` category.
  Its object universe is u+1 and morphism universe is u. This does not collapse
  these universes. The coefficient and section universes u+1 are exactly those
  of the supplied comparison, including finite rings via universe lifting.
- Constant-ring module sheaves are expressed in the published dependency's equivalent
  fixed-coefficient presentation `Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)`.
  This is the presentation used by the recorded
  `fixedScalarRestrictionDirectImage_kInjective`; no new module category or
  replacement coefficient action is defined here.
- Underived restriction is the published `Sheaf.restrictScalars`; its exact termwise
  localization is `Sheaf.derivedRestrictScalars`. Its relation to `Q` is the actual
  `mapDerivedCategoryFactors` isomorphism. The general ring-sheaf operation is
  Mathlib's `SheafOfModules.restrictScalars`, read in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`; the fixed-coefficient
  restriction used here is its standard constant-module presentation, already fixed
  by the statement dependency. The module introduces neither a second restriction
  definition nor an alternative to the recorded comparison.
- The canonical rho_T is exactly
  `Sheaf.derivedRestrictScalarsCompIso (Scheme.ProEt.topology T)
  (f := φ) (g := ψ) rfl`. Its source is Res_ψ followed by Res_φ, and its target is
  Res_(ψ.comp φ). I read its real-data definition in the upstream
  `DerivedBaseChange` module: it is the inverse exact-functor composition isomorphism
  followed by `mapDerivedCategoryNatIso (restrictScalarsCompIso ...)`. I also read
  `restrictScalarsCompIso`: it uses `ModuleCat.restrictScalarsComp'` symmetrically,
  which is identity on elements in each direction. Thus this is exactly the specified
  identity on underlying abelian sheaves, with action a·m=ψ(φ(a))·m, localized termwise.
- P_R is `R((f)_*[ModuleCat.{u + 1} R])`, the existing unbounded K-injective-defined
  derived direct image. It is the direct image already used in the supplied comparison.
  The ordinary constant-ring operations dependency is imported; no new direct-image
  construction or arbitrary functor is substituted.
- Each β_θ is literally `fixedScalarRestrictionDirectImage θ f`, the natural
  isomorphism in the recorded dependency module. Its normalization is the dependency's
  `fixedScalarRestrictionDirectImage_kInjective` theorem, whose full signature and
  docstring were read.
- Uniqueness is `fixedScalarRestrictionDirectImage_unique`. The candidate γ is a
  natural isomorphism with exactly those endpoints. The hypothesis `hγ` quantifies over
  every K-injective H, every K-injective I, and every quasi-isomorphism j from the
  restricted H to I. It repeats verbatim the supplied normalization equation with γ
  replacing the specified β, including `QuasiIso (p_* j)`. This latter condition is
  part of the normalization, and the dependency already proves it for every such j;
  it adds no restriction on f or the coefficient map. After transporting through the
  displayed evaluation isomorphisms and canceling the invertible localized p_*j, the
  equation says precisely that the component is `[p_*j]⁻¹`. The conclusion is equality
  of natural isomorphisms `γ = fixedScalarRestrictionDirectImage φ f`.
- The arbitrary derived object is
  `L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} C))`;
  there is no boundedness, constructibility, flatness, or other condition on L.
- The cocycle left side is `P_A.map (rho_X.hom.app L) ≫ β_χ.hom.app L`.
  The right side is `β_φ.hom.app (Res_ψ.obj L) ≫ Res_φ.map (β_ψ.hom.app L)
  ≫ rho_Y.hom.app (P_C.obj L)`. Lean composes left to right, so this is exactly
  the displayed node equation read in conventional right-to-left notation.
- There is no hypothesis that any scalar restriction preserves K-injective complexes.
  `H.IsKInjective` and `I.IsKInjective` describe the original representative and the
  separately chosen target resolution; they impose no property on the restricted H.

The module and both theorem docstrings name the source and blueprint id. The uniqueness
proof docstring spells out node steps 1--2. The cocycle proof docstring spells out
steps 1 and 3--5, including d=a rho inverse, the identity homotopy representative,
strict-composite normalization, application of the generic comparison-composition
statement, and final cancellation. Stacks derived.tex at label
`lemma-K-injective-defined` (Tag 070Y), including its proof and the following
K-injective-existence lemma, was read directly. The extra coefficient argument is
correctly identified as agent-written, just as in the node.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`
  and `Scheme.ProEt.topology`, the small weakly-etale site.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, the general restriction operation.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`, and
  their shift and triangulated instances, the recorded exact-functor dependency.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `Scheme.proEtaleConstantRingPushforward` and the ordinary constant-ring operations;
  imported for the recorded operation-definition dependency and the proof plan.
- `Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage`:
  `AlgebraicGeometry.ProEtale.fixedScalarRestrictionDirectImage`,
  `fixedScalarRestrictionDirectImage_kInjective`, the underived square,
  `fixedScalarRestrictionDirectImageMap`, and its factorization and inverse statements.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars`:
  `CategoryTheory.Sheaf.restrictScalars` and `restrictScalarsCompIso`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange`:
  `CategoryTheory.Sheaf.derivedRestrictScalars` and `derivedRestrictScalarsCompIso`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and its Q.
- `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`:
  `CategoryTheory.Functor.kInjectiveDerivedMapComputation` and its transition interface.
- `Sheaf.CategoryTheory.NormalizedDerivedComparisonComposition`:
  `CategoryTheory.Functor.normalizedDerivedComparison_composition` and its
  normalization/localization helpers. The generic comparison theorem is imported
  non-publicly as a proof dependency, rather than restated.

Edge cases checked before drafting: identity coefficient homomorphisms; identity
scheme morphism; the empty scheme; zero coefficient rings and zero objects; the
non-flat map Z/4→Z/2; and arbitrary unbounded complexes. None is excluded. Restriction
composition is an isomorphism of the same underlying groups even in the zero-ring
case. In the non-flat case no preservation of K-injectives is inferred: each restricted
complex gets its own resolution. The uniqueness proof cancels only genuine evaluation
isomorphisms and the dependency's invertible localized direct-image resolution map.

Searches actually run (full wrapper results are in the sandbox search log):

- LeanFinder: `K-injective normalized derived direct image restriction of scalars
  comparison satisfies composition cocycle and is unique`. Eight hits on bounded-below
  injective-resolution calculations and exact-functor quotient comparisons; no exact
  pro-etale uniqueness or coefficient-cocycle statement.
- LeanSearch: `Derived direct image restriction of scalars natural comparison uniquely
  determined by K injective resolution normalization`. Eight hits including
  `PresheafOfModules.restrictScalarsObj`, injective-resolution naturality, and module
  restriction; no exact match.
- Loogle: `"restrictScalarsComp"`. Twelve hits, including
  `ModuleCat.restrictScalarsComp` and `restrictScalarsComp'` with their identity-on-element
  lemmas. These supply the ordinary associator, not the theorem being delivered.
- msearch grep: `restrictScalarsComp|rightDerivedFunctorComparison` in CategoryTheory.
  Five hits on the generic localization comparison in
  `PointwiseRightDerived.lean`; none states the geometric cocycle or uniqueness.
- msearch grep: `restrictScalars.*[Cc]omp|[Dd]erived.*[Rr]estrict` in
  Algebra/Category/ModuleCat. Sixteen hits on ordinary scalar-composition and exactness;
  no matching derived direct-image theorem.
- rg over both project Lean trees and `dag/lean_names_upstream.json`:
  `direct.image.*scalar.*(cocycle|unique)|fixedScalarRestrictionDirectImage.*(comp|unique)|normalized.*[Cc]omparison.*unique|derivedRestrictScalarsCompIso`.
  Found the existing upstream associator used here. Read the nearby compact-support
  cocycle and coefficient-pullback cocycle; neither is the direct-image uniqueness and
  cocycle statement for arbitrary scheme morphisms. The similarly named chain lemmas
  in `FiniteCoefficientDirectImage` concern pullback. No name clash for either new
  declaration was found.
- `grep -rn 'lem-sf-direct-image-scalar-restriction-cocycle' lean/WeilConjectures`
  returned no upstream declaration tagged with this node id.

Validation: `scompile.py NH lem-sf-direct-image-scalar-restriction-cocycle` compiled the
single delivered module successfully in both sandbox and library contexts, with no
errors or warnings (9.9 s and 13.1 s). All variables and universes are explicitly bound,
all lines are at most 100 characters, and both delivered theorem proofs are `sorry`.

## Self-check

Re-read the original node and the completed module together after compilation. The
uniqueness clause is represented separately from the cocycle, so neither is lost.
Checked the rho orientation at both ends: the source is double restriction, the
intermediate target is restriction along ψφ, and the final target is restriction of
P_C L along ψφ. Checked that the γ hypothesis uses every resolution, not just a chosen
one, and uses the same Q evaluation maps as the recorded dependency. No statement
correction, dependency repair, or extra definition was needed.

## Second reading by NH

No second reading by another worker: this dispatcher brief requires direct worker
delivery and forbids starting other agents. The maintainer's independent review reads
this delivery. The self-check above is by the author, not an independent review.
