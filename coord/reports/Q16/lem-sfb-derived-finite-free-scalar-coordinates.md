## Worker report

Stage-2 handoff of the accepted stage-1 split. The live node has no `lean` record
and no `reviewed_lean`. Q06's PASS is the review of its nine-step natural-language
split, not a stage-2 landing. The 2026-10-22 handoff instruction in
coord/brief-stage2.md §0 explicitly permits recording this statement. No repair
note exists. The accepted statement, proof, proof dependencies and review are
preserved.

The module Sheaf.CategoryTheory.DerivedFiniteFreeScalarCoordinates states
SheafOfModules.RingedTensor.derived_finiteFreeScalarCoordinates. Its only
postponed proof is this named theorem. Five helpers give the basis maps and
package the coordinate and inverse-image normalization equations; their data
are actual composites or propositions, with no choice or postponed construction.
The repair adds one definition ownership node for two definitions already in the
landed tower module. The item publicly imports that existing module. The tower
module and its node record are absent from this delivery. No mathematical
statement is corrected.

Hypotheses and clauses, in node order:

- The site small in the module universe is `{C : Type u} [SmallCategory C]`,
  `J : GrothendieckTopology C`; ring sections and module sections are in `u`.
  This is the small presentation fixed by def-weil-size-convention, not a site
  functor assumption. The independently bound `w` is the selected derived-Hom
  universe, with explicit `HasDerivedCategory.{w}` for both module categories.
- The ring map is `a : R ⟶ S` for `R S : Sheaf J CommRingCat.{u}`. The module
  category is exactly Mathlib `SheafOfModules.{u} (ringSheaf R)`, definitionally
  the recorded `CategoryTheory.ringedSiteModules` specialization.
- `d : ℕ` includes zero. `θ` is the specified isomorphism from the product of
  `Fin d` copies of the regular R-module sheaf to `restriction a` of the regular
  S-module sheaf. In an abelian category this finite product is also the finite
  direct sum; using the product fixes its projections without choosing a second
  finite-biproduct instance.
- `scalarBasisInclusion` is the product lift of the identity/zero components,
  followed by `θ.hom`. Applying it to 1 gives b_i. `scalarBasisCoordinate` is
  `θ.inv` followed by `Pi.π`, hence exactly q_i. These definitions work without
  a terminal site object: they evaluate at every `U : Cᵒᵖ`.
- Restriction is the actual `SheafOfModules.restrictScalars` via the published
  abbreviation `RingedTensor.restriction.{u,u}`. Its module universe is explicit;
  otherwise that abbreviation leaves an independent universe metavariable.
- Ordinary extension is the existing `RingedTensor.tensorFunctor a`: the
  sectionwise balanced change-of-rings presheaf followed by module sheafification.
  Its object and map functions are precisely `changeOfRings` and
  `changeOfRingsHom`, as used by the generic recorded derived-change-of-rings
  dependency. No second scalar-extension functor is defined.
- Exactness is the existential pair `PreservesFiniteLimits (tensorFunctor a)`
  and `PreservesFiniteColimits (tensorFunctor a)`. The analogous restriction and
  finite-power structures are also supplied, not assumed; these allow the
  statement to form the standard termwise derived functors.
- Preservation of every quasi-isomorphism is the clause quantifying over all
  `K L : CochainComplex ... ℤ`, all `f : K ⟶ L`, and `QuasiIso f`. There is no
  K-flatness, boundedness, or nonzero-rank hypothesis in this clause.
- `E`, `ε` and `E.IsLeftDerivedFunctor ε (quasiIso ... (.up ℤ))` specify the
  universal counit-normalized derived scalar extension already supplied by
  lem-pur-derived-change-of-rings. Quantifying over every universal pair avoids
  a fresh choice of derived extension. These binders specify what E_a denotes;
  they are not a flatness or representative hypothesis. The generic
  DerivedChangeOfRingsCochainModel publicly retained by the recorded module gives
  precisely this universal pair, with its ordinary E identified with tensorFunctor.
- `∀ K, IsIso (ε.app K)` says termwise extension computes E on EVERY unbounded
  complex, not merely on the K-flat resolving complexes of the dependency.
  The counit is natural, so this also gives the normalized natural factorization
  through the entire derived category.
- `φ : tensorFunctor a ⋙ restriction a ≅ Functor.const (Discrete (Fin d)) ⋙ lim`
  is the ordinary natural coordinate isomorphism, with actual module-sheaf maps.
  `IsFiniteFreeScalarCoordinateIso` records its forward formula after every
  projection: the sheafification image `scalarPure a M U s m` is sent to
  `q_i(s) • m`. Its inverse on every product section x is explicitly the sum
  `∑ i, scalarPure a M U b_i (π_i(x))`. No assertion identifies sections of a
  general tensor sheaf with an objectwise tensor product.
- `Φ : E ⋙ (restriction a).mapDerivedCategory ≅ Functor.const ... ⋙ lim`
  is the natural isomorphism in the DERIVED category required in the node.
  The target is the actual finite product of K with itself, hence K^{⊕d},
  rather than only cohomology groups or a guessed derived-power functor.
- The equation for every complex K and coordinate i normalizes Φ on every
  representative. Its right side first applies derived restriction to ε_K,
  then the standard restriction factorization, then Q of the degreewise φ
  followed by the degreewise i-th projection. The composition isomorphism
  `mapHomologicalComplexCompIso` fixes the intermediate parenthesization.
  Consequently the inverse of Φ is also the localization of the degreewise
  inverse φ; the ordinary inverse formula above specifies exactly the sum in
  the node. Invertibility and joint uniqueness of the finite projections ensure
  there is no unconstrained derived automorphism.
- `FiniteFreeCoordinatesInverseImage` quantifies over EVERY geometric morphism
  `g : GeometricMorphism (Sheaf J' (Type u)) (Sheaf J (Type u))` of small
  presented topoi, never just a functor of sites. `R'`, `S'`, `IR`, `IS` are
  arbitrary normalized presentations of g^{-1}R, g^{-1}S and their module
  inverse images, using the existing AlgebraicInverseImage interface used by
  the recorded scalar-inverse-image-tower theorem. The compatibility equation
  for `a'` says exactly that it is g^{-1}a. The presentation graph laws fix all
  ring and module operations; arbitrary underlying functors are not substituted.
- The inverse-image predicate SUPPLIES additivity and exactness of IR, IS,
  a'-extension, a'-restriction and target finite powers. None is an additional
  assumption on g. The target `HasDerivedCategory.{w}` binder merely selects
  the target localization when stating its derived equality.
- `χ` is the balancing comparison; `IsScalarInverseImageComparison ... χ`
  pins it on every generalized elementary tensor, exactly as in the recorded
  scalar-tower statement. `ρ` is restriction comparison; its underlying-sheaf
  equation forces it to be the identity under the two transport identifications.
  `σ` is finite-sum comparison, pinned by all the projections.
- `κ` and `κS` are regular-module comparisons, pinned by their underlying ring
  identifications. `τ` is the finite-power comparison on the regular module,
  pinned by its projections. The displayed equation `τ.hom ≫ θ'.hom = ...`
  says exactly θ' = g^{-1}θ under these comparisons; `θ'` is not an arbitrary
  basis. `IsFiniteFreeScalarCoordinateIso a' d θ' φ'` gives BOTH formulas
  using precisely the transported basis and inverse coordinates.
- The ordinary square is
  `IR.map φ_M ≫ σ_M = ρ_(T M) ≫ restriction(a').map χ_M ≫ φ'_(IR M)`.
  The final derived clause now binds the actual `(E, ε, Φ)` from the theorem.
  For EVERY target universal pair `(E', ε')`, it supplies invertibility of `ε'`
  on all complexes and a `Φ'` satisfying exactly the same representative
  normalization `IsDerivedFiniteFreeScalarCoordinateIso a' d E' ε' φ' Φ'`.
  It supplies `β : E ⋙ D(IS) ≅ D(IR) ⋙ E'`, normalized by the displayed
  counit equation on every complex using ε, ε', χ and the standard composition
  and localization factorizations. Thus β is the derived balancing in the node.
  The derived finite-sum comparison σD is fixed by every projection. Finally,
  for EVERY derived object K, the equation is literally
  `D(IR).map (Φ_K) ≫ σD_K = D(ρ)_(E K) ≫ D(r_a').map β_K ≫ Φ'_(D(IR) K)`
  with the two canonical derived composition isomorphisms included around D(ρ).
  This replaces the former redundant equality between descents of the ordinary
  square; that equality did not involve Φ or any target derived extension.


Dependencies and exact declarations used:

- Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings:
  SheafOfModules.restrictScalars, its additive instance.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses:
  cochainModulesMonoidal and the retained actual sheafified tensor construction.
- Mathlib.Algebra.Homology.DerivedCategory.Basic:
  DerivedCategory, HasDerivedCategory and DerivedCategory.Q.
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules,
  transparently Mathlib SheafOfModules, with its abelian structure.
- Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings: the public generic
  DerivedChangeOfRingsCochainModel and its existence theorem. The primary
  ModuleCat declaration recorded by the latest dependency repair is an added
  specialization; the full generic sheaf construction is still public.
- Sheaf.CategoryTheory.Sites.GeometricMorphism: GeometricMorphism, its inverse,
  adjunction and leftExact. This is the underlying geometric datum in the
  original ringed-topos dependency; the structural maps here are the specified
  inverse-image ring identifications.
- Sheaf.Paper.RingedTopoiTensorSections: ringSheaf, underlying, restriction,
  tensorFunctor. Sheaf.Paper.RingedScalarExtensionComplexAdjunction:
  scalarExtension_additive. Sheaf.CategoryTheory.ScalarInverseImageTowerDiagram:
  scalarPure and IsScalarInverseImageComparison, used in place through the new
  existing:true ownership node. The item publicly imports their existing module.
- WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor:
  mapDerivedCategoryNatIso, mapDerivedCategoryCompIso and their representative
  normalizations; Mathlib ExactFunctor: mapDerivedCategoryFactors.
- The proof imports retain the recorded K-flat-resolution, geometric-module
  transport, exact inverse-image, module-colimits-forgetful, kernel/cokernel
  exactness, module sheafification and localization interfaces used in the
  accepted nine-step proof. Existing ordinary finite-free coordinates are also
  imported as supporting proof material, not restated or rebound to this node.

The added statement dependencies are already landed nodes for the explicit
geometric-morphism datum, scalar section calculus, scalar-extension additivity,
and the newly owned scalar inverse-image normalization definition. The algebraic
inverse-image node is now cited explicitly. The tower theorem is retained only
in proof_deps, not stmt_deps. No existing dependency is
replaced, weakened, or given a private copy. The original ringed-topos dependency
remains imported and its natural-language citation stays unchanged.

Edge cases checked before stating and after elaboration:

- d = 0: the finite product is zero, θ forces the regular S-module to vanish,
  hence S is the zero ring sheaf; extension is zero, both formulas have empty
  sums and the derived target is zero. Projection-normalization is vacuous only
  for this zero target, whose maps are already unique.
- d = 1 and a = identity: for a basis scaled by a unit b, the formulas are
  b^{-1}s m and b tensor m, rather than silently imposing the standard basis.
- M = 0, the zero complex, zero rings and a degenerate sheaf topos are permitted.
- No terminal site object or enough points are required. Basis elements are
  evaluated over each object. Generalized-element normalization makes inverse
  image independent of any lifting assumption on sections.
- Identity geometric morphisms, arbitrary normalized lifts of inverse image,
  nontrivial g and arbitrarily unbounded complexes are all included.
- Finite products are the canonical finite direct sums in the abelian and
  additive triangulated categories; all size parameters are explicitly bound.

Searches performed:

- msearch LeanFinder: “Finite free extension of sheaves of rings induces derived
  scalar extension isomorphic to a finite direct sum, compatible with inverse
  image”. Eight hits on free-module pullback and mapFree naturality; none is
  the unbounded derived finite-basis coordinate theorem.
- msearch Loogle: `SheafOfModules.restrictScalars, Functor.mapDerivedCategory`.
  No hits; this index does not know the latter qualified identifier.
- msearch grep: `finiteFreeScalar|finite_free_scalar|scalar.*coordinates` in
  Algebra/Category/ModuleCat. No hits.
- msearch LeanSearch: “finite free scalar extension sheaves modules derived
  category coordinate isomorphism inverse image”. Eight free-module-pullback
  and mapFree hits; none supplies the asserted derived comparison.
- rg in project Sheaf and upstream WeilConjectures found
  CategoryTheory/FiniteFreeScalarCoordinates (ordinary internal module objects),
  ScalarInverseImageTowerDiagram (ordinary balanced comparison), and specialized
  finite-coefficient scheme scalar-extension results. None states this arbitrary
  ring-sheaf unbounded result with the specified inverse-image normalization.
- rg for this node ID in both source roots found no existing declaration.
  rg for all five new full name suffixes in both source roots and
  dag/lean_names_upstream.json found no collision.

No STATEMENT-DISPUTED flag or mathematical node fault. The sole inherited issue
was the stale stage-1 “already merged” ending, resolved by the explicit stage-2
handoff rule and the live node's absence of a Lean record.

## Repair of return f61320890a14

H13: the saved packet passed its initial dry run at 8e9eeedc802, but that packet
still replaced the landed tower proof with sorry. Removed the sandbox tower
module and tower node record entirely, so neither is delivered. Removed
ScalarInverseImageNormalization.lean. The new definition node now has
existing:true, module Sheaf.CategoryTheory.ScalarInverseImageTowerDiagram,
declarations scalarPure and IsScalarInverseImageComparison, the existing
predicate signature verbatim, and no file. The item uses public import
Sheaf.CategoryTheory.ScalarInverseImageTowerDiagram. Its accepted statement,
helpers, derived square, and stmt_deps are retained. This implements every part
of the return's requested correction without touching the landed stage-3 proof.

The current server tower source was read with scompile.py --source and its two
existing definitions agree with the local declarations. Its named tower theorem
has a full proof and private proof helpers; no part is copied into this packet.

The earlier H3 repair is retained: the final clause uses the actual derived
coordinate square with Φ, E, ε, target E', ε', normalized Φ', counit-normalized
balancing β, and projection-normalized finite-sum comparison σD. The maintainer
already checked this item statement clause by clause in the return.

## New nodes

`def-sfb-scalar-inverse-image-normalization` is an existing:true ownership record
for SheafOfModules.RingedTensor.scalarPure and
SheafOfModules.RingedTensor.IsScalarInverseImageComparison in
Sheaf.CategoryTheory.ScalarInverseImageTowerDiagram. No new Lean file is supplied.
The first definition is the actual sheafification-unit image of the balanced
scalar tensor; the second quantifies over every module, test sheaf and generalized
pure tensor and pins the inverse-image comparison on all their sections. The
signature in lean.statement is verbatim from the existing module. Source: Stacks
03EK/03EL and blueprint main-20261015 det-prop-scalar-six-pullback.proof.md (1), (3),
read locally. The node's original search records are retained as historical search
results: they found these two exact project helpers and no definition node owning
them, while Mathlib and upstream had no equivalent normalization. The ownership
is now recorded in place rather than extracting or duplicating their definitions.

The new node imposes neither a geometric adjunction nor a coefficient-square
hypothesis: it defines a predicate for arbitrary algebraic presentations and a
candidate isomorphism. Existence of the normalized candidate remains the theorem's
conclusion. The test sheaf T and all its sections are quantified, so no global
section-generation assumption enters. Empty sites and zero rings are allowed.

## Self-check by Q16

Read the accepted statement, the repaired helper definitions, and the theorem
signature clause by clause. The finite basis, exactness, preservation of arbitrary
unbounded quasi-isomorphisms, universal E and invertible ε, ordinary formulas and
representative normalization retain their original meaning. The inverse-image
clause now uses Φ itself and supplies target E', ε', Φ' as well as β. Both Φ and Φ'
are pinned by the same projection formula on representatives. All maps in the
counit square have the correct direction; β starts at D(IS)(E K) and ends at
E'(D(IR) K). The final square starts at D(IR)(r_a(E K)) and ends at (D(IR) K)^d.
The representative normalization of β rules out changing it to absorb arbitrary
coordinates, and derived σD is fixed by projections. The d=0 target is a zero
object; d=1 scaled bases retain the inverse-unit coordinate and original basis
insertion formulas. Identity g and arbitrary normalized presentations remain
included. Site and coefficient universe u and derived-Hom universe w are explicit.

No STATEMENT-DISPUTED flag or source-based statement correction: the accepted
mathematical statement is unchanged. A separate worker was not started, as the
assignment explicitly forbids other agents; the maintainer performs independent
review of the delivery.

## Validation of repaired packet

scompile.py compiled the final item separately in sandbox and library contexts
in 6.9 s and 6.8 s, respectively, with no errors or unexpected warnings.
deliver2.py --no-push then returned OK at 5f900d98835: the repaired packet passes
preflight and compiles, including a server probe of both existing definitions.
The exact staged set was the report, the item node, the new ownership node and
the item Lean module. No tower module, tower node or normalization module occurs
in that set. The wrapper rebased the packet on current sheaf-dag automatically.

The final self-check compared both lean.statement signatures verbatim with their
source declarations. The new node has existing:true and no file. There is exactly
one delivered Lean file, with one sorry (the main named theorem), explicit
universes and variables, no overlong lines, and the required public tower import.
The item's statement and proof plan match current main; its stmt_deps remain as
accepted in the returned delivery. No mathematical correction was made. The
landed tower module, its proof helpers, stage-3 proof and node record are untouched.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
