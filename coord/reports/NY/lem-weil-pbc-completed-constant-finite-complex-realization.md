## Worker report

The module `Sheaf.Paper.CompletedConstantFiniteComplexRealization` states
`AlgebraicGeometry.Scheme.completed_constant_finite_complex_realization` with `sorry`.
Its helper definitions contain real data, or bundle precisely specified diagrams and
universal properties. They introduce the realization and comparisons of this node,
rather than independent mathematical notions. No node statement was changed.

The scalar extension is an actual construction: `completedConstantExtension` selects
from `SheafOfModules.derivedChangeOfRingsIndependentCoefficients` the ordinary
functor whose objects are `changeOfRings` and whose maps are `changeOfRingsHom`.
These two specifications determine the functor, so this is not a choice of an
unconstrained object from an existence theorem. Its additive witness is extracted
from the same statement. `completedConstantRealization` composes it with the actual
constant-module functor. Nothing selects an unspecified natural isomorphism as a
definition's data.

Hypotheses and clauses, in the order of the node:

- A is `A : Type (u + 1)`, with `[CommRing A] [IsNoetherianRing A]`; I is `Ideal A`.
  `hfinite : ∀ n, Finite (A ⧸ I ^ (n + 1))` is precisely finiteness of every positive
  quotient. The node's inverse systems use positive levels; the omitted exponent
  zero is the zero ring, whose finiteness is automatic.
- C is Mathlib's `AdicCompletion I A`, with its existing ring and A-algebra structures.
  J = IC is not copied as a new notion: realization uses the A-restriction of a
  C-module. The subgroups I^n N and (IC)^n N are identical (products of images of
  elements of I generate both), so the quotient modules and completed sheaves are
  exactly N/J^n N. This is not completion over A of a different module.
- X is an arbitrary `Scheme.{u}`. `adicLisseRingSystem X I` and
  `adicLisseCompletedRing X I` are the dependency's actual constant-quotient diagram
  and its limit H = widehat A_X. The small site is unchanged: object universe u+1,
  morphism universe u, coefficient/module universe u+1. The two infrastructure
  instances explicitly transport abelian sheafification through the existing small
  model at that coefficient size; no equality of site universes is imposed.
- `CompletedConstantModuleRealization.scalar_projection` specifies constant C → H
  by evaluation C → P_n at every projection. Thus the scalar map is the canonical
  completion scalar map, not an arbitrary ring morphism.
- `completedConstantRealization X I scalar` is scalar extension of the constant
  C-module sheaf. `realization` identifies it with
  `adicLisseCompletedModule X I (completedConstantUnderlyingModule I N)`, the
  dependency's inverse limit of actual quotient-module sheaves. `linearity` gives
  exactly the componentwise H-action at every projection; `naturality` specifies
  every induced map by the constant quotient map `completedConstantQuotientMap`.
  Together these identify the functor with N ↦ lim underline(N/J^n N), including
  its maps and its completed-scalar action.
- `exact_finite` states preservation of finite limits and finite colimits on the
  full subcategory `completedConstantFiniteModules C`. This is exactness of c_X
  on finite C-modules. `lisse` is exactly the recorded `IsAdicLisseModule X I`.
  No freeness of these modules, or finiteness of their underlying sets, is assumed.
- `completedConstantFiniteComplex` means every term is finite and the terms vanish
  outside a bounded interval. `completedConstantMapComplex` applies the actual
  realization functor termwise, including its differential.
- `completedConstantResolutions C` is the category of quasi-isomorphisms F → Q
  with bounded finite Q and bounded-above finite-free F; its morphisms are
  commutative squares. `CompletedConstantReductionComparisons` explicitly asserts
  existence of such a resolution for every Q, so its naturality is not vacuous.
  F may be unbounded below. It computes Q tensor^L_C P_n, including higher Tor.
- `CompletedConstantQuotientTower` has objects exactly the constant P_n modules
  restricted along the completed-ring projections. Its `transition` fixes all
  arrows on all sections to the actual quotient-ring maps.
- `completedConstantTensorTower` is total tensor with this whole quotient system,
  followed by derived localization. `CompletedConstantDerivedTower` specifies its
  everywhere-defined left derived functor by its universal counit and requires the
  counit to be an isomorphism on every K-flat complex. This is the same K-flat
  meaning of derived tensor as `lem-pur-derived-change-of-rings`. Resolving either
  input gives the usual inverse-image-of-resolution followed by counit comparison.
- `CompletedConstantReductionTower.level` specifies the right hand side as ordinary
  extension F → F tensor_C P_n, then the actual constant module sheaf, restricted
  along R → H → underline(P_n). `map_level` specifies the exact action on chain
  maps. `transition` sends p tensor x to its quotient residue tensor x on every
  sheafification generator. These conditions determine the ordinary tower and its
  functoriality; its arrows cannot be replaced by arbitrary maps.
- The first `CompletedConstantReductionComparisons` uses R=H and beta=id. Its
  natural isomorphism compares the derived realization of Q with the constant
  reductions of F, as whole functors to `ℕᵒᵖ ⥤ D(H)`. This states the displayed
  derived-tensor isomorphism in the ambient derived category of H-modules, where
  underline(Q tensor^L_C P_n) has the projection-induced H-action. This is the
  natural module action on both sides of the node's display.
- The second comparison quantifies every scheme T and f:X→T. Its coefficient is
  exactly B=(proEtaleSheafInverseImage f CommRingCat).obj H_T. The equation for beta
  states beta followed by pi_X,n = inverse-image(pi_T,n) followed by the canonical
  inverse-image-of-constants map. This determines the projection-induced B→H;
  no equality between B and H, even for identity f, is assumed.
- The relative realization functor is the same c_X composed with actual scalar
  restriction along beta. The same comparison definition with R=B gives precisely
  derived tensor over B, whose quotient module has the action through
  u^-1 underline(P_n)_T → underline(P_n)_X. Inverse image preserves constants, so
  these are the same coefficient module, without commuting inverse image with H's
  infinite limit. The relative isomorphism is in D(B), retaining this action.
- Both comparisons are natural isomorphisms into a diagram category. Naturality
  within that category is compatibility with *every* quotient transition; functor
  laws include the identities and all composites. Naturality in the resolution
  category includes morphisms over identity Q, hence independence of finite-free
  resolution, as well as arbitrary chain maps between bounded finite complexes.
  The left-derived universal property and its computation on all K-flat complexes
  ensure that its K-flat resolution is not restricted to the finite-free ones.

The theorem's docstring gives all eight proof steps, including sectionwise flat
limit tensor realization, the explicit finite-free construction, the distinction
between B and H, the balancing maps for scalar restriction, and the quotient
transition formulas. Every theorem left open belongs to this node: the main
statement is the only new `sorry`.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and its ideal-finiteness
  meaning; `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`:
  `AdicCompletion`, `IsAdicComplete`, its ring/algebra structures and `evalₐ`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory` supplies the same small site;
  the general coefficient H/B derived categories directly use its Mathlib
  `DerivedCategory`/`HasDerivedCategory.standard` implementation.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.Paper.AdicLisseModule`: `adicLisseConstantRing`, `adicLisseConstantModules`,
  `adicLisseRingSystem`, `adicLisseCompletedRing`, `adicLisseModuleSystem`,
  `adicLisseCompletedModule`, `adicLisseForget`, and `IsAdicLisseModule`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` and the standard localization.
- `Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses` and its public
  `ProEtaleInverseImage` dependency: `proEtaleSheafInverseImage`,
  `proEtaleConstantInverseImageMap`; the ring inverse image is used for B.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`:
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`, read both locally
  and through `scompile.py --source`. Compiler inspection found the published
  K-flat interface is named `IsKFlatIndependentCoefficients`; this exact interface
  is used with all three universes explicit. The locally recorded newer spelling
  `IsKFlat` is not silently specialized to equal site universes.

All stated proof-dependency modules are imported non-publicly, including the
completion, finite-module, limit-flat, finite-free, K-flat, tensor descent, and
ringed-topos pullback inputs. `lem-weil-pbc-completed-constant-sheaf-reduction` and
`lem-weil-pbc-constant-completion-equivalence` have no recorded module in this
snapshot and are proof-only dependencies, so neither can be imported yet. The
source dependency interfaces are used without copies or repairs.

Edge cases checked: empty X (no nonemptiness restriction); zero module and zero
complex; an empty support interval; I=0; I=A and A=0 (completion and finite
C-modules then zero); positive level one; exponent zero (zero quotient); arbitrary
characteristic; nonregular C and nonprojective finite modules (F unbounded below
is allowed); arbitrary f including identity; and composites of quotient maps.
There is no hypothesis identifying inverse image with the infinite limit and no
finite Tor-dimension or perfection assumption.

Searches:

- `msearch.py ... leanfinder "Completed constant sheaf realization of finite modules
  is exact and commutes with derived reduction modulo powers of an ideal"`: eight
  hits, including `AdicCompletion.map_exact`, local cohomology and condensed-module
  ambient-category constructions; no statement match.
- `msearch.py ... loogle "AdicCompletion, CategoryTheory.constantSheaf"`: zero hits.
- `msearch.py ... grep "completedConstant|constantCompletion|CompletedConstant"`:
  zero Mathlib hits.
- `msearch.py ... leansearch "Completed constant realization of finite complexes on
  the pro etale site"`: service unavailable, Internal Server Error; not evidence
  of absence. The other searches were available.
- `rg` for the same completed-constant names and the exact node id in the read-only
  slopmaster2 `WeilConjectures` tree: no statement match.
- `rg` in `lean/Sheaf` for completed-constant realization and adic-lisse completion:
  found the reused `AdicLisseModule` systems and existing coefficient/reduction
  material, not this finite-module exactness plus absolute/relative comparison.

Validation: the delivered module compiled cleanly through `scompile.py`, including
its side-only imports. The remaining step is the prescribed delivery dry run.
No new nodes, dependency record repairs, or statement corrections are needed.

## Second reading by NY

Read the item's complete node and module, every statement-dependency node and its
recorded declaration, the completion Mathlib leaves, and the exact pro-etale
framework notes and source. There is no statement_change, new node or dependency
module in this delivery. No mathematical statement correction was needed.

Source check before matching: proetale.tex `definition-adic` (09BT) assumes a
Noetherian coefficient ring and an arbitrary scheme. Its clause (3) uses a complete
module with finite first reduction and imposes no freeness. `lemma-weird` (09BV)
assumes a weakly contractible affine scheme for the converse reconstruction of a
module from a sheaf. This item instead realizes an already given finite completion
module, by its explicitly recorded agent argument; it does not assert that converse.
Thus importing the weak-contractibility or affineness assumption would be wrong.
The exactness input in algebra.tex `lemma-completion-flat` (00MB) assumes a
Noetherian ring, with no local-ring or proper-ideal assumption. The sectionwise
argument in sites-modules.tex `lemma-constant-exact`,
`lemma-tensor-with-finitely-presented`, `lemma-flat-sections`, and
`lemma-completion-flat` (093J--093M) works on an arbitrary site. Coherence required
for flat sections follows from Noetherianity here. No characteristic or
nonemptiness hypothesis occurs in these passages.

The node's objects, hypotheses and conclusions, matched item by item:

1. Commutative Noetherian A and an ideal I: `{A : Type (u + 1)} [CommRing A]
   [IsNoetherianRing A] (I : Ideal A)` in the theorem. Verdict: exact; no field,
   local-ring, nonzero-ring or Jacobson-radical hypothesis is added.
2. Every quotient P_n is finite as a set: `hfinite : ∀ n : ℕ,
   Finite (A ⧸ I ^ (n + 1))`. Verdict: exact positive-level indexing. Level zero
   in the mathematical indexing is A/I^0 = 0 and automatically finite; dropping
   that terminal zero quotient changes neither compatible families nor the limit.
3. C = lim A/I^n with its A-algebra and finite projections:
   Mathlib `AdicCompletion I A`, `algebraMap A (AdicCompletion I A)` and
   `AdicCompletion.evalₐ I (n + 1)`. I read Basic's compatible-family definition
   and Algebra's algebra evaluation map. Verdict: the actual completion and its
   canonical projections, not a field or a separately chosen complete ring.
4. J = IC and N/J^n N: `completedConstantUnderlyingModule I N` restricts the
   actual C-module along A → C. The quotient in `adicLisseModuleSystem` is
   `N ⧸ (I ^ (n + 1) • ⊤)`. Verdict: exact. Restricting scalars identifies this
   submodule with J^(n+1)N, since J is the ideal generated by the images of I;
   Mathlib's `restrictScalars_map_smul_eq` and ideal-map powers express precisely
   this relation. N is finite over C, not required to be finite over A.
5. Arbitrary X and its small pro-etale site: `(X : Scheme.{u})`, `X.ProEt` and
   `ProEt.topology X`, imported through the recorded inverse-image dependency.
   Verdict: exact original site, with object universe u+1 and Hom universe u.
   Coefficients and module carriers live in u+1, the site's chosen larger universe.
   The two infrastructure instances construct sheafification through a small
   model; they add no hypotheses or equality of these universe levels.
6. H = widehat A_X = lim constant P_n: `adicLisseCompletedRing X I`, namely the
   limit of `adicLisseRingSystem X I`. I read that dependency's construction with
   `Functor.ofOpSequence` and `Ideal.Quotient.factorPowSucc`. Verdict: exactly the
   constant quotient sheaves and their actual quotient transitions.
7. The functor c_X(N) = lim constant(N/J^nN):
   `completedConstantRealization X I d.scalar` is constant sheafification followed
   by ordinary extension of scalars. `CompletedConstantModuleRealization.realization`
   identifies it with the dependency's `adicLisseCompletedModule`, `naturality`
   fixes its action on every module map by the induced quotient map, and
   `linearity` fixes its componentwise H-action on every projection. Verdict: the
   same functor, expressed by its natural H-linear identification with the limit.
   The conditional linearity test is sufficient: quotient constant-ring sections
   lift locally, and the asserted equality is a sheaf-local equality.
8. Its scalar map constant C → H: `scalar_projection` requires every finite
   projection to be the constant sheaf of `AdicCompletion.evalₐ`. Verdict: canonical
   map determined by the limit, not an arbitrary scalar action. The selected
   ordinary scalar-extension functor in `completedConstantExtension` is likewise
   fixed on objects and maps by `derivedChangeOfRingsIndependentCoefficients`.
9. Exactness on finitely generated C-modules: `exact_finite` asserts preservation
   of finite limits and finite colimits on the full subcategory defined by
   `completedConstantFiniteModules`. Verdict: exactness in this abelian category;
   its kernels and cokernels are finite because C is Noetherian. No underlying-set
   finiteness or projectivity of N is required.
10. Values adic lisse of finite type: `lisse` uses the recorded `IsAdicLisseModule`
    verbatim. I opened its covering sieve, complete local module, finite first
    quotient and projectionwise completed-linearity conditions. Verdict: matches
    09BT(3) and the dependency node, without requiring the local module to be free.
11. Bounded complex Q of finite C-modules and termwise c_X(Q):
    `completedConstantFiniteComplex` requires finiteness in every degree and
    `IsZero` outside an integer interval. `completedConstantMapComplex` is the
    existing `mapHomologicalComplex`, with its actual induced differentials.
    Verdict: exactly bounded finite complexes; a zero complex is permitted.
12. Absolute derived comparison for every Q and every quotient level:
    `CompletedConstantReductionComparisons X I H (𝟙 _) ...` includes a resolution
    for every such Q. `completedConstantResolutions` consists of quasi-isomorphisms
    F → Q with bounded-above finite-free F; it imposes no lower bound on F.
    `CompletedConstantDerivedTower.universal` specifies the left derived tensor
    with the quotient diagram and `computes` applies to every K-flat complex.
    `CompletedConstantReductionTower.level` identifies the other side with
    constant(F tensor_C P_n), restricted along the projection. Verdict: the node's
    derived isomorphism, with higher Tor retained, in the ambient D(H). All inputs
    and outputs retain the required coefficient action.
13. Naturality and compatibility with all quotient reductions:
    `Nonempty (... ≅ ...)` is an isomorphism of functors on the category of
    resolutions with values in `ℕᵒᵖ ⥤ D(H)`. `map_level` fixes chain-map functoriality;
    `transition` fixes successive quotient maps on sheafification tensor generators.
    Functor laws then fix all composite transitions. Commutative squares over the
    same Q are included, and quasi-isomorphisms between bounded-above projective
    resolutions give the usual resolution independence. Verdict: natural in Q and
    compatible with the whole quotient tower; not merely isolated isomorphisms.
14. Every scheme morphism u : X → T and B = u⁻¹ H_T:
    `∀ (T : Scheme.{u}) (f : X ⟶ T)` and
    `(proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
    (adicLisseCompletedRing T I)`. I opened the recorded inverse-image construction
    and the adjoint constant-section map. Verdict: all such morphisms, including
    identities, and the exact inverse image of H_T.
15. Projection-induced B → H and the same complex viewed over B:
    the equation after `∃ β` specifies every projection using inverse image of
    `limit.π` followed by `proEtaleConstantInverseImageMap`. The relative c is the
    same `completedConstantRealization` followed by `restrictScalars` along β.
    Verdict: canonical coefficient map and scalar restriction; no B = H assertion.
16. Relative derived comparison and all reductions: the second
    `CompletedConstantReductionComparisons`, now with R = B, uses the quotient
    ring action β followed by H → constant P_n and the same tower conditions.
    Inverse image of a constant sheaf is canonically the constant sheaf, and the
    displayed equation specifies exactly its B-action. Verdict: this is tensor
    over B with u⁻¹ constant(P_n)_T, with target in D(B). The K-flat universal
    computation imposes no finite Tor-dimension assumption and does not commute
    inverse image with H_T's infinite limit.

Edge cases checked independently: the empty scheme and morphisms involving it;
zero rings, modules and complexes; an empty support interval (a > b); I = 0
(including finite A), I = A, and the first positive quotient; the omitted exponent
zero quotient; arbitrary characteristic; nonregular C and finite nonprojective
modules requiring an unbounded-below resolution; identity f and all composites of
quotient transitions. No binder excludes these. All universes are explicitly
bound, and neither site Hom size nor object size is silently identified with the
other. The common larger coefficient universe is the dependency's size convention.

Independent searches, using terms other than the worker's query:

- LeanFinder: `Inverse limit of constant quotient module sheaves over the adic
  completion is exact on finitely generated modules and has compatible derived
  tensor reductions`. Eight hits: `AdicCompletion.map_exact`,
  `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian` and its formulas,
  `AdicCompletion.ofTensorProduct`, and its finite-product equivalence.
  These concern ordinary module completion and tensor realization, not the
  absolute/relative sheaf-derived assertion here. No exact match.
- Loogle: `"constantSheaf", "tensor"`. Zero hits.
- The prescribed grep search: `adic.*realiz|realiz.*adic|completed.*module.*sheaf`.
  Zero Mathlib hits. Direct rg over Mathlib, upstream WeilConjectures, the project's
  Sheaf tree and its exact WeilConjectures framework for constant/completed
  realization, adic finite complexes and the node id found no matching theorem.
  Opened `EtaleConstantRingModuleEquivalence`: its realization is on the etale
  site with constant coefficients, with no completion or derived reductions.
  Opened `ConstructibleSheaf.ProEtaleModule.Def`: its internal module-object
  finite-presentation/constructibility predicates do not define this realization.
  The generic K-flat, tensor, localization and constant-sheaf declarations are
  reused through their actual APIs, not replaced by new mathematical notions.

No helpers choose unconstrained objects from postponed existence proofs. The
scalar-extension existence theorem specifies the functor's objects and all maps;
its choice is determined up to the equality used here. Tower structures instead
state existence of diagrams with explicitly fixed levels and arrows. There is
exactly one new sorry, the named main theorem. Its docstring carries all eight
steps, including the downward finite-free construction and the relative balancing
calculation. Every declaration has its source and this node's blueprint tag.

Mismatch found and repaired: the current `def-pur-sheaf-tensor-product` record
names `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`, while
this module reached only the older TensorProduct module through its public
statement dependencies. Added the recorded universe-general tensor module as a
non-public proof import, as required by stage 2 rule 7. No signature, helper
construction, node statement or dependency record was changed. Already correct
mathematical content was left intact.

Validation: `scompile.py` compiled the module cleanly before the import repair;
the repaired file is checked again by the same wrapper and by the prescribed
no-push delivery preflight. A direct text check confirms `lean.statement` is
verbatim the theorem signature, all lines have at most 100 columns, and the only
sorry in this module is the main theorem's proof. The unchanged Worker report
above records the first writer's work; this section records the independent read.
