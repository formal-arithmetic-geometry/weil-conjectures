## Worker report

The module `Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum` states
`AlgebraicGeometry.ProEtale.CondensedRing.constructibleExtContinuityStratum`, with a
`sorry` proof. It is the stratum continuity lemma in the current main-20261015 blueprint,
`sec-smooth-purity/sk-prop-sf-localization/sk-lem-constructible-ext-continuity-stratum.md`.
The source statement and all nine expanded proof steps of the DAG node were read.
The declaration docstring contains those nine steps and their named dependencies.
There is no statement correction and no disputed statement.

Hypotheses and conclusion, clause by clause:

- A qcqs scheme X: `{S Z V X : Scheme.{u}} [CompactSpace X]
  [QuasiSeparatedSpace X]`. No Noetherian, separated or finite-type condition is added.
- Admissible coefficients: `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`,
  `[MonObj Λ] [IsCommMonObj Λ]` and `hΛ : IsAdmissibleCoefficient Λ`.
  This is the coefficient family used in the recorded stratum Hom dependency, including
  finite prime-power-torsion rings, integral and rational ell-adic coefficients and
  the algebraic closure. `condensedRingObj Λ T` is the actual pulled-back ring on T.
- The factorization a = i after u: `(i : Z ⟶ X) (uS : S ⟶ Z)` with
  `[IsClosedImmersion i] [IsOpenImmersion uS] [QuasiCompact uS]`.
  No extra arbitrary extension-by-zero functor or morphism is assumed.
- Its quasi-compact open complement: `(j : V ⟶ X) [IsOpenImmersion j]
  [QuasiCompact j]` and `hij : Set.range i.base = (Set.range j.base)ᶜ`.
  Thus j is the complementary open, not an unrelated open immersion.
- The finite locally free module: `(L : supportModules Λ S)` and
  `hL : ProEtale.IsLisseCoefficientModule Λ L`. The landed predicate means pro-etale
  locally finite free, allowing varying finite ranks and rank zero. Its scheme parameter
  is inferred as S from L; it imposes no Noetherian or connectedness hypothesis.
- The filtered diagram: `{I : Type (u + 1)} [SmallCategory I] [IsFiltered I]`
  and `K : I ⥤ CochainComplex (supportModules Λ X) ℤ`.
  The index and derived-Hom sizes use the common larger universe of the coefficient
  sheaves. Filtered means nonempty, with cones on pairs and equalizers of parallel arrows.
- Vanishing in degrees below a common b: `(b : ℤ)` and
  `hK : ∀ (t : I) (n : ℤ), n < b → IsZero ((K.obj t).X n)`.
  This is strict termwise vanishing, rather than just vanishing cohomology, and the same
  b works for every t. The diagram may be unbounded above.
- Its colimit K: `colimit K` inside `colimit.post`, formed in the category of complexes,
  whose colimits are degreewise colimits of coefficient modules.
- The source a!L is precisely `(lowerStar Λ i).obj
  ((openImmersionLowerShriek Λ uS).obj L)`, put in degree zero by
  `DerivedCategory.singleFunctor (supportModules Λ X) 0`.
  This is exactly the object in `closedSupport_stratum_globalHom`.
- Derived Hom into K_t[q] and K[q]: the functor is `DerivedCategory.Q ⋙
  shiftFunctor (DerivedCategory (supportModules Λ X)) q ⋙
  preadditiveCoyoneda.obj (op (a!L[0]))`. It first localizes an ordinary complex,
  then shifts, then takes its abelian group of derived morphisms from a!L[0].
- The natural map and bijectivity for every q: `(q : ℤ)` is arbitrary and the conclusion
  is `IsIso (colimit.post K (the above functor))`. By Mathlib's `colimit.ι_post`, its
  composite with the t-th colimit leg is the functor applied to `colimit.ι K t`, hence
  postcomposition by the localized, shifted cocone leg K_t -> K. Isomorphism in
  AddCommGrpCat is equivalent to bijectivity of this underlying group homomorphism.
  It is not an arbitrary comparison or merely existence of some isomorphism.

Dependency declarations read and used:

- `sk-def-pe-site`: `AlgebraicGeometry.Scheme.ProEt`, `Scheme.ProEt.topology`,
  Mathlib.AlgebraicGeometry.Sites.Proetale. The covering condition is the pro-etale
  fpqc finite-refinement topology, not just jointly surjective families.
- `sk-def-sfb-condensed-ring`: `Profinite.CondensedRing`,
  Sheaf.Topology.ProfiniteCondensedRing, the transparent `Mon (Sheaf ... Ab)` encoding;
  its underlying sheaf with MonObj is the unbundled encoding used in the statement.
- `sk-def-sfb-pulled-back-coefficients`: `coefficientRing`, `condensedRingObj`,
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic. The latter is p_X^*Λ;
  the coefficient-ring functor transports the ring structure through the monoidal pullback.
- `def-weil-sheaf-of-modules-category`: `CategoryTheory.ringedSiteModules`,
  Sheaf.CategoryTheory.RingedSiteModules. Read its general ring-sheaf category signature.
  For the condensed ring-object presentation, use the dependency's existing
  `supportModules Λ X` abbreviation for the category of modules over condensedRingObj;
  no new module category or category structure is constructed.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, Mathlib.Algebra.Homology.DerivedCategory.Basic. The instance is
  supplied by the existing Grothendieck module-object framework in universe u+1.
- `def-sfb-right-derived-functor`: `rightDerivedFunctorOfQuasiIsoResolutions`,
  Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions. Read its arbitrary
  K-injective-resolution hypothesis, universal pair and comparison. Reexported through
  the recorded stratum Hom dependency; the statement itself only uses localization.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.colimit`, `colimit.post`,
  `colimit.ι_post`, Mathlib.CategoryTheory.Limits.HasLimits; `CategoryTheory.IsFiltered`,
  Mathlib.CategoryTheory.Filtered.Basic.
- `det-lem-formal-closed-support-stratum-hom`:
  `AlgebraicGeometry.ProEtale.CondensedRing.closedSupport_stratum_globalHom`,
  Sheaf.AlgebraicGeometry.ClosedSupportStratumHom. Its full signature and docstring
  give the same supportModules, extension object and unbounded derived Hom convention.
- `def-pur-sheaf-tensor-product`: `SheafOfModules.cochainModulesMonoidal`,
  Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses, retained through the
  stratum Hom module. Tensor appears in the proof plan through its existing
  `stratumDualTensor`; it is absent from the final Hom continuity signature.
- `def-weil-pbc-scheme-conventions` and `def-weil-size-convention` are metatheoretic
  convention records. Their recorded meanings give the scheme-property classes and
  the explicit u/u+1 universes, not additional definitions.
- The added existing `def-pur-admissible-condensed-ring` supplies
  `IsAdmissibleCoefficient` in Sheaf.AlgebraicGeometry.AdmissibleCondensedCoefficients.
  The added existing `def-sfb-lisse-coefficient-module` supplies
  `AlgebraicGeometry.ProEtale.IsLisseCoefficientModule` from
  `Sheaf.Paper.CoefficientHeartCommonStratification`. Its full signature and docstring
  were checked against the landed node: an existential pro-etale scheme cover, with
  canonical coefficient-module pullback finite free on every member.

Recorded proof modules are imported using non-public imports for proof-only modules,
with the smaller-API exception described in the validation notes below.
For the four Mathlib-only proof leaves the imports are respectively the quasi-separated
scheme API, ExactFunctor, HomologySequence (already public in the stratum Hom module),
and FilteredColimitCommutesFiniteLimit. The current server source was read with
`scompile.py --source` for RingedSiteGrothendieckAbelian, TruncationHypercohomology and
TruncationTriangle, which are absent from the older local source checkout.

Edge cases checked before writing:

- Empty S, empty Z, empty X, empty V, and identity open/closed immersions are allowed.
  The lisse predicate permits the empty covering of the empty scheme and adds no
  nonemptiness assumption. In particular Z=X and V empty are included.
- Rank zero and locally varying ranks are included by Mod.IsFree's existential `n : ℕ`.
  No chosen basis, global constant rank or nonzero coefficient ring is required.
- The zero coefficient ring is included by the existing admissibility predicate.
- Every integer b and every integer q is allowed, including negative q and q<b.
  There is no relation imposed between them and no uniform upper bound.
- I may be a singleton, a directed poset or a genuinely filtered category with parallel
  arrows. The empty indexing category is correctly excluded by filteredness itself.
- No bounded-injective-resolution diagram, derived-complete subcategory, finite Tor
  amplitude, constructible target complex or compactness in all unbounded diagrams is
  inserted as a hypothesis. The conclusion is only for diagrams with a common strict
  lower bound, exactly as in the source.

Searches for an existing statement (msearch.py with group N1 and the item id):

- leanfinder: `Hom from extension by zero of a finite locally free sheaf commutes with
  filtered colimits of uniformly bounded below complexes`. Eight hits about sheaf free
  modules and colimit-compatible functors, none the asserted derived stratum continuity.
- loogle: `CategoryTheory.Limits.colimit.post, CategoryTheory.preadditiveCoyoneda`.
  Zero hits; direct source inspection found both named constructions.
- grep: `colimit.post|isIso.*colimit`, CategoryTheory/Limits. Twenty-five hits, including
  HasLimits.lean:843 for the canonical colimit map, no stratum-continuity theorem.
- rg of the exact item id throughout upstream WeilConjectures: no match. Targeted rg in
  upstream ConstructibleSheaf, published ModuleObject/Colimit, and shared Sheaf pro-etale
  material found coefficient-change compatibility and local finite presentation,
  not this statement. The old source lacks ModuleObject; its published source was read
  from the specified shared framework instead.
- The original local-free search missed the already landed lisse predicate. In this
  repair, `rg --files dag/nodes lean/Sheaf` found the lisse definition node and its
  recorded module; both were opened. `rg` for `def IsFree` in the published module-object
  framework confirms finite free means a finite biproduct, including rank zero.
  The original search conclusion is withdrawn: the existing lisse definition is used.

## Repair of returned delivery

The return on immutable head `31ca687c50b3` identified H12/H4: the local-free definition
introduced a second definition of the landed lisse notion. Deleted the new node
`def-pur-condensed-finite-locally-free` and its module `ProEtaleFiniteLocallyFree.lean`.
Replaced that added statement dependency by the already landed
`def-sfb-lisse-coefficient-module`, retaining every original base dependency and the
existing admissible-coefficient dependency. The module now publicly imports
`Sheaf.Paper.CoefficientHeartCommonStratification` and uses exactly
`(hL : ProEtale.IsLisseCoefficientModule Λ L)`. Updated `lean.statement` verbatim.
There are no new definition nodes or dependency modules in the repaired packet.

The source statement, all nine proof steps, and all remaining Lean binders are retained.
The returned review had checked them correct. The current shared base and saved node
were compared as parsed JSON: only `lean` and `stmt_deps` differ. The delivery wrapper
rebases the packet onto current `newtargets-dag`; no direct repository edits or Git
commands were used.

## Validation notes

The retained proof imports use the smaller existing upper/lower-star API instead of
the broad CartesianCoefficients module. The original compile encountered transitive
universe errors in CoefficientRingedSequenceSite through that broad proof import.
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs` supplies the
exact coefficient pullback needed by proof step 2, together with supportPullback's
exactness and adjunction in the imported closed-support dependency. The DAG proof and
proof_deps are unchanged.

The repaired module passed the prescribed `scompile.py` check in both sandbox
(10.5 seconds) and library (20.4 seconds) contexts, with no errors or warnings.
The author also checked that `lean.statement` is byte-for-byte the declaration signature,
all base statement dependencies are retained, only the two authorized node fields differ
from the current base, and the packet has one module and one node with one sorry theorem.

The initially requested saved-packet dry run began on the old two-module packet. The
repair deleted its duplicate file before that run read back its sources, so it failed
with FileNotFoundError on ProEtaleFiniteLocallyFree.lean. The dry run is rerun on the
complete repaired one-module packet before pushing.

## Second reading by N1

Placeholder under the dispatcher's post-2026-10-17 direct-delivery convention.
No separate worker or independent review is claimed here; the maintainer independently
reviews the delivery. The author's self-check matches every hypothesis and conclusion
above, and specifically checks the landed local-freeness predicate and the verbatim
Lean record after this repair.
