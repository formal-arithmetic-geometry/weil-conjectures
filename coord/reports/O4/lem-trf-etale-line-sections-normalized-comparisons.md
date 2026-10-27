## Worker report

The single theorem `AlgebraicGeometry.Scheme.etale_line_sections_normalized_comparisons`
states the complete node. Its proof is `sorry`; no definitions or other postponed
theorems are introduced. The node is unchanged outside `lean`. No statement correction,
new node or dependency repair is needed.

Sources read: Stacks `descent.tex`, proposition-equivalence-quasi-coherent (03DX),
proposition-equivalence-quasi-coherent-functorial (03LC),
remark-change-topologies-ringed-sites, lemma-equivalence-quasi-coherent-properties
(05VG). Also read the current blueprint ancestor
`latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`.
The item is an auxiliary construction in its proof, not a blueprint unit statement.
The source gives the associated-module functor, its pullback compatibility and
preservation of finite local freeness; the eight-step node proof expands precisely
the normalization and coherence needed here. The theorem docstring follows all eight
steps, including their adjunction and associativity arguments.

Hypotheses and clauses, in the order of the Lean statement:

1. `universe u`, `X : Scheme.{u}` and `X.Etale`/`X.smallEtaleTopology` implement the
   scheme, size convention and small etale site. The site has objects in `u+1`,
   morphisms in `u`, and the section modules and rings are in `u`. There is no
   extra Noetherian, separated, finite-type, nonempty or quasi-compact hypothesis.
2. `TrfInvertibleModules X` is the existing full subcategory on
   `Modules.IsInvertible`; its morphisms are every ordinary module morphism.
   `A X : TrfInvertibleModules X ⥤ TrfEtaleLineModules X` gives the functor.
   The line-valued codomain records the local-triviality conclusion of the node,
   rather than an extra hypothesis on an arbitrary input module sheaf.
3. `α X L : trfLineSections ((A X).obj L) ≅ trfInvertibleSections L` supplies the
   section coordinates. The latter is exactly the recorded
   `Modules.etaleTensorSectionsSheaf L.obj`, using invertibility's quasi-coherence
   instance. Thus these coordinates have the actual tensor-pullback section groups
   and the existing unit-normalized restrictions, with no extra sheafification.
   The first conjunct pins the scalar action to the usual action on these groups.
   Since `α` is a sheaf isomorphism, it also intertwines every site restriction.
4. The second conjunct quantifies over `h : L.obj ⟶ K.obj`, without invertibility
   assumptions on `h`, and identifies its image in section coordinates with
   `((Modules.tensorPullback U.hom).map h).app ⊤`. The functor type supplies the
   identity and composition laws.
5. `ε X` is a module-sheaf isomorphism to the structure module of
   `trfEtaleStructureRing X`. That ring's presheaf is exactly
   `X.etaleStructurePresheaf ⋙ forget₂ CommRingCat RingCat`, namely global functions
   on each etale object with their usual restrictions. The third and fourth
   conjuncts specify epsilon and its inverse in section coordinates as
   `trfTensorUnit U.hom` and its inverse. This existing comparison is the unique
   tensor-adjunction comparison to the ordinary pullback, followed by its unit map;
   its local tensor formula is `a ⊗ b ↦ a u♯(b)` with inverse `a ↦ a ⊗ 1`.
   This is a sheaf tensor formula, not a claimed tensor/global-section commutation.
6. The witness `p` is the conclusion that `(Modules.tensorPullback v).obj L.obj`
   is invertible for every etale `v`. It is existential proof data, not an assumed
   extra pullback-invertibility hypothesis.
7. `β X Y v L` is an isomorphism of module presheaves after precomposition by
   `trfEtaleCompose v`, whose value at `W` is `W.hom ≫ v`. The restricted structure
   ring is definitionally the structure ring for `Y`: both give the same rings
   `Γ(W.left, ⊤)` and the same restriction homomorphisms. Beta's target is a module
   sheaf, so its source is a sheaf as well. Thus this is exactly the module-sheaf
   restriction comparison, expressed through the fully faithful presheaf forgetful
   functor, without assuming a separate site-continuity interface. The fifth
   conjunct specifies its component by `(Modules.tensorSectionsComp W.hom v).inv`.
   Beta's type includes linearity, naturality for every site arrow, and its inverse.
8. The sixth conjunct is beta's naturality for every `h`; the order of factors
   matches the node: beta followed by the image of `v^*h` equals the restricted
   image of `h` followed by beta.
9. The seventh conjunct is identity coherence using `trfTensorId` and the site
   identification `trfEtaleIdArrow`. It includes arbitrary sections and every
   site object, and hence equality of the specified natural transformations.
10. The eighth conjunct is composition coherence, with the comparison
    `Modules.tensorSectionsComp w v` in its forward direction after the two betas.
    `trfEtaleCompArrow` supplies the canonical associativity identification of the
    iterated restriction. Both `v` and `w` carry precisely `[Etale ...]`.
11. The ninth conjunct is the structure compatibility equation from proof step 7:
    epsilon on Y, after `A_Y(trfTensorUnit v)` and beta, equals restricted epsilon
    on X, at every test object and section. This also makes the unit-compatible
    identity and iterated-restriction cases explicit through the preceding laws.
12. The last conjunct quantifies over every Zariski open family `V`, its covering
    condition `_hV`, and every chosen tensor-pullback frame `frame`. It asserts
    `CoversTop` for their etale images, and gives isomorphisms `τ i` to the structure
    module whose components are exactly beta, the image of `frame i`, and epsilon.
    The inverses of `τ` are therefore the required local frames. Their type supplies
    naturality for all site restrictions, not just a pointwise bijection. The
    index `I : Type (u+1)` follows the site's ambient size convention; no finite
    index or quasi-compactness hypothesis is introduced.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`,
  `Scheme.smallEtaleTopology`, and the jointly-surjective covering criterion.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, its quasi-coherence and unit instances.
- `WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf`:
  `Scheme.Modules.etaleTensorSectionsSheaf` (through `trfInvertibleSections`).
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the actual
  `tensorPullback`, uniquely section-normalized adjunction and identity/composition
  interfaces. The module retains the recorded tensor construction.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules`, with its linear morphisms.
- `WeilConjectures.AlgebraicGeometry.EtaleTensorSections`:
  `tensorSectionsComp`, `tensorSectionsUnit`, `etaleTensorSectionsRestriction` and
  `etaleTensorSectionsPresheaf`; their normalized adjunction is the existing one.
- The proof imports retain `EtaleQuasiCoherentDescent`, `TensorPullbackAdjunction`,
  `TensorPullbackStructureSheaf`, `EtaleTensorUnitRestrictionEquation`,
  `Mathlib.AlgebraicGeometry.Modules.Tilde`, `Adjunction.CompositionIso`,
  `Adjunction.Mates`, and `ZariskiEtaleInclusionMorphismOfSites`.
  Imports already public through the shared definitions module are not duplicated.
  The abstract-pullback quasi-coherence lemma transports to tensor pullback by
  their canonical left-adjoint comparison; no new hypothesis is imposed.

Shared-definition import: `SchemeEtaleInvertibleComparison` already owns
`TrfInvertibleModules`, `TrfEtaleLineModules`, `trfEtaleStructureRing`,
`trfInvertibleSections`, `trfLineSections`, `trfEtaleCompose`, `trfComparisonMap`,
`trfTensorId`, `trfTensorUnit`, `trfStructureInvertible`, `trfEtaleIdArrow`, and
`trfEtaleCompArrow`. All were read and are reused verbatim. Its theorem
`scheme_etale_invertible_comparison` is NOT used: it asserts a categorical
equivalence, while this item constructs the functor and additionally records the
unit compatibility and the frames from every chosen cover. It therefore is not
an exact existing match for this node. No new categorical equivalence is asserted.
The owner node is a DAG consumer of this item, so it is not added as a dependency:
this import is solely for its already shared definitions. A future reverse proof
import from that mixed definition/theorem module would close the path
`SchemeEtaleInvertibleComparison -> EtaleLineSectionsNormalizedComparisons ->
SchemeEtaleInvertibleComparison` and must be omitted under stages/2-statements §3.7;
the maintainer may separate the shared definitions when proving the consumer.
No declaration in this delivery is defined from the consumer's theorem.

Edge cases checked before writing: the empty scheme and empty trivializing family
are allowed; the coverage hypothesis for an empty family forces the scheme empty.
There are no nontriviality assumptions on global function rings. Zero maps,
noninvertible module maps, identity scheme maps, composite etale maps and arbitrary
(including infinite) trivializing covers are retained. No global sections/tensor
product commutation is assumed. No extra equality of site object and morphism
universes is imposed. No statement dispute was found.

Searches for an exact existing statement (all via prescribed msearch, plus source rg):

- LeanFinder query: `Invertible module small etale tensor section functor normalized
  restriction comparison`. Eight hits on Kaehler differentials and ordinary ring
  etale theory; none on this module-sheaf comparison.
- Loogle query: `"tensorSectionsComp"`. Zero hits.
- Mathlib grep query: `etale.*[Rr]ing|[Rr]ing.*etale|tensorSections` in
  `AlgebraicGeometry`. Twelve files on etale ring maps/sites, no matching theorem.
- LeanSearch query: `The sheaf of sections of tensor pullbacks of an invertible
  sheaf on the small etale site is a module sheaf functor with normalized unit and
  coherent restriction comparisons`. Eight hits, on module pullback, its adjunction,
  sections functors and the unit; none is the full normalized comparison.
- `grep -rn` for the item id in `lean/WeilConjectures`: no occurrence.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the theorem name,
  `tensorSections.*Functor`, `etaleTensor.*Functor`, and the structural-ring and
  etale-module names found the shared trf definitions above and the existing
  additive section functor in `EtaleTensorSectionsRightExact`. The latter lands in
  abelian sheaves (with a universe lift and sheafification for arbitrary modules),
  and does not state this ring-module comparison or its normalized coherences.

Validation: the module passed scompile.py in both sandbox and library module forms
with no errors or warnings after replacing the reserved `λ` binder by `frame`.
The prescribed deliver2.py --no-push dry run passed preflight and compilation
(431b7658fe2). The unowned older sandbox draft was preserved under scratch/ so
that only the current node-owned module enters the delivery. Final delivery follows.

## Second reading by O4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
