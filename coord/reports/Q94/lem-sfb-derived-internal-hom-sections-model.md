## Worker report

The module `Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel` states
`CategoryTheory.DerivedInternalHomSectionsModel.tensorRightAdjoint_iso` and
`CategoryTheory.DerivedInternalHomSectionsModel.derived_internalHom_sections_model`.
Together they render both numbered clauses of the node. Both proofs are `sorry`;
all helper definitions have actual data and only specialize or compose existing
constructions. No statement correction, new node, or dependency repair is needed.
The existing definition node `def-pur-derived-internal-hom` is added to `stmt_deps`
to reuse its landed, independently universe-polymorphic internal-Hom bifunctor.

Sources read: `sites-cohomology.tex`, Section `section-internal-hom` (08J7),
`equation-internal-hom`, `lemma-RHom-well-defined` (0A95),
`lemma-RHom-from-K-flat-into-K-injective` (0A96),
`lemma-section-RHom-over-U` (08JA), and `lemma-internal-hom` (08J9), including
all displayed Hom-complex calculations and proofs. The current main-20261015
unit `sec-six-functors-basics/sk-lem-int-ext/_section.md` was also read; the
item supplies the global derived-Hom interpretation used by its detail node
`det-lem-int-ext-formula`. There is no change to that unit's assertion or route.

Hypotheses and clauses, in the namespace
`CategoryTheory.DerivedInternalHomSectionsModel`:

- Site: `{C : Type c} [Category.{v} C] {J : GrothendieckTopology C}`. Its objects
  and arrows need not have the same universe. The section universe `max c v r`
  contains both and the coefficient bound. Thus this is a small site in the
  node's size convention, without imposing an equality of site universes.
- Commutative ring sheaf: `R : Sheaf J CommRingCat.{max c v r}`. No condition of
  nonzeroness, finite coefficients, or constant coefficients is imposed.
- Module category: `Modules R` abbreviates the recorded `ringedSiteModules`
  specialized to the underlying ring sheaf of R. It is definitionally the
  original `SheafOfModules`, not another category.
- The sheafification and locally bijective-equivalence instances are the
  infrastructure giving this small-site module category its abelian structure.
  They are available in the selected containing universe, not restrictions
  on the site, the coefficients, or the complexes.
- Unbounded derived category: `Derived R` abbreviates `DerivedCategory (Modules R)`.
  `HasDerivedCategory.{w}` selects its morphism universe. The abelian-group
  derived category independently uses `HasDerivedCategory.{z}`; such choices
  always exist by `HasDerivedCategory.standard`. Neither universe is equated
  with the site or coefficient universe.
- Hom complex: the existing `homComplexFunctor` and `homComplex` are used
  verbatim. No second sheaf-Hom or Hom-complex construction is made.
- K-flat complexes: `CochainComplex.IsKFlatIndependentCoefficients (R := R) P`.
  The helper `totalTensor` is the recorded curried sheaf tensor, extended by
  `map₂HomologicalComplex` to its direct-sum total cochain complex. Its signs
  are the signs of `CochainComplex.mapBifunctor` from the tensor-complex node.
- Fixed K and its derived tensor functor: `tensorRightAdjoint_iso` binds
  `K : Derived R` and `T : Derived R ⥤ Derived R`. Its `model` is exactly the
  node's description of derived tensor: for every K-flat P and representative
  isomorphism `Q.obj P ≅ K`, there is a natural isomorphism
  `Q ⋙ T ≅ (totalTensor R).obj P ⋙ Q`. In particular it computes T on every
  complex representing N, and also on chain maps. This is not an arbitrary
  map or an assumed conclusion about internal Hom.
- Any right adjoint: the same theorem binds arbitrary `H` and `adj : T ⊣ H`.
  It asserts a natural isomorphism `H ≅ (internalHom R).obj (op K)`.
  Here `internalHom` only curries the previously recorded
  `derivedInternalHomOfUniverses`; it makes no new choice of right adjoint.
- Arbitrary A and K-injective J: the domain of the first two natural
  isomorphisms of `derived_internalHom_sections_model` is
  `(Complexes R)ᵒᵖ × (injectiveProperty R).FullSubcategory`. The first factor
  consists of every unbounded complex A, and the second consists of precisely
  the K-injective complexes I, with every chain map between them.
- Clause 1: the first conjunct is a natural isomorphism
  `representedInternalHom R ≅ representativeHom R ⋙ Q`. Its component at
  `(op A,I)` is `RHom(Q A,Q I) ≅ Q(Hom(A,I))`. Compose with
  `tensorRightAdjoint_iso` evaluated at `Q I`, and transport along any
  supplied representative isomorphisms `Q A ≅ K` and `Q I ≅ M`, to obtain
  exactly `H.obj M ≅ Q(Hom(A,I))`. Naturality in maps I to I' is part of the
  natural isomorphism, not omitted or replaced by pointwise existence.
- Global sections: `sections` is exactly
  `preadditiveCoyoneda.obj (op (SheafOfModules.unit ...))`, i.e. Hom_R(R,-).
  `derivedSections` applies the already-defined `Functor.rightDerivedFunctor`
  to it with the same Grothendieck/K-injective infrastructure as the recorded
  `ringedSiteZerothHypercohomologyOfUniverses`. It retains the full derived
  complex instead of composing with zeroth homology. No functor is chosen
  from a mere existence statement. At the standard abelian-group localization,
  composing with zeroth homology is the recorded zeroth-hypercohomology functor.
- Clause 2, full complex: the second conjunct is a natural isomorphism
  `representedInternalHom R ⋙ derivedSections R ≅ globalHom R ⋙ Q`.
  `globalHom` is the termwise application of `sections` to `representativeHom`.
  Thus it is exactly the ordinary sections complex of Hom(A,I), localized
  in the derived category of abelian groups. The same composition with the
  first theorem handles any chosen H. Naturality includes every source map
  A' to A and target map I to I', because these are exactly the morphisms
  in the product domain of this natural isomorphism.
- Clause 2, global morphism complex and degree terms: the third conjunct
  provides a chain isomorphism from that sections complex to Mathlib's
  `CochainComplex.HomComplex A I`, even for arbitrary I. Its degree n is
  `HomComplex.Cochain A I n`, the family of morphisms A.X p to I.X q with
  p+n=q. Equivalently, it is the product over p of A.X p to I.X (p+n),
  exactly the displayed product in the node. Its differential is
  `d_I f - (-1)^n f d_A`. The equation following the isomorphism states
  explicitly, at every p,q,hpq, that pre- and postcomposition are
  `f.f p ≫ component ≫ g.f q`. This also records the comparison's naturality
  as an ordinary complex, before localization.
- The “in particular” assertion is the final conjunct, for arbitrary
  `K M : Derived R` and `n : ℤ`: the additive equivalence between
  `(homologyFunctor ... n).obj (RΓ(RHom(K,M)))` and `(K ⟶ M⟦n⟧)`.
  Through `tensorRightAdjoint_iso` it yields the stated H_K formula.
- The final sentence is respected literally: there is no boundedness
  predicate on K, M, A, or I and no flatness predicate on A. K-flatness
  occurs solely in the characterization of the derived tensor functor.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`,
  including its exact alias to `SheafOfModules` and its abelian-instance hypotheses.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `HasDerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory` and `DerivedCategory.Q`;
  the full size documentation and localization signature were read.
- `Sheaf.Algebra.Homology.HomComplex`, `CategoryTheory.homComplexFunctor` and
  `CategoryTheory.homComplex`, including the product, differential and
  functoriality specification in `homComplex_exists`.
- `Sheaf.Algebra.Homology.KFlat`,
  `CochainComplex.IsKFlatIndependentCoefficients` and its canonical monoidal
  and zero-map-preserving infrastructure; the full predicate was read.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`,
  `CochainComplex.IsKInjective`, whose definition is null-homotopy of maps
  from acyclic complexes, with no degreewise injectivity assumption.
- `Mathlib.Algebra.Homology.BifunctorShift`, `CochainComplex.mapBifunctor`,
  the recorded total tensor, obtained functorially by `map₂HomologicalComplex`;
  and `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`,
  `SheafOfModules.monoidalCategory` and `curriedTensor`.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`,
  `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses`, including its
  entire defining expression for H0 composed with RΓ. The source of
  `Functor.rightDerivedFunctor` and its K-injective computation was read.
- Added landed dependency `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`,
  `CategoryTheory.derivedInternalHomOfUniverses`, with its product-localization
  definition and natural comparison/representative theorems, read in full.
- `def-weil-size-convention` has no Lean declaration by design. It is rendered
  by the explicit universes and localization choices just described.

Edge cases checked before writing: the empty site; the zero ring sheaf; zero
source or target complexes; unbounded complexes in either direction; n=0 and
negative integers; non-flat source complexes; sites with different object and
arrow universes, notably object universe t+1 and arrow universe t with
coefficients max u (t+1). None is excluded by the binders. The object/arrow
universe equations required explicit universe arguments on the transparent
aliases; that elaboration repair does not equate or restrict these universes.
The naturality equation was checked for identities and arbitrary f,g, with
f contravariant and g covariant. The global Hom differential matches the
sign convention of the recorded sheaf Hom complex.

Searches made (actual queries/results):

- `msearch.py`, leanfinder: “Derived internal Hom of module sheaves is the Hom
  complex into a K-injective and its derived global sections are the global
  Hom complex”. Eight hits: Ext, presheaf sheafification Hom equivalences,
  LightCondensed internal-Hom evaluations, ordinary sheaf cohomology. None
  states this full-complex comparison or the arbitrary-right-adjoint assertion.
- `msearch.py`, loogle: `CochainComplex.HomComplex, CochainComplex.IsKInjective`:
  zero hits.
- `msearch.py`, grep: `HomComplex|IsKInjective`, subdirectory `Algebra/Homology`:
  25 hits for the existing K-injective predicate and external Hom-complex API.
- Direct rg in Mathlib for the intended full declaration names: no collision.
- Direct rg of upstream `WeilConjectures` for HomComplex, homComplex,
  derivedInternalHom, RHom, and derived/global sections: generic closed
  derived categories and specialized geometry constructions, no matching
  ringed-site statement. Direct grep by this node id gives no match.
- Direct rg of `lean/Sheaf`: found and read `DerivedInternalHomOfUniverses`,
  `RhomGlobalSectionsOfUniverses`, `RingedInternalHomExactRestriction`,
  `HomComplexGlobalHomotopy`, and the normalized global-cochain interfaces.
  The first is reused as a landed dependency. The others concern H0 only,
  derived currying, or ordinary global cohomology; none includes the full
  derived global sections for arbitrary A and any chosen tensor right adjoint.
  The intended new declaration names and namespace have no existing matches.
- DAG: read every recorded statement dependency and the additional landed
  internal-Hom node. No new notion is introduced that requires another node:
  helpers only apply recorded functors, take a full subcategory, or curry them.

Validation uses only the required `scompile.py` wrapper and `deliver2.py --no-push`.
The only proof holes are the two named theorem statements above, each with a
source-based complete proof docstring, both belonging to this DAG statement.

## Second reading by Q94

I read the unchanged item statement and its six proof steps against Stacks
`sites-cohomology.tex`, Section 08J7 (`section-internal-hom`), equation-internal-hom,
08JA (`lemma-section-RHom-over-U`), 08J9 (`lemma-internal-hom`), 0A95 and 0A96.
The source assumes a ringed site throughout; it imposes no Noetherian, characteristic,
boundedness, nonzero-ring or source-flatness hypothesis. The commutativity assumption
in the node is the one needed for its module-valued tensor/internal Hom. There is no
statement_change or maintenance repair note for this item.

Here is my object/hypothesis/conclusion checklist, in node order. All Lean names below
are in `CategoryTheory.DerivedInternalHomSectionsModel` unless qualified.

1. A small site C: `{C : Type c} [Category.{v} C] {J : GrothendieckTopology C}`.
   The chosen module universe `max c v r` contains the site objects and arrows.
   Verdict: exact, including unequal site universes; no SmallCategory equality.
2. A sheaf of commutative rings O: `R : Sheaf J CommRingCat.{max c v r}`.
   Verdict: exact. R is an arbitrary sheaf, not necessarily constant or nonzero.
3. Mod(O): `Modules R` specializes the recorded `ringedSiteModules` on R's
   underlying RingCat sheaf. I opened RingedSiteModules.lean: this is exactly
   `SheafOfModules`, with Mathlib's linear maps and abelian structure. Verdict: exact.
4. The unbounded derived category: `Complexes R` uses `CochainComplex ... ℤ`;
   `Derived R` uses `DerivedCategory` with `[HasDerivedCategory.{w} ...]`.
   I read Mathlib's localization signature and size convention. Verdict: exact;
   no truncation or equality between w and the site/coefficient universes.
5. The Hom complex: `representativeHom` applies the dependency's
   `homComplexFunctor`, and the third conjunct uses `homComplex (R := R) A I`.
   I read HomComplex.lean, including its product terms, differential and maps.
   Verdict: the recorded sheaf Hom complex, not the external Hom complex substituted
   for it. `CochainComplex.HomComplex` appears only after applying sections.
6. K-flatness and total tensor: `IsKFlatIndependentCoefficients` is the recorded
   acyclic-total-tensor predicate. `totalTensor` applies the canonical sheaf tensor
   and `map₂HomologicalComplex` with the standard cochain total signs.
   I opened KFlat.lean and the tensor-complex node's Mathlib declarations.
   Verdict: exact; no extra termwise flatness or boundedness premise.
7. Fix K and any right adjoint H_K: `tensorRightAdjoint_iso` binds K, T, H,
   `model`, and `adj : T ⊣ H`. The model states the natural functorial tensor
   computation for every K-flat P with `Q.obj P ≅ K`; it does not assume an
   internal-Hom comparison. Verdict: this expresses the node's derived tensor
   hypothesis and arbitrary right adjoint. Quantifying over all such P adds no
   mathematical restriction to the derived tensor functor described in the node.
8. Any representative A of K and K-injective I representing M: the domain
   `(Complexes R)ᵒᵖ × (injectiveProperty R).FullSubcategory` includes every A and
   precisely every K-injective I, with all chain maps. `representedInternalHom`
   evaluates the existing derived bifunctor at `(op (Q.obj A), Q.obj I)`.
   Transport along arbitrary representative isomorphisms gives the node's general
   K,M; it imposes no equality of complexes and derived objects. Verdict: exact.
9. Clause 1: the first conjunct of `derived_internalHom_sections_model` is a
   natural isomorphism `representedInternalHom ≅ representativeHom ⋙ Q`.
   Compose its component at `(op A,I)` with the component of
   `tensorRightAdjoint_iso` to get `H.obj (Q.obj I) ≅ Q.obj (homComplex A I)`.
   Naturality in every map of K-injective targets follows from both natural
   isomorphisms. Verdict: the node's complete first clause, with no flatness of A.
10. RΓ and clause 2: `sections` is literally `Hom_O(O,-)` through
    `preadditiveCoyoneda.obj (op (SheafOfModules.unit ...))`.
    `derivedSections` uses its actual `rightDerivedFunctor`, using the same
    Grothendieck/K-injective instance as the recorded
    `ringedSiteZerothHypercohomologyOfUniverses`. I opened both that definition
    and the upstream rightDerivedFunctor construction: this retains the full
    derived complex before H0, with an independent target localization z.
    The second conjunct identifies this functor on represented internal Hom with
    `globalHom ⋙ Q`. Verdict: full derived-sections comparison, not only H0.
11. Naturality in A' → A and I → I': the second conjunct is a natural isomorphism
    on the product category, so includes simultaneous contravariant source and
    covariant target maps. The arbitrary H version follows through item 9.
    Verdict: both variables present with the correct variance.
12. The global morphism complex and its degree-n product: the third conjunct
    gives an ordinary chain isomorphism to Mathlib's `CochainComplex.HomComplex A I`.
    I opened its `Cochain`, `Triplet`, differential and `HomComplex` definitions:
    degree n consists of all maps A^p → I^q with p+n=q, equivalently the product
    over p of Hom(A^p,I^(p+n)); the differential is d_I f - (-1)^n f d_A.
    The displayed component equation is precomposition by f.f p and postcomposition
    by g.f q. Verdict: all degree terms, differential and pre-localization
    naturality agree. Allowing arbitrary I in this ordinary comparison is valid:
    no K-injectivity enters the underived sections/product identification.
13. In particular, every integer n: the last conjunct gives the additive
    equivalence between `H^n (RΓ (internalHom K M))` and `K ⟶ M⟦n⟧` for all
    `K M` and `n : ℤ`. TensorRightAdjoint_iso transports it to any H_K.
    Verdict: exact all-degree group isomorphism, not a nonnegative Ext-only claim.
14. Final absence of bounds/flatness: no theorem premise bounds A, I, K or M.
    The only K-flatness premise occurs in the tensor model. Verdict: exact.

I also opened the recorded derived-internal-Hom definition and all its independent-
universe comparison signatures. Its definition is the actual product-localization
of Hom with canonical K-injective replacement, and the new `internalHom` just curries
it. The canonical sections functor and right derived functor are specializations of
already recorded constructions; the other helpers merely compose functors or restrict
to a full subcategory. They introduce no independent mathematical notion requiring a
new definition node. There are no new nodes or dependency modules in this delivery.
The K-injective dependency is a Mathlib leaf, whose `mathlib_match` is exactly
`CochainComplex.IsKInjective`; I checked its null-homotopy definition directly.

Edge cases: the empty site and zero ring sheaf are allowed by the binders; there is
no chosen site object or global point. Zero source and target complexes are allowed.
The product is over all integers and needs no finite-support condition. n=0 and
negative n are included. Characteristic is unrestricted. The module and coefficient
universe contains c and v separately; in particular c=t+1 and v=t works without an
equality. Derived morphism universes w,z stay independent. Sheafification and locally
bijective-equivalence instances are the usual infrastructure at the containing
universe, not extra geometric assumptions. No index nonemptiness or flatness of A
was introduced. I checked that every variable and universe in the file is bound.

Independent searches during this reading:

- LeanFinder through msearch.py: "The hypercohomology of sheaf Hom into an unbounded
  K-injective complex equals morphisms into every shift in the derived category".
  Eight hits, led by
  `CochainComplex.HomComplex.CohomologyClass.bijective_toSmallShiftedHom_of_isKInjective`.
  I opened DerivedCategory/KInjective.lean. That theorem supplies the external Hom
  cohomology/derived-morphism comparison, without the sheaf internal Hom, its full
  RΓ comparison, or arbitrary tensor right adjoints; it is not the item.
- Loogle through msearch.py: `"rightDerivedFunctor", "HomComplex"`: zero hits.
- msearch.py grep: `RHom|derivedHom|internalHom`: 25 largely unrelated substring
  matches (OrderHom, field embeddings, etc.), no full ringed-site comparison.
- Direct rg with `derived.*(sections|hom)|rhom|hom.*kinjective` in upstream
  WeilConjectures and the project's homological modules. I opened
  `RhomGlobalSectionsOfUniverses`: its comparison is H0 only. I opened
  `HomComplexGlobalHomotopy`: it takes H0 and concerns homotopy morphisms.
  Neither is the full statement here. Upstream sheaf MonoidalClosed contains
  the ordinary, un-derived tensor-Hom adjunction, which also does not match.
- Direct rg for both new theorem names in Mathlib, upstream and the shared project
  found no existing declaration; only this sandbox's own module/node records.
  No existing complete statement was found, so this is not an existing:true item.

Mismatch found and repaired: H9 / stage-2 import convention. The worker had not
explicitly imported several recorded proof-dependency modules. I added ordinary
imports for KFlatResolutionIndependentCoefficients, QuasiIsoHomComplexMap,
KInjectiveHomComplex, HomComplexGlobalHomotopy, HomTensorTotal,
RingedSiteKInjectiveResolutionsOfUniverses, Mathlib's derived KInjective and
BifunctorShift, and upstream sheaf InternalHom; HomComplex is an explicit public
statement import. These keep the node's proof plan available for stage 3.
The mathematical signatures, helper data, node statement and dependency interfaces
were already correct and are unchanged. All definitions have real data; the only
proof holes remain the two named theorems. Their docstrings cover the six node proof
steps: representative invariance, tensor-Hom currying and Koszul exchange, uniqueness
of the right adjoint, the K-flat comparison and RΓ computation, natural transport,
and the global-cochain/shifted-Hom identification. Both carry the exact source and
blueprint id. No proof, private definition, local notation, or local instance was added.

Validation: scompile.py compiled the delivered module both before and after the import
repair, with no error or warning (latest library run: 4.9 seconds). The node's
`lean.statement` remains verbatim equal to the final theorem signature. Delivery
preflight and push results are recorded below after running the prescribed wrapper.

Dry run: `deliver2.py Q94 lem-sfb-derived-internal-hom-sections-model --no-push`
returned OK, commit b5b4f693eb, with preflight and compilation passing. No files beyond
the item's module, item node and report were staged.
