## Worker report

The item is stated by `CategoryTheory.CoherentSitePseudofunctor.varyingSite_evaluation_adjoints`
in `Sheaf.CategoryTheory.VaryingSiteEvaluationAdjoints`. Its conclusion is the existence of
`AbelianEvaluationAdjoints`, which retains every component, transition, and Hom formula.
The only postponed proof is this named theorem; its docstring gives all eleven proof steps.
All definitions have concrete data. No statement correction is made.

Hypotheses and clauses, matched individually:

- The small index category is `{I : Type u} [Category.{v} I]`; no order, filteredness,
  nonemptiness, uniqueness of arrows, or finiteness hypothesis is imposed.
- The small sites and coherent site functors are the existing
  `CoherentSitePseudofunctor I F`, with `F : LocallyDiscrete Iᵒᵖ ⥤ᵖ Cat.{w,w}`.
  Its `coverage` and `site` use `Precoverage.IsSiteForCoverings`; `continuous` and
  `preservesCoverPullbacks` express continuity of the site functors. `F.mapId` and
  `F.mapComp` include the unit/pentagon coherence. Thus no strictness is assumed.
- The morphism-of-sites condition is `siteMorphism`, finite-limit preservation of the
  actual inverse image on sheaves of sets, `D.inverseImage a`. Preservation of colimits
  follows from its actual adjunction, so this is the exactness of the source convention.
- Abelian inverse/direct images are `abelianInverse` (the sheafified left Kan extension)
  and `abelianDirect` (precomposition on sheaves); `abelianAdjunction` is their actual
  Mathlib adjunction. The two quantified `Additive` instances are precisely the supplied
  additive adjunction hypothesis. `abelianInverseId` and `abelianInverseComp` are mates
  of `abelianDirectId` and `abelianDirectComp`, induced by the site pseudofunctor.
- The category S is `D.AbelianSystem`: its `obj`, `transition`, `transition_id`, and
  `transition_comp` are the family and identity/cocycle laws. Its Hom is the subgroup
  `abelianSystemHom` of ALL compatible component maps, with the stated compatibility
  equation. Category operations and the preadditive structure are componentwise.
- Evaluation is the actual `abelianEvaluation i`; its object/map formulas are explicit,
  and `abelianEvaluationAdditive` supplies additivity.
- `left` and `right` are functors, with `left_additive` and `right_additive`.
  `leftAdjunction` and `rightAdjunction` are exactly L_i ⊣ ev_i ⊣ R_i.
- `leftComponent` identifies the j-component with the coproduct over `a : j ⟶ i`
  of `(D.abelianInverse a).obj A`; `rightComponent` identifies it with the product
  over `a : i ⟶ j` of `(D.abelianDirect a).obj A`. These are Mathlib sheaf products
  and coproducts, not sectionwise coproducts mistaken for sheaves.
- `left_naturality` and `right_naturality` impose naturality in A using `Sigma.map`
  and `Pi.map`. Compatibility across j is exactly the two transition fields below.
- `left_transition` precomposes with the pulled-back a-coprojection and inserts the
  actual inverse-image compositor before the `(c ≫ a)` coprojection.
- `right_transition` postcomposes with the b-projection. Its right side pulls back
  the `(b ≫ c)` projection followed by the inverse direct-image compositor, and then
  applies the counit at `(D.abelianDirect b).obj A`. No inverse image of a product is
  identified with the product of inverse images.
- `left_hom` specifies restriction to the identity summand, inserting the inverse
  of `abelianInverseId`; `left_hom_inverse` specifies every summand of its inverse
  as inverse image of h followed by the system transition.
- `right_hom` specifies identity-factor projection, followed by `abelianDirectId`;
  `right_hom_inverse` fixes every factor to the adjunct of transition followed by h.
  Mathlib `Adjunction.homEquiv` includes both naturality laws and both inverse identities.
- Empty products and coproducts use the same actual universal constructions as every
  other index set; in abelian sheaves they are zero objects. No nonempty-arrow assumption
  or singleton-identity simplification is used. The statement uses isomorphisms for the
  source's canonical identifications, as required by the stage's isomorphism convention.

Universes: `u` sizes index objects, `v` index arrows, and `w` site objects/arrows.
Coefficients are `AddCommGrpCat.{max v w}`, so arrow-indexed products/sums fit while
site and index universes stay independent. Every universe and variable is explicitly
bound; `autoImplicit` is false. The displayed size convention permits these common bounds.

Dependencies read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, the recorded site dependency.
- `Sheaf.CategoryTheory.TotalSitePseudofunctor`:
  `CategoryTheory.CoherentSitePseudofunctor`, and Mathlib `Pseudofunctor` for its input.
  This existing structure is now owned by `def-per-coherent-site-diagram`,
  which the item and the abelian-system definition cite.
  No total-site theorem, total-site hypothesis, or total sheaf category is assumed.
- `Sheaf.CategoryTheory.TotalSiteSheafSystems`: existing set-valued inverse image and
  its comparison pattern. The node `def-per-coherent-site-sheaf-adjunction` owns
  its set-valued fibre/direct/inverse/adjunction declarations, including the actual
  inverse image in the morphism-of-sites hypothesis. Abelian coefficients require
  the separate abelian-system definition below.
- `Mathlib.CategoryTheory.Sites.Pullback`:
  `Functor.sheafPullbackConstruction.sheafPullback` and `sheafAdjunctionContinuous`.
- `Mathlib.CategoryTheory.Adjunction.CompositionIso`:
  `Adjunction.leftAdjointIdIso` and `leftAdjointCompIso`, the actual mate constructions.
- `Mathlib.CategoryTheory.Limits.Shapes.Products`: `piObj`, `Pi.π`, `Pi.map`,
  `sigmaObj`, `Sigma.ι`, `Sigma.map`; coproduct is the discrete colimit of the
  recorded `def-weil-pbc-category-colimit` declaration `Limits.colimit`.
- Proof imports: `Mathlib.CategoryTheory.Adjunction.Limits`
  (`Adjunction.leftAdjoint_preservesColimits`, `rightAdjoint_preservesLimits`);
  `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic` (`combinedIsColimit`);
  `WeilConjectures.CategoryTheory.SiteMorphismComposition` (`siteMorphism_composition`).
  Sheafification and sheaf limit modules, already public in the import closure, provide
  `presheafToSheaf`, `sheafificationAdjunction`, `Sheaf.createsLimits`.
  `Adjunction.mkOfHomEquiv`, `Adjunction.comp`, and `Adjunction.id` are likewise imported
  through the actual sheaf adjunction interfaces. The metatheoretic size node has no
  Lean object, and is represented by the explicit universes.

Edge cases checked before drafting: empty I (the theorem quantifies i and is vacuous,
while the definition still makes sense); discrete I (other fibres have empty sums and
products); zero A (all formulas use zero maps); the walking arrow (free support points
backward and cofree support forward); a one-object monoid (all endomorphisms are retained,
and only the identity summand/factor defines the Hom restriction). Identity comparisons
are not assumed literally identities; both are inserted in the Hom equations.

Searches: prescribed `msearch.py` LeanFinder query "Evaluation on compatible systems
of abelian sheaves over varying sites has coproduct inverse image and product direct image
adjoints" returned fixed-site sheaf adjunctions, no match. Loogle
`CategoryTheory.evaluationLeftAdjoint, CategoryTheory.Adjunction` returned ordinary
`evaluationAdjunctionRight`, which has a single fixed target category. Grep
`evaluationLeftAdjoint|evaluationRightAdjoint|Pseudofunctor.*Section|structure.*Section`
found ordinary evaluation adjunctions and an unrelated multiequalizer section.
LeanSearch "Category of compatible abelian sheaves on a pseudofunctor of sites with
componentwise morphisms and evaluation functors" returned sheaf category/preadditive
instances and sheafification, no varying-site system. Loogle `CategoryTheory.Sheaf,
CategoryTheory.Adjunction` returned sheafification adjunctions. Grep
`AbelianSystem|abelianEvaluation|SheafSystem` in Mathlib CategoryTheory returned no hits.
Local rg of WeilConjectures and Sheaf for varying-site/evaluation/cofree/system terms
found the existing set-valued `TotalSiteSheafSystems`, ringed semisimplicial systems and
fixed-site coefficient towers; none supplies this abelian notion or this theorem.
Searching the exact item id in WeilConjectures found no declaration.
`tools/blueprint_refs.py search 'compatible systems of abelian sheaves'` returned zero
blueprint matches. DAG searches found the current item and its consumers, but no
standalone definition of these arbitrary varying-site abelian systems.
The new node records the full raw outputs of four prescribed searches.

The source was read locally: `sites-cohomology.tex` lemma-colim-sites-injective (0EXZ),
including its arrow-indexed product proof, and `spaces-simplicial.tex`
lemma-restriction-to-components-site (09WG), including (5)-(7) and the summand Hom proof.
The item explicitly generalizes their constructions to arbitrary coherent small diagrams.
There is no disputed statement or silent source correction.

## New nodes

`def-per-coherent-site-diagram` owns the existing structure
`CategoryTheory.CoherentSitePseudofunctor` in its declaring module
`Sheaf.CategoryTheory.TotalSitePseudofunctor`. Source: Stacks 09WC Case A and
preceding pseudofunctor discussion, for a general small index category. This is
an `existing: true` record, with no duplicate structure or new Lean module.

`def-per-coherent-site-sheaf-adjunction` owns the four existing declarations
`fibreSheaves`, `directImage`, `inverseImage`, and `imageAdjunction` in their
declaring module `Sheaf.CategoryTheory.TotalSiteSheafSystems`. Its primary
declaration is `inverseImage`. Source: Stacks 00WX. The node depends on the
coherent-site definition and the recorded sheafification definition. Its
`existing: true` record lists all four declarations. The item cites both new
owners; the abelian-system definition cites the coherent-site owner. Searches
of DAG, blueprint and project found no definition-node owners, and Mathlib
searches found the constituent constructions but no assembled coherent-site
interface. Both nodes retain the full raw search results. Neither total-site
theorem is a statement dependency.

`def-per-varying-site-abelian-systems` owns
`Sheaf.CategoryTheory.VaryingSiteAbelianSystems`. It defines the actual abelian sheaf
fibres, canonical inverse/direct images, their adjunction and mate comparisons, all
compatible systems, compatible component maps, their category and preadditive structure,
and additive evaluation. Source: Stacks 0EXZ systems and 09WF compatible families.
The existing set-valued `CoherentSitePseudofunctor.SheafSystem` cannot supply abelian
sheaves, additive maps, or the required Hom groups; it is not copied or redefined.
The site/pseudofunctor interface and Mathlib sheaf constructions are reused. Searches
above and in the node's mathlib_searches found no abelian-system definition.

## Second reading by Q22

Independent second reading (maintainer review service, head 304cf397), replacing the
earlier self-read. Node clauses, with the Lean rendering and verdict:

1. Small category I, fixed universes: `{I : Type u} [Category.{v} I]`; no filteredness,
   nonemptiness or arrow-uniqueness assumption. OK.
2. Small sites C_i and site morphisms f_a: `D : CoherentSitePseudofunctor I F`
   (now owned by `def-per-coherent-site-diagram`, existing structure in
   `TotalSitePseudofunctor`: precoverage + `IsSiteForCoverings`, continuity, cover-pullback
   preservation of `F.map a.op`), plus `siteMorphism`: `PreservesFiniteLimits
   (D.inverseImage a)` on the set-valued inverse image (owned by
   `def-per-coherent-site-sheaf-adjunction`, Stacks 00WX). Variance: Lean `a : j ⟶ i`
   gives `abelianInverse a : fibre i ⥤ fibre j`, i.e. the node's f_a^{-1} for a:j→i. OK.
3. Additive adjunction f_a^{-1} ⊣ f_{a,*} with mate identity/composition comparisons:
   `abelianAdjunction`, `abelianInverseId/Comp` as mates of `abelianDirectId/Comp` from
   `F.mapId/mapComp`; additivity = the two quantified `Additive` instances. Not stronger. OK.
4. Category S: `D.AbelianSystem` (identity and cocycle laws, all compatible component
   families as morphisms, componentwise preadditive structure). OK.
5. L_i ⊣ ev_i ⊣ R_i, additive: `left/right`, `left_additive/right_additive`,
   `leftAdjunction/rightAdjunction`. OK.
6. (L_iA)_j = ⊕_{a:j→i} f_a^{-1}A, (R_iA)_j = ∏_{a:i→j} f_{a,*}A, natural in A:
   `leftComponent/rightComponent` with Mathlib sheaf `∐`/`∏ᶜ`, `left_naturality/
   right_naturality`. Empty sums/products are Mathlib's (zero) objects. OK.
7. L transition: `left_transition` sends the pulled-back a-summand through
   `abelianInverseComp c a` to the `c ≫ a` (= a∘c) summand. OK.
8. R transition: `right_transition`, b-projection = Q_c of the `b ≫ c` projection,
   `abelianDirectComp b c`.inv, counit at P_b A. OK.
9. Hom formulas: `left_hom` (identity summand after the inverse identity comparison),
   `left_hom_inverse` (a-summand = Q_a h ≫ φ_a), `right_hom` (`homEquiv.symm`, identity
   factor then `abelianDirectId`), `right_hom_inverse` (a-factor = adjunct of φ_a ≫ h).
   Naturality in both arguments is part of Mathlib `Adjunction`. OK.

Edge cases: empty I (vacuous in i), discrete I (empty sums/products), one-object monoid
(all endomorphism summands kept; only `𝟙 i` in the Hom formulas), walking arrow, A = 0.
Universes: coefficients `AddCommGrpCat.{max v w}`, no universe equality imposed; the
filtered-colimit shrink instance is the real Mathlib transport.

Searches: side-live DAG nodes mentioning `CoherentSitePseudofunctor` are only the trf
theorem nodes and sfb semisimplicial nodes; none is a definition owner, so the two new
`existing: true` def nodes are the right H2 repair. Their `lean.statement`s are verbatim
the source lines (TotalSitePseudofunctor.lean:34-35, TotalSiteSheafSystems.lean:55-56).
No abelian varying-site system exists in Mathlib, `Sheaf/` or `WeilConjectures/`.

Mismatches found: none in the Lean or records; only this section was replaced (H11).

Worker's own notes, retained:

The coefficient-universe repair is the real Mathlib transport
`preservesFilteredColimitsOfSize_shrink` in the named instance
`abelianCoefficientForgetFiltered`; it lets concrete sheafification use its site-sized
filtered diagrams without identifying the site and coefficient universes.

Validation: scompile.py compiled both files separately against the live published
library, including the private sibling overlay, with no errors or warnings. The final
reported file timings were 15.3 s for the systems sandbox and 31.5 s for the theorem
sandbox (27.8 s for its library-path check), below the fixed 60 s bound.

## Returned delivery repair

H2, returned immutable head `40e6f2c222b1`: removed the item statement dependencies
`lem-trf-slice-site-total-pseudofunctor` and `lem-trf-slice-site-total-systems`,
which had been cited only for definitions in their modules. The abelian-system
node no longer cites the first theorem node either.

Added exact-existing definition-node owners by actual declaring module:
`def-per-coherent-site-diagram` owns `CoherentSitePseudofunctor` in
`Sheaf.CategoryTheory.TotalSitePseudofunctor`; and
`def-per-coherent-site-sheaf-adjunction` owns its `fibreSheaves`, `directImage`,
`inverseImage`, `imageAdjunction` in `Sheaf.CategoryTheory.TotalSiteSheafSystems`.
The latter depends on the former and on `def-weil-pbc-sheafification`.
The item cites both owners; `def-per-varying-site-abelian-systems` cites only
the structure owner. No total-site theorem conclusion is used as a statement
dependency. Existing declarations are recorded with `existing: true`, following
brief-stage2 §1(A)/§5; copying them into new modules would duplicate the notions.

Source 09WC Case A and its preceding pseudofunctor discussion, plus 00WX, were
reopened and checked against the full signatures and bodies of all five definitions.
The new nodes' three-kind searches and the project/DAG/blueprint searches found no
other definition-node owner. The first preflight required the structure record to
name its actual declaring module, so ownership is split as above.

Current main was compared with the retained sandbox: the item still has no Lean
record and its original four statement dependencies. The sandbox changes only
lean and stmt_deps on that item. Both delivered Lean files retain their reviewed
contents. Only ownership records, dependency links and this report change in the
repair; there is no source statement correction or mathematical assumption added.

Repair validation: scompile.py returned exit 0 for both delivered modules and a
module-mode public-import probe checking all five existing declarations. The probe
confirmed their names and complete signatures. The scratch probe is outside lean/
and is not delivered. The dry run checks the existing records again, including
that each primary declaration occurs in its named declaring module. Independent
mathematical review is the maintainer's review quoted in the return; the dispatch
prohibits other agents.
