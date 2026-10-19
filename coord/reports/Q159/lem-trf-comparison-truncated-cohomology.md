## Worker report

Group Q159, item `lem-trf-comparison-truncated-cohomology`, stage 2.

The module `Sheaf.TraceFormula.ComparisonTruncatedCohomology` states
`CategoryTheory.RefinedTopologyComparison.comparisonTruncatedCohomology`, with
`sorry` as its only theorem proof. Its docstring gives all nine DAG proof steps,
including the degree-(r+1) monomorphism needed before taking derived sections.
The node changes only in `lean`. There is no statement correction or disputed
statement, no dependency repair, and no new node.

Source read: `literature/stacks-project/sites-cohomology.tex`,
`section-compare-general` (lines 6808 onward), Situation 0EZ3, and
`lemma-V-implies-cohomology-general` / Tag 0EZB (lines 7029 onward). The DAG
intentionally retains assumptions (1)--(4), rather than the refinement assumption
(5) of the wider situation: this is valid because this particular lemma uses
only assumption (3) and the supplied vanishing. None of (1)--(4) was omitted.

### Hypotheses and conclusions, clause by clause

- The category small in the fixed universe is `{C : Type u} [SmallCategory C]`;
  abelian groups take values in `AddCommGrpCat.{u}`. Objects, arrows, the site and
  coefficient sets are within the common chosen bound. No universe is inferred.
- The actual site structures are `τ τ' : Precoverage C`, with
  `hτsite : τ.IsSiteForCoverings` and `hτ'site : τ'.IsSiteForCoverings`, using the
  recorded definition of the site axioms. Their associated sieve topologies are
  `τ.toGrothendieck` and `τ'.toGrothendieck`.
- Every τ'-cover is a τ-cover is `[hτ : Fact (τ' ≤ τ)]`. `Fact` merely makes that
  exact inequality available to instance search; it is not an additional condition.
- The slices are literally `Over X`, with `τ.toGrothendieck.over X` and
  `τ'.toGrothendieck.over X`. Mathlib `over` tests the underlying covering sieve,
  so these are the arrow/triangle slice sites specified in the node.
- The comparison direct image is
  `(𝟭 (Over X)).sheafPushforwardContinuous AddCommGrpCat ... ...`.
  It precomposes with the identity and changes no underlying presheaf data.
  The inverse image is Mathlib's corresponding `sheafPullback`, with adjunction
  `sheafAdjunctionContinuous`. Its construction is left Kan extension along the
  identity followed by finer sheafification, hence canonically the finer
  sheafification of the underlying coarser sheaf. This uses the actual adjunction,
  not an arbitrary functor or a hypothesis postulating a comparison isomorphism.
- For each f, relocalization inverse image is exactly
  `τ'.toGrothendieck.overMapPullback AddCommGrpCat f`. Its direct image is
  `(Over.map f).sheafPushforwardCocontinuous`, with the existing
  `sheafAdjunctionCocontinuous`. Thus the inverse image on U → X is evaluation
  of the original sheaf on U → X → Y, as required.
- `P : ∀ ⦃X Y : C⦄, (X ⟶ Y) → Prop` is the arbitrary morphism class.
  `A' X` is a predicate on the actual coarser-slice abelian sheaf category;
  predicates describe its full subcategories without choosing extra morphism data.
- `hzero` is containment of zero, `hiso` is closure under all isomorphisms,
  `hkernel` and `hcokernel` quantify over every morphism between members,
  and `hextension` uses `ShortComplex.ShortExact` and the outer-to-middle
  closure. These are the weak Serre conditions, not the stronger Serre condition
  of closure under arbitrary subobjects and quotients.
- Assumption (1) is `hbaseChange`: for every f in P and every g, there exist
  a fibre-product object T and projections p, q with `IsPullback p q f g` and
  `P q`. This spells out existence of the fibre product and membership of its
  base-changed projection, without assuming pullbacks for other arrows and
  without a hidden `let` binder in the statement.
- Assumption (2) is `hrelocalization`, for every f without a P restriction.
- Assumption (3) is `htauSheaf`, the actual finer sheaf condition on `H.obj`.
- Assumption (4) is `hderivedImage`, for f in P and every `i : ℕ`, including zero;
  it uses the ordinary `Functor.rightDerived i` of the canonical direct image.
  These are Mathlib's injective-resolution right derived functors.
- `r : ℕ` includes r = 0. In `hr`, the condition on H is precisely existence
  of H' with `A' X H'` and `Nonempty (H ≅ epsilonInverse.obj H')`.
  This is the specified strictly full essential image A_X, with no choice of H'.
  The conclusion of `hr` is `IsZero` of the ordinary higher direct image for
  every `i : ℕ` satisfying `1 ≤ i` and `i ≤ r`, for every X and every such H.
- `L : DerivedCategory.Plus (Sheaf ... AddCommGrpCat)` is a bounded-below derived
  object. `hconnective` gives zero cohomology for every integer degree below zero.
  `hcohomology` puts the cohomology in A'_X for every integer in `[0,r]`.
  There is no bound or membership condition in degrees above r.
- The conclusion is `IsIso` of the component at L of
  `comparisonHypercohomology ... (Over.mk (𝟙 X)) r`. Sections here are the existing
  `sheafToPresheaf ⋙ evaluation` at the terminal slice object. Their bounded-below
  right derived functors, followed by `DerivedCategory.Plus.homologyFunctor`, are
  exactly injective-resolution hypercohomology on the two sites.
- The particular map is defined in `comparisonDerivedSections`: whisker the
  canonical derived adjunction unit by derived coarse sections, reassociate, and
  apply `Functor.rightDerivedFunctorPlusCompIso'` to the identity identification
  of coarse sections after direct image with fine sections. Direct image preserves
  injectives because inverse image preserves monomorphisms. The input iso is
  `Iso.refl _`, so this identification contains no arbitrary comparison data.
- `comparisonHypercohomology` is the whiskering of that natural transformation
  with degree-r cohomology. Thus its components obey naturality in every derived
  morphism. The theorem asserts invertibility on every allowed L, exactly a
  natural isomorphism on the full subcategory in the node. No separate arbitrary
  group isomorphism is supplied or chosen.

### Recorded dependencies and interfaces used

- `def-weil-size-convention`: explicit common universe u and small category, as its
  metatheoretic convention record requests; it has no declaration to import.
- `def-weil-pbc-sites-and-cohomology`: import
  `Sheaf.CategoryTheory.SiteCoveringAxioms`, use
  `CategoryTheory.Precoverage.IsSiteForCoverings`, Mathlib sheaf categories,
  evaluation, and injective-resolution right derived functors.
- `def-trf-geometric-morphism`: import
  `Sheaf.CategoryTheory.Sites.GeometricMorphism`; the concrete comparison and
  relocalization use the already existing Mathlib adjunctions with exact inverse
  image, realizing that datum. No duplicate geometric-morphism structure is defined.
- `def-weil-pbc-sheafification`: Mathlib `presheafToSheaf` and its adjunction are
  used by the identity-site `sheafPullback` construction. The finer pullback is
  left exact, left adjoint and additive through existing construction lemmas.
- `def-weil-abstract-derived-category`: Mathlib `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Plus`. The Grothendieck-abelian
  `HasDerivedCategory` instance is imported from the published upstream module.
- `def-sbc-standard-tstructure-derived-category`: its Mathlib match
  `DerivedCategory.TStructure.t`, with `DerivedCategory.Plus.homologyFunctor`
  and the bounded-below category of this standard t-structure.

All stated proof-dependency modules are imported for the stage-3 plan, including
exact derived functors, adjunction shift compatibility, morphisms of triangles,
single-object identification, shift identification, the truncation-isomorphism
lemma, truncation triangles, long exact sequences and derived composition.
The Mathlib leaves are supplied by the corresponding Mathlib imports.

The helpers `comparison`, `sliceComparison` and `relocalization` in the existing
`Sheaf.TraceFormula.ComparisonInductionStep` were read. That module is a consumer
of this lemma at the DAG proof level. It is deliberately not imported: adding this
lemma to its proof imports would then make a Lean import cycle. The present module
uses Mathlib's original sheaf functors and adjunctions directly; it copies none
of those helpers and assumes none of the downstream induction theorem.

The eleven declarations recorded in `lean.declarations` comprise the theorem,
the two canonical-map definitions, and structural instances needed for these
specific existing functors (continuity, inequality on slices, additivity,
left-adjointness, exactness and preservation of injectives). All instance data
come from existing Mathlib constructions and lemmas. No definition contains sorry.

### Edge cases

- r = 0: `1 ≤ i ≤ 0` is empty; cohomology membership is only required in degree 0.
- A'_X may be the zero subcategory or the full category; weak Serre closure is
  stated in full without accidentally requiring all subobjects to belong.
- P may be empty; assumption (4) is then vacuous but assumptions (2) and (3)
  still quantify as the source specifies. No existence of a P-arrow is added.
- C may be empty; the theorem is quantified over X and adds no nonemptiness.
- L may be zero, and may have arbitrarily high nonzero cohomology. No bounded-above
  condition or membership condition above r is introduced.
- Equal topologies and arbitrary finer/coarser topologies are both allowed.
- No global pullback assumption, enough-points assumption, subcanonicity or
  coefficient finiteness hypothesis was added.

### Searches

Searches executed through the prescribed `msearch.py`, with Q159 and the item id:

1. LeanFinder: “Comparison of hypercohomology for two topologies from vanishing
   higher direct images through r”: eight hits, concerning continuous functors
   and hypercovers; no statement of the lemma.
2. Loogle: `GrothendieckTopology.over, sheafPushforwardContinuous, rightDerived`:
   zero hits; Loogle did not recognize the first identifier. The full signatures
   were consequently read directly from the source files.
3. Mathlib grep: `def.*(over|Over)|def.*(pushforward|pullback)|def.*comparison`
   under `CategoryTheory/Sites`: 25 hits, no exact lemma.
4. LeanSearch: “Geometric morphism comparing finer and coarser topology on slice
   sites with sheafification inverse image”: eight hits, including
   `sheafificationAdjunction`, `Presieve.isSheaf_of_le`, and
   `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`.
5. LeanFinder: “Canonical comparison morphism for sheaves on slice sites with
   two topologies”: eight hits, including `GrothendieckTopology.overPullback`
   and `overMapPullback`; no specialized hypercohomology map or lemma.
6. `rg` of the upstream `WeilConjectures` and project `lean/Sheaf` trees for
   comparison, truncated cohomology, hypercohomology, right derived functors,
   and `0EZB`, and a literal item-id search in upstream: no exact declaration.
   The general bounded-below derived adjunction and canonical composition
   isomorphism were found and their full definitions read. The exact existing
   slice-site and relocalization functors were reused.
7. Loogle follow-up with the fully qualified `CategoryTheory.sheafificationAdjunction`:
   ten hits including the adjunction, its unit/counit and reflective isomorphisms;
   no finite-range derived comparison statement. The upstream name index and
   both source trees have no collision for any delivered declaration name.
8. DAG searches for weak Serre and refined-topology comparison, and
   `tools/blueprint_refs.py search 'slice topology comparison'` (zero blueprint
   matches), identified the downstream helper module described above, not an
   independent pre-existing statement of this lemma.

### Validation

The canonical-map definitions compiled cleanly through the authorized `scompile.py`,
both the local overlay sandbox check and server confirmation (22.8 s and 42.2 s).
The complete theorem module also compiled cleanly in both checks (25.2 s local;
the wrapper reported 104.2 s for the library confirmation, including server overhead).
The final preflight recompiles the delivered file with its default per-file limit. No global build or
live-source edit was performed. The delivery dry run is also run before the push.

## Second reading by Q159

This is the dispatcher's worker self-check, not a claim that another agent read
this delivery; the brief forbids starting other agents and assigns independent
review to the maintainer. I reread the node, source and complete signature.
The weak Serre conditions match individually; all four situation assumptions
and exactly the finite vanishing range are present. I checked that the cohomology
membership is required only in degrees 0 through r and that L need not be bounded
above. I checked that the conclusion uses the canonical derived unit and canonical
composition map, with the source-to-target direction in the node, rather than
merely asserting existence of a group isomorphism. Naturality is provided by the
actual natural transformation. The existential pullback square in (1) avoids
an un-unfoldable let binder and adds no pullbacks beyond the source assumption.
The initial compiler failures were instance elaboration problems; no mathematical
hypothesis was added to resolve them. No mismatch requiring a node correction was found.
