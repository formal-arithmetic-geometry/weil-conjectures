## Worker report

Item: `lem-coef-ind-kappa-presentability`, group Q32, stage 2, 2026-10-17.
Module: `Sheaf.CategoryTheory.IndKappaPresentability`.
Main declaration: `SSet.Presentability.indKappa_presentability`.
The natural-language statement is unchanged. The item's `stmt_deps` gains the already
landed `def-coef-infinity-presheaf-yoneda`, whose actual coherent presheaf and Yoneda
construction the file uses. No new node or dependency repair is needed. The shared
snapshot initially lacked the presentability record, but the published module was
read with `scompile.py --source`; the shared node and source became available during
the task, and the final delivery uses that landed interface without replacing it.

The module gives real simplicial data for the Ind completion appearing in the
statement. `IsIndKappaObject` expresses a small kappa-filtered Yoneda presentation
in the presheaf category, up to a specified equivalence edge. `indKappaSubcomplex`
applies the existing vertexwise full-subcomplex constructor to this predicate.
`indKappa` is that subcomplex's simplicial set and `indKappaInclusion` is its
inclusion. `indKappaYoneda` is `SSet.Subcomplex.lift` of the existing Yoneda map;
its composite with the inclusion is definitionally that map. Its data therefore
do not depend on any arbitrary choice of a functor or colimit. The named theorem
`infinityYoneda_range_le_indKappa` supplies only the proof of membership. The
named theorem `indKappa_quasicategory` supplies the quasicategory proof, registered
as an instance. These are well-definedness obligations of the objects in this
node, with proof plans and the same blueprint tag. Together with the main theorem,
these are the only three postponed proofs. Every theorem has exactly `by sorry`.

Hypotheses and clauses, in the order of the node:

- The small universe is `u`; `C : SSet.{u}` and `[SSet.Quasicategory C]` mean an
  arbitrary small infinity category, with no nonemptiness assumption. Presheaves
  and Ind live in `u + 1`. The ambient space universe in compactness is supplied
  by the existing `IsKappaCompact` definition, which tests diagrams in `u + 2`.
- `κ : Cardinal.{u}` and `hκ : κ.IsRegular` give an infinite regular small cardinal.
  Mathlib's `IsRegular` includes infinitude. No stronger cardinal hypothesis is used.
- `CategoryTheory.Spaces.infinityPresheaves C` is precisely the existing internal
  functor simplicial set from the universe lift of the order-reversing opposite
  of C to `CategoryTheory.Spaces.infinityCategory.{u}`. The representable functor
  is the existing constructed `CategoryTheory.Spaces.infinityYoneda C`, whose
  Hom pairing uses singular-realization rigidification, including all coherences.
- `IsIndKappaObject C κ X` quantifies over `I : SSet.{u + 1}`, a quasicategory
  proof `hI`, `IsSmall.{u, u + 1} I`, and `IsKappaFiltered κ I`. It supplies a
  coherent `F : I ⟶ ulift C`, a whole cocone on `F ≫ infinityYoneda C` colimiting
  in presheaves, and an equivalence edge from X to its apex. Thus the defining
  colimit is computed in presheaves and the full subcategory is replete. No
  presentation data are chosen from an existence theorem. Factoring the diagram
  through Yoneda is equivalent to using its full essential image, by full
  faithfulness, as in the node's proof.
- Full faithfulness of the restricted functor j is
  `SSet.Enhanced.IsFullyFaithful (indKappaYoneda C κ hκ)`.
- For every `c : C _⦋0⦌`, the next conjunct is
  `IsKappaCompact (indKappa C κ) κ ((indKappaYoneda C κ hκ).app _ (ULift.up c))`.
  This is compactness in Ind, including preservation by the actual coherent
  corepresented functor in the containing space universe.
- Local smallness is `IsLocallySmall.{u, u + 1} (indKappa C κ)`, testing mapping
  spaces up to weak equivalence to small spaces rather than demanding that the
  displayed presheaf mapping simplicial set itself have small sets of simplices.
- Existence of small filtered colimits is
  `HasSmallKappaFilteredColimits (indKappa C κ) κ`.
- Preservation by the inclusion is `PreservesColimitsIn (indKappaInclusion C κ)`
  with class predicate `∃ hI, IsSmall I ∧ IsKappaFiltered κ I`. The imported
  predicate sends every colimiting coherent cocone to its actual postcomposed
  cocone and requires that cocone to be colimiting in presheaves.
- Every `X : indKappa C κ _⦋0⦌` has a small filtered index I, a diagram F into
  the lift of C, and a colimiting cocone on `F ≫ indKappaYoneda C κ hκ` **in Ind**,
  with an equivalence edge from X to the apex. This separately states the internal
  generation clause; it is not merely the presheaf presentation used in the definition.
- `IsKappaAccessible (indKappa C κ) κ` states precisely the accessibility conclusion,
  using the dependency's locally small, essentially small compact generators convention.
- `PreservesColimitsIn (indKappaYoneda C κ hκ) (fun I _ _ ↦ IsKappaSmall κ I)`
  states preservation of every kappa-small colimiting cocone that exists in C.
  Its codomain is Ind. It does not require Yoneda into all presheaves to preserve
  those colimits and does not assume their existence throughout the theorem.
- The final implication's antecedent says that every diagram
  `F : K ⟶ ulift C` with `IsKappaSmall κ K` has a colimiting cocone. There is no
  quasicategory restriction on K. Its conclusion is both
  `HasSmallColimits.{u, u + 1} (indKappa C κ)` and
  `IsPresentable.{u, u + 1} (indKappa C κ)`. Thus all small colimits and
  presentability are claimed only under the source's additional hypothesis.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.PresentableInfinityCategory`:
  `SSet.Presentability.IsSmall`, `IsKappaSmall`, `IsKappaFiltered`,
  `IsLocallySmall`, `HasSmallKappaFilteredColimits`, `IsKappaCompact`,
  `IsKappaAccessible`, `HasSmallColimits`, `IsPresentable`, `PreservesColimitsIn`.
  The definitions of `IsEssentiallySmall` and `IsAccessible` were also read as
  components of the accessibility/presentability predicates.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.fullSubcomplex`, `IsFullyFaithful`, `IsEquivalenceEdge`,
  `coconeCategory`, `IsColimiting`; their full signatures and docstrings were read.
- `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`:
  `CategoryTheory.Spaces.infinityCategory`, `corepresented`, `mappedCocone`,
  `PreservesColimit`; the latter three provide the existing preservation semantics.
- `Sheaf.CategoryTheory.InfinityPresheafYoneda`:
  `CategoryTheory.Spaces.infinityPresheaves`, `infinityYoneda`, and their
  explicitly constructed coherent Hom pairing. This entire source was read.
- Mathlib's `SSet.Subcomplex.range`, `Subcomplex.lift` and subcomplex inclusion
  provide restriction with actual data; `SSet.uliftFunctor` handles sizes.

All currently recorded proof-dependency modules are imported without `public`:
`EnhancedFunctorConeCalculus`, `CoherentNerveComparison`,
`InfinityDirectedUnionLocalColimits`, `InfinityFullEssentialImage`,
`InfinityJoinConeCalculus`, `RelativeConeEquivalence`,
`Sheaf.AlgebraicTopology.InfinitySmallColimitGeneration`, `ParametricUniversalArrows`,
and `SpaceTransportClassification` (the unqualified names in this list have prefix
`Sheaf.CategoryTheory`). Presentability is also a public statement import.
The other proof dependencies currently have no Lean records, so there is no module
to import for them. Their mathematical roles are retained explicitly in all eleven
steps of the main theorem's docstring. No dependency module is changed.

Edge cases checked before writing:

- C empty: no nonempty filtered index maps to C, so Ind is empty. Local smallness,
  full faithfulness and the objectwise claims are vacuous, and the empty category
  has all its possible small filtered colimits. Accessibility allows the empty
  full subcategory of generators. The final antecedent fails at the empty
  diagram, so cocompleteness of the empty category is not asserted.
- C terminal: every filtered colimit of the representable point is equivalent
  to that point. Ind is equivalent to the terminal category, consistently with
  compactness and the conditional presentability conclusion.
- The empty diagram is included in kappa-filteredness tests by the dependency;
  in particular the filtered presentation index is nonempty. It is also included
  in kappa-small colimit preservation and in the final antecedent. No explicit
  nonempty assumption accidentally deletes initial objects or empty coproducts.
- If C has an initial object, its image is claimed initial **inside Ind**;
  its Yoneda presheaf need not be initial in all presheaves.
- `κ = ℵ₀` is admitted. Kappa-smallness counts nondegenerate simplices across all
  degrees, so the finite simplicial indexing convention is preserved. The proof's
  finite-poset realization is used only for spans, not arbitrary finite simplicial sets.
- No idempotent completeness or kappa-small cocompleteness hypothesis is imposed
  before the final implication. Universes remain `u`, `u + 1`, `u + 2`; no equality
  between the small and ambient universes is introduced.

Searches for an existing statement/construction:

- `msearch.py ... leanfinder "Ind completion of a small infinity category is kappa
  accessible and presentable if it has kappa small colimits"`: eight ordinary
  category accessibility/presentability hits, including
  `CategoryTheory.IsLocallyPresentable` and `IsAccessibleCategory`; no infinity
  category Ind theorem.
- `msearch.py ... loogle "CategoryTheory.Ind, CategoryTheory.IsAccessibleCategory"`:
  zero hits for the combined query.
- `msearch.py ... grep "IndCompletion|indCompletion|IsKappaCompact|quasicategory.*presentab"
  CategoryTheory`: zero hits.
- `msearch.py ... leansearch "Ind kappa completion of a small quasicategory Yoneda
  compact objects accessible presentable"`: eight ordinary-category hits,
  including `CategoryTheory.Ind.yoneda` and `Limits.isIndObject_yoneda`. These
  use ordinary Type-valued presheaves and do not express the node's statement.
- `rg` over the upstream `WeilConjectures/CategoryTheory` and the side
  `lean/Sheaf/CategoryTheory` for Ind, Yoneda, IsKappa, IsPresentable, IsAccessible
  and IsLocallySmall, followed by focused `rg -l` for the infinity names: found
  `InfinityPresheafYoneda` and `IntermediatePresheafKan`, reused the former.
  Ordinary upstream Pro/Ind and presentability declarations do not match.
- `rg` for `lem-coef-ind-kappa-presentability` in upstream `WeilConjectures`:
  no occurrence. Read the upstream name index's presheaf/Yoneda entries; none
  supply this theorem. Read the dependency node files and the side presheaf node.
- Read the official HTT PDF at
  <https://people.math.harvard.edu/~lurie/papers/HTT.pdf>, especially the project server--the project server,
  the project server and the project server(4). The statement's distinctions between colimits in
  presheaves, colimits in Ind, existing colimits in C, and the conditional
  cocompleteness conclusion match these source locations.

Validation: the delivered module compiled cleanly through the required
`scompile.py Q32 lem-coef-ind-kappa-presentability` wrapper, with no warnings or
errors. All variables and universes are explicit; no private definitions,
file-local notation, or proof of a theorem is introduced. The node record's
`statement` is extracted verbatim from the main theorem's signature.
No `STATEMENT-DISPUTED` issue and no statement correction.

## Second reading by Q32

I read the node statement against HTT Proposition the project server, Proposition the project server,
Corollary the project server, Propositions the project server and the project server, and Theorem the project server(4).
The source defines `Ind_kappa(C)` as the full subcategory of the space-valued
presheaf category classified by small kappa-filtered right fibrations; Corollary
the project server identifies this with the filtered-colimit-of-representables description
used by the node. The source's small C, regular kappa, and all-small-colimits
conventions agree with the dependency definitions.

The statement checklist and verdicts are:

* `u` is the small universe; `C : SSet.{u}` with
  `[SSet.Quasicategory C]` is an arbitrary small infinity category, with no
  nonemptiness or idempotent-completeness hypothesis. `kappa : Cardinal.{u}`
  and `hκ : kappa.IsRegular` give the source's regular infinite cardinal.
* `P(C)` is rendered by `CategoryTheory.Spaces.infinityPresheaves C`, using the
  existing space-valued coherent functor construction, and `j` is rendered by
  `CategoryTheory.Spaces.infinityYoneda C`. This is the source's presheaf and
  Yoneda pair, not an ordinary Type-valued presheaf.
* The Ind object predicate is rendered by `IsIndKappaObject`: an index
  `I : SSet.{u + 1}` with `hI`, `IsSmall.{u,u+1} I`, and
  `@IsKappaFiltered.{u,u+1} kappa I hI`; a coherent `F` into the universe lift
  of `C`; a colimiting cocone on `F` followed by the existing Yoneda in `P(C)`;
  and an equivalence edge from the presheaf vertex to that cocone apex. Thus
  the predicate is replete and uses actual cocone data, exactly the node's
  filtered-representable clause.
* `Ind_kappa(C)` is rendered by the vertexwise full subcomplex
  `indKappaSubcomplex` and `indKappa`; its inclusion is the actual
  `indKappaInclusion`. The range theorem and `SSet.Subcomplex.lift` give the
  restricted `indKappaYoneda`, so no arbitrary choice of a functor is hidden.
* The first conclusion clause, `IsFullyFaithful (indKappaYoneda C kappa hκ)`,
  is the node's full faithfulness of `j`.
* The second clause quantifies every `c : C _⦋0⦌` and states
  `IsKappaCompact` for its actual Yoneda image. This includes the dependency's
  filtered-colimit existence and the larger-space-universe mapping test.
* The third and fourth clauses are respectively
  `IsLocallySmall (indKappa C kappa)` and
  `HasSmallKappaFilteredColimits (indKappa C kappa) kappa`; neither adds a
  finiteness, Noetherian, or universe-equality assumption.
* The fifth clause states that the inclusion preserves exactly the small
  kappa-filtered colimits whose index has a quasicategory witness, is
  `IsSmall.{u,u+1}`, and is `IsKappaFiltered`; the preservation predicate still
  requires an actually given colimiting cocone. It does not assert extra
  colimits in `C`.
* The sixth clause quantifies every Ind vertex `X` and supplies the same kind of
  small filtered `I`, `hI`, and `F`, but now supplies a colimiting cocone in Ind
  on `F` followed by the restricted Yoneda, together with an equivalence edge
  identifying its apex with `X`. This is the node's generation clause, not just
  membership in the presheaf subcomplex.
* The seventh clause is `IsKappaAccessible (indKappa C kappa) kappa`, so it
  includes local smallness, filtered colimits, an essentially small compact
  generating full subcategory, and the displayed filtered presentations.
* The eighth clause says the restricted Yoneda preserves every kappa-small
  colimiting cocone that exists in `C`; `PreservesColimitsIn` supplies the
  colimit premise and therefore does not assume such colimits exist.
* The final antecedent quantifies all `K : SSet.{u+1}` with
  `IsKappaSmall kappa K` and every diagram `F : K -> ulift(C)`, requiring a
  colimiting cocone. Its conclusion is exactly all small colimits in Ind and
  `IsPresentable` for Ind. No quasicategory condition is silently imposed on
  `K`, matching the dependency convention and the node.

The edge cases were checked explicitly. The empty `C` makes the objectwise
generation clauses vacuous and does not create an unwanted object; the final
antecedent fails for the empty diagram, so no cocompleteness is asserted there.
For terminal `C`, the construction reduces to the terminal Ind category. The
empty test diagram is included in `IsKappaFiltered`, so filtered indices are
nonempty where required and empty colimits remain covered. Empty kappa-small
diagrams are included in Yoneda preservation. `kappa = aleph_0` is admitted by
`Cardinal.IsRegular`; its smallness is the nondegenerate-simplex condition in
the dependency. No characteristic, n, zero-object, or extra universe case is
excluded.

For the one-definition check I ran `msearch.py` LeanFinder and Loogle queries
for Ind completion, kappa compactness, accessibility, and Yoneda, and searched
Mathlib, the upstream `WeilConjectures`, and the repository's `lean/Sheaf` with
`rg`. The hits are ordinary Type-valued `CategoryTheory.Ind` and presentability
notions; none states this coherent space-valued infinity-category theorem.
The exact existing presheaf/Yoneda construction is
`Sheaf.CategoryTheory.InfinityPresheafYoneda`, recorded by
`def-coef-infinity-presheaf-yoneda`, and was read in full. No duplicate
definition or existing theorem was found.

The only interface mismatch found was in the base node copy: its `stmt_deps`
did not list `def-coef-infinity-presheaf-yoneda`, although the statement's
`P(C)` and `j` require that recorded construction. I added that dependency to
the sandbox node and imported its module; the mathematical statement and all
of its clauses were unchanged. The Lean signature remains verbatim equal to
the node copy. No dependency repair, statement correction, hollow definition,
private copy, or extra hypothesis was needed. The module and its sibling-free
file set compile with `scompile.py` cleanly, with only the intended `sorry`
declarations.
