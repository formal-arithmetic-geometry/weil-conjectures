## What changed

Proved `Algebra.exists_limit_finite_presentation_core` with its exact existing signature.
Added proof-only imports of `WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits`,
`WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation`, and
`Mathlib.RingTheory.RingHom.FiniteType`.

The source library already proves descent of finite-presentation algebras. Apply it to the
full finite-type integer subalgebra colimit, restrict to subalgebras containing the descended
stage, and construct every model by a categorical pushout. All functor and cocone equations
are proved by the pushout universal property. Pushout cancellation proves both required
families of squares. The restricted base colimit is proved from its supremum being top.
No data is defined from an unproved existence theorem.

Updated the Core node to this route and attached the proved source declaration
`CommRingCat.exists_isPushout_of_finitePresentation` to the existing blueprint node
`lem-kun-fp-algebra-descent`; no duplicate node or theorem was created. This is a generic
proved algebra tool, not a replacement of any unit step. Core does not itself realize a
step or statement in `dag/units/sk-thm-p1.json`.

## Proved and sorry left

Closed 1 hole: `Algebra.exists_limit_finite_presentation_core`
(node `lem-weil-pbc-limit-finite-presentation-core`). Added 0 holes. No sorry remains in
any delivered Lean module. This is a full proof, not a decomposition.

Local compilation succeeds without warnings in about 3 seconds. Explicit `#print axioms`
for the completed theorem and the source descent theorem both list exactly
`propext`, `Classical.choice`, `Quot.sound`. Lines are at most 100 characters.
The proof covers the zero ring, empty variable or relation presentations, and universe
`u = 0`: no nontriviality, nonzero generator count, or strict inequality is used.

## No longer needed

No existing import was removed: all four public imports serve the unchanged statement.
All three added proof imports are used. The direct proof dependencies
`def-weil-pbc-algebra-hom-quotient` and `lem-weil-pbc-polynomial-scalar-extension` are
removed from the Core node; their explicit quotient and scalar-extension calculations
are encapsulated in the already-proved source descent theorem. They may remain used
elsewhere, and this does not claim a reduction in the transitive compiled Mathlib imports.
The other original dependencies remain. No Sheaf dependency module was imported or split.

## Where the brief, the DAG or earlier work was wrong

The earlier search correctly found individual Mathlib presentation models but missed the
source library's fully proved finite-presentation descent theorem. Its generic tool form
is precisely the existing blueprint node `lem-kun-fp-algebra-descent`, whose Lean record
was absent. The new record names the source declaration and its section context.

The source theorem is annotated `@[stacks 00R4]`, but Stacks 00R4 is miracle flatness.
The correct source is Tag 05N9, `lemma-colimit-category-fp-algebras`, clause (1), in algebra.tex;
the proof uses finitely many relation coefficients and quotient base change.
Read Stacks 00R0 and Section 00QL online because the literature bodies are absent from
this read-only clone. No source-library citation or signature was edited here.

Searches ran through msearch: LeanFinder and Loogle supplied the presentation-model API;
grep confirmed it. A second LeanSearch call on finite-presentation descent returned
HTTP 500 (unavailable); LeanFinder returned Mathlib's Hom-factorization results rather
than object descent; msearch grep for the source theorem returned no hits because it
searches Mathlib. Direct rg found the source declaration at
`lean/WeilConjectures/Mathlib/Algebra/Category/Ring/FinitePresentation.lean:222`.
Blueprint searches for finite presentation, finitely presented, and colimit found the
existing algebra-descent node, so no new node was introduced.

The first dry run also exposed a preflight scanner false positive: the column-zero
`:= by` line in the existing file is parsed as an `other` command by leanindex, so
proof-body replacement is reported as an interface command change. Documented in
`coord/changes/limit-finite-presentation-core-proof-scanner.md`; no tool was edited,
no signature or public import changed, and no downstream adaptation is needed.

## Second reading by S4

1. **Interface: pass.** Read the entire repository and sandbox Core files and their
   diff. The existing theorem signature is byte for byte identical, including `Type u`,
   all ring and finite-presentation hypotheses, nonempty directed preorder, both cocones,
   arbitrary point equalities and their transports, both finite-type assertions, both
   pushout assertions, and the base colimit. No definition, visibility, public import,
   namespace, universe or attribute changed. The scanner change record accurately
   describes the column-zero `:= by` continuation; this is no mathematical interface change.
2. **Proof: pass.** Independently compiled the sandbox module with `lcompile.py --all`
   without errors or warnings (3.6 seconds). Compiled the scratch copy with explicit
   `#print axioms` for Core and the source descent theorem: each reports only `propext`,
   `Classical.choice`, `Quot.sound`. The delivered module has no `sorry`, forbidden axiom
   command or data definition. Read the source descent proof at lines 222–256: its finite
   polynomial relations descend to one stage, and the quotient universal property gives
   the pushout. The existential witnesses are chosen inside the theorem proof from this
   proved result; no data is selected from an unproved existence assertion.
3. **Split statements: pass, none.** No new theorem or node and no lower hole was added.
   The existing `lem-kun-fp-algebra-descent` states exactly the finite-stage algebra
   descent provided by the source theorem (ring pushouts are algebra tensor base change).
   Checked its section hypotheses, including preservation by the forgetful functor;
   Core infers this from Mathlib's filtered-colimit preservation instance. Empty relations,
   zero variables, zero rings and `u = 0` introduce no extra hypotheses. Independent
   `rg` searches of Sheaf and the upstream ring modules, and msearch grep with
   `finitely presented.*descend|finitePresentation.*[Pp]ushout|limit_finite_presentation`,
   found the same existing upstream descent tool, not a shorter whole-system theorem.
4. **Route and pruning: pass.** Read the subalgebra diagram and colimit constructions
   at FilteredColimits.lean lines 61–137. The restricted family is nonempty at `j`, is
   directed under binary supremum, and covers each element by adjoining its singleton.
   Read every functor/cocone equation: pushout desc equations and hom extensionality
   prove the laws, and `IsPushout.of_left`/`of_top` cancel precisely the intermediate
   pushouts to give the two required families. Finite type is preserved by base change.
   Each added import is used; removing RingHom.FiniteType in a scratch copy fails with
   missing pushout instances as well as missing finite-type tools. The four original
   public imports serve the unchanged interface. The two removed proof dependencies
   are exhaustively listed under No longer needed. Read `dag/units/sk-thm-p1.json`:
   Core is below its realized statement and steps, all of which remain unchanged.
   Algebra descent is a proved generic tool, not a replacement for a unit step.
5. **DAG: pass after provenance clarification.** Read both delivered node records and
   the original Core dependencies, and compared the descent node against the repository.
   Core's five steps match the actual descent, restricted base colimit, pushout diagram,
   finite-type verification and pushout cancellation. Its proof_deps is exactly the
   union of those steps' uses. No new-node fields are needed. Independently read
   [Stacks 00R0](https://stacks.math.columbia.edu/tag/00R0) and
   [Stacks 05N9](https://stacks.math.columbia.edu/tag/05N9), clause (1): these support the
   approximation and descent routes, respectively.

Changed only the descent node's `lean.note` to explicitly record the section hypothesis
`[PreservesColimit F (forget CommRingCat)]` and explain how Core supplies it, and added
this second reading. No Lean proof repair was needed. Confirmed holes closed: 1
(`Algebra.exists_limit_finite_presentation_core`); holes added: 0; split off: 0.
