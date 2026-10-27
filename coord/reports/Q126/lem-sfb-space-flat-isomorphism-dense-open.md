## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-flat-isomorphism-dense-open.json`: item, statement retained verbatim; five-step split.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-flat-finite-presentation-dense-open.json`: statement-only input, Stacks 0877; not in Mathlib.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-flat-pullback-schematic-density.json`: statement-only input, Stacks 089D; not in Mathlib for algebraic spaces.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-flat-monomorphism-representable.json`: statement-only input, Stacks 0B8A; not in Mathlib.
- `citations.json`: verbatim statement quotations for every step/use pair.
- `searches.jsonl`: actual msearch log. All newly recorded node searches are copied from it with their returned digest and hits.

## Attachments

None. A whole-project search for the item tag and for schematic density found no exact declaration in `lean/WeilConjectures/`. The normal-dense-open scheme declarations have normality hypotheses and different conclusions. The existing Mathlib leaf `lem-pe-flat-lfp-monomorphism-open` is reused, not recreated.

## Literature wanted

None. Read the actual local Stacks sources: spaces-more-morphisms.tex Tag 0879 (lemma-zariski), Tag 0877 (lemma-flat-finite-type-finitely-presented-over-dense-open-X) and Tag 0B8A (lemma-flat-case); spaces-morphisms.tex Tags 089D, 03MB and 03MO; spaces-descent.tex Tag 041X. The local tags/tags table confirms the labels. Read the scheme proof in flat.tex Tag 081M as background, but do not cite it as a new node.

## What was wrong or changed

The item was unsplit with an empty proof. Its statement is correct and has been left byte-for-byte unchanged. Its inherited conventions include blowups, closed immersions and quasi-coherent ideals not needed to state this lemma; these are harmless unused conventions retained to avoid gratuitous statement edits.

The source proof uses finite presentation, relative dimension zero, local quasi-finiteness, representability, and the scheme dense-open Zariski lemma. This split retains the finite-presentation input but uses a shorter elementary closed-diagonal argument to prove monomorphism, followed by Rydh's flat-monomorphism representability and the already available scheme Mathlib leaf. This is explicitly marked as an agent assembly, rather than attributed to the proof of 0879. It changes no unit-level route: this is an auxiliary algebraic-space lemma far below the compactification prerequisites. The latest blueprint has no statement of these three supporting results; `blueprint_refs.py ancestor` returns null for this inherited auxiliary chain, which is retained and described precisely. Read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`, as well as the recorded unit and chapter records.

The first grep for the finite-presentation input mistakenly gave a nonexistent subdirectory `AlgebraicGeometry/Morphisms/Flat`; its empty answer is not used as evidence. It was corrected by a logged grep of the existing Morphisms directory. A Loogle query used a nonexistent identifier `Scheme.Hom.IsSchematicallyDominant`; it was corrected to `AlgebraicGeometry.IsSchemeTheoreticallyDominant`. Only the successful corrected queries are used for the new nodes. The corrected query found the exact scheme analogue; it was read in Mathlib/AlgebraicGeometry/Morphisms/SchemeTheoreticallyDominant.lean:95-118. Passing to algebraic spaces is a substantive etale-local theorem, so 089D is not a Mathlib leaf. FlatMono.lean:25-58 was also read; its scheme-domain hypotheses rule out using it for representability or for the entire item.

## Unfinished work

No unfinished part of the item's assembly proof. The three new supporting nodes remain unsplit, as required for a one-level split. No Lean was written and no compiler, Lake or build tool was run.

## Not duplicates

lem-sfb-space-flat-finite-presentation-dense-open vs lem-sfb-space-reduced-generic-flat-finite-presentation: the latter finds some dense open on a reduced base on which a finite-type map is flat and finitely presented; 0877 starts with a specified quasi-compact schematically dense open and global flatness and concludes finite presentation on the entire base, without reducedness or quasi-compactness of the morphism.

lem-sfb-space-flat-pullback-schematic-density vs lemma-nagata-dense-flat-pullback: the latter concerns schemes and their scheme-theoretic images; the new node concerns small-etale sheaves on algebraic spaces and quasi-compact open subspaces, not assumed representable schemes. Its extension from the scheme theorem requires etale descent, and is not a one-line specialization.

lem-sfb-space-flat-monomorphism-representable vs lem-pe-flat-lfp-monomorphism-open: the latter is a scheme Mathlib leaf assuming local finite presentation and proving openness. The new node has an algebraic-space source and target and proves representability without any finiteness hypothesis; it does not assert openness.

No existing node source states Tags 0877, 089D or 0B8A. A coincidental 0B8A occurrence in the ring-theoretic Zariski-main node is in recorded search metadata, not its source or statement; it concerns localization of the integral closure of a finite-type ring map, not flat space monomorphisms. Whole-DAG and whole-blueprint searches were made by tags and the notions finite presentation/dense open, schematic density/flat base change, and representable/flat monomorphism.

## Review by Q126

I checked the item against the three numbered hypotheses of Tag 0879. Separated, flat and locally finite type are all required, and the open immersion must be quasi-compact and schematically, rather than merely topologically, dense. The conclusion is exactly open immersion; there is no covert surjectivity, properness, quasi-compactness of g, quasi-compactness of the base, or Noetherian hypothesis. The new 0877 statement preserves all three source hypotheses, including finite presentation of the restriction rather than its being an isomorphism. The 089D input preserves quasi-compactness of the open; its additional quasi-compact-open conclusion is immediate on scheme tests under base change. The 0B8A input is the unrestricted flat-monomorphism representability theorem, not its finite-presentation corollary.

For step 1 I read `def-weil-etale-morphism`, whose statement explicitly includes local finite presentation, and `def-sfb-space-morphism-properties`, whose statement supplies the compatible-etale-chart test. Thus an isomorphism on V is locally finitely presented, and the new 0877 node applies to the actual flat locally-finite-type map and specified open. I did not infer finite presentation directly from finite type or use Noetherianity.

For step 2 the fibre-product node explicitly constructs P and gives preservation of etale covers. The locality node explicitly says flatness is preserved by arbitrary algebraic-space base change, so the first projection P to Y is flat. The 089D node is applied twice: first to g, then to that projection. Its first conclusion includes that Y_V is a quasi-compact open, so the second application has its required hypothesis. This avoids silently asserting that a composite is flat without a citation.

For step 3 the morphism-property definition explicitly identifies separatedness with a diagonal represented by closed immersions. I read the full statement of `lem-sfb-space-ideal-closed-subspace-correspondence`: it gives the bijection with quasi-coherent ideals and says etale inverse image restricts the ideal. On W, which is exactly the product over V, the diagonal is the diagonal of the given isomorphism, so the restricted ideal is zero. The injection of structure sheaves from step 2 kills the original ideal, hence the diagonal is the zero-ideal closed subspace, namely all of P. The last sentence checks monomorphism on every test scheme by pairs; it is an elementary sheaf/ideal calculation and not a new lemma disguised as a citation. It does not confuse topological density with schematic density or infer equality of closed subspaces from equality of points.

For step 4 I checked Rydh's statement and proof in 0B8A: its hypothesis is precisely flat plus monomorphism, with no local finite presentation needed, and its conclusion is representation by schemes on every scheme test. It therefore supplies exactly the scheme sources required in the next step, without assuming what we are proving.

For step 5 the algebraic-space definition supplies the scheme etale atlas. The fibre-product node supplies the etale map Y_U to Y; representability from step 4 makes Y_U a scheme. Consequently the compatible charts in the morphism-property definition give flatness and local finite presentation directly. Monomorphism is preserved by this base change by the pair calculation, with no additional theorem needed. The reused scheme leaf states exactly flat + locally finitely presented + monomorphism implies open immersion. I verified its actual Mathlib declaration in FlatMono.lean:38. The last cited node, `lem-trf-space-open-immersion-etale-local`, states descent along a jointly surjective etale family with scheme targets and explicitly concludes representability and open immersion. It applies to this atlas, with no quasi-compactness of it needed. This off-unit generic descent tool is declared in split_report.tool_uses; the product node is likewise a generic construction, not a replacement of a unit step.

I checked B through E of delivery-errors point by point against these statements: new nodes contain no proofs; all objects and nonstandard notions have definitions or inline meanings; tags and labels agree; citations use the statements, never hidden parts of proofs; no circularity or restatement of the desired open-immersion conclusion occurs in a new node. The new facts are genuinely independent inputs: none assumes a separated map isomorphic on a dense open and concludes open immersion. Every proof step is below 2000 characters.

Small cases: when T is empty all maps and products are empty and the conclusion holds; when V=T the given map is already an isomorphism; if V is empty, schematic density forces the zero structure sheaf, hence T is empty (no nonempty scheme chart has zero structure sheaf). Empty Y with nonempty V cannot satisfy the isomorphism assumption. A proper dense open inclusion satisfies the assumptions and gives an open immersion that is not surjective, so the proof never upgrades the conclusion globally to an isomorphism. Infinitesimal closed thickenings of a field demonstrate why ordinary density cannot replace schematic density in the zero-ideal argument. For the new representability input the generic-point inclusion Spec K to Spec R of a valuation domain is flat and a monomorphism even when not locally of finite presentation: representation is true, and no erroneous openness assertion has been added. The finite-presentation input allows empty source and nonreduced base; the density input imposes no finite type assumption on the flat morphism.
