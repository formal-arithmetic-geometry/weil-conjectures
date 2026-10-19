# Worker report: lem-per-completion-supported-constant-comparison

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-completion-supported-constant-comparison.json`: existing statement, now split into seven steps; no new nodes and no Mathlib leaves created.
- `citations.json`: one verbatim statement quote for each of the 21 step citations.

## Attachments

None. I searched the whole read-only `WeilConjectures/` source by the exact blueprint id and by completion/cohomology, formal-base-change, and supported-cohomology vocabulary. The exact-id search found no declaration. The broader search finds formalism base-change declarations and proper/strictly-henselian comparisons, which do not state supported completion invariance for arbitrary excellent local rings. No source declaration was used as a finished attachment.

## WANTED

None for this proof. I read ILO XVII, Lemma 3.6.3, printed p. 279: it cites Fujiwara Corollary 6.6.4 for the completion reduction. The necessary comparison is reconstructed here from the already existing node for ILO XVII Corollary 4.2.3, whose statement and immediate justification on printed p. 281 I also read. The original Fujiwara article is not present and is not being represented as read or cited as an independent dependency. The proof is consequently marked `proof_origin.by: agent`.

## Findings and changes

The item statement is unchanged, including excellence, henselianity, arbitrary signed twists and cohomological degrees, ordinary etale coefficients, and the canonical pullback. Its former proof was empty. The source invokes a general formal-base-change theorem; the split proves the needed specialization with regular base change and an explicit closed-fibre calculation. Henselianity is retained as a stated hypothesis, although this argument only needs the excellent local ring assumptions. No regularity or finite-type hypothesis has been introduced.

The two main identifications have been written rather than left as “transport”: (i) the actual completed closed fibre is the same residue-field scheme, via the canonical quotient map, and (ii) sections of the supported exceptional inverse image compute the ordinary derived kernel of restriction, with the pullback map checked on injective representatives. I separated the coefficient-action transport from this derived calculation so that the abelian-sheaf adjunction is not silently cited as a module-sheaf theorem.

The four Mathlib searches already carried by the repository item were read and retained: LeanFinder on formal base change and closed-point cohomology, LeanSearch on completion and local etale cohomology, Loogle on `"IsAdicComplete", "cohomology"`, and grep on `formal.*baseChange|completion.*etale|etale.*completion`. Their recorded hits concern algebraic etaleness, localizations and condensed locally constant functors, and do not state this assertion. No search was invented or rerun with the same question. No new node needs fresh searches. The sandbox had only dispatcher marker files on resumption, and a process-list check found no interrupted delivery invocation to repeat.

## Unfinished work

None at the stage-1 level: this delivery supplies the natural-language split, not Lean proofs of its dependencies. Delivery validation and its result are recorded below when available.

## Not duplicates

No new nodes. I searched the whole DAG for completion/cohomology, formal base change, Fujiwara, regular supported base change, and the relevant completion vocabulary, and ran blueprint searches for `formal base change`, `completion`, `regular morphism`, `supported`, and `henselian`. No blueprint statement repeats this completion comparison. Existing nodes already supply every algebraic and derived interface needed. In particular `lem-per-regular-supported-base-change` has the prime-power coefficient statement required here; `lem-per-regular-closed-support-base-change` has only the prime-field statement, so it was not substituted for the prime-power theorem. The regular theorem's dependency closure was checked and does not contain this item.

## Review by Q22

I read the chapter and `sk-p-dl-a1-perverse` unit records, the item's blueprint provenance, the ILO pages described above, and Stacks source passages at 07QT (`definition-excellent`), 07GH (`definition-G-ring`), 0381 (`lemma-geometrically-regular`), 0316 (`lemma-completion-Noetherian-Noetherian`), 05GG (`lemma-hathat-finitely-generated`), 05GI (`lemma-radical-completion`), 01U5 (`lemma-flat-characterize`), and 09XQ (`lemma-sections-with-support-acyclic`). I also read the complete statement of every cited node, including the signed-twist and derived-resolution interfaces. This is below the unit level: the comparison supports the normal top-class completion reduction in the potential-dualizing construction already in the ancestor's route.

Step 1 uses exactly the Noetherian-completion theorem, the local-completion/residue-field theorem, the affine quotient closed-immersion theorem, and the affine fibre-product theorem. Those statements supply, respectively, Noetherianity, the unique maximal ideal and its quotient, the two closed immersions, and the scheme-theoretic cartesian square. The tensor/quotient isomorphism is written on pure tensors. A mere equality of point sets would not suffice, and is not used.

Step 2 reads excellence as including the G-ring property and applies the G-ring definition at the maximal ideal of the local ring. Localizing there changes no element, because every denominator is a unit. The affine flatness theorem supplies scheme flatness. I explicitly used the existing finite-field-extension geometric-regularity theorem: the G-ring definition is phrased using purely inseparable extensions, whereas the supported base-change node asks for all finite extensions. The affine tensor formula and regular-scheme definition then verify exactly its fibre condition. Thus the hypotheses required by regular exchange have all been proved, without treating a singular excellent ring as regular.

Step 3 uses the supported-kernel adjunction only for what its statement says on abelian sheaves. Naturality under scalar multiplication gives the module-linear isomorphism and adjunction; faithful exact forgetting detects exactness. The Hom extension calculation proves preservation of injectives directly from its definition. It is an elementary consequence of these cited statements, not an unproved theorem about module injectives.

Step 4 uses the enough-injectives, bounded-below injective-representative, and right-derived-on-injectives statements with their actual boundedness hypotheses. Step 3 makes the same complex injective after supported restriction. Consequently both sides of the supported-sections identification are computed by the same sectionwise kernel complex; the definition of derived supported sections says precisely this. This avoids confusing ordinary global sections with derived global sections on a residue field that need not be separably closed.

Step 5 cites the prime-power regular-supported theorem, with the Noetherian source and target, regular completion morphism and invertible prime checked in Steps 1–2. The coefficient is exactly Z/ell^n. The twist pullback theorem applies with modulus ell^n and coefficient ring Lambda and covers negative as well as positive twists. The support comparison is the theorem's specified closed-counit comparison, not an arbitrary abstract isomorphism.

Step 6 checks that this comparison induces the requested canonical pullback. I used bounded-below K-injectivity to represent the derived pullback by a chain map into the target injective resolution. Pullback preserves the condition that the complementary-open restriction of a section is zero. The resulting map on kernels corresponds to the closed-counit characterization in the supported-exchange statement. Therefore the maps in the displayed composite, under Step 4's identifications, are the actual supported pullback. Choices of comparison maps are homotopic.

Step 7 takes derived sections along the residue-field isomorphism from Step 1 and applies degree-q cohomology. An isomorphism of schemes transports both its site and its injective resolutions, so the first arrow really is invertible even if the residue field has nonzero higher etale cohomology. The second is invertible by Step 5. This proves all degrees of the unchanged statement.

For delivery-errors B–E I checked self-contained original hypotheses and the definition dependencies; there are no statement-only helper nodes, Mathlib leaves, new tags, or new duplicate statements to audit. All 21 citation pairs have quotes copied verbatim from the actual statements. Proof dependencies are the union of step uses. Off-unit algebra and derived-category interfaces are declared as generic tools in `split_report.tool_uses`; they do not replace a step of the Fourier/perverse unit. No source forbidden by the route lock is cited. Every step is below 2000 characters, and the two possible hidden comparisons have their arguments written in Steps 3–4 and 6.

Small cases checked: if A is a field, completion and the closed square are identities and the result preserves the full Galois cohomology of that field. The same is true for an Artinian local ring, whose maximal ideal is nilpotent. If A is already complete the comparison is the identity. Singular excellent rings are allowed because only the morphism to the completion, not the local ring, is regular. Negative q gives zero cohomology on both sides; arbitrary signed m uses the actual invertible Tate sheaf. These checks revealed no statement dispute. No new statement was created or weakened.
