# Stage-1 repair: lem-pur-integral-operations-scalar-extension

## Files written

- Item node `dag/nodes/sec-smooth-purity/lem-pur-integral-operations-scalar-extension.json`: retained the statement and Lean record, and replaced returned Step 3 with four short steps (twelve steps total; maximum 1708 characters).
- New statement-only node `lem-pur-derived-complete-koszul-reconstruction`: no Mathlib match; isolates the strict Koszul/quotient tower and Roos reconstruction.
- New statement-only node `lem-pur-derived-complete-reflector-transfer`: no Mathlib match; isolates transfer of local completeness and the specified completion unit across an isomorphism.
- `citations.json`: 32 verbatim step/node citations.
- `searches.jsonl`: retained the prior searches and their recorded results.

## Attachments

None. The source search found no sorry-free declaration of the item. Existing `lem-pur-compact-support-roos-cofinality` supplies the arithmetic Roos subsequence fact, so the attempted duplicate helper was deleted and the item now cites that existing node.

## WANTED

None.

## What was wrong and what changed

The returned Step 3 was 2324 characters and hid two lemmas: the comparison of the Koszul completion with the specified quotient Roos object, and the finite-block arithmetic reindexing of the Roos cone. I retained the route and statement, split the first argument into the two new statement-only nodes above, and cited the existing `lem-pur-compact-support-roos-cofinality` for the second. The first dry-run retry identified the latter as a duplicate of existing nodes `lem-pur-compact-support-completed-projection-coherence` and `lem-pur-compact-support-roos-cofinality`; I read both statements, deleted the duplicate file, changed Step 6 and its citation to the existing cofinality node, and kept only the two genuinely new helpers. No statement was weakened or changed.

## Review by Q109

I read the item source `literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/def-weil-derived-pullback-tensor-hom.md`, especially the integral/common-stage paragraph, and the current `sk-thm-sf-compatibility` unit. The item statement and its complete Lean record remain byte-for-byte equal to the current shared node. I read the source records and statements of every node cited by all twelve steps; each citation quote in `citations.json` is a literal substring of the cited statement.

Steps 1–2 use the valuation-ring extension, finite quotient, completeness, completed-coefficient, and completed-constant-sheaf statements for the uniformizer basis and finite-level reduction. The hypotheses are instantiated with (A=\mathcal O_E), (B=\mathcal O_L), (t=\varpi_E), and (v=\varpi_L). Step 3 uses the Koszul reflector and the completed reduction model. Step 4 uses the derived-completeness Roos triangle, strict-tower homotopy-limit triangle, the K-flat resolution existence statement, and the new reconstruction statement; the injectivity hypothesis is supplied by the two-term reduction from Step 2. Step 5 uses the reflector output criterion, reconstruction isomorphism, and the new reflector-transfer statement. Step 6 uses exact countable products, strict Roos comparison, and the existing cofinality statement. The latter is stated for constant coefficients, so I corrected Step 6 to apply it after forgetting from completed $S_W$-modules to constant $B$-modules. Kernels, cokernels, products and cones retain the same underlying sheaves; hence forgetting detects the required quasi-isomorphism. The displayed block maps use only the original transitions and finite sums, so they are $S_W$-linear. This checks the missing coefficient hypothesis instead of treating the constant-coefficient statement as a theorem about arbitrary sheaves of rings. The node explicitly supplies the resulting natural quasi-isomorphism, augmentation compatibility, and composition under subsequences.

Steps 7–9 use the derived change-of-rings, scalar-extension, integral-operation, K-flat, finite-constant inverse-image, and tensor-pullback statements. I checked that the coefficient maps are (f^{-1}R_Y\to R_X) and (f^{-1}S_Y\to S_X), with no unsupported equality of completed inverse images. Steps 10–11 use the internal-Hom restriction/currying, local-completeness, complete-elements, internal-Hom, K-injective existence, and localized K-injective statements. Step 12 is elementary after those cited maps: it checks multiplication/evaluation on pure tensors and uses the completion unit for the identity extension.

For the two new nodes, I checked B1–B7: each is self-contained, TeX-formatted, statement-only, has its own definitions as statement dependencies, records the Stacks source and blueprint ancestry, and has LeanSearch, Loogle/LeanFinder, and grep searches recorded. I searched the whole DAG and blueprint before creating them. The existing cofinality node was opened after the duplicate diagnostic; it is strictly more general for the arithmetic tower, so no duplicate remains. The reconstruction and transfer statements were tested at the zero object, an invertible parameter, and the point-site example (mathbb Z,t=2); the latter catches the distinction between quasi-isomorphic complexes and isomorphic complexes. The arithmetic statement was checked at (e=1), (e=2), identity and zero-transition towers, zero complexes, and a finite initial nonzero segment. No SGA source, Lean compiler, Lake, or live-project write was used.

## Not duplicates

- `lem-pur-derived-complete-koszul-reconstruction` vs `lem-pur-compact-support-roos-cofinality`: the existing node only compares one tower with an arithmetic subsequence; the new node compares regular-element Koszul and quotient towers and reconstructs a specified Roos object.
- `lem-pur-derived-complete-reflector-transfer` vs `lem-weil-pbc-ringed-koszul-completion-reflector`: the existing node constructs the reflector and its criterion; the new node isolates the inference from an arbitrary isomorphism (K\cong C(K)) to the specified unit.
- `lem-pur-derived-complete-koszul-reconstruction` vs `lem-weil-pbc-ringed-strict-tower-homotopy-limit`: the existing node supplies a Roos triangle for a fixed tower; the new node adds the regular-element quotient comparison and projection-normalized reconstruction.

- `lem-pur-derived-complete-koszul-reconstruction` vs `def-weil-pbc-ringed-koszul-system`: the existing node defines a strict Koszul system and unit, without the quotient-tower levelwise quasi-isomorphism or reconstruction of a separately specified Roos triangle.
- `lem-pur-derived-complete-koszul-reconstruction` vs `lem-weil-pbc-ringed-cech-koszul-dual-limit`: the existing node identifies a Cech-derived Hom with a Koszul-tower limit, without identifying that tower with quotient sheaves or a given quotient-Roos object.
- `lem-pur-derived-complete-koszul-reconstruction` vs `def-coef-ringed-sequence-site`: the existing node defines a sequence-site total-limit construction, without the regular-element Koszul/quotient comparison and projection-compatible reconstruction.
- `lem-pur-derived-complete-koszul-reconstruction` vs `lem-coef-derived-system-evaluation-calculus`: the existing node gives a coefficient-system evaluation/adjunction calculus, without the asserted tower quasi-isomorphism and Roos reconstruction.
- `lem-pur-derived-complete-koszul-reconstruction` vs `lem-coef-finite-adjunction-diagram-realization`: the existing node realizes finite adjunction diagrams, without regular-element quotient reconstruction.
- `lem-pur-derived-complete-koszul-reconstruction` vs `lem-sf-integral-compactification-system-realization`: the existing node concerns compactification systems on constructible inputs, without the arbitrary ringed-site Koszul/quotient theorem.
- `lem-pur-derived-complete-koszul-reconstruction` vs `lem-cbc-completed-pullback-triangles`: the existing node proves completed pullback triangles, without a regular-element tower comparison or specified Roos-object isomorphism.
- `lem-pur-derived-complete-koszul-reconstruction` vs `lem-pur-compact-support-completed-projection-coherence`: the existing node compares completed projection mates, without the Koszul/quotient levelwise quasi-isomorphism and reconstruction.
- `lem-pur-derived-complete-koszul-reconstruction` vs `lem-sp-completion-mate-comparison`: the existing node compares completion mates, without identifying a quotient Roos object with a Koszul completion.
- `lem-pur-derived-complete-koszul-reconstruction` vs `lem-sp-levelwise-kinjective-tower-image`: the existing node computes images of K-injective towers, without the regular-element quotient comparison or reconstruction.
- `lem-pur-derived-complete-reflector-transfer` vs `lem-weil-pbc-ringed-localization-rhom-calculus`: the existing node gives localization Hom restriction and currying, without the inference from an isomorphism (K\cong C(K)) to the specified unit criterion.

- `lem-pur-derived-complete-koszul-reconstruction` vs `lemma-weil-pbc-koszul-quotient-limit`: the existing node assumes a pro-etale complete coefficient datum and compares its intrinsic and quotient completions; the new node treats an arbitrary small ringed site with a regular element and also reconstructs an object from a separately specified distinguished Roos triangle.
- `lem-pur-derived-complete-koszul-reconstruction` vs `prop-weil-pbc-koszul-reconstruction`: the existing node requires the Noetherian finite-perfect completed coefficient datum and starts with invertibility of the Koszul unit; the new node assumes only a regular element on a ringed site and obtains an object isomorphism from the supplied quotient Roos triangle.

## Retained repair checked against the current shared head

I compared the retained sandbox with the current shared item: only proof, proof dependencies, split report, search records and split status differ; its statement, Lean record, statement dependencies and maintainer fields are equal. Original Steps 1–2 are identical. The later original steps keep their arguments, with internal step numbers updated after the insertion. The 2324-character original Step 3 is replaced by Steps 3–6: the Koszul reflector application, the strict quotient reconstruction, transfer to the specified unit, and arithmetic Roos cofinality. I added the explicit K-flat existence citation to the reconstruction application; that fact was already used and cited later in the original proof.

I reopened Stacks `algebraization.tex`, `lemma-derived-completion` (099B), and `lemma-derived-completion-koszul` (0A0E), and `sites-cohomology.tex`, `lemma-derived-limit-is-ok` (0941). These give the local reflector, the Koszul limit formula, and strict-tower Roos comparison respectively. The first new statement additionally isolates the regular-element quotient comparison and the isomorphism of triangles with the same product arrow; it does not identify chain complexes literally. The second isolates transport of the local vanishing condition across an isomorphism before applying the specified unit criterion. I read the retained Mathlib search results, including `Functor.essImage.unit_isIso` and its source at `CategoryTheory/Adjunction/Reflective.lean:87`: it concerns a specified reflective adjunction rather than the ringed-site vanishing criterion and arbitrary endofunctor hypotheses of the new transfer node. No search was invented or repeated.

I checked the arithmetic lemma's actual displayed maps and its constant-ring hypothesis against Step 6. Restriction of coefficients preserves the underlying module sheaves, and both displayed maps remain linear for the completed ring, so the existing lemma supplies the required quasi-isomorphism and augmentation compatibility. This leaves no inline block-elimination lemma in the item. The final proof has twelve steps, each shorter than 2000 characters. The two new helper statements remain unsplit.


## Unfinished

The two new helpers are deliberately statement-only and enter the queue. The resumed server dry run passed at f8fc94f87b (preflight passed, not pushed). All 32 step/node citations were checked again against the current statements, with no missing or extraneous entries and no non-verbatim quote. The twelve proof steps have lengths 1248, 1307, 433, 699, 306, 1067, 1194, 1314, 771, 911, 1625 and 1708 characters. No remaining proof step exceeds the human limit. The statement, full Lean record and maintainer-owned fields remain unchanged. The final dry run is rerun after this report update, then the delivery is pushed.

