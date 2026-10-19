# Stage-1 report: lem-weil-pbc-sequence-relative-hom-telescope

1. **Files written.**

   - `dag/nodes/sec-proper-base-change/lem-weil-pbc-sequence-relative-hom-telescope.json` — statement, split proof, no new nodes, Mathlib searches recorded.
   - `citations.json` — verbatim statement quotes for each cited node in each proof step.
   - `searches.jsonl` — preserved existing search log and appended the executed Q89 searches.

2. **Attachments.** None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-newtargets-master/WeilConjectures` for the item id, its telescope/Hom terminology, and the blueprint tag; no declaration states this item exactly.

3. **WANTED.** None. The proof follows the available Stacks Project source `literature/stacks-project/derived.tex`.

4. **What was checked and changed.**

   The imported statement and its three statement dependencies were read in full. The statement was retained unchanged, including the two and only two coproduct comparison hypotheses and the absence of a general compactness hypothesis. Its existing blueprint ancestry points to the integral-lattice denominator calculation under `thm-weil-pbc-finite-extension`; that ancestry was retained and the item's `from.place`, `same_as`, and `split_report.blueprint` were completed.

   I read the relevant Stacks passages: Tag 093W (`lemma-compute-colimit`) for the cokernel presentation of a sequential colimit, Tag 0CRK (`lemma-cohomology-of-hocolim`) for the five-term exact sequence after applying Hom, Tag 094A (`lemma-commutes-with-countable-sums`) for the telescope argument, and Tags 0146/0149 for the distinguished-triangle Hom exactness. The existing node `lem-weil-pbc-hom-into-triangle-exact` states exactly the factorization and zero-composition facts used in Step 3; its statement is quoted verbatim in `citations.json`. The colimit universal property used in Steps 4–5 is exactly the statement of `def-weil-pbc-category-colimit`, also quoted there. `def-weil-triangulated-category` supplies additivity, shifts, rotations, and distinguished triangles.

   Step 1 identifies the two assumed comparison maps with the maps induced by `1-s` and its shift on the direct sums of Hom groups. The defining relation `s iota_n = iota_(n+1) u_n` is checked on each finite-support summand, and the shifted relation is checked using the shifted coprojections. Step 2 checks injectivity of `1-shift` on the shifted Hom direct sum by the coordinate recurrence `g_0=0`, `g_(n+1)=u_n[1] g_n`; this explicitly verifies that no transition map is assumed injective or surjective. Step 3 applies the cited triangle exactness to the telescope triangle and its rotations, obtaining surjectivity and identifying the kernel with the image of `1-shift`. Step 4 proves directly, from finite-support sums and the colimit universal property, that the quotient by this image is the sequential colimit with postcomposition transitions. Step 5 descends the Hom map to that quotient, proves injectivity and surjectivity, and checks on each stage that the resulting map is exactly `f ↦ p iota_n f`.

   I tested the statement on the edge cases `K=0`, all `X_n=0`, zero transitions, identity transitions, and a non-injective transition; the coordinate and quotient arguments still apply. I also checked that `lem-pc-compact-hom-hocolim` is not a duplicate: it assumes full compactness for all countable families, whereas this item assumes only the two displayed families. `lem-kun-complex-colimit-hocolim` is derived-category/complex-specific and asserts a termwise colimit model; it does not state this arbitrary triangulated-category Hom comparison. `lem-kun-functor-preserves-hocolim` concerns an exact coproduct-preserving functor and is likewise different.

   No new node was needed. Every non-elementary fact in the five steps is cited, `proof_deps` is the union of the cited nodes, and no SGA source is used. No Lean file was written and no compiler, Lake, or build tool was run.

## Not duplicates

- `lem-weil-pbc-sequence-relative-hom-telescope` vs `lem-pc-compact-hom-hocolim`: the existing node assumes compactness of `K` for every countable family; this item assumes only the two specified sequence coproduct comparisons and works in an arbitrary triangulated category.
- `lem-weil-pbc-sequence-relative-hom-telescope` vs `lem-kun-complex-colimit-hocolim`: the existing node is a derived-category theorem identifying a termwise complex colimit with a homotopy colimit; this item is a Hom-group comparison for an arbitrary chosen telescope triangle.
- `lem-weil-pbc-sequence-relative-hom-telescope` vs `lem-kun-functor-preserves-hocolim`: the existing node transports telescopes through an exact coproduct-preserving functor; this item proves a Hom-colimit bijection from two sequence-specific comparison maps.

## Review by Q89

   I reread the item source, the chapter and unit records, the current blueprint ancestry, and every cited node statement. For Step 1 I verified that the source and shifted source families use precisely the given coprojections and that the equations with `1-s` follow on finite-support summands. For Step 2 I checked the coordinate induction and its edge cases, including arbitrary transition maps. For Step 3 I checked both triangle rotations, the direction of the Hom factorization, and the identification of the kernel with the image of the first triangle map. For Step 4 I checked the quotient's cocone relation and its universal factorization for an arbitrary compatible family of abelian-group homomorphisms. For Step 5 I checked that the descended map is well defined, injective, surjective, and agrees with `p iota_n f` on every stage. I corrected the imported empty proof by expanding it into these five source-linked steps; no statement or dependency was weakened, and no hidden hypothesis beyond the two displayed comparison bijections was introduced.

The resumed review compared the sandbox item with the current shared item: its statement, statement dependencies, source and ownership metadata agree; the sandbox adds the proof and split report. I read Stacks derived.tex lines 10326–10426 and 358–410 directly, and reread the exactness and colimit node statements used by the proof. Each non-elementary step is under 2000 characters; no long step conceals a separate lemma. The first resumed dry run rejected only the heading of this signature section, which is now corrected. No further mathematical correction was needed.
