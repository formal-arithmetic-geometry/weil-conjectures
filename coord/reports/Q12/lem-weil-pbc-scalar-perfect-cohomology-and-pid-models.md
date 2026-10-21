## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-scalar-perfect-cohomology-and-pid-models.json`: item, statement, split into six steps; original statement preserved exactly.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-pid-submodule-finite-basis.json`: new statement, Mathlib leaf, exact match `Submodule.nonempty_basis_of_pid`, `Mathlib/LinearAlgebra/FreeModule/PID.lean:280` (proof through line 293).
- `citations.json`: ten entries, one per cited node per proof step, using verbatim extracts of the cited statements.
- `searches.jsonl`: search-command log retained unchanged; the node records copy its actual tool/query/results. `bhatt-scholze.txt` is the sandbox-only text extraction of the locally supplied PDF, not a delivery file.

## Attachments

None for the item. I searched all `lean/WeilConjectures/` for its blueprint id and for the perfect-cohomology and two-term resolution notions. `DerivedCategory.IsPerfect.finite_homology` in `CategoryTheory/DerivedCategory/Perfect.lean:136` proves finite generation, not finite presentation or the PID model. `DerivedCategory.IsPerfect.exists_homologyConcentratedIn` at line 114 gives an existential interval, not the complete explicit assertion. `DerivedCategory.prop_of_boundedFiniteCohomology` in `CategoryTheory/DerivedCategory/PrincipalIdealDevissage.lean:83` proves triangulated-subcategory membership but does not supply the specified surjection and augmented quasi-isomorphism. I read these implementations; none is an exact attachment of the whole item, even together. The new finite-basis result is already in Mathlib, so it is a leaf rather than an unsplit project proof.

## WANTED

None. All source documents used are available locally.

## Findings and corrections

The imported statement is correct. No STATEMENT-DISPUTED correction is needed. Its original proof was empty. The old `def-weil-derived-cohomology-sheaves` statement dependency is about module sheaves on sites; the present assertion is about scalar modules, and its cohomology is already defined in `def-weil-abstract-derived-category`. I removed that irrelevant dependency and added the definition of free modules, which supplies the meaning of finite bases and the coordinate free modules used by the statement.

The existing `lem-sfb-scalar-finite-free-resolutions` only handles a DVR (or a field in its second assertion). A general PID such as Z is not necessarily local, so using this node to justify the item's PID assertion would be C4. The existing Z-subgroup and DVR-torsion-free freeness nodes are likewise special cases. The new leaf states the general finite-basis theorem with the same hypotheses as Mathlib; it does not restate the item's resolution, quasi-isomorphism, perfectness, or cohomology clause.

I kept the proper-base-change unit and chapter unchanged. This is the scalar supplement under `lem-weil-pbc-integral-stratified-perfect-characterization`, realizing the first sentence "Choose an integral lattice for K" in the current main-20261015 blueprint proof of `thm-weil-pbc-finite-extension`. I read the chapter, the `sk-thm-properbasechange` unit and that blueprint proof. The ring-theoretic identity Perf(A) = thick(A[0]) is a generic tool, declared in `split_report.tool_uses` for `lem-sf-perfect-ring-classical-generator`; it changes no geometric route.

## Unfinished

No mathematical part is left unfinished. One new node is a Mathlib leaf, with no proof body. Delivery is subject to the required server dry run and push below.

## Not duplicates

lem-weil-pbc-pid-submodule-finite-basis vs lem-sc-valuation-proper-coherent-higher-direct-images: the existing statement concerns coherent cohomology of a proper flat finitely presented morphism over a valuation ring; its text mentions Tag 0ASU only in proof/search material, and does not state a finite basis theorem for submodules over arbitrary PIDs.

lem-weil-pbc-pid-submodule-finite-basis vs lem-sc-valuation-proper-coherent-sections: the existing statement concerns H^0 of an invertible sheaf under a proper flat morphism over a valuation ring, not a basis of an arbitrary scalar submodule; its Tag 0ASU reference is ancillary.

lem-weil-pbc-pid-submodule-finite-basis vs lem-weil-subgroup-finite-free-abelian-group-free: the existing node assumes A = Z and cannot be specialized to an arbitrary PID; the new leaf has arbitrary PID coefficients and a specified finite ambient basis.

lem-weil-pbc-pid-submodule-finite-basis vs lem-sfb-scalar-finite-free-resolutions: the existing node asserts resolutions only over DVRs and basis existence over fields, whereas this leaf is a basis theorem for submodules over arbitrary PIDs and does not assert a resolution.

lem-weil-pbc-pid-submodule-finite-basis vs lem-sfb-scalar-model-finite-flat-resolution: the existing node concerns extension of scalars to a flat ring sheaf over a DVR, or to a ring sheaf over a field; it neither covers arbitrary PIDs nor states the submodule basis theorem.

lem-weil-pbc-pid-submodule-finite-basis vs lem-a1-semilocal-submodule-basis: that node chooses an ambient E-basis inside a generating D-submodule using a local ring with infinite residue field and a semilocal algebra; it does not give an A-basis of an arbitrary submodule over a PID.

lem-weil-pbc-pid-submodule-finite-basis vs lem-sc-dvr-fg-torsionfree-free: the existing node only covers finitely generated torsion-free modules over DVRs; the new leaf covers all submodules of finite free modules over arbitrary PIDs.

## Review by Q12

I read Stacks `more-algebra.tex`, Tag 0657 (`definition-perfect`), Tag 066Q (`lemma-perfect-module`), Tag 0ATI (`lemma-perfect-ring-classical-generator`), and Tag 0ASU (`lemma-split-off-free-part`), particularly its first clause and finite-free ambient induction. I read `algebra.tex`, Tag 00IK (`lemma-Noetherian-basic`) and Tag 00FP (`lemma-Noetherian-finite-type-is-finite-presentation`), including their submodule and finite-presentation assertions. I also read Bhatt–Scholze Proposition 6.8.11(3), printed pages 60–61: its proof uses a finite projective resolution of the scalar module. The explicit resolution here supplies that scalar fact, with the stated extra generality to PIDs. For the one new node I read Mathlib `LinearAlgebra/FreeModule/PID.lean`, especially the ambient CommRing/IsPrincipalIdealRing/IsDomain assumptions and lines 280–305; the theorem has precisely a finite ambient basis and an arbitrary submodule, with no missing Noetherian or torsion-free hypothesis.

For step 1, I opened `def-pc-perfect-ring-complex` and `def-weil-abstract-derived-category`. The former supplies the bounded finite-projective representative; the latter explicitly gives the kernel/image cohomology formula and cohomology functors on the localization. The vanishing argument is the computation of a quotient of the zero module. It applies to every term interval of every such representative, rather than using only the existential bound in the source Lean theorem.

For step 2, I opened `lem-weil-pbc-noetherian-submodule-finite` and `lem-sc-noetherian-finite-module-finite-presentation`. The hypotheses are respectively the Noetherian ring A and the finite module C^q, and then the same ring and the finite cohomology quotient. The statements give exactly these two conclusions. The quotient's finite generation is written out using images of generators, rather than concealed behind an uncited finiteness theorem. A presentation transports across the cohomology isomorphism by composition, with unchanged kernel.

For step 3, I reread the new finite-basis leaf. Apply it to the actual kernel S of the given map v inside the finite free module A^r, with its standard coordinate basis. Its conclusion supplies basis vectors in S itself. The displayed finite sum defines h, and basis uniqueness supplies its injectivity; basis spanning supplies its surjectivity. Composing with the kernel inclusion therefore gives the specified injective u with exactly the desired image. The surjection has not been replaced by a newly chosen presentation. This is the only substantive PID algebra input; it is smaller than the item's resolution assertion and is already proved in Mathlib.

For step 4, I opened `def-weil-abstract-derived-category` again: it defines a quasi-isomorphism as an isomorphism on every cohomology object. The equation vu = 0 makes the displayed augmentation a chain map. I checked degree -1 using injectivity, degree 0 using the kernel equality and surjectivity of v, and every other degree using zero terms. The formula [x] -> v(x) is well-defined since v annihilates im u. Thus the step uses the cited criterion, not an uncited general theorem about resolutions.

For step 5, I opened `def-weil-pbc-free-module`, `lem-weil-pbc-free-module-projective`, and `def-pc-perfect-ring-complex`. The first allows empty bases, the second explicitly says free implies projective over any commutative ring, and the last is exactly the bounded finite-projective representative definition. The finite coordinate bases also generate the terms, and the zero terms have the empty basis. Step 4 provides the required identification in the derived category. For step 6, I opened `lem-sf-perfect-ring-classical-generator`: its statement explicitly identifies perfect complexes with thick(A[0]), so it really gives the claimed membership under the commutative-ring hypothesis, without using anything hidden in that node's proof.

I tested the edge cases rather than assuming N torsion-free. Over Z with N = Z/2 and v the quotient Z -> Z/2, the kernel basis is 2, giving [Z --2--> Z] with cohomology Z/2 in degree zero and zero in degree -1. For N = 0 and any r, v is zero and one may take s = r, u = identity. For r = 0, surjectivity forces N = 0 and s = 0 works. If v is an isomorphism, its kernel has the empty basis and s = 0. The first clause also allows the zero Noetherian ring and the zero complex, and a representative of an acyclic nonzero complex gives vanishing cohomology as expected. No PID assertion is made for the zero ring because 1 != 0 is explicit.

I checked B–E of delivery-errors.md in both sections of the merged file: new statements are self-contained, with no proof sketches; the new leaf names the exact declaration/file/line and all queries are genuine search-command log entries; the non-elementary steps each cite the statements actually used; elementary steps give their full kernel/quotient calculations; no new clause is a relabeling of the item; and the new leaf has no edge back to the item. Every cited statement was opened and ten verbatim quotations were written to citations.json. The largest step is 793 characters, so no step reaches the 2000-character hidden-lemma threshold. I used only the authorized literature, no SGA source, no agents, no compiler or build, and no repository or launcher writes.

## Validation

The first server dry run passed with receipt commit 4dc7d4fbc83. A final source-line reread corrected only the ambient-assumption line references in the new leaf to 98–99, 103 and 139; the theorem match and all mathematics are unchanged. The final dry run is repeated after that correction.
