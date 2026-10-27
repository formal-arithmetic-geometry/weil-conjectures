# Q09 stage-1 delivery: lem-trf-galois-p-property-prime-towers

## Files written

- dag/nodes/sec-trace-formula/lem-trf-galois-p-property-prime-towers.json: item, statement, split; no exact Mathlib match for the whole statement.
- dag/nodes/sec-trace-formula/lem-trf-finite-galois-intermediate-fixed-recovery.json: statement, exact Mathlib leaf IsGalois.fixedField_fixingSubgroup (Mathlib/FieldTheory/Galois/Basic.lean:314).
- dag/nodes/sec-trace-formula/lem-trf-subgroup-prime-power-successor.json: statement, exact Mathlib leaf Sylow.exists_subgroup_card_pow_succ (Mathlib/GroupTheory/Sylow.lean:645).
- citations.json: ten verbatim statement quotations, one for each step/node pair.
- report.md; searches.jsonl is the search tool's own record. The two write scripts are sandbox-only preparation artifacts, not DAG deliveries.

## Attachments

None. I searched lean/WeilConjectures for the item id, prime towers, Galois p-groups, and the proposed tool declaration names. There is no project declaration proving the whole item. The project already has purely inseparable root towers, but those cover only the last part; their existing node is cited.

## Literature wanted

WANTED: literature/temkin-stable-modification-arXiv-0707.3953v3.pdf, proof of Theorem 6.3.1, printed p. 49, and proof of Corollary 6.1.6, printed p. 41, for lem-trf-galois-p-property-prime-towers. The inherited node names this PDF but it is absent from this read clone. I did not write to literature or download it. I read the primary-source PDF online at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf: Theorem 6.3.1 explicitly uses the larger-subgroup chain and separately the purely inseparable tower, while Corollary 6.1.6 repeats the possibly inseparable tower reduction. The actual detailed argument below is marked agent-written, with the available Stacks source and Mathlib supplying all substantive inputs.

## Problems found and corrections

No statement dispute: the imported hypotheses are sufficient, and the statement is retained word for word. Characteristic zero is allowed with any prime p; its purely inseparable part is trivial. Characteristic p permits nonseparable L/F, so a purely separable argument alone would be insufficient.

The imported node had no proof. Its subgroup-chain assertion requires keeping the subgroup H fixing the separable part, not just choosing unrelated subgroups of orders p^j. The existing subgroup-order node does not assert containment of a prescribed subgroup. I used the stronger exact Mathlib enlargement theorem and wrote out the finite induction. I also avoided assuming the separable part is Galois over F: it embeds in a finite Galois envelope, and H need not be normal. The new fixed-recovery leaf concerns arbitrary intermediate fields, whereas the existing normal-subgroup quotient theorem does not state this assertion.

I searched the full DAG, blueprint_refs.py searches for Galois, fixed field, subgroup, p-group, prime-degree, separable-first, purely inseparable, and the new tool declarations. Existing decomposition, envelope, automorphism-count, finite-action-degree, degree-multiplication and purely inseparable tower nodes are all reused. The current blueprint locality proof is the Varshavsky contraction proof; this item is a deeper supporting branch already recorded by its ancestor trail, and no chapter or unit route is changed.

The existing Mathlib-search history is retained, and additional actual searches with their log digests are recorded. Earlier searches for maximal subgroups led to a stronger and simpler usable result, the prescribed-subgroup enlargement theorem. No failed search service is reported as an absence verdict. The grep tool's single-file output sometimes mislabels the line as the file; the final recorded greps use directories and I read the actual source files to verify names and lines.

## Unfinished work

None for this one-level split. Both new nodes are exact Mathlib leaves with empty proofs and proof dependencies. Existing supporting nodes remain the responsibility of their own items. No Lean file was written and no compiler, Lake, or build tool was run.

## Review by Q09

I read the item against the two passages in Temkin's primary PDF and against Stacks fields.tex, labels lemma-separable-first (030K), lemma-normal-closure (09DT), lemma-normal-closure-galois (0EXM), theorem-galois-theory (09DW), lemma-finite-Galois (09I1), lemma-galois-over-fixed-field (09I3), lemma-multiplicativity-degrees (09G9), and lemma-finite-purely-inseparable (09HI). I verified these tags in tags/tags. For the new recovery leaf I read the statement and proof of 09DW and Mathlib Basic.lean:314-323; the theorem assumes finite-dimensional N/F and IsGalois F N and returns exactly the field E. For the new enlargement leaf I read Sylow.lean:641-676, especially its signature at 645-647: the starting subgroup H is retained, the group need only be finite, and the divisibility hypothesis is explicit. There is no Stacks tag for this generalized Sylow theorem, so I do not attach an invented one.

In step 1, lem-weil-pbc-separable-first-purely-inseparable explicitly supplies the subfield E, separability of E/F, pure inseparability of L/E, and E=L in characteristic zero. Algebraicity from finite-dimensionality is the written linear dependence of powers. E/F is finite as a linear subspace; an F-spanning set of L also spans over E. Thus both finiteness hypotheses for later nodes actually hold.

In step 2, lem-weil-pbc-finite-galois-receiving-separable-extensions accepts the single finite separable extension E/F and supplies the embedding into a finite, normal and separable N/F. lem-weil-pbc-finite-galois-fixed-field explicitly supplies finiteness of G, its order [N:F], and the fixed field F. I checked all three clauses in its statement. The item's Galois p-property is used only on N/F, not assumed for an intermediate base.

In step 3, the new recovery leaf applies to the intermediate image of E in N without requiring that E/F be normal. lem-wf-finite-field-action-fixed-degree states [N:N^H]=|H| for a finite faithful action. H is a subgroup of the already finite group G and its inclusion into Aut(N) is injective, so faithfulness is satisfied. The recovery equality identifies N^H with E. lem-weil-pbc-field-degree-multiplicativity states precisely the product formula for finite towers, whose finiteness was checked in this step. The only remaining integer calculation is that a positive divisor of p^a is p^b with b≤a, written using prime factorization; neither Sylow nor Lagrange is silently invoked here.

In step 4, the only cited statement is the new enlargement leaf. The induction invariant is H_0=H and |H_j|=p^(b+j), with containment at each stage. Its divisibility hypothesis holds because b+j+1≤a. The endpoint is G by finite cardinality and containment. This is a finite induction using a cited theorem, not a new standalone subgroup-chain lemma hidden in the text. It is marked elementary for the assembly of that theorem; the nontrivial enlargement theorem itself is a cited Mathlib leaf.

In step 5, the fixed fields are explicit sets, so reversed inclusions follow by checking which automorphisms fix each element. The already established endpoint equalities are reused, not obtained from an uncited correspondence theorem. lem-wf-finite-field-action-fixed-degree gives each ambient degree, and lem-weil-pbc-field-degree-multiplicativity turns their ratio into the required successive degree p. I checked the orientation: H grows from H to G, but T_i uses H_(r-i), so T grows from F to E. Pullback along the original embedding is described explicitly, and preservation of degrees is the basis bijection. Thus the final chain lives in the original L, not just in an isomorphic copy in N.

In step 6, lem-weil-pbc-purely-inseparable-pth-root-tower states every degree-p clause and the generation of L over E, so its statement, not its proof, is what is used. L/E is finite and purely inseparable by step 1; in positive characteristic its base E has the same characteristic p. In characteristic zero step 1 has already established E=L. Concatenation lists E once, and the degree-p inequalities give strict inclusions.

I tested L=F (empty tower), E=F (entirely purely inseparable), E=L (entirely separable), a=b (H=G), a=0 (trivial Galois envelope), and p=2. For a nonnormal separable example the proof still uses an arbitrary H and never forms G/H as a group. Finite fields are not mistaken for fields satisfying the hypothesis: a finite field has extensions of degrees prime to p, so it does not satisfy this Galois p-property. Removing the characteristic restriction would fail for a separably closed imperfect field in a different characteristic q: its degree-q purely inseparable extensions need not admit degree-p towers. The retained restriction is therefore substantive.

Against delivery-errors B: the two new statements introduce every object, use inline meanings for Galois, fixed fields and subgroups, cite the notions they require, carry no proof sketches, use normal single TeX escapes, give exact declarations/files/lines, and have all search methods actually logged. Against C: I opened all eight distinct cited node statements, wrote ten exact quotations in citations.json, and used their stated clauses only; off-unit generic tools are declared in split_report.tool_uses. The new leaves have no proof dependencies and statement dependencies only on definitions, so they cannot create a cycle through the item. Against D: neither new node restates the item or a separable/inseparable clause; the item supplies the decomposition, subgroup induction, degree calculation and assembly. Against E: all finite, faithful, Galois, characteristic and embedding hypotheses were verified above. No non-elementary proof step exceeds 2000 characters (the maximum is 671).

## Not duplicates

lem-trf-finite-galois-intermediate-fixed-recovery vs lem-dl-a1-trivial-inertia-finite-etale-normalization: the new leaf recovers an arbitrary intermediate field E from its own fixing subgroup in a finite Galois N/F; this existing node concerns Finite Galois normalization with trivial inertia is finite etale, not that arbitrary-intermediate-field recovery.

lem-trf-finite-galois-intermediate-fixed-recovery vs lem-per-finite-galois-normal-fixed-quotient: the new leaf recovers an arbitrary intermediate field E from its own fixing subgroup in a finite Galois N/F; this existing node concerns Restriction identifies the Galois group of a normal fixed field, not that arbitrary-intermediate-field recovery.

lem-trf-finite-galois-intermediate-fixed-recovery vs lem-per-tame-inertia-snc-root-quotient: the new leaf recovers an arbitrary intermediate field E from its own fixing subgroup in a finite Galois N/F; this existing node concerns Tame inertia normal form by roots of normal crossings parameters, not that arbitrary-intermediate-field recovery.

lem-trf-finite-galois-intermediate-fixed-recovery vs lem-weil-pbc-finite-galois-fixed-field: the new leaf recovers an arbitrary intermediate field E from its own fixing subgroup in a finite Galois N/F; this existing node concerns A finite Galois extension has finitely many automorphisms and fixed field the base, not that arbitrary-intermediate-field recovery.

lem-trf-finite-galois-intermediate-fixed-recovery vs lem-weil-pbc-galois-invariant-closed-subset-descends: the new leaf recovers an arbitrary intermediate field E from its own fixing subgroup in a finite Galois N/F; this existing node concerns Galois-invariant closed subsets of a Galois base change descend, not that arbitrary-intermediate-field recovery.

lem-trf-finite-galois-intermediate-fixed-recovery vs lem-sfb-epp-artin-schreier-presentation: the new leaf recovers an arbitrary intermediate field E from its own fixing subgroup in a finite Galois N/F; this existing node concerns Artin–Schreier presentation and field-algebra dichotomy, not that arbitrary-intermediate-field recovery.

lem-trf-finite-galois-intermediate-fixed-recovery vs lem-sfb-equivariant-galois-polynomial-envelope: the new leaf recovers an arbitrary intermediate field E from its own fixing subgroup in a finite Galois N/F; this existing node concerns A compatible finite Galois polynomial envelope for a nonfaithful field action, not that arbitrary-intermediate-field recovery.

lem-trf-finite-galois-intermediate-fixed-recovery vs lem-sfb-finite-galois-vector-space-descent: the new leaf recovers an arbitrary intermediate field E from its own fixing subgroup in a finite Galois N/F; this existing node concerns Finite Galois descent for arbitrary semilinear vector spaces, not that arbitrary-intermediate-field recovery.

lem-trf-finite-galois-intermediate-fixed-recovery vs lem-sfb-finite-semilinear-field-envelope: the new leaf recovers an arbitrary intermediate field E from its own fixing subgroup in a finite Galois N/F; this existing node concerns Finite normal field envelope retaining a semilinear finite group, not that arbitrary-intermediate-field recovery.

lem-trf-finite-galois-intermediate-fixed-recovery vs lem-sfb-orbit-kummer-normal-model: the new leaf recovers an arbitrary intermediate field E from its own fixing subgroup in a finite Galois N/F; this existing node concerns Orbit Kummer field and its equivariant normal relative model, not that arbitrary-intermediate-field recovery.

lem-trf-subgroup-prime-power-successor vs lem-sfb-finite-subgroup-prime-power-order: the existing theorem only produces some subgroup of a prescribed order; the new theorem requires containment of the already prescribed H, which is essential to reach the separable field E. The current existing node does not include that clause.

lem-trf-subgroup-prime-power-successor vs lem-sfb-finite-p-group-normal-index-p: that node finds a normal index-p subgroup without controlling containment of H; the new leaf enlarges a specified H, needs no normality and applies in any finite group satisfying the divisibility hypothesis.

lem-trf-finite-galois-intermediate-fixed-recovery vs lem-wf-finite-field-action-fixed-degree: that node gives the Galois property and degree over an already defined fixed field; it does not identify an arbitrary intermediate E with the fixed field of its fixing subgroup.

The new Mathlib leaf statements remain statement-only. No new decomposition or purely inseparable tower node was created, since the existing ones state precisely the needed facts.
