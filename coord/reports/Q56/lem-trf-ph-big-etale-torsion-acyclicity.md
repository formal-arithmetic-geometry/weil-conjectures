# Stage-1 repair: lem-trf-ph-big-etale-torsion-acyclicity

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-ph-big-etale-torsion-acyclicity.json`: repaired item; its statement, statement dependencies and blueprint ancestry are unchanged.
- `dag/nodes/sec-trace-formula/lem-trf-ph-etale-comparison-hypotheses.json`: new statement-only prerequisite, Stacks 0F0I; not in Mathlib.
- `dag/nodes/sec-trace-formula/lem-trf-refined-topology-comparison-vanishing.json`: new statement-only prerequisite, the first assertion of Stacks 0EZF with its five hypotheses written out; not in Mathlib.
- `citations.json`: verbatim statements for each of the four citations in the three proof steps.

The prior item Mathlib records and `searches.jsonl` were retained, and the four logged searches from the first Q56 attempt were added to the item's records. The new prerequisites each have four searches actually run through msearch.py: LeanFinder, Loogle, grep and a differently phrased LeanSearch question. None is a Mathlib leaf. `repair.py` is a sandbox-only editing script, not a project file.

## Attachments

None. Searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag and for ph-topology, ph-site, ph-sheaf and comparison/induction names found no declaration stating the item or either prerequisite. The generic weak-Serre derived-category material concerns closure of complexes under triangles, not this comparison theorem.

## WANTED

None. All sources are in the supplied Stacks checkout.

## What was wrong and how it was repaired

The returned split's Step 2 simply applied 0DE4(1), the item itself. Its uses listed definitions, so it supplied neither a proof nor nodes for the non-elementary input. The old Step 3 likewise quoted 0DDW without a node and incorrectly attributed its ph-sheaf assertion to the big/small etale retraction node. The successful initial mechanical dry run (`fee28ee3da`, not pushed) did not establish mathematical correctness. I continued the existing sandbox and compared it with the current shared item: the differences were the old proof, proof dependencies, proof origin, split report and split status; its mathematical statement and base metadata agreed.

The replacement follows the actual proof of 0DE4(1): its geometric input is precisely lemma-compare-ph-etale, now a prerequisite node with the weak Serre condition and all five properties. Its cohomological input is the general theorem lemma-V-C-all-n-general, now a separate prerequisite node on arbitrary sites. The item checks their specialization and takes n=q. It does not use 0DE4(1) as an assumption. The degree-zero clause uses property (A-sheaf) of the geometric input and the universal property of sheafification, so it gives exactly the ordinary adjunction unit.

Both prerequisites are left unsplit: they have empty proof and proof-dependency lists, and no proof sketch in their statements. They carry work genuinely below the item. The first establishes a geometric hypothesis package, including closure under all proper higher direct images and refinement of covers; it is not a new name for this item's acyclicity. The second is the general site-theoretic vanishing theorem, independent of schemes, etale sheaves or proper morphisms. Its explicit hypotheses are essential. These are the two source lemmas the return required the DAG to carry.

## Not duplicates

No current DAG node carries 0F0I, 0EZF, compare-ph-etale or V-C-all-n-general. Searches covered all DAG chapters by tags and by phrases including two topologies, refinement and weak Serre; blueprint_refs searches included those labels/tags, `ph topology`, `weak Serre comparison`, `covering Serre`, and `two topologies`. There are no existing-node pairs sharing either new node's source tag.

The existing `def-trf-ph-scheme-site` defines the topology but proves no comparison hypothesis package. The existing `lem-trf-big-small-etale-exact-retraction` states exact restriction and the small-site unit, not the ph sheaf property or ph acyclicity. The existing item and its parent `lem-trf-ph-etale-torsion-comparison` state the concrete vanishing and small-site derived comparison respectively, not the general site theorem with its hypotheses. None subsumes the new prerequisite statements. Mathlib's dense-subsite equivalences assume an equivalence of entire sheaf categories, which this setup does not have; their occurrence in search results does not make the generic vanishing theorem a Mathlib specialization.

## Review by Q56

I read Stacks `etale-cohomology.tex`, section-ph-etale: 0DDW (lemma-describe-pullback-pi-ph), the entire statement and proof of 0F0I (lemma-compare-ph-etale), and 0DE4 (lemma-V-C-all-n-etale-ph), especially the proof of part (1). I also read `sites-cohomology.tex`, section-compare, 0EZ3 (situation-compare), the definition of (V_n), lemma-V-implies-C-general, lemma-V-implies-cohomology-general, lemma-V-implies-cohomology-extra-general, lemma-make-class-zero-general, the full induction step, and 0EZF (lemma-V-C-all-n-general). I checked the unit/chapter and the ancestor's current blueprint_update: this remains the ph descent input in the normal-cone specialization route; it uses no prohibited trace/purity route.

For the new geometric prerequisite, the source 0F0I explicitly asserts weak Serre and exactly the five listed properties. I checked their meanings in 0EZ3, rather than retaining a tag as a substitute for their statements. Weak Serre here means closure under kernels/cokernels between objects and extensions, not closure under arbitrary subobjects. The source proves it using the exact fully faithful small-to-big pullback and the exact retraction. It proves base-change-P using proper base change stability, restriction-A using the big/small pullback square, A-sheaf using 0DDW, A-and-P using 0DDJ(2) together with torsion-direct-image (0DDD), and refine-tau-by-P using dominate-fppf-etale-locally (0DET), finite properness and proper-surjective ph coverings. Those are genuine tasks left in the new unsplit node. In particular, the argument of 0DDW uses the ph-sheaf criterion 0DBQ and proper-pushforward stalks 0A3T; I no longer claim that the retraction node proves it. I checked the equalizer on a nonempty geometric fibre: equality of the two pullbacks of a locally constant function forces equal values at any two geometric points, so the equalizer consists of constants. Surjectivity is essential at that point.

For the new generic prerequisite, every hypothesis is written out from 0EZ3, including the intermediate singleton covering in P and both coarser-topology coverings in the refinement. The morphisms are relocalizations of the slice sites; this is not a claim about arbitrary maps of sites. Its conclusion is exactly the first assertion of 0EZF. The source starts from the vacuous (V_0) and uses the induction step; that step uses (V_n) to obtain (C_n), cohomology comparison through n and the degree-(n+1) injection, then refines a cover through P to kill a class locally in the coarser topology. This substantial argument is retained as an unsplit theorem, not hidden inside an elementary step of the item. I did not copy the source's additional derived-complex conclusions, which the item does not need.

Step 1 cites only the geometric prerequisite. I opened its statement and checked that it supplies all five conditions and the weak Serre hypothesis, as well as the topology inclusion and comparison functors. The identification of (Sch/T)/X with Sch/X is written out: its objects are U to X to T and its morphisms are X-morphisms; the coverings agree on the underlying families. This works for every X over T with the compatible universe presentations, without a finite-type or quasi-compactness assumption.

Step 2 cites the same prerequisite specifically for property (3) and the stated description of epsilon as sheafification/inclusion. G lies in A'_T by the definition of that subcategory. Once G is a ph sheaf, the universal property makes the sheafification unit invertible: the identity gives the inverse and uniqueness proves both inverse equations. That last two-line argument is elementary. The step does not cite the big/small exact retraction for a ph-sheaf claim, repairing C4.

Step 3 cites both prerequisite statements. It uses exactly the five properties of the first and the all-n vanishing assertion of the second, with the object id_T in Sch/T and H=epsilon_T^{-1}G in A_T. Choosing n=q yields the required vanishing for each positive q. Both statements quantify over locally torsion sheaves with no common annihilator and place no invertibility condition on torsion orders. All three item steps have fewer than 2000 characters, and none contains an inline cohomological induction or proper base-change proof.

I checked edge cases for all three statements. For F=0 and for the empty scheme, all the sheaf and higher-direct-image assertions are zero assertions. For constant Z/n, including n divisible by a residue characteristic, the geometric hypothesis package has no invertibility requirement. For Q/Z it requires no common exponent. In the generic theorem n=0 is an empty vanishing range; for tau=tau' the comparison is the identity and positive derived images vanish; taking each A'_X to be the zero subcategory makes the conclusion vacuous. The generic theorem quantifies over small site presentations, not a colimit over all schemes in an unbounded universe.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the files. Definitions are cited or supplied inline (slice sites, weak Serre, inverse-image class, refinement). Every non-elementary assertion used in the item is now a statement of one of its cited nodes; the verbatim quotes in citations.json show which. The two new nodes have the item's chapter/unit and proper blueprint ancestry, use existing definitions, and create no cycle through the item or its parent. No off-unit theorem is used directly in the item, so split_report.tool_uses remains empty. No item statement was corrected or weakened. No Lean source, compiler, Lake or global build was used.

## What remains

Only the two newly exposed prerequisite statements remain unsplit, as required by the one-level split. The repaired delivery must pass the server dry run before pushing.
