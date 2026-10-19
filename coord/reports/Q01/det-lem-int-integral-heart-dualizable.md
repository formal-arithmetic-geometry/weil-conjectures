# Worker report: det-lem-int-integral-heart-dualizable

## Files written

- `dag/nodes/sec-six-functors-basics/det-lem-int-integral-heart-dualizable.json`: the item, split into ten steps using existing nodes only. No new nodes and no new Mathlib leaves.
- `citations.json`: 30 verbatim statement quotations, one for each node/step citation.

The sandbox also contains the mandated search-command log and a sandbox-only writing script. These are not proposed project changes. The unit's key node is `sk-lem-int-integral-heart`, not this item, so no unit realization was changed.

## Attachments

None. I searched the read-only `WeilConjectures/` source for the item id, the blueprint tag, integral-heart/local-dual language, dualizability and finite-perfect derived Hom. No project declaration found states every clause of this item with these coefficient sheaves, local-model hypothesis, both Tor bounds and the residue example. Generic perfect-duality declarations and sorry-containing reference material are not attachments of this item. No source or Lean file was written, and no compiler was run.

## WANTED

None for this split. The blueprint and the Stacks TeX needed for the argument are present locally. No SGA source is used.

## Statement and proof changes

The source is the current main-20261015 blueprint, `sec-six-functors-basics/sk-lem-int-integral-heart/sk-lem-int-integral-heart-dualizable.md` and its `.proof.md`. I also read the chapter and unit records, particularly unit steps 4 and 5. The item follows their two-term free-resolution route.

The statement now introduces the previously implicit prime, finite extension, valuation ring, uniformizer, coefficient sheaf, local-model convention and arbitrary-module meaning of Tor amplitude. Its hypotheses and conclusions are the same local assertion as the imported text. In particular, no finite-type or Noetherian hypothesis on the scheme or stratum is needed or added: existence of the chosen local model is already assumed. The constant scalar ring sheaf and the completed coefficient sheaf are distinguished explicitly. The residue example is written on the stratum, with its cohomological shift unambiguous. The original import flags and blueprint metadata have been retained, and `same_as` is filled after searching.

## Source error

The blueprint says that local derived evaluation and coevaluation maps glue and that their triangle equalities hold globally because they hold locally. The latter inference is not available for arbitrary derived morphisms. For example on the ordinary topological site of the circle, a nonzero class in `Hom(Z,Z[1]) = H^1(S^1,Z)` restricts to zero on every contractible arc. Restriction detects isomorphisms and vanishing of objects, but need not detect equality of morphisms in a derived category. The statement of this item remains correct; this is a proof error, not a disputed statement.

I repaired it by constructing a single global map `K tensor D -> RHom(K,K)`, checking that this map is an isomorphism using the local finite free computation, and defining coevaluation by its inverse applied to the global identity. The first triangle is its adjunction identity. The second follows by tensor interchange and injectivity of the global adjunction bijection. Neither equality is inferred by local restriction. This is the canonical-map argument of Stacks 08JJ and 0FPU, with the triangle verification omitted in 0FPU supplied here. The two-term resolution and the unit route are unchanged. I also corrected the sign in the Hom differential: the ordinary cochain-Hom convention gives minus the transpose, isomorphic to the displayed positive-transpose model by negating degree one.

## Not duplicates

There are no new nodes, so there are no new/existing same-tag pairs requiring a distinction. Whole-DAG keyword and tag searches and `tools/blueprint_refs.py search` were used before deciding whether any auxiliary result needed a node. Searches included dualizable, local duals, free resolutions over a discrete valuation ring, derived Hom of strictly perfect complexes, Tor amplitude and 08JJ. The only equivalent local-duals blueprint statement found is this item itself; the parent integral-heart statement has additional clauses and is not an equivalent duplicate.

In particular I reused the existing Noetherian-kernel and DVR torsion-free-module Mathlib leaves, the completed-coefficient flatness node, the generic ringed-site bounded-free RHom model, the generic RHom currying/restriction node, the bounded-above-flat K-flat node and the sheaf cover-local isomorphism leaf. No node was created for the two-line construction of a length-one resolution, the support bounds for a tensor complex, or an individual clause of this item. The tempting `lem-pc-perfect-*` tools concern scheme structure sheaves/quasi-coherent objects and do not directly apply here; `prop-sf-dualizable` does not state both triangle identities under the present hypotheses. I did not treat their titles as their statements. Nor did I cite `det-lem-int-tensor-product`, whose dependency route returns through the parent and would risk circularity.

## Mathlib searches

Every search recorded in the node was actually run through the mandated `msearch.py Q01 det-lem-int-integral-heart-dualizable` command. The sandbox `searches.jsonl` preserves exact tool/query strings and results. The searches used leanfinder, loogle, grep, and leansearch, with second phrasings about local completed-coefficient modules and about bounded finite free sheaf complexes. All services returned results in this run, so none was mislabeled unavailable or absent after a failed service call. The records retain the command's UTC date, 2026-10-16, rather than substituting the local calendar date.

The results were read. Natural-language hits about BDeRham, generic t-structures, discrete valuation local rings, perfect bilinear pairings and finite sheaf presentations do not give this theorem. LightCondensed internal-Hom and module-presheaf tensor-Hom hits are underived statements, and do not give ringed-site derived duality or either Tor bound. Loogle found no `IsDualizable` or derived-category dual match in the chosen queries; the prescribed source grep searches likewise found no theorem for this statement. These observations explain the no-match verdicts; I do not claim that Mathlib lacks the individual algebra facts already carried by existing Mathlib nodes.

## Review by Q01

I performed this first-worker self-review with the item, every directly cited statement, the current blueprint proof and the relevant Stacks TeX open. This signature is my review of the split, not the later independent second reading.

For the item I compared all clauses with the main-20261015 source and unit steps 4–5: local completion of a finite module, dualizability with the derived internal Hom as dual, both specified Tor intervals, and the torsion example. No new statement needs its own source audit. For the algebra I read Stacks 00IK, `algebra.tex`, `lemma-Noetherian-basic`, and 0AUW, `more-algebra.tex`, `lemma-dedekind-torsion-free-flat`, including the PID clause. For constant/completed sheaves I read 093J, `sites-modules.tex`, `lemma-constant-exact`, and 093M, `lemma-completion-flat`. For the sheaf-derived calculations I read `sites-cohomology.tex`: 08J9 (`lemma-internal-hom`), 08JB (`lemma-restriction-RHom-to-U`), 08JI (`lemma-Rhom-complex-of-direct-summands-finite-free`), 06YQ (`lemma-bounded-flat-K-flat`), 08JJ (`lemma-dual-perfect-complex`), and 0FPU (`example-dual-derived`). The actual bounded-flat tag here is 06YQ, not the resolution-existence tag 06YS. I also checked the nearby K-flat pullback construction underlying 0G7E.

1. The coefficient lemma explicitly supplies that A is a domain and a DVR/PID. The Noetherian submodule node explicitly says a submodule of a finite module is finite; its hypotheses hold since all ideals of this PID are principal. The torsion-free/free node explicitly applies to finite torsion-free modules over a DVR. I wrote out why the presentation kernel is torsion-free, so this step does not assume a finite resolution or a structure theorem without a citation.
2. The integral-limit node explicitly identifies the completed coefficient sheaf as a limit of constant finite quotient rings. The completed-constant-sheaf node explicitly gives flatness over the constant scalar sheaf for a Noetherian A, with no finiteness hypothesis on the scheme U. The constant-module node's part (1) gives exactness on every site object, which suffices for the exact constant sheaf sequence. Thus the augmentation really is a quasi-isomorphism after completion. This is not an identification of completed and constant sheaves.
3. The size convention provides the small skeletons required by all general site tools. The exact slice-restriction statement gives exactness, not just a definition of restriction. The tensor-pullback statement gives derived monoidal compatibility for a ringed-topos morphism; I spelled out the localization adjunction using products and diagonals, with exact restriction as its module pullback. The RHom restriction statement is for arbitrary ringed sites and unbounded complexes, so it needs no perfectness assumption. The cover-local-isomorphism leaf is applied to underlying cohomology sheaves, with its covers-top condition justified by base changing the given cover. The existing Mathlib leaf `lem-weil-pbc-unbounded-derived-iso-cohomology` supplies the final implication from isomorphisms on every cohomology sheaf to a derived isomorphism; this was added explicitly during the last citation audit rather than left as implicit background. Its statement is for any abelian category and has no boundedness hypothesis. No test for equality of derived morphisms is claimed.
4. The currying statement and the degree-zero global-sections statement actually provide the two isomorphisms displayed. Their composition gives the needed Hom-set adjunction for standard sheaf RHom. The closed coefficient-category definition identifies the intended tensor and Hom; the uniqueness comparison is supplied by transposing counits, rather than silently equating different internal-Hom constructions. No theorem is taken from a definition node's proof.
5. The bounded-free RHom model has a bounded-above source and bounded-below target. Here the source has precisely two globally finite free terms on each slice, and the target R is in degree zero, so those hypotheses hold. Its differential formula yields minus the transpose. Finite free flatness is shown by finite direct sums, and the bounded-above-flat lemma then says exactly that these complexes are K-flat. There is no appeal to an underived module dual for a torsion module.
6. The derived-tensor definition permits a K-flat argument to compute tensor. The two displayed complexes then have the claimed term supports, so the cohomology assertion is immediate from kernels and images. I used exact restriction, tensor compatibility, and the sheaf-local isomorphism test only for vanishing. The Tor-amplitude definition explicitly quantifies over every module sheaf; the proof leaves G unrestricted.
7. The bounded-free Hom model is applied a second time with target K_U itself, a degree-zero sheaf. It therefore does not need an unbounded-target strengthening of that model. The two complexes have terms K_U^b and K_U^a and exactly the same differential. The canonical map is identified by its evaluation formula on a basis, which checks it is an actual isomorphism of complexes. The canonical global map and its restriction are compared by the adjunction, and the cover test then applies to isomorphisms. I did not cite the scheme/quasi-coherent version of perfect duality.
8. The first triangle is the transpose of alpha composed with eta; naturality makes the displayed composite its transpose. Since alpha eta equals u by its global definition, the first triangle follows from the bijection of the stated adjunction. This is a short formal calculation, with no hidden descent theorem.
9. I expanded the second triangle before comparing it. Both evaluations after inserting eta give the same e tensor e by interchange. The first triangle reduces this to e; the global Hom adjunction is injective, so the second endomorphism is the identity. This supplies the detail that Stacks 0FPU explicitly omits, instead of creating a node that merely restates dualizability.
10. The coefficient-resolution node explicitly states exactness for every scheme and every n at least one, so S and n=1 are permitted. The bounded-free Hom node gives the signed dual differential. Injectivity follows from that exact sequence, and the quotient chain map gives cohomology only in degree one. Thus the dual is the quotient sheaf shifted by minus one, not the quotient sheaf in degree zero.

I tested N=0, finite free N, N=A/pi, N=A/pi^r, and sums of a free and a torsion module. The zero module allows a=b=0. A free module has dual in degree zero, which lies in both asserted intervals. The torsion examples have zero underived Hom to A and their derived dual cohomology in degree one; this confirms the shift and prevents replacing RHom by ordinary Hom. Tensoring A/pi with a pi-torsion test module produces both degree -1 and degree 0, so the left Tor interval cannot be collapsed to degree zero. The empty stratum causes no problem: all module sheaves and maps in its topos are the unique zero objects, and the amplitude and duality assertions are vacuous. Ranks may vary between charts; no globally fixed ranks or global free resolution are assumed.

Against B–E, the outcome is concrete: there are no new nodes to contain unsupported proof sketches, duplicate statements or fabricated search records (B, D1–2). The expanded statement introduces its objects and definitions and uses singly escaped TeX (B2–4). The quoted Stacks tags were checked against the local labels (B5), and no new Mathlib match is asserted (B6,8). Every cited statement was opened, and its exact text is in citations.json; no citation takes a fact from another node's proof (C1,3,4). Formal steps marked elementary contain the displayed adjunction, tensor or term-support calculations (C2). A read-only dependency traversal found no route from the proposed direct proof tools back to this item (C6). Off-unit generic tools are justified individually in `split_report.tool_uses`; they implement the unit's two-term-resolution route (C7–8). Hypotheses and coefficient categories were checked as described above, and the source's local-equality shortcut and Hom-sign issue were repaired (E1–6). The source error is reported explicitly rather than reproduced (E7).

## Unfinished work and delivery

No mathematical part of this one-level split is left unfinished. The existing dependencies retain their own statuses; this delivery does not claim to prove or split them. The independent second reader must still read the accepted sandbox and make the actual delivery. The first no-push run passed preflight at 5ac0491da6. The final citation audit then added the existing cohomology-isomorphism criterion explicitly in step 3, with its quotation, and the required no-push check is repeated for that final version. This worker does not push.

## Repair after landing return

The landing return identified a stale path `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-site-perfect-evaluation-iso.json` in the prior delivery history. I compared the sandbox against the current `origin/newtargets-dag`; that path is absent from the current DAG. I repaired the split rather than re-pushing unchanged content: step 7 now cites the live node `lem-pc-finite-projective-internal-hom-evaluation`, whose statement gives the finite-projective tensor-dual evaluation isomorphism used there. I added its proof dependency, declared the generic cross-unit tool use in `split_report.tool_uses`, and added the verbatim statement quote to `citations.json`. The step text now names this lemma as the source of the degreewise evaluation isomorphisms. The current node statements and all other cited dependencies were reread against the current DAG; no stale node id remains.

## Earlier second reading (a previous round; superseded)

Item statement: compared every coefficient, local-model, dualizability, Tor-amplitude, and residue-shift clause with the current main-20261015 blueprint statement and proof, the parent unit, and the cited definition nodes; verdict faithful and self-contained. Checked zero and finite-free modules, $A/\pi_E^r$, $N=0$, rank-zero resolutions, the field case, and the empty stratum; all edge cases are permitted and the stated intervals and shift remain correct.

Step 1: checked the DVR/PID and Noetherian hypotheses, finite presentation kernel, torsion-free kernel argument, and finite torsion-free DVR-module theorem against the three cited algebra statements; verdict every used fact is stated and the two-term resolution is constructed rather than assumed.

Step 2: checked the completed coefficient limit, flatness over the constant sheaf, exact constant-module sequence, and augmentation after tensoring against the three cited coefficient/sheaf statements; verdict the completed and constant coefficient sheaves are kept distinct and the quasi-isomorphism follows under the stated hypotheses.

Step 3: checked size conventions, exact slice restriction, derived tensor pullback, internal-Hom restriction, cover-local sheaf isomorphism, and the unbounded cohomology criterion against all six cited nodes; verdict local calculations are used only to detect isomorphisms or vanishing, with no unsupported equality-of-morphisms descent.

Step 4: checked the currying and global-sections identifications, the closed derived tensor-Hom adjunction, and the transposed-counit comparison against the three cited statements; verdict the chosen standard sheaf RHom is identified with the coefficient-category internal Hom and evaluation is globally defined.

Step 5: checked the bounded-free RHom hypotheses, degree ranges, signed transpose differential, finite-free flatness, and K-flat conclusion against the bounded-free RHom and bounded-flat K-flat statements; verdict both local complexes satisfy the exact hypotheses and the sign convention is explicitly reconciled.

Step 6: checked arbitrary module-sheaf quantification, K-flat tensor computation, term support, restriction compatibility, and local vanishing detection against the tensor-Hom definition, constructibility definition, restriction/tensor nodes, and cover-local node; verdict the two Tor intervals are proved without finiteness or flatness assumptions on the test sheaf.

Step 7: checked the canonical comparison map, its basis evaluation formula, the second bounded-target RHom application, and global isomorphism detection against the cited RHom model, tensor-Hom definition, restriction node, and cover-local node; verdict this supplies one global isomorphism and avoids gluing locally chosen maps.

Step 8: checked the transpose definition of coevaluation, adjunction naturality, and the first triangle identity against the closed-structure definition; verdict the calculation is formal from the global comparison inverse and uses no local equality inference.

Step 9: checked tensor interchange, both evaluation composites, and injectivity of the global adjunction bijection against the same closed-structure statement; verdict the second triangle is explicitly calculated rather than delegated to the source's omitted argument.

Step 10: checked the $n=1$ coefficient resolution, signed Hom complex, injectivity, quotient cohomology, and cohomological shift against the Nakayama-resolution and bounded-free RHom statements; verdict the residue dual is $(\mathcal O_{E,S}/\pi_E)[-1]$ with the correct degree-one cohomology.

New nodes: none. Therefore B1--B7 and new-node Mathlib/duplicate audits are vacuous; the item’s recorded searches and all 31 citation quotations were checked against the current search log and node statements, including the repaired finite-projective evaluation citation, and no new Mathlib leaf or duplicate was introduced.

Changes made in this second reading: step 7 was repaired as described above after the landing return. The source-error discussion correctly records and repairs the blueprint’s invalid local equality-of-morphisms shortcut and the Hom-differential sign issue. The required dry run is being rerun against the current DAG after this repair.


## Current repair review by Q01 (2026-10-17)

The retained sandbox already contained an earlier repair of the returned stale dependency. I reread every current direct statement and verified the 31 original quotations before changing it further. In particular the replacement finite-projective internal-Hom evaluation statement assumes additive-group sheafification and a characterization of local equivalences. Step 7 only needs globally finite free terms, so I removed that unnecessary general tool citation and wrote its basis map and explicit inverse directly: h maps to the finite sum of h(e_j) tensor e_j^*. Both composites are identities, the formulas commute with sheaf restriction, and precomposition with the presentation matrix gives the same signed differential on the two complexes. This is an elementary calculation, including rank zero, rather than a new lemma or a change of proof route. The final citations.json therefore has 30 entries and no citation of either the stale perfect-evaluation node or the general finite-projective evaluation node.

Against the present DAG, the algebra statements still supply DVR/PID, finite kernel, and finite torsion-free freeness (step 1); the coefficient statements still supply the completed limit, flatness and constant-sheaf exactness (step 2). Exact restriction, tensor pullback, RHom restriction, small universes and the cohomology/sheaf isomorphism tests still have the hypotheses used in step 3. The currying and global-sections statements still give the actual Hom adjunction of step 4. The bounded-free RHom model still applies to both degree-zero targets R and K (steps 5 and 7), and bounded-above-flat K-flatness still justifies the tensor calculations (steps 5–6). The arbitrary-module quantifier in Tor amplitude is retained. Steps 8–9 use the global adjunction and interchange, with no inference of equality from local restrictions. The coefficient exact sequence still applies with n=1 on S (step 10), giving degree-one dual cohomology and the shift [-1].

I reread Stacks sites-cohomology.tex at lemma-internal-hom (08J9), lemma-restriction-RHom-to-U (08JB), lemma-Rhom-complex-of-direct-summands-finite-free (08JI), lemma-bounded-flat-K-flat (06YQ), lemma-dual-perfect-complex (08JJ), and example-dual-derived (0FPU), including the explicit omission of triangle verifications in the latter. The current blueprint proof has the same two-term resolution route and the same local-equality shortcut already repaired by the global-map argument. The correction introduces no new node, Mathlib leaf, coefficient identification, or scheme hypothesis. The cases N=0, finite free N, N=A/pi^r, varying chart ranks and the empty stratum remain valid.

The required delivery tool constructs its temporary worktree from the refreshed origin/newtargets-dag, so the no-push check rebases the proposed node onto the current DAG without a manual shared-repository operation. No Lean compiler or Lake command is run. The preceding historical review sections describe earlier retained versions; this section records the final repair and its 30 citations.

## Second reading by Q01

Item statement: checked against the current main-20261015 blueprint node and proof, the parent unit, and the definition nodes named in `stmt_deps`; verdict faithful, self-contained, and unchanged in hypotheses and conclusions. The coefficient limit, local completed finite-module model, dualizability, both Tor intervals, and residue shift were tested on the zero module, a finite free module, a field, $A/\pi_E^r$, and the empty stratum.

Step 1: checked the DVR/PID, Noetherian kernel, torsion-free kernel, and finite free resolution claims against the three cited algebra statements; verdict each dependency states the needed fact and the resolution is constructed in the step.

Step 2: checked the completed limit, flatness, exact constant-module sequence, and augmentation against the three cited coefficient/sheaf statements; verdict the constant and completed sheaves remain distinct and the hypotheses apply.

Step 3: checked size, exact slice restriction, derived tensor pullback, internal-Hom restriction, cover-local isomorphism, and the unbounded cohomology criterion against every cited statement; verdict only isomorphisms and vanishing are detected locally, with no unsupported equality-of-morphisms claim.

Step 4: checked the currying, global-sections, and closed derived tensor-Hom adjunction statements; verdict the standard sheaf RHom adjunction and its evaluation are identified by transposed counits.

Step 5: checked the bounded-free RHom hypotheses, Hom differential sign, finite-free flatness, and K-flat conclusion against the two cited nodes; verdict both displayed complexes satisfy the stated degree and finiteness hypotheses.

Step 6: checked arbitrary module-sheaf quantification, K-flat tensor computation, term supports, restriction, and local vanishing against the cited definition and site nodes; verdict the exact intervals follow without assumptions on the test sheaf.

Step 7: checked the second bounded-free RHom calculation, basis evaluation and inverse (including rank zero), differential compatibility, and global isomorphism test against the cited nodes; verdict the canonical comparison is globally defined and locally an isomorphism.

Step 8: checked the coevaluation definition and first triangle by the global adjunction bijection; verdict the triangle follows from the transpose of $\alpha\eta=u$, without local equality inference.

Step 9: checked the expanded tensor-interchange calculation and injectivity of the global adjunction; verdict the second triangle is proved explicitly and does not rely on the omitted source argument.

Step 10: checked the $n=1$ coefficient resolution, signed Hom complex, injectivity, quotient cohomology, and shift against the cited resolution and RHom model; verdict the residue dual is exactly $(\mathcal O_{E,S}/\pi_E)[-1]$.

New nodes: none; therefore B1--B7 and duplicate/Mathlib-leaf checks are vacuous. All 30 citation quotations were reread against the current DAG statements, and the recorded Mathlib searches were checked in `searches.jsonl`; no stale evaluation citation remains.

Changes made in this second reading: no mathematical node or proof step required repair. I added this independent audit section because the prior report contained historical review headings but lacked the required exact `## Second reading by Q01` heading.
