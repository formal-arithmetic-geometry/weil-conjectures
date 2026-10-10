# lemma-weil-pbc-etale-degree-zero

## Files written

- `dag/nodes/sec-proper-base-change/lemma-weil-pbc-etale-degree-zero.json`: three-step split following Stacks Tags 0A0B, 09ZF and 0A0C. No new node is delivered.

## Attachments

No exact attachment for the full abelian-sheaf statement. `AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_of_henselianRing` at `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/SixFunctors/Etale/BaseChangeTheorems/DegreeZero.lean:84-94` states the comparison only for sheaves of modules over a fixed commutative ring `Λ`. It is a narrower specialization of this item, and its own proof is `sorry`; it cannot close the item.

## WANTED

None. The relevant Stacks source is `/home/ubuntu/weil-conjectures-sheaf-F2/literature/stacks-project/etale-cohomology.tex`: Tag 09ZF, label `lemma-gabber-h0`, lines 14974-15070; Tag 0A0B, label `lemma-zariski-h0-proper-over-henselian-pair`, lines 18167-18200; Tag 0A0C, label `lemma-h0-proper-over-henselian-pair`, lines 18202-18211.

## Corrections and proof route

The imported proof used `lemma-weil-pbc-spectral-restriction`, whose statement covers only locally constant Zariski sheaves, and then asserted the comparison for arbitrary sheaves without supplying the missing argument. It also used closures of opens in a finite refinement in place of the actual Tag 09ZF descent. Stacks 0A0C instead applies Tag 0A0B, which gives the full Zariski comparison for every sheaf of sets, on the proper scheme and on all its finite covers, then applies Tag 09ZF.

Step 1 forms the closed fibre and checks that the proper scheme is quasi-compact and quasi-separated. A finite morphism over it is proper over `Spec A`; the 0A0B node therefore supplies both Zariski hypotheses of 09ZF. Step 2 applies `lem-weil-pbc-gabber-h0-etale-criterion` to the closed immersion and takes the abelian specialization of its set-valued conclusion. Step 3 records naturality of canonical restriction and its cartesian finite-pullback equation. The generic 0A0B and finite-proper statements are in `tool_uses`; their statements were read and supply exactly the claims used.

The cited 09ZF criterion was created by the now-landed `lemma-weil-pbc-proper-strict-henselian-h0` delivery. Its statement matches Tag 09ZF hypothesis by hypothesis (qcqs scheme, closed immersion, every Zariski sheaf on the scheme and on each finite cover, conclusion for every etale sheaf of sets). I compared it with the duplicate I initially created, deleted my duplicate, and searched the whole blueprint with `tools/blueprint_refs.py search` for `09ZF`, `Gabber H0` and `Zariski etale sections`; none states that criterion. This commit is rebased onto the tip containing the shared node.

Edge cases: if the closed fibre is empty while the proper scheme is nonempty, the all-sheaves hypothesis of 09ZF fails for a sheaf supported on the scheme. If both are empty the restriction is the unique map between singleton section sets. The statement keeps the original naturality and finite-pullback clauses and makes `Y_0`, `i`, and the inverse-image map explicit.

## Checks

- The two 09ZF criterion statements and Stacks Tag 09ZF were read side by side.
- `python3 tools/blueprint_refs.py check lemma-weil-pbc-etale-degree-zero`: 0 errors after rebase.
- `python3 tools/check_dag.py --cycles`: 0 cycles; 15 reach and 11 route warnings outside this item remain on the rebased tree.
- `python3 tools/review_split.py lemma-weil-pbc-etale-degree-zero`: PASS after rebase onto the shared criterion node.

## Unfinished

No Lean was written or built. This split is ready for lead review.

## Review by E1

I read Stacks Etale Cohomology 0A0B, 09ZF and 0A0C at their labelled lemmas. The item assumes a henselian pair and a proper scheme, as in 0A0C, and restricts the source's set-valued conclusion to abelian sheaves. Its new proof does not need the imported locally-constant-sheaf shortcut. The landed lem-weil-pbc-gabber-h0-etale-criterion states the exact 09ZF qcqs, closed-immersion, and all-finite-cover Zariski hypotheses and its set-valued conclusion; I checked it against the source and against the item's use. No new node remains in this delivery, and whole-DAG and blueprint searches found no duplicate to create.

Step 1 uses the cited closed-immersion base-change statement, properness of a finite composite, and the 0A0B Zariski comparison on Y and every finite Y'. Proper over an affine base supplies qcqs, and the fibre-product identity identifies each finite cover's closed fibre with its base change. These are precisely 09ZF's hypotheses. Step 2 applies the landed criterion; bijectivity on underlying sets of an abelian sheaf gives an isomorphism of groups because the restriction is a homomorphism. Step 3 uses functoriality of inverse image and the cited finite-pullback identity for the canonical restrictions; no noncanonical inverse is chosen. The empty-fibre case is covered by 0A0B's all-sheaves hypothesis, so no hidden nonemptiness assumption enters. The read-only Lean theorem is only a Lambda-module-sheaf specialization and directly has sorry, so it does not close this all-abelian-sheaf node. The worker removed a duplicate 09ZF node and corrected that attachment wording before this review; I found no remaining A-E defect.
