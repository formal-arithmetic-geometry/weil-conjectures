# Stage 1 report: lem-per-etale-closed-sheaf-internal-adjunction

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-etale-closed-sheaf-internal-adjunction.json`: item split into seven proof steps; no new DAG nodes.
- `citations.json`: verbatim quotations for every cited node at every step.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, its blueprint tag, and the support/internal-Hom terminology; no sorry-free project declaration states this item exactly.

## WANTED

None. The Stacks etale-cohomology source, sites/modules source, the ILO PDF, and all cited DAG nodes are present locally.

## What was wrong or incomplete in the imported item

The imported node had an empty proof and no proof dependencies. Its statement is retained. The existing abelian-sheaf support node is strictly narrower: it has abelian sheaves and ordinary Hom bijections, while this item requires arbitrary constant-ring module sheaves, preservation of module injectives, and a sheaf-valued internal Hom isomorphism. I therefore lifted that support adjunction using scalar-linearity and wrote the slice-site construction explicitly. I did not create a duplicate node for the abelian result or for the already existing ringed closed-kernel adjunction, because those statements are already in the DAG and the present item follows the small étale constant-ring route.

## Review by Q23

I read the item, its chapter and unit records, the imported blueprint ancestry, and the source passages in Stacks Tags 09XP/09XQ and 04CA. I also read every statement quoted in `citations.json`. Step 1 uses the exactness and faithful underlying functor for module sheaves, exact constant-ring inverse image, sectionwise direct image, and the existing abelian supported-kernel adjunction; these statements give the kernel, its canonical unit, and exactness of closed pushforward. Step 2 uses the existing abelian transpose and closed full faithfulness, then checks scalar-linearity locally from the constant-sheaf definition, so it really proves the module adjunction. Step 3 applies the injective extension criterion directly and verifies that the monomorphism remains a monomorphism under exact closed pushforward. Step 4 checks the hypotheses after every étale base change: the pulled-back closed immersion and complementary open immersion exist, and the site restriction and direct-image formulas are sectionwise. Step 5 defines the slice comparison by the two canonical supported-kernel units and normalizes it by the support counit, so it does not assume an unstated inverse-image base-change theorem. Step 6 applies the definition of internal sheaf Hom to the slice map sets and gives both inverse formulas. Step 7 checks restriction along arrows, naturality in both sheaves, and module linearity of the inverse and hence the forward map. I tested the statement conceptually on $Z=\varnothing$, $Z=X$, $A=0$, and a strictly henselian DVR with $F=A_X$; the kernel and Hom formulas reduce as expected. I searched the whole DAG for the Stacks tags and support/internal-Hom keywords, and checked the existing abelian support node and the generic ringed closed-kernel node for overlap. Mathlib searches were run through `msearch.py` for LeanFinder, LeanSearch, Loogle, and grep; the hits were generic module pullback/direct-image adjunctions, structure-sheaf kernels, or monoidal closed constructions and did not state this closed-support result. The server-side `check_dag` preflight passed with no finding introduced by this sandbox.

## Not duplicates

- `lem-per-etale-closed-sheaf-internal-adjunction` vs `lem-pur-etale-supported-kernel-adjunction`: the latter is for abelian sheaves and ordinary Hom bijections; this item adds arbitrary constant-ring modules, module injectives, and internal sheaf Hom.
- `lem-per-etale-closed-sheaf-internal-adjunction` vs `lem-sf-ringed-closed-kernel-adjoint`: the latter is on small pro-étale sites and gives an ordinary module adjunction/derived endpoint; this item is on small étale sites and includes the slice-local internal Hom formula.
- `lem-per-etale-closed-sheaf-internal-adjunction` vs `def-pur-sheaf-hom`: the latter defines sheaf Hom; it does not state a closed-immersion adjunction or support kernel.
