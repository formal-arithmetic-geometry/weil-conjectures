# Stage-1 report: Q98

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-signed-projection-resolution-normalization.json`: item, statement; split into eight proof steps. No Mathlib match for the full normalized resolution statement.
- `citations.json`: one entry for each of the 18 step/node citations, with a verbatim statement from the cited live node.
- `searches.jsonl`: the search command's actual log, retained without alteration.

No new nodes and no new Mathlib leaves. `write_split.py` is sandbox-only scratch code, not a delivery file.

## Attachments

None. Searched the project under `lean/WeilConjectures/` for the blueprint tag, signed totalization, projection normalization, and the model names. No declaration there states every clause of the item. `lean/Sheaf/Paper/PerfectProjectionFormula.lean` has `Resolution.sourceModel`, `Resolution.targetModel`, and `totalization_compatibility`, which were read as the expanded source calculation. This is not an upstream project attachment covering the whole item with arbitrary coefficient object P; the stage-1 split remains necessary. The mixed representative lemma is already an existing node and is reused.

## WANTED

None.

## Findings and changes

The item was genuinely unsplit: the sandbox contained no node, report, citations, or searches. Copied the current live item, preserved its statement and inherited searches, and supplied the proof. No statement dispute arose and no hypothesis or conclusion changed. Added the existing fixed-tensor localization comparison to statement dependencies to make the specified normalization of the mixed comparisons explicit.

The main reusable input is `lem-weil-pbc-proetale-mixed-projection-mate`, whose statement gives an equality for all flat-term K-flat coefficient complexes, without the bounded splitting assumption. It is not merely an isomorphism assertion and it identifies the canonical counit mate. Its use avoids both reproducing its nontrivial representative calculation and creating a duplicate. The bounded split-perfect K-injective tensor lemma supplies the target resolution property independently. A dependency traversal found no path from these inputs back to this item.

The proof follows the second and third paragraphs of the main-20261015 perfect-projection proof: signed totalization, then independence of the package. It stays within the proper-base-change unit. The bounded-above flat criterion, filed in the Picard unit, is used only as the generic K-flat tool; `split_report.tool_uses` explains this. No unit or chapter file was changed.

The logged Mathlib searches used LeanFinder twice with distinct formulations, Loogle, LeanSearch, and two source grep patterns. All services returned successfully. Hits include general projective-resolution maps, Tor naturality, and abstract derived-counit factorization; none states the specified module-sheaf mixed tensor comparison and finite-retract inverse. The counit factorization source was read in `Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean`, lines 114–130, in particular `derivedε_fac_app` at 125. These results do not make the item a one-line Mathlib specialization. Existing inherited search records were retained and are distinguished from this session's six logged queries.

## Not duplicates

No new node was created. Searched the whole DAG and whole blueprint for projection formula, signed totalization, mixed representatives, and K-injective tensor facts, and reused existing nodes. The totalization inverse node states the two inverse identities, but not the specified arbitrary-resolution normalization; it was not used to replace the present argument. The mixed-mate node supplies a genuinely more general coefficient hypothesis for one intermediate normalization equation, not the entire item.

## Review by Q98

I read the current main-20261015 blueprint proof of `lemma-weil-pbc-perfect-projection-formula`, especially its second and third paragraphs, and its expanded calculation in `lean/Sheaf/Paper/PerfectProjectionFormula.lean` around sourceModel, targetModel, transport_projection, and totalization_compatibility. I read Stacks `sites-cohomology.tex`, Tag 0B56 (`equation-projection-formula-map`) and Tag 0944 (`lemma-projection-formula`): the forward map is the adjunct of counit tensor identity, not an arbitrarily chosen isomorphism. I also read the actual mixed-mate statement and its signature in `ProEtaleMixedProjectionMate.lean`, and the mixed-comparison resolution square in `ProEtaleProjectionFormulaArrows.lean`. No SGA source is used. There are no new-node sources to audit.

For step 1 I opened all four cited node statements. The package really supplies a retract of a finite free sheaf in every degree, and flatness means exactness of the tensor functor. I wrote out why its tensor sequence is an exact retract of a finite sum. The bounded-above criterion applies because F is bounded; the ringed-topoi tensor lemma explicitly preserves both flat terms and K-flatness under pullback. I checked the Stacks bounded-flat lemma (`lemma-bounded-flat-K-flat`, Tag 06YQ) rather than relying on the stale 06YS label in the existing criterion's source field. This delivery does not edit that other node.

For step 2 I checked the operations node gives exact module pullback for the supplied coefficient isomorphism. Thus it preserves zero terms and the finite-free splitting, with the same finite bounds. The split-perfect tensor K-injective node explicitly allows unbounded I and nonzero coefficient differential; its differential convention is exactly the one in the item. The K-injective total-derived node explicitly says the comparison is an isomorphism on every K-injective, so it applies separately to I and J. I read the supporting Stacks K-injective computation/existence statements in `derived.tex`, labels `lemma-K-injective-defined` and `lemma-enough-K-injectives-implies`, and the tensor-Hom K-injective statement in `sites-cohomology.tex`, label `lemma-RHom-from-K-flat-into-K-injective`. No termwise injectivity of I is assumed.

For step 3 I opened the fixed-tensor exactness and fixed-tensor localization node statements. They provide computation with an arbitrary varying first factor and the precise resolution formula, respectively. This is why it is legitimate to tensor f_*I without assuming it K-flat. I verified the mixed-comparison formula has the inverse of c, since c points from the ordinary representative to derived tensor. The operations node supplies exact pullback and its localization comparison. Every factor of S and T is consequently invertible, in the displayed directions.

For step 4 I checked that the module pullback tensor node states simultaneous naturality, the termwise adjunction node explicitly supplies natural counits and the adjunction, and the right-adjoint limits node gives finite products. In an additive module category these are the finite biproducts used here. I explained the unit coefficient case by the triangle identity and the free case by its standard summands, rather than taking an unrelated finite-sum isomorphism to be the specified mate. This step is elementary relative to the cited inputs.

For step 5 I reread the actual arrows definition to check the direction and order of p, q, and i. The written equations use naturality with i for st and with p for ts. In particular they do not require the degreewise splittings to commute with d_F. I opened the tensor-complex definition and checked its (-1)^a convention; naturality of an inverse with d_F preserves a, and with d_I has no sign. The finite biproduct preservation needed for f_* of the total is explicitly cited. These are componentwise calculations, not a concealed totalization theorem.

For step 6 I verified that the mixed-mate node states exactly the used equation, including the right-derived unit at J even when J is not assumed K-injective by that lemma. Here step 2 proves it is invertible, so cancellation is valid. I wrote the equation and both comparison directions explicitly. I did not take any unmentioned result from the proof of that node.

For step 7 the ringed projection mate node explicitly says the structures are natural in both arguments. The formula with a and b is that naturality square. Tensor bifunctoriality then gives S=ua and T=vb; this handles arbitrary derived isomorphisms alpha and beta, not merely quasi-isomorphisms represented by selected chain maps. For step 8, the two compositions follow directly by functoriality from the chain identities already proved in step 5; the final equality of inverses is written out.

I checked delivery-errors B through E: all used notions have existing definitions; there are no new statement-only nodes or unverifiable Mathlib leaves; the JSON uses single TeX escapes after decoding; every step/node citation has a literal quote; no cited node is used for a clause outside its statement; non-elementary tensor, K-injective, and mate-comparison inputs are all cited; the finite-retract, sign, and conjugation arguments are written out rather than hidden behind “transport.” All eight steps are below 2000 characters. Edge checks included N=0, F=0, a single coefficient degree, nontrivial d_F with splittings that are not chain maps, f the identity, and I unbounded in both directions. Bounds only enter to make each total diagonal finite; the target K is never required bounded. There was no mathematical correction to the imported statement.

## Unfinished work

None in this stage-1 item. No Lean was written and no compiler, Lake command, or local DAG preflight was run. The required remote dry run and direct delivery are the remaining operational checks.
