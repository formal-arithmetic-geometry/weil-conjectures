# Q56 stage-1 delivery

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-geonormal-divisorial-scalar-comparison.json`: item, statement, split in eight steps; no exact Mathlib match.
- `citations.json`: 25 step/node citations, each quoting the cited statement literally.
- `searches.jsonl`: five fresh searches of the item, with actual results; earlier searches in the live node are retained.
- `report.md`: this report.

## New nodes

None. Existing nodes supply every non-elementary ingredient. In particular this delivery reuses the general flat finite-presentation Hom theorem, the fractional-lattice theorem, and the one-equation dimension leaf rather than creating specializations of them.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id and for reflexive, divisorial, geometric normality and dual/base-change terminology. The reflexivity results found concern linear algebra or Verdier duality, and the Picard dual-pullback result concerns invertible Cartier ideals. None states every clause of this item. The upstream declaration evidence does not finish this item.

## Wanted sources

None. All ingredients used were read in the local Stacks sources. No SGA source is used.

## Corrections and scope

The statement is retained, including arbitrary field extension, canonical evaluation compatibility, all signed divisor coefficients and compatibility with the embedded rational functions. There was no existing proof in the item. The source's proposed codimension-discarding route is not used as an unexplained fact: the proof writes the height-one calculation directly using the extended prime ideal and the local one-equation theorem. This is a proof-level choice below the fixed unit route, with the same divisorial construction.

The inherited `blueprint.from.node` is null: the mandated ancestor command reports `None` for this historical chain. Its already specific `from.place` and `via` are preserved. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, in particular paragraph (3); it now assembles open and proper images and does not state this historical Picard tool. Blueprint searches for reflexive/divisorial terms find no matching blueprint proposition, so `same_as` remains empty. The fixed chapter and unit were read; this item does not replace a unit step. Off-unit inputs are declared in `split_report.tool_uses` as generic algebra and coherent-sheaf tools.

## Not duplicates

No new node is proposed, so there are no new/existing pairs. The DAG search found `lem-per-divisorial-fractional-module-lattices` (0EBM/0AVB), `lem-weil-pbc-flat-base-change-hom-finitely-presented` (087R), `lem-sfb-coherent-reflexive-hull`, and the existing dimension leaf; they are cited instead of duplicated. The other 00P3 nodes are dimension results, not used as unsupported assertions of codimension preservation.

## Review by Q56

I read delivery-errors B through E in full and checked the actual statements of all cited nodes, rather than their titles or proofs. The sources for the item are divisors.tex, the construction in `lemma-normal-class-group` (0EBM) and the reflexive tensor lemma (0EBL); more-algebra.tex, `lemma-pseudo-coherence-and-base-change-ext` (087R) and `lemma-reflexive-over-normal` (0AVB); and algebra.tex, `lemma-one-equation` (00KW) and Noetherian permanence (00FN). There are no new nodes requiring separate source checks.

Step 1 uses exactly Noetherianity of finite-type algebras, faithful flatness of field tensors, the definition of geometric integrality, coherent = quasi-coherent finite type, and finite affine sections. The field is Noetherian because its only ideals are zero and the unit ideal; the localization argument for Noetherianity and the denominator-ideal argument for normality are written out. I did not confuse a Noetherian topological spectrum with a Noetherian ring: `lem-sfb-finite-type-noetherian-spectrum` is not used.

Step 2 uses the explicit flat Hom-comparison map in the 087R node, with target module A. The affine modules are finite over Noetherian A, so that node explicitly supplies the finite-presentation hypothesis. Its localization specialization also supplies the identification with the sheaf Hom kernel. The finite-kernel node proves that the dual is finite; the sheaf Hom definition identifies the transposed presentation kernel, and tensor pullback supplies the base-changed presentation. The map on pure tensors is stated, fixing which canonical comparison is proved invertible. The Mathlib search hit `IsBaseChange.toDualBaseChange` was read in `Mathlib/LinearAlgebra/Dual/BaseChange.lean`: it assumes finite freeness. It therefore does not settle this item for arbitrary coherent modules. Normalization and fractional ideal extension search hits do not settle the sheaf comparison either.

Step 3 applies Step 2 to the coherent dual, not to an unjustified new object. The inverse of the dual of theta has the correct variance in the double-dual comparison. The evaluation pairing is computed explicitly. Finite generators and the tensor balancing formula prove coherence and monoidality; generic tensoring with Frac B proves rank preservation. The divisorial-open node explicitly states closure of the reflexive rank-one tensor product on a normal scheme, which is all this step takes from it.

Step 4 uses flat tensor exactness to identify the actual extended ideal and quotient. Geometric integrality of the given reduced Z_i means that the scalar quotient is a domain, not just that its support is irreducible. Contraction equals the original ideal by injectivity over the field, so distinct divisors remain distinct. Affines missing a divisor have the unit ideal and are treated separately.

Step 5 uses the DVR assertion in the fractional-lattice node for the original height-one prime. At the extended prime, its entire maximal ideal is generated by the image of the original uniformizer, because the prime is the extended ideal. The quotient is a field. The localization dimension/chains node supplies the height interpretation; applying the full-height principal quotient leaf to the local ring is legitimate because its maximal ideal has full height, and the uniformizer is a nonzero element in a domain. Thus the dimension is one and the valuation multiplicity is one. This avoids using topological dimension at a point as though it were local-ring dimension, and avoids silently assuming that field extensions have zero-dimensional fibres.

Step 6 uses the concrete lattice node's intersection and localization formulas, including the sign I(H) = O(-H). Those formulas prove I([p]) = p, and the tensor ideal equality from Step 4 proves the negative-prime comparison inside the function field. This step does not import a flat-pullback claim from a node that only defines reflexivity.

Step 7 checks the positive sign by identifying dual maps with multiplication by a rational function. The lattice intersection formula proves the inequalities with the opposite sign. The normal-divisorial node states the tensor-addition isomorphism; the displayed height-one computation, the flat Hom theorem for localization, and the reflexive-hull node prove that the isomorphism used here is the one induced by rational multiplication. Repeated signed tensor products then handle all integers, including negative coefficients, without a positivity assumption.

Step 8 checks the canonical formula b tensor f maps to b p(f), and uses the lattice localization and divisorial restriction statements exactly as written. It is elementary assembly of the constructed maps. In particular the proof does not assert the false equality E tensor_F k(Y) = k(Y_E) for transcendental extensions. For example, if Y is the affine line and E = F(t), then 1/(x-t) need not belong to E tensor_F F(x); only the natural inclusion and multiplication map are needed.

Small cases checked: identity extension E = F; transcendental and inseparable extensions (only field flatness and geometric hypotheses are used); M = 0; M torsion (the dual-kernel computation still applies); dimension-zero Y (no prime divisors); an empty list of divisors; zero coefficients and cancellation of opposite coefficients; negative coefficients; affines disjoint from a chosen divisor. A geometrically nonintegral divisor may split or become nonreduced after extension, explaining why the stated geometric integrality hypothesis cannot be omitted. No source or statement dispute was found.

No proof step exceeds 2000 characters; the longest is 1319. The short computations implement this item's comparison rather than packaging its clauses as new nodes. Statement dependencies include the tensor definition used by its reflexive tensor clause. Each non-elementary step names its needed theorem nodes, and `proof_deps` is the exact union of `uses`.

## Unfinished work

None in the requested one-level split. The dependencies retain their own existing statuses. This delivery makes no Lean changes and runs no compiler or Lake command.
