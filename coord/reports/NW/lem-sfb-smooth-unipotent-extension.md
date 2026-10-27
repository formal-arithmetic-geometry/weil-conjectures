# lem-sfb-smooth-unipotent-extension — NW, stage 1

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-unipotent-extension.json`: item, statement unchanged, split into seven proof steps; not a Mathlib leaf.
- `citations.json`: nine entries, one for every step/node citation, with verbatim statement excerpts.

No new nodes and no Mathlib leaves. The sandbox also contains `searches.jsonl`, the local extracted source `milne.txt`, and `write_split.py` used to assemble the JSON; these are research artifacts, not DAG deliveries.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag, the item identifier, unipotence, and faithful representation terminology. The hits do not prove this algebraic-group statement. In particular categorical biproduct unipotent matrices and lisse representations are not attachments.

## WANTED

None. All source material needed for this split is present in Milne, *Algebraic Groups*, `literature/milne-algebraic-groups_iAG2017.pdf`.

## What needed correction

The item had a statement and searches but no proof. I retained its statement, statement dependencies, creation data and inherited blueprint ancestry. Its source had referred readers to section 14(c), pp.286–287, for the matrix interpretation; the directly applicable equivalences are actually Proposition 14.3, Theorem 14.5 and Corollary 14.12, pp.280–283. I corrected that location in the source field. This is a source-location correction, not a statement dispute.

Milne's definition in 6.45 is the rational fixed-vector condition, whereas the item uses geometric unipotent matrices in a faithful closed representation. Merely copying the short paragraph in 6.45 would have left both implications between these formulations implicit. Step 1 supplies the conversion for the hypotheses using an existing node; steps 5–7 construct the required faithful unipotent representation for the conclusion.

The ordinary pointwise fixed-vector node only promises fixedness under rational points. I instead use the stronger existing unitriangular-subgroup node, whose statement promises fixedness over every commutative algebra. This avoids an uncited passage from rational points to a trivial subcomodule, and avoids adding a redundant lemma.

## Route and duplicate searches

I read the chapter and unit records and the latest blueprint files under `literature/blueprint/latest/`, snapshot main-20261024, commit ef6f9619fdbffa59e88528fb56483d76c70258c8. The direct-images proof retains its finiteness/compactification route. This item is a supporting algebraic-group fact in the inherited alteration/moduli/Picard chain. I do not modify the chapter or unit. The ancestor command prints `blueprint.from.node = None`; I preserve that existing null ancestor and the detailed inherited `from.place` and `via` chain.

Whole-DAG searches by unipotence, representations, fixed vectors, normal invariants, kernels, and Milne 6.45/14.3/14.5/14.12 found the supporting nodes used here. Whole-blueprint `blueprint_refs.py search` queries for `unipotent` and `fixed vector` found no node stating this item. The former finds the finite local-system Sylow filtration; the latter finds Tate-module fixed-vector vanishing, which is different. Thus `same_as` remains empty. Nothing was created before these searches.

Fresh logged Mathlib searches for the item used leanfinder, leansearch, loogle and grep, including a second semantic formulation. Returned abstract nilpotent-group quotients and group homomorphism factorization do not imply the claim for algebraic group schemes: nilpotent groups and unipotent matrix group schemes are different notions. The other hits concern Lie primitive vectors and topological Lie groups. The Loogle and algebraic-geometry grep searches found no unipotent group-scheme theorem. The old recorded searches are preserved, and the actual new runs and their results are appended to the item. No match or unavailable service is invented.

## Review by NW

I read Milne 6.45, printed p.135, including its argument that the normal-subgroup invariant space carries the quotient action. I then read Proposition 14.3, Theorem 14.5 and Corollaries 14.6–14.12, pp.280–283, to check that the manuscript's definition agrees with the item's smooth geometric-matrix formulation. I also read Remark 4.1, p.84, Theorem 4.9, p.87, Theorem 5.13 and Lemma 5.15, pp.101–102, Corollary 5.19, p.103, and the quotient/torsor statements on pp.104–105. No SGA source is used.

For step 1 I opened `lem-sfb-geometric-unipotence-unitriangular-embedding` and checked its full statement: it accepts a smooth affine finite-type group over any field with an all-algebra-point faithful representation unipotent over an algebraic closure. The item's embeddings are closed immersions, hence pointwise injective over every algebra, and its geometric hypothesis includes the algebraically closed base field. Both N and Q are smooth by the item, so the cited statement supplies closed embeddings into unitriangular groups over k. It does not require connectedness.

For step 2 I opened `lem-sfb-unitriangular-subgroup-rational-fixed-vector` and `lem-sfb-rational-representation-comodule-dictionary`. The former gives a nonzero fixed vector over every commutative algebra, exactly the stronger assertion needed for descent; the latter identifies finite-dimensional group-scheme representations with coactions and identifies the trivial coaction. I choose a basis to apply the coordinate-space formulation and restrict the given rational E-action to N. Its dimension is positive because V is nonzero. The fixed vector therefore satisfies the coaction hypothesis verbatim, not merely a statement about k-points.

For step 3 I opened `lem-sfb-affine-normal-quotient-geometry` and `lem-sfb-central-kernel-cyclic-representation-descent`. The quotient geometry statement says the fppf quotient is represented and that its quotient map is faithfully flat in the coordinate-algebra sense. The item's Q represents the same sheaf, so the representing isomorphism identifies its q with that map. The descent node's statement, despite its historical name, explicitly imposes no centrality hypothesis. It takes a finite-dimensional rational module and a nonzero vector fixed scheme-theoretically by the kernel, and supplies the nonzero cyclic rational submodule W and its descended Q-action. The kernel is exactly the specified N. The step uses only the stated conclusion and not a construction hidden in that node's proof.

For step 4 I again checked the unitriangular fixed-vector statement, now for Q acting on the positive-dimensional W. The embedding from step 1 is the missing hypothesis. Its vector is fixed under Q(A) for every A, and the descended-action pullback identity from step 3 evaluates at each e to show fixedness under E(A). This evaluation does not assume that every Q(A)-point lifts to E(A).

For step 5 I checked the dictionary statement again, including the coaction identities. The dimension induction is written out: dimension zero, a rationally trivial one-dimensional submodule, the explicit quotient coaction, descent of its identities, the induction on the smaller dimension, and the inverse-image flag. These are elementary operations on vector spaces once step 4 is available. A subspace inclusion and quotient remain exact after extending scalars because a vector-space sequence splits. This is an elementary proof step rather than an unnecessary new flag node. It does not assert the desired extension theorem as a black box.

For step 6 I opened `lem-sfb-normal-subgroup-representation-kernel` and `lem-sfb-geometric-unipotence-faithful-closed-immersion`. The former allows the trivial normal subgroup and supplies a representation in positive dimension with exactly that scheme-theoretic kernel; it includes a formula on all algebra points. The trivial subgroup is closed in the affine group by its augmentation ideal, so the hypothesis holds even without connectedness. I wrote the group calculation showing injectivity, then used the latter node's all-algebra-point criterion to get a closed immersion. This avoids treating existence of a faithful representation as an unnamed theorem.

Step 7 is elementary assembly from the actual flag: its matrix zero entries and diagonal entries follow on every algebra extension, and a strictly upper triangular matrix in dimension d has d-th power zero by lowering the flag. The faithful representation remains a closed immersion after a constant change of basis. Thus the conclusion holds over every algebraically closed extension, not just over k. No new object or hypothesis appears in that final step.

I tested the statement and the chosen inputs at N=1, Q=1, E=1, d=1, the zero-dimensional module in the induction, and disconnected finite constant p-groups in characteristic p. The proof handles all of them. In particular nothing invokes Lie–Kolchin for connected solvable groups or exponential maps, which would have imposed extra hypotheses. The smoothness in the geometric-to-unitriangular input matters: the nonsmooth multiplicative group scheme mu_p illustrates why a rational-point-only criterion would not suffice without it. This split does not apply that criterion to a nonsmooth group.

Against B–E: there are no new nodes to be incomplete, duplicated, elementary, or restatements of the item. Each of the nine citations is accompanied by an actual statement quotation in citations.json. The dependency union is the proof_deps list; I checked each supporting node's dependency closure and found no return path to the item. The proof is an invariant-vector argument and an explicit flag construction, not a relocation of the extension claim to a new node. Every non-elementary fact is a cited node. All seven supporting nodes have the item's unit, so no off-route tool-use declaration is needed. The seven proof steps have respectively 616, 533, 634, 565, 982, 538 and 859 characters, so none meets the long-step review threshold. No Lean file, compiler, Lake or local preflight checker was used.

## Unfinished work

None in the stage-1 split. The seven existing supporting nodes remain their own items according to their live status. Delivery validation is recorded by the dry-run and final delivery command outputs.
