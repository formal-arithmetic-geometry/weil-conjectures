## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-dense-restriction-semisimple.json: split the item into five complete steps; statement and statement dependencies unchanged.
- citations.json: three step/node entries, quoting the actual statements.
- report.md: this report. searches.jsonl is the search command's unmodified log; milne.txt is a local text extraction for reading.

## New nodes

None: 0 new nodes, 0 new Mathlib leaves. The existing Mathlib leaf lem-sfb-module-socle-complements supplies the general ring-module complement result. The existing lem-sfb-smooth-group-rational-point-subspace-test supplies the scheme-theoretic comparison.

## Attachments

None for the item. Searched the project source by the exact blueprint id and by dense, semisimple, and stabilizer. Read WeilConjectures/AlgebraicGeometry/GroupScheme/GeneralLinear/Representation.lean and the relevant Lie.lean subspace comparisons, and WeilConjectures/Mathlib/RepresentationTheory/Semisimple.lean. The rational representation definitions and simplicity equivalences impose characteristic zero and the latter semisimple restriction theorem assumes a normal abstract subgroup. Neither states this item, which allows positive characteristic and a dense subgroup without normality. The dual-number preservation theorem in Lie.lean gives only dual-number stability, not the all-algebra conclusion. No sorry declaration is treated as a proof.

## WANTED

None. All sources used are available locally. No SGA source was used.

## Issues found and changes

The live item had a statement and previous searches but no proof. It is mathematically correct against Milne. The potentially dangerous distinction is between topological density, rational-point invariance, and preservation over every algebra. The proof separates these: closed stabilizers give invariance under every k-point; the existing smooth-group rational-point test then gives all-algebra invariance. Thus no unjustified identification of set-theoretic and schematic density is needed in the item.

The inherited blueprint.from.node is null: the actual ancestor command returns None for this chain. Its long, specific from.place and via list are retained. I read the latest blueprint's six-functor stability statement and proof and the closed-stabilizer statement/proof. The supporting Milne argument remains exactly the inherited alteration-route prerequisite, not a new unit route. No statement correction is necessary.

## Searches and reuse

Read the prior searches recorded in the live item; there was no earlier sandbox split, report, citation file or search log to recover. Ran the required msearch.py commands for Q153 and this item: leanfinder (two formulations), leansearch, loogle, and grep in RepresentationTheory. All services responded. The exact queries and returned summaries are appended in mathlib_searches and preserved in searches.jsonl. Read the returned signatures and Mathlib/RepresentationTheory/Semisimple.lean:33--48. Module.End.IsSemisimple.restrict concerns a single endomorphism; Maschke and FDRep.simple_iff_end_is_rank_one assume a finite group (and suitable characteristic). The invariant-submodule hits do not compare group schemes with dense subgroups. There is no exact Mathlib match for the item.

Searched the whole DAG for schematically dense, dense subspaces, stabilizers, sums of simple modules, complements, Corollary 4.4 and Proposition 4.17. Ran tools/blueprint_refs.py search for dense, stabilizer, and semisimple, and ancestor for the item. Read the relevant actual nodes. The search found the three dependencies used below, so I created no replacement nodes.

## Not duplicates

No new node pairs to resolve. lem-wf-stabilizer-density supplies the general closed-stabilizer assertion, but its consequence concerns a specific monodromy representation and has none of the item's complement or splitting assertions. lem-sfb-smooth-group-rational-point-subspace-test compares all k-points with all algebra points, without a dense subgroup or semisimplicity. lem-sfb-module-socle-complements is a general ring-module result and is reused as a leaf, not recreated.

## Review by Q153

I read Milne, Algebraic Groups (2017), Proposition 1.10 on printed pp.9--10, Proposition 4.3 and Corollaries 4.4--4.5 on p.85, Definition 4.15 and Proposition 4.17 on p.90, and the proof of Lemma 13.6 on p.256. Proposition 4.3 makes a subspace stabilizer closed by the off-block matrix equations; Corollary 4.4 explains why dense points detect invariant subspaces. Proposition 4.17 proves complements for a sum of simple modules, and Lemma 13.6 uses simplicity on the dense subgroup and stable isomorphic lifts of finite-jet surjections. These are precisely the item's inputs. The item uses none of Lemma 13.6's separate geometric fixed-locus conclusions or linear-reductivity assumptions: it assumes directly the needed semisimplicity of M.

Step 1 uses only the first assertion of lem-wf-stabilizer-density, whose actual statement says that the stabilizer of any vector subspace is Zariski closed. I opened it and did not use its specialized Pi/H_geom consequence. Pulling this closed set back under the rational morphism rho and using the definition of dense proves invariance under every k-point; applying the same assertion to g inverse gives equality. This is a generic tool from another unit, declared in split_report.tool_uses, not a replacement of the six-functor unit route.

Step 2 uses the actual equivalence (i)--(ii) in lem-sfb-smooth-group-rational-point-subspace-test, which I opened with its reviewed proof. All its hypotheses are present: algebraically closed k, smooth affine finite-type G, finite-dimensional M. Its condition (ii) explicitly quantifies over every commutative k-algebra, so this citation really supplies rational stability, including nonreduced test algebras. The converse is evaluation at k. This avoids citing a pointwise stabilizer assertion as if it supplied schematic invariance.

Step 3 uses the equivalence already proved in steps 1--2, not an uncited restriction theorem. A subspace of a simple summand is also a subspace of M, and its all-algebra invariance is inherited inside the summand because vector-space inclusions split and remain injective after tensoring. This is elementary linear algebra, and the same original finite direct sum remains a direct sum after restriction. No connectedness or characteristic condition is introduced.

Step 4 uses lem-sfb-module-socle-complements, whose statement I read in full: every module over an arbitrary unital ring that is a sum of simple submodules has a submodule complement to each submodule, including the zero module. I also checked its recorded Mathlib match IsSemisimpleModule.of_sSup_simples_eq_top at Mathlib/RingTheory/SimpleModule/Basic.lean:200--202 and the complemented-lattice definition at lines 63--66. The proof constructs the group algebra and its action explicitly, and checks both directions of its submodule correspondence using a[1], [gamma], and finite sums. Thus M meets the leaf's hypothesis from step 3; the ring need not be commutative and Gamma need not be finite. This citation is not silently replaced by the assumption that an algebraic group is reductive.

Step 5 proves the section rather than citing a new node restating that clause: its kernel is stable by equivariance, q restricted to C is injective by C intersect ker q = 0, and surjective by M = ker q + C. Uniqueness of preimages proves linearity and equivariance of the inverse, explicitly, so q composed with s is the identity. The action on V need not be rational.

I checked B--E individually. No new statement-only node, new notion, hidden lemma, duplicated Mathlib result, source section-number substitution, changed hypothesis, proof citation to a mere definition, or cyclic dependency was introduced. Every cited node's exact used text is in citations.json. Every non-elementary step is below 800 characters, so no step exceeds the 2000-character review threshold. The elementary steps are the simple-summand argument after the established subspace equivalence and the explicit inverse to a bijective restriction, not the density or module-complement theorem.

Small cases checked: M=0 uses an empty sum and forces V=0 for a surjection; N=0 gives C=M and N=M gives C=0; a zero target gives the unique zero section. A trivial action has simple one-dimensional summands and ordinary vector-space complements. For disconnected G the closed-set argument still covers every component because Gamma is dense in all of G. Positive characteristic causes no division by group order. An infinite Gamma poses no problem because elements of k[Gamma] have finite support. Dropping density really can fail (restriction of the standard irreducible SL2 module to its upper-unipotent subgroup is not semisimple), which confirms where the argument needs the actual hypothesis. Smoothness is used only through the existing all-algebra test; it prevents infinitesimal group directions from being invisible to rational points.

## Unfinished work

None for this one-level split. Required validation and push are performed with the supplied delivery command; no Lean file, compiler, Lake tool or repository git command was run.
