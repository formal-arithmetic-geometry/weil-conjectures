# Q146 stage-1 delivery: lem-a1-pulled-koszul-tower-chain-comparison

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-pulled-koszul-tower-chain-comparison.json`: existing statement split into six proof steps, using only existing nodes. Mathlib verdict: no exact match or one-line specialization; all new search records are actual msearch.py outputs.
- `citations.json`: 19 verbatim statement quotations, one for every proof-step citation.
- `searches.jsonl`: five searches run by the prescribed command; results read and retained.
- `report.md`: this report and signed self-review.

New nodes: 0. New Mathlib leaves: 0. No Lean, repository, launcher, unit or chapter file was written; no compiler, Lake or build was run.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, pulled Koszul terminology, and Koszul/tower combinations. No project declaration states the entire item. The existing principal strict-replacement result is a dependency, not an attachment of this pullback comparison.

## WANTED

None. All sources needed for this split are available locally.

## What changed and what was wrong

The imported item had no proof. Its mathematical statement is unchanged. The split uses the existing generic flat-term K-flat pullback theorem, the existing normalized cochain tensor comparison, and the already split principal Koszul replacement theorem. No new node is needed for a special case of one of these results or for the two-term scalar/transition calculations.

The definition `def-a1-principal-completed-koszul-towers` uses natural-number index k and exponent k+1. The item's positive index n corresponds to k=n-1; the objects, adjacent transitions and augmentations are unchanged under this reindexing. This is only an index convention, not a statement dispute.

The blueprint ancestor is `lem-a1-finite-map-purity`. I read its current main-20261015 statement and proof, and the chapter/unit records. The actual blueprint paragraph uses geometric-stalk restriction to prove finite-map purity; it does not itself contain this completed-coefficient homological calculation. The ancestry records a chain of agent refinements. The present split realizes step 2 of the already split parent `lem-a1-finite-pullback-strict-tower-comparison`, namely its old steps 3-5: good pulled complexes, strict Koszul tensor comparison, and target augmentation. It keeps the unit's route.

## Not duplicates

No new nodes are proposed. Whole-DAG searches found several existing forms of Tag 0G7E; I use `lem-weil-pbc-ringed-pullback-preserves-kflat`, whose coefficient-last formula agrees literally with G. I reuse `lem-pur-cochain-pullback-tensor-coherence` rather than introducing a generic tensor-comparison node, and reuse `lem-a1-principal-koszul-strict-replacement` for the target augmentation. Whole-blueprint searches for Koszul, principal Koszul and Koszul tower found no blueprint node stating this particular strict pullback comparison; `blueprint.same_as` remains empty. The two matching intrinsic-completion definitions in the Koszul-tower search define completion rather than this theorem.

## Review by Q146

I read delivery-errors B-E in full, including the merged copy, and checked the actual node statements rather than using their proofs as an interface. I read Stacks `sites-cohomology.tex`, Tag 0G7E, label `lemma-pullback-K-flat`, statement and proof: it requires K-flatness and flat terms, exactly the good-complex hypotheses here, and does not require the ring map to be flat. I also read Tag 07A4, `lemma-pullback-tensor-product`, especially its displayed ordinary isomorphism of total complexes and the identification of its constituents with `sites-modules.tex` Tag 03EL, `lemma-tensor-product-pullback`; I read that lemma and its bilinear-adjunction proof. The tower argument uses the levelwise abelian statement in the existing Tag 02MZ node, `lemma-inverse-systems-abelian`. No SGA source is used.

Step 1 uses the statement of `lem-a1-principal-koszul-strict-replacement`, which explicitly supplies good source tensor levels and the coefficient hypotheses, and the statement of `lem-weil-pbc-ringed-pullback-preserves-kflat`, which explicitly gives both K-flatness and termwise flatness for arbitrary structural ring maps. `def-a1-flat-term-kflat-complex` defines good, and `def-weil-pbc-completed-pullback` specifies exactly the ordinary coefficient-last pullback and projection-induced c_g. Thus the two applications have precisely their required hypotheses. There is no substitution of finite-coefficient exact pullback for the completed-ring functor G.

Step 2 reads the first paragraph of `def-weil-pbc-completed-pullback` for each component of c_g, the constant-ring paragraph of `def-weil-proetale-inverse-image` for its constant-section formula, and `def-sp-completed-uniformizer-section` for its constant residues. The inverse-limit universal property then proves c_g(t)=t. The two balanced unit maps are written explicitly using the sheafified tensor definition `def-pur-sheaf-tensor-product`; their inverse equations are the balancing relation. This step uses definitions and direct calculations, not a hidden flatness assertion.

Step 3 uses `lem-pur-cochain-pullback-tensor-coherence`, whose statement gives an ordinary chain isomorphism for arbitrary unbounded complexes, its local generator formula, both-variable naturality and action unitors. This is stronger than a mere derived tensor isomorphism, which would be insufficient here. I reconcile its coefficient-first convention with the coefficient-last convention explicitly: the scalar has degree zero. The Koszul definition supplies its two degrees and differential; `def-pc-tensor-complex-sheaves` supplies the exact sign (-1)^p. The displayed basis maps and inverse, scalar equation and the two differential contributions prove the two-term identification inline; this is an elementary specialization of that existing comparison, not a new derived comparison lemma or a per-degree substitute for one. The item itself requires a strict cochain isomorphism and the proof constructs that stronger object before any localization.

Step 4 uses only the naturality clause of that same cochain comparison and the stated adjacent Koszul transitions. I checked both terms of phi_n G(t,1)=(t,1) phi_(n+1), not just cohomology. All other tower arrows are finite composites of adjacent arrows. I wrote the generator formula for the naturality square with an arbitrary chain map; it introduces neither a degree shift nor a scalar adjustment.

Step 5 applies the full statement of `lem-a1-principal-koszul-strict-replacement` at W=T' and P=GP, whose good-complex hypothesis was proved in step 1. That node explicitly specifies the actual quotient augmentation, its levelwise quasi-isomorphisms, its quotient transitions and chain-map naturality. The strict augmentation square is also written out with pi_n=q pi_(n+1); tensor functoriality from the Koszul and total-tensor definitions preserves this equation. Consequently I never use preservation of arbitrary source quasi-isomorphisms by G.

Step 6 uses exactly the kernel/cokernel and levelwise exactness clauses of `lem-weil-tower-category-levelwise-abelian`, and the kernel/image definition of cohomology and quasi-isomorphism in `def-weil-abstract-derived-category`. Replacing image by kernel of cokernel gives the asserted levelwise H^r directly. The inverse naturality-square argument proves that componentwise isomorphisms form an isomorphism of towers; no separate unproved detection theorem is invoked. Reindexing towers of complexes as complexes of towers is the direct equality of their data and equations.

I checked B1-B9 and the non-attachment condition B10: no new unsplit nodes, hollow construction, unsupported new notion or false Mathlib leaf was introduced. The five fresh Mathlib searches include two semantic phrasings, Loogle and grep. I read the actual hits: ordinary sheaf pullback/free pullback and its adjunction/composition do not include this Koszul tower or augmentation; the Kahler/cotangent and generic quasi-isomorphism hits concern other objects. I read `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean` and `PullbackFree.lean`, including `pullbackObjFreeIso` at line 118. Earlier item searches were retained verbatim, not relabelled as searches of this group.

For C1-C8, every non-elementary input is a named existing statement. `citations.json` quotes what each step actually takes, including strict chain-level formulas, target augmentations and exactness. No proof-only object is borrowed. The off-unit generic preservation and tensor calculus tools, together with defining coefficient interfaces, are declared in `split_report.tool_uses` with explanations; they do not replace the unit's geometric argument. The server dry run checks graph acyclicity and route declarations.

For D1-D5, the steps carry the basis, scalar, differential, transition and naturality argument; there is no newly named restatement of a clause. The target augmentation follows an existing general replacement theorem after the new pulled-goodness verification. No induction or omitted standard argument is hidden. All six steps are shorter than 2000 characters (569, 752, 1085, 754, 809, 723), and I reviewed them for hidden lemma content independently of that limit.

For E1-E6, I tested n=1, adjacent and identity tower arrows, P=0, a one-term P, a complex unbounded in both directions, and an empty scheme. In the two-term tensor there are only the q=-1,0 summands in each total degree, so no additional boundedness assumption appears. Zero objects and zero-ring sheaves cause no failure of the balanced unitor maps. Arbitrary nonflat c_g is allowed throughout; both preservation and the cochain comparison expressly permit it. Target regularity and quotient augmentation are supplied by the existing principal replacement theorem at the target, rather than inferred by applying nonexact G to source exactness. No mathematical statement dispute or source correction was needed (E7).

## Unfinished work

None in the stage-1 split. The independent maintainer review remains part of the delivery process. Dry-run and push results are recorded below after the commands finish.
