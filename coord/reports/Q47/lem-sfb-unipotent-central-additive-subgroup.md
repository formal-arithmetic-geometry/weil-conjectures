## Worker report

Q47 split lem-sfb-unipotent-central-additive-subgroup, retaining its statement and seven statement dependencies exactly. All edits are in this sandbox. No Lean was written, compiled or built; no repository or launcher file was changed.

Files written: dag/nodes/sec-six-functors-basics/lem-sfb-unipotent-central-additive-subgroup.json (six-step split); citations.json; report.md; and these four statement-only nodes, all searched and absent from Mathlib:

- lem-sfb-nilpotent-connected-central-series: statement, unsplit. Milne 6.38--6.39 gives a series of connected subgroup varieties from an arbitrary central series.
- lem-sfb-bounded-exponent-reduced-p-kernel: statement, unsplit. This spells out the reduced neutral component used in Milne 14.55, including the bounded-exponent assumption which makes it nontrivial.
- lem-sfb-perfect-exponent-p-vector-group: statement, unsplit. Milne 14.54, characteristic p, smooth connected commutative groups killed by p.
- lem-sfb-char-zero-commutative-unipotent-vector-group: statement, unsplit. Milne 14.32--14.33, the vector-group classification in characteristic zero.

Attachments: none. A project-wide search of lean/WeilConjectures for the item tag, unipotent/Unipotent, nilpotence, centrality, exponent and group schemes found no declaration giving this item or these four inputs. The abstract-group and Lie-algebra search hits are different objects.

WANTED: none. The necessary source is the local literature/milne-algebraic-groups_iAG2017.pdf.

The imported item has a true statement and an empty proof. Its characteristic-zero source sentence is a correct conclusion but omits its prerequisites. I supplied a common central-variety reduction followed by the two characteristic-specific vector-group theorems. The stronger existing lem-sfb-perfect-unipotent-additive-series is deliberately not used: Milne 16.24 depends on 16.22 and ultimately the present central-additive result. There is no statement dispute or hypothesis change.

Nothing in this one-level split remains unfinished. The four new nodes are intentionally unsplit dependencies for later workers; they contain no proof, proof dependencies or proof sketch inside their statements.

## Sources and searches

I read Milne 6.34--6.40 (pp.133--134), 6.49 (pp.136--137), 14.21 (pp.284--285), 14.24, 14.31--14.33 (pp.288--289), and 14.49--14.55 (pp.296--297), plus 1.34, 1.38--1.39 and 1.52 for reductions and components. The source's “group variety” means smooth algebraic group (Milne 1.28). The characteristic-zero classification is proved using 14.21 and 14.24 and does not depend on the present item; it is therefore safe here.

I read the chapter and unit records and the latest blueprint sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. The inherited long support chain to direct-image preservation is retained, without changing any unit or chapter route. tools/blueprint_refs.py ancestor returns null for this item, as its ancestor chain has a broken historical blueprint link; the existing null anchor and via chain are preserved, and new nodes prepend this item to that chain. The exact supporting Milne clauses are appended to from.place.

Whole-DAG statement/source searches covered unipotent, nilpotent, central series, 6.40, 14.32, 14.33, 14.54, exponent p, reduced identity component, p-kernel and multiplication by p. Whole-blueprint searches via tools/blueprint_refs.py covered unipotent, nilpotent, exponent, commutative unipotent, kernel of p and central series. None states a new node. I opened the existing unitriangular embedding, coordinate filtration, affine centre, smooth derived subgroup, normal image, smooth-unipotent-solvable and additive-series statements. All Mathlib searches were run with the required msearch.py command and their actual output was read. Each new node has LeanFinder, Loogle, grep, LeanSearch and a second semantic phrasing. searches.jsonl and the per-query text files retain the results. Services answered; no unavailable result is mislabeled no-match. The hits concern abstract groups, Lie algebras, perfect rings, analytic objects and number fields, not the group-scheme assertions. There are zero Mathlib leaves.

## Not duplicates

lem-sfb-nilpotent-connected-central-series vs lem-sfb-perfect-unipotent-additive-series: the new node assumes a possibly nonsmooth central series and produces smooth connected terms for any nilpotent smooth connected group; it neither assumes unipotence nor asserts additive quotients. The existing additive-series theorem is stronger in that particular setting but its source proof uses this item's conclusion, so cannot be an input here.

lem-sfb-nilpotent-connected-central-series vs lem-sfb-smooth-connected-derived-subgroup: the latter gives only the ordinary derived subgroup over an algebraically closed field. It neither gives mixed commutators in the descending central series nor descent over a general perfect field.

lem-sfb-nilpotent-connected-central-series vs lem-sfb-smooth-unipotent-solvable: the latter supplies only solvability, with no smooth connected central filtration.

lem-sfb-bounded-exponent-reduced-p-kernel vs lem-sfb-unipotent-central-additive-subgroup: the new lemma assumes commutativity and bounded p-power exponent and identifies a specific reduced p-kernel; it neither finds a central subgroup in a noncommutative group nor identifies any subgroup with Ga.

lem-sfb-perfect-exponent-p-vector-group vs lem-sfb-one-dimensional-unipotent-additive: the new node has arbitrary dimension, assumes exponent p and a perfect field, and does not assume unipotence or use the one-dimensional classification. The existing node is only one-dimensional over an algebraically closed field and depends on the present item.

lem-sfb-char-zero-commutative-unipotent-vector-group vs lem-sfb-perfect-unipotent-additive-series: the new node is the characteristic-zero commutative classification by a vector group, not a filtration of arbitrary noncommutative groups in all characteristics.

## Review by Q47

I checked B--E against the source and each node, including the hidden-lemma rule. The item is unchanged and remains valid for every perfect field, with no dimension restriction. Each new statement introduces its own field, group, characteristic and subgroup notions. Their only extra notions (reduction, kernel and identity component) are defined in the p-kernel statement; the reduction and fibre-product definitions are cited. All four are statement-only with empty proof and proof_deps, valid TeX, the current chapter/unit and inherited blueprint reference. None restates the item. I corrected an initially mistaken identity-component source reference from 5.9 to 1.34 and 1.52 after checking the actual text.

Step 1 uses exactly the existing geometric-unipotence-unitriangular-embedding statement to get a closed immersion over k, not merely over an algebraic closure. Its hypotheses hold because V is smooth, affine and finite type and its faithful representation detects geometric unipotence. The existing coordinate-filtration statement supplies normal subgroups, the coordinate homomorphisms, their kernels and trivial unitriangular conjugation. For v and h, the coordinate of the commutator is p(vhv^-1)-p(h)=0; hence it lies in the next kernel. Intersecting is given by the explicit coordinate equations, including all nilpotent test algebras. I checked these assertions directly in both cited statements, rather than relying on their proofs.

Step 2 uses exactly the new central-series statement, whose input allows the possibly nonsmooth intersections of step 1. Perfectness, smoothness and connectedness are available. Choosing the last nontrivial term of its finite series is elementary, and the stated commutator containment makes that term central over every algebra. Two elements of C therefore commute. Restricting the already constructed closed embedding gives the matrix representation required later. The new input does not assert a Ga subgroup: the characteristic-specific work is still needed.

Step 3 uses the new characteristic-zero commutative classification. I checked commutativity from step 2 and the closed unitriangular embedding, rather than applying an exponent-p theorem in characteristic zero. Its exact conclusion is a group-scheme isomorphism from Ga^d; d=0 would force C=1, so d is positive.

Step 4 is the explicit elementary matrix argument which supplies a uniform exponent over every k-algebra, not just geometric points. Strict upper triangularity gives T^n=0 by matrix multiplication. Repeated binomial expansion in characteristic p gives (I+T)^(p^e)=I+T^(p^e). Since C is commutative, this power map is [p^e]. It vanishes for p^e at least n. This is a short algebra calculation and creates no new node.

Step 5 uses precisely the new p-kernel lemma, with its bounded-exponent assumption supplied by step 4. That statement provides smoothness, connectedness, closedness, commutativity, nontriviality and exponent p for K. Perfectness is needed both here and in the next cited vector-group theorem. I checked the latter's hypothesis is [p]=0, not merely p-power torsion. Its conclusion gives Ga^d isomorphic to K and nontriviality excludes d=0. The full statements used in both applications are quoted verbatim in citations.json.

Step 6 is coordinate selection, not a new structural theorem. In either positive-dimensional vector group the first coordinate axis is cut out by x_2,...,x_d; it is a subgroup with the additive law of def-sc-gm-ga and is isomorphic to Ga by that coordinate. The composition of the closed embeddings has the sum/pullback of their defining ideals, so remains closed. Polynomial coordinates lift freely across nilpotent quotients, establishing smoothness of this affine line, and k[t] is a domain, establishing its connectedness. Since it is inside C, the all-algebra centrality of step 2 gives the requested clause. No centrality is inferred from k-points alone.

I tested the central-series input on the trivial group (length zero), Ga, Gm and the upper-unitriangular Heisenberg group; connected commutative groups are allowed, and the last term need not equal all of V. For the p-kernel lemma, Ga has K=Ga and a length-two Witt group has a positive-dimensional p-kernel even though [p] need not vanish on the whole group. A torus fails the bounded-exponent hypothesis. The nonsmooth finite alpha_p and disconnected finite constant p-groups fail the smoothness or connectedness hypotheses, so cannot incorrectly force a Ga subgroup. A smooth connected zero-dimensional group with its identity rational point is trivial; thus nontriviality is enough. The vector-group lemmas allow d=0, while the item's applications force d>=1. I checked p=2 and n=1 in the matrix step: the binomial argument still holds, and n=1 would contradict V nontrivial. No step exceeds 2000 characters, hides an induction, cites SGA, or borrows a lemma from a forbidden route.

## Argument retained for the new p-kernel input

The nontriviality omitted in the short proof of Milne 14.55 is not an assumption that every unipotent group is already a vector group. Here is the argument for the next worker. A nontrivial smooth connected group C has positive dimension: a smooth connected zero-dimensional scheme over k with its identity k-point is Spec k. If ker[p] had dimension zero, each fibre of [p] would be a translate of that zero-dimensional kernel after passing to an algebraic closure. The image of [p] would therefore have dimension dim C. More generally the same conclusion applies to the restriction of [p] to every successive scheme-theoretic image of [p]^j, since its kernel is a closed subgroup of ker[p]. Thus every iterated image would have dimension dim C. This contradicts [p]^e=0, whose image has dimension zero. Consequently ker[p] has positive dimension. Reduction preserves its underlying space; over a perfect field it is a smooth subgroup by Milne 1.39. Its connected identity component is a closed smooth subgroup and has the same dimension as every component (translation after algebraic closure); hence it has positive dimension and is nontrivial. It is contained in the p-kernel, so is killed by p. This argument will require image/fibre-dimension prerequisites when the new node itself is split; they are not hidden facts used directly by the present item's assembly.

## Validation

The initial required deliver.py --no-push exited successfully and printed preflight passed. Its checks covered the full delivery, including the DAG, split shape, recorded searches and verbatim citation quotes. After correcting the source reference and adding the preceding explanation, I reran the required dry run before pushing the final content.
