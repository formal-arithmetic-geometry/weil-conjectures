# Stage-1 delivery: lem-sfb-rho-regular-weyl-orbit

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-rho-regular-weyl-orbit.json`: item, statement, split into seven proof steps; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-weyl-reflection-realization.json`: new statement-only lemma, unsplit; no Mathlib match. It identifies the algebraic-group normalizer quotient with the abstract root reflection group, including faithfulness on the root span.
- `dag/nodes/sec-six-functors-basics/lem-sfb-root-chamber-simple-transitivity.json`: new statement-only lemma, unsplit; no Mathlib match. It gives the general real root-system chamber/base correspondence and the simply transitive reflection-group action.

The sandbox also holds `citations.json`, the unmodified command-generated `searches.jsonl`, a local text extraction of Milne, and the script that wrote the split. Only the three node files and this report are delivery files.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint tag, rho regularity, Weyl, half sums, RootPairing and chambers. No project declaration states the item or either new supporting theorem. No Lean was written or compiled.

## WANTED

None. The source used throughout is already present: `literature/milne-algebraic-groups_iAG2017.pdf`.

## Problems found and corrections

The item was an unsplit statement with no proof or Lean audit attachment. Its source described the intended simple-reflection calculation but did not expose the non-elementary chamber theorem or the bridge from the normalizer quotient to the abstract reflection group. In particular the existing Borel-pair and rank-one nodes do not assert that the rank-one reflections generate the whole normalizer quotient. I exposed that bridge instead of silently treating the two groups as equal.

The mathematical statement is unchanged. Its doubled literal TeX backslashes were normalized to single TeX commands. The inherited source locator says C.21--C.22, p.613; in the actual Milne PDF these paragraphs occur on printed p.612. I used the verified printed pages in all new sources and proof steps and left the item's maintainer-owned source field unchanged. No STATEMENT-DISPUTED issue was found.

The current blueprint was read under `literature/blueprint/latest/`, in `sec-six-functors-basics/sk-thm-sf-ctf-stability/`, including its unit and direct-images proof. This root-system result is an inherited supporting input to the double-flag/Haboush/alteration branch of direct-images proof (3). It does not replace a unit step. The ancestor command reports `blueprint.from.node = None`; I retained that existing ancestry and used the prescribed via chain on both new nodes, with precise added places identifying their work. The whole blueprint searches for Weyl, root system, chamber and reflection found no equivalent blueprint statement; the one reflection hit is Fourier inversion and is unrelated.

## Unfinished work

The two new lemmas deliberately remain statement-only, to be split later. The present item's proof is complete relative to their exact statements. No mathematical obstruction remains in the item.

## Not duplicates

lem-sfb-weyl-reflection-realization vs lem-sfb-reductive-borel-pair-structure: the existing statement constructs the root datum and each reflection but does not identify the full normalizer quotient with the reflection-generated group or assert its faithful action on the root span.

lem-sfb-weyl-reflection-realization vs lem-sfb-reductive-rank-one-reflections: the existing node gives a finite normalizer quotient, individual rank-one reflection elements and equivariance of coroots; it does not give generation or the faithful restriction required here.

lem-sfb-weyl-reflection-realization vs lem-sfb-longest-weyl-open-cell: the existing node gives a unique opposite-positive-root element and an open multiplication chart, not the group identification. Its geometric chart is not needed in this proof.

lem-sfb-root-chamber-simple-transitivity vs lem-sfb-crystallographic-positive-base: the existing Mathlib leaf proves integer linear independence of positive indecomposables, not the topology of chambers or their simply transitive action.

lem-sfb-root-chamber-simple-transitivity vs lem-sfb-root-base-rational-integral-spans: the existing node identifies simple-root/coroot spans and bases, not the chamber theorem.

lem-sfb-root-chamber-simple-transitivity vs lem-sfb-bruhat-longest-cell-charts: the existing statement is a scheme-theoretic Bruhat chart theorem for a reductive group, not the general reflection-group chamber theorem. Neither new lemma is the rho conclusion, the simple-coroot pairing formula, or the item's longest-element characterization relabelled.

## Review by Q159

I read Milne C.8--C.22 (printed pp.609--612), 21.37--21.41 (pp.435--436), 21.72 (p.447), and C.46 with its proof (pp.618--619). For the item, C.19 gives exactly the finite averaging used to make an invariant positive definite form, C.20 identifies root reflections with orthogonal reflections, and C.22 supplies the chamber theorem. Definition 21.72 confirms the opposite-chamber element and its involution. I also read the complete statements of the existing Borel-pair, rank-one reflection, longest-cell, root-span and positive-base nodes before deciding which could actually be cited.

For the new normalizer-identification node, 21.37 and 21.38 identify the normalizer quotient with the root-datum Weyl group; C.46 gives faithfulness on the roots. Since the roots span E this is the asserted faithful restriction to E, and conversely a transformation trivial on E fixes all roots. This works with a central torus retained in X; it does not assume the roots span the whole character space. For the chamber node, C.9 and C.10, together with C.21--C.22, give the stated base/chamber bijection and simple transitivity. The real vector space, root-system axioms, bases, positive roots, orthogonal reflections, hyperplanes and chambers are all introduced in its own statement. Its invariant inner product is an assumption, so it does not hide an existence theorem inside that statement.

Step 1 uses the Borel-pair statement for the root datum and sign-coherent base, and the new normalizer-identification statement for finiteness, generation and faithfulness; these assertions really are in the respective statements. Step 2 cites the Borel-pair statement for the reflection formula, reducedness and the same-sign coefficients. The argument is written out: a nonsimple positive root has a nonzero coefficient away from the chosen simple root, that coefficient survives reflection, and the involution makes the resulting map a permutation. Step 3 only reindexes that permutation and compares two formulas for the reflected half sum; the nonzero simple root allows cancellation. It divides by two in a rational vector space, not in F.

Step 4 again cites the Borel-pair and normalizer-identification statements. The dot product is constructed in a basis and averaged over the finite W, with positivity following from the identity summand. Invariance is reindexing; substituting the explicit reflection formula gives the factor 2/(alpha,alpha), not an assumed comparison between two unspecified forms. The base extends from Q to R by its coordinate basis, and proportional rational roots remain rationally proportional by a nonzero coordinate, verifying real reducedness. These are the required hypotheses of the chamber node; irreducibility and semisimplicity are not assumed. Extension of a rational linear action to R is faithful by the same basis matrices, so the chamber action detects the original quotient element.

Step 5 cites the chamber node for the component C and its simple transitivity, and the normalizer-identification node to return from a real reflection to an element of W. Positivity comes from step 3 and the explicit inner-product formula of step 4. If w fixes rho, wC and C share rho and hence are the same component; this is why the free action applies. Step 6 cites those same two statements: transitivity supplies w0 carrying C to -C, and the positive-root characterization in the chamber node proves explicitly that this is equivalent to carrying Phi+ to -Phi+. The inverse-image argument in the converse is included; there is no unexplained transfer from chamber permutations to root permutations. Applying w0 twice fixes C, so freeness and faithfulness give w0 squared equal to 1. Step 7 uses only finite sums, the previously proved stabilizer calculation and the normalizer-identification statement for the empty root system. Every step-citation has an exact verbatim statement quote in citations.json.

I tested the small cases: the trivial group and any torus give empty Phi, E=0 and W=1; A1 gives rho=alpha/2, simple-coroot pairing 1 and the unique nonidentity reflection sending rho to -rho. A reducible product of A1 systems verifies that neither new theorem needs irreducibility. A2 illustrates why the longest element need not act as -1 on the whole space even though it sends rho to -rho; no such false assertion was added. SL2 in characteristic two still has the rational weight alpha/2 and the Weyl reflection, since the argument uses characters rather than their differentials. Positive definiteness is essential in the chamber node and is explicitly assumed there and constructed at its application.

I checked delivery-errors B--E against the files: new nodes have no proof sketch in their statements, all notions are defined inline or cited, all new searches are actual msearch.py invocations recorded in searches.jsonl, and the source places are verified printed locations in Milne (no applicable Stacks tag is being substituted by a section number). LeanFinder and LeanSearch returned root-base induction and abstract Weyl-group declarations; Loogle found only the abstract definitions or no hits, while grep located the prose mention in Base.lean:27--29 and the invariant-form files. I opened Base.lean, WeylGroup.lean and CanonicalBilinear.lean; no declaration there gives either full new theorem, so neither is marked a Mathlib leaf. Each new statement received two semantic phrasings. DAG/blueprint searches and the comparisons above rule out existing specializations. The simple-reflection permutation and averaging are explicit elementary arguments, not extra nodes. No step exceeds 2000 characters. Proof dependencies equal the union of uses, and the two supporting nodes depend only on previously existing notions, so neither points back to this item. No SGA source is used.
