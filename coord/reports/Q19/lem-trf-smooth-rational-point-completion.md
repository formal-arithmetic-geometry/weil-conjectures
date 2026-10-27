# Q19: lem-trf-smooth-rational-point-completion

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-smooth-rational-point-completion.json`: statement, split into nine steps; no exact Mathlib match.
- `citations.json`: a verbatim statement quote for every proof-step citation.
- `searches.jsonl`: five actual searches performed by the required search command. Their results are also appended to the inherited Mathlib-search record, which is retained intact.

No new nodes and no new Mathlib leaves. Only the sandbox is written; no Lean, compiler, Lake, build, or repository git command was used.

## Attachments

None. Searched the live `lean/WeilConjectures/` by the exact blueprint id and by smooth/completion and etale/completion concepts, also inspecting the search results in `lean/Sheaf/`. There is no project declaration stating both clauses under these hypotheses. The smooth-section completion chart concerns an augmentation, which is not supplied here. A field power-series/valuation completion is also not this statement.

## WANTED

None. The sources used are present locally.

## Corrections and scope

The inherited statement is correct; no hypothesis or conclusion was changed. Added the existing multivariable-polynomial definition to its statement dependencies. The item was unsplit and the sandbox contained no earlier item or report. Its inherited source correctly says that neither 054L nor 0AGX alone states the conclusion. The proof now explains how these results imply it, including the centering of coordinates using the *given* residue-field identity, the differential-rank calculation, and the coefficient calculations needed for both completion and associated graded. No statement dispute arose.

The chapter and unit records were read. This is a generic algebra input on the inherited historical auxiliary branch below `lem-trf-local-term-locality`, rather than the key node of `sk-i-curve-zero`; its `realized` fields therefore are not changed. The inherited blueprint ancestor, place and via list are retained. Whole-blueprint searches for 054L, 0AGX, completion, power series and associated graded found no blueprint node stating this item. The existing 054L node is cited instead of creating another normal-form node. Off-unit generic tools are declared in `split_report.tool_uses`; they supply algebra facts, without replacing any unit proof route.

## Mathlib searches

Ran LeanSearch, Loogle, grep of RingTheory, and two different LeanFinder phrasings, through `batch2/msearch.py`, and read every returned hit. All services answered. The semantic hits give smoothness and standard-smooth presentations, not this completion or graded theorem. Read `Mathlib/RingTheory/MvPowerSeries/Equiv.lean`, especially `toAdicCompletionAlgEquiv` at line 344: its ideal consists only of the variables, whereas here the base maximal ideal must also be completed. `LaurentSeries.powerSeriesRingEquiv` has a one-variable field/valuation setting. Neither specializes in one line to this item. No new node is declared absent from Mathlib without a logged search, since no new node is created.

## Not duplicates

No new-node/existing-node pairs: no new node was needed. Reused the existing normal-form, differentials, flatness, maximal-ideal, completion-isomorphism and completion-mod-power statements. In particular `lem-trf-mvpolynomial-noetherian` only asserts Noetherianity over Z, so it is not used over the arbitrary base R. Instead the existing locally-Noetherian finite-type theorem and localization theorem give the needed local Noetherianity. The existing algebraically-closed-field etale completion node has stronger hypotheses on the base and cannot replace 0AGX here.

## Review by Q19

I read the item against `literature/stacks-project/morphisms.tex`, lemma-smooth-etale-over-affine-space (054L), and `more-algebra.tex`, lemma-flat-unramified (0AGX), including their proofs. I also read the supporting Algebra statements: lemma-differentials-localize (00RT), lemma-differentials-polynomial-ring (00RX), lemma-formally-etale-omega (0H93), lemma-etale-at-prime (00U4), definition-etale (00U1), lemma-flat-localization (00HT), and lemma-hathat-finitely-generated (05GG), and the affine etaleness characterization in Morphisms (02GJ). There are no new-node sources to review. All cited DAG statements were opened and read; citations.json copies their statement text, without extracting hidden proof material.

Step 1 uses the existing essentially-smooth definition to choose the smooth algebra, proves explicitly that its localization is the stalk at the contracted maximal ideal, and applies the affine smoothness equivalence and 054L normal form. The local-base observation ensures the resulting polynomial algebra is over R itself, not a smaller base. These cited statements supply precisely the algebra presentation and affine etale chart used.

Step 2 uses the polynomial definition/evaluation universal property. Since R/m -> S/n is the specified identity of L, every residue coordinate has a lift in R. Translating by these lifts really makes the inverse image prime equal to (m,Z); equal abstract residue-field isomorphism types would not suffice. The induced local map T -> S therefore induces the required identity on L.

Step 3 uses 02GJ's actual two cotangent-vanishing clauses to discharge exactly the hypotheses of the existing formally-etale differential comparison node. The polynomial differential-basis and differential-localization nodes then give a free S-module with d basis vectors. Thus d equals the specified differential fibre dimension, rather than an unrelated chart dimension.

Step 4 uses the locally-Noetherian finite-type theorem, the definition of locally Noetherian, and the localization-Noetherian theorem to establish the Noetherian hypothesis on T. It uses the etale-flat and localization-flat statements to get flatness over C and writes the two-tensor argument for composition; the flat-over-localization statement then yields flatness over T. The etale-prime statement applies to the actual prime b of the actual chart C -> B and gives QS=n. It does not assume that a localization S of B is finitely presented over C.

Step 5 applies exactly the existing 0AGX node: T and S are Noetherian local rings; T -> S is flat, its maximal ideal extends to n, and its residue map is an isomorphism. The cited node specifies the induced completion map coordinatewise, so compatibility with R and its completion is available, not inferred from existence of an abstract isomorphism.

Step 6 is a coefficient calculation from the polynomial definition. I checked both inclusions in the coefficient ideal of Q^N and wrote the finite geometric-series inverse proving that localization changes no finite quotient. Step 7 constructs both directions of the inverse-limit/power-series identification coefficient by coefficient and verifies multiplication using finite convolutions. These are elementary calculations, not citations to a power-series theorem whose ideal differs.

Step 8 invokes exactly the kernel and quotient assertion of the existing 05GG node for the finitely generated ideal m. The compatible inverse argument proves that the completed coefficient ring is local; the recursive series inverse proves locality of the series ring. The explicit decomposition of a zero-constant series gives the stated maximal ideal, including d=0. The quotient-tower description also shows completeness for this maximal-ideal topology.

Step 9 applies 05GG to QT and n, which are finitely generated because T and S are Noetherian. Since the completion isomorphism in Step 5 is the *induced* map, it identifies the actual maps on all finite quotients. Their kernels give every positive graded piece; degree zero is L. The coefficient description and its multiplication then give the graded polynomial algebra with variables of degree one. Constants throughout are the images of R, proving the compatibility with the base graded map.

I checked B--E of delivery-errors point by point: no new unsplit proof sketches, hidden definition claims, new duplicates, clause-restatement nodes, unsupported source citations, or use of a cited node's proof in place of its statement. The coefficient computations are spelled out rather than replaced by “transport” or “standard”. Every step is shorter than 2000 characters. No SGA source is used. Small cases checked: s=0 yields the 0AGX completion isomorphism and unchanged graded ring; R=L gives the usual formal affine-space ring and polynomial tangent cone; a nonreduced base such as L[epsilon]/(epsilon^2) retains its nilpotent coefficient and its graded relation, so the argument does not accidentally assume regularity or that R contains a coefficient field. Mixed characteristic is also allowed because only lifts of residue coordinates, not a section L -> R, are chosen.

## Unfinished work

None in this one-level split. Server checks and delivery are performed with the required launcher tools.
