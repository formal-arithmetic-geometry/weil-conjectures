# Q45: lem-trf-toric-normalized-desingularization

## Files written

- dag/nodes/sec-trace-formula/lem-trf-toric-normalized-desingularization.json: split into six steps; statement and stmt_deps unchanged.
- dag/nodes/sec-trace-formula/lem-trf-smooth-functorial-ordinary-resolution.json: statement, unsplit; no Mathlib match. The input is ordinary resolution, without normalization or equivariance.
- dag/nodes/sec-trace-formula/lem-trf-normalized-blowup-calculus.json: statement, unsplit; no Mathlib match. One-center universal property, normality and smooth comparison, without any resolution rule.
- dag/nodes/sec-trace-formula/lem-trf-conductor-smooth-base-change.json: statement, unsplit; no Mathlib match. Conductor support and smooth comparison, without a desingularization assertion.
- dag/nodes/sec-trace-formula/lem-trf-toric-realization-finite-type.json: statement, unsplit; no whole-node Mathlib match. Mathlib supplies the finite-type monoid algebra fragment and a domain instance, but not the monoscheme gluing and split smooth group-scheme assertions.
- citations.json: a verbatim quotation for each citation of each of the six steps.
- report.md and searches.jsonl: report and the actual msearch audit. ilo.txt and write_split.py are sandbox-only reading/authoring aids, not delivery files.

## Attachments

None. I searched the slopmaster2 WeilConjectures tree for the item id, its blueprint tag and desingularization/toric notions. There is no project declaration for this item or any new node. Project normalization declarations do not contain the ordered resolution, normalized-blowup or conductor statements. No upstream master sorry is treated as a proof.

## WANTED

None. I read the local ILO PDF and the local Stacks source. No SGA source is used.

## Findings and changes

The statement is retained exactly. It asks for arbitrary smooth scheme maps, not just toric/monomial maps, and includes finite disjoint unions and retention of ordered ideals. I therefore construct the rule first on all reduced finite-type Q-schemes and restrict only at the end. No independent affine or component resolutions are chosen.

There is an initial-level convention issue in a literal reading of ILO VIII 2.3.3 and 2.3.12: a normalized blowup of the unit ideal on a nonnormal scheme is its normalization, rather than the identity. For example A=Q[t^2,t^3] has Bl_(1)(Spec A)^nu=Spec Q[t], which is not Spec A. One cannot merely say that normalization commutes with deletion of every unit-ideal stage on arbitrary reduced inputs. This does not dispute the existence statement of the item. Steps 1--2 normalize ordinary resolution towers only on normal starting schemes, where deletion is valid at every level. Step 3 first performs a canonical normalized blowup of the conductor on a nonnormal input, then uses that normal-input construction. A unit conductor forces normality, so the optional first stage is also safe to delete. This preserves the intended normalized resolution route while spelling out the literal unit-center convention. I do not assert that the normalized blowup of the conductor equals the finite normalization: in higher dimension it can be a further modification.

The nearest blueprint ancestor is lem-trf-local-term-locality, through the assigned historical alteration branch. I read the current main-20261015 node and the sk-i-curve-zero unit: their corrected contracting-correspondence argument is not replaced. This item is a generic input already assigned below the historical fan-resolution branch, not the unit's key theorem. I leave the unit and chapter records unchanged. Whole-blueprint searches for desingularization, regular centers, normalized blowups, conductor, toric, and monoid algebra found no blueprint statement duplicating any proposed child.

## Source readings and the new inputs

For the item I read ILO Expose VIII 2.1.1--2.1.11 (printed pp.86--88), 2.2.1--2.2.12 (pp.89--91), 2.3.1--2.3.17 (pp.91--95), and 3.2.19 (p.106). The nonnormal initial-level refinement is my argument, so proof_origin.by is agent; the proof does not claim to be verbatim ILO.

For lem-trf-smooth-functorial-ordinary-resolution I read Theorem 2.3.10 with the functorial tower conventions 2.3.4 and Remark 2.3.5. Finite-type Q-schemes fall in its reduced quasi-excellent domain, including nonseparated schemes; I imposed no extra separatedness or saturation hypothesis. This is an unsplit specialization of the ordinary theorem, not the normalized toric theorem being delivered.

For lem-trf-normalized-blowup-calculus I read ILO 2.2.3--2.2.9, especially Proposition 2.2.4 and Lemma 2.2.9. I also read morphisms.tex Tags 035Q (lemma-normalization-normal), 035S (lemma-nagata-normalization), and 0H7D (lemma-normalization-trivial), and divisors.tex Tags 0805 (lemma-flat-base-change-blowing-up) and 0806 (lemma-universal-property-blowing-up). These establish the familiar one-center normalization comparison and its canonical uniqueness; the child leaves the proof of that comparison for its own split. Its universal property is restricted to normal sources taking generic points to generic points, and centers are nowhere dense. Smooth comparison is only invoked for finite-type Q-schemes. I do not confuse a relative normalization of an arbitrary morphism with absolute componentwise normalization.

For lem-trf-conductor-smooth-base-change I read algebra.tex Tag 07T8, lemma-annihilator-flat-base-change, and morphisms.tex Tags 035P, 035S, 0H7D with ILO 2.2.9. The deduction to be split below this child is as follows. Locally the finite normalization is an injective finite ring map A -> B. Its quotient C=B/A is finite; Ann_A C localizes by 07T8, hence defines a coherent ideal. C vanishes at a prime exactly when the normalization is an isomorphism there, equivalently when the local ring is normal. The normal locus is dense since the normalization is birational, so its complement is nowhere dense. Under a smooth map A -> A', normalization commutes with that map, giving B'=B tensor_A A'. Flatness identifies B'/A' with C tensor_A A'. The finite-module clause of 07T8 gives Ann_(A')(C tensor_A A')=(Ann_A C)A'. These are equalities of ideals and thus compose. This input is a genuine generic scheme comparison, not a clause asserting resolution or equivariance.

For lem-trf-toric-realization-finite-type I read ILO 3.1.4, 3.1.10(ii), 3.2.2 and 3.2.4--3.2.5, and the torus usage in 2.3.17 and 3.2.19. The underlying argument is that a fine torsion-free chart P embeds in its finite-rank free group completion, so Q[P] embeds in a Laurent polynomial domain; its finite generating set generates the algebra. Finite charts give finite type, and components are the finitely many irreducible components of the monoscheme. The generic group gives a split torus; its products have Laurent polynomial charts, making the projection smooth and surjective and preserving reducedness and finite type. This justifies the larger-domain applications rather than silently assuming a toric scheme is already normal or smooth.

## Review by Q45

I read the statement of every node each step cites, including the full existing definition def-trf-monoscheme-toric-realization, and copied their actual statements to citations.json. The item has no changed hypotheses and none of the new statements contains a proof sketch; their proof and proof_deps are empty. All four children are needed generic inputs and are strictly different from the normalized toric resolution rule.

Step 1 cites the ordinary resolution theorem for the finite ordered tower and regular endpoint, and the one-center normalized-blowup comparison for replacing every positive level by its normalization. That comparison explicitly says B_J(S)=B_(J O_(S^nu))(S^nu), normality, surjectivity/birationality and regular schemes being unchanged. Thus it supplies both the connecting maps and persistence of nonempty nowhere dense centers. The base is expressly normal, so its level-zero normalization is itself.

Step 2 cites those same two statements for smooth comparison before and after normalization. All its normalized levels, including zero, are normal. Thus precisely the unit-ideal stages are identities, and ordered centers, identity comparisons and composition survive deletion. This repairs the initial-level gap rather than invoking an unstated commutation with contraction on a nonnormal scheme.

Step 3 cites the conductor statement for coherence, nowhere density, the normality criterion for a unit conductor, and the normalized-blowup statement for normality and finite type of the first new scheme. It then uses the already constructed tower of Step 1. The first ideal is nonempty as a closed center exactly when it is not the unit ideal. If it is unit the scheme is normal, so deletion is valid. The endpoint of the concatenation is the regular endpoint of the tail.

Step 4 uses the literal ideal equality of the conductor node and the smooth base-change comparison of the one-center node. This produces the smooth map P(Y)->P(X) required for Step 2, with normal source and target. I checked separately X normal, Y normal but X nonnormal, both nonnormal, the empty source, identity, composition and surjective h. Surjective pullback cannot lose any nonempty center, including the preliminary conductor center. The comparison preserves ideals, not merely the isomorphism classes of the underlying blowup maps.

Step 5 uses the toric-realization node for exactly the reduced finite-type domain and for smoothness and finite type of its component tori and their projections. The resolution H is defined on the entire larger family, so its evaluation on T times X is legitimate. The action and projection are both surjective, eliminating synchronization ambiguity. Extending a component torus trivially on the other components retains the single global order of centers. The normalized-blowup node is also cited because its canonical pullbacks are the stage identifications used in this comparison; it is not being used as a definition of smoothness.

Step 6 uses the existing toric definition only for the meaning of ideal invariance, and the one-center normalized-blowup universal property and comparisons for constructing each action lift. The group-law and unit checks use uniqueness on normal dominating sources; they are not assumed merely from an unspecified transport. I checked the first stage, the induction for every later center, the trivial tower, the rank-zero torus, and products of two group parameters. The lift of the action is the map from the common smooth pullback of a single stage. The two composites in each group-law diagram have the same map downstairs and the same invertible pulled-back ideal, so final-object uniqueness makes them equal.

The small cases for the new statements include the empty scheme, a point, a Laurent polynomial ring, a free monoid N^r, the nonsaturated cusp monoid <2,3>, nonseparated finite affine gluings, and a disjoint union of a normal and a nonnormal component. On a normal singular scheme the conductor stage is absent but the normal-input resolution tail need not be trivial. On a cusp it is present; on a smooth map into the normal locus it becomes an identity. No excellence assertion is made about arbitrary DVRs or arbitrary non-Noetherian schemes.

I checked delivery-errors B--E against these files: definitions are either named existing nodes or introduced explicitly; no unsupported source tag stands in for a proof citation; every non-elementary step has actual statement citations; no new child restates the item or its equivariance clause; no child depends on the item, so there is no induced cycle. Mathlib queries were executed only through msearch.py and recorded with their actual results. I inspected the conductor source and the returned monoid-algebra finite-type and domain instances; they do not prove the whole new scheme statements. No source or Lean match has been asserted by a fabricated search. All six steps are shorter than 2000 characters, and none hides another independent lemma beyond the four named inputs. This report supplies the argument and hypotheses for the agent refinement, not only a mechanical checklist.

## Not duplicates

The entries below compare the statements of all existing nodes sharing a cited Stacks tag with either relevant child. The other two children have no same-tag existing nodes. No existing generic smooth comparison for normalized blowups or scheme conductor comparison was found by keyword, source-place and whole-blueprint searches.

lem-trf-conductor-smooth-base-change vs lem-weil-pbc-scheme-theoretic-support: the existing node constructs the annihilator support of a given module; it does not identify the normalization quotient, its nonnormal support or its comparison under arbitrary smooth maps.

lem-trf-conductor-smooth-base-change vs lem-weil-pbc-annihilator-element-flat-base-change: the existing node treats the annihilator of an element of the base ring; the new conductor comparison concerns a finite normalization quotient module and its scheme gluing.

lem-trf-conductor-smooth-base-change vs lem-weil-pbc-annihilator-affine-basic-open: the existing node treats annihilator restriction to one principal open, not normalization quotients and arbitrary smooth base changes.

lem-trf-conductor-smooth-base-change vs lem-weil-pbc-annihilator-localization-finite: the existing node treats localization of an arbitrary finite module, not the normalization quotient and arbitrary smooth pullback.

lem-trf-normalized-blowup-calculus vs lem-sbc-normal-finite-stage-universal: the existing node descends a normal scheme to a finite Noetherian approximation stage; it gives neither normalized blowups nor conductor ideals.

lem-trf-normalized-blowup-calculus vs lem-sbc-normalization-dominant-lift: the existing node lifts a dominant map to an integral normalization, without blowups, smooth comparison or conductor ideals.

lem-trf-normalized-blowup-calculus vs lem-weil-pbc-reduced-algebraic-normalization-field-change: the existing node supplies finite normalization and separable field extension comparison; it gives neither arbitrary smooth scheme pullback of conductor ideals nor the normalized-blowup comparison.

## Unfinished work

No clause of the item remains unproved at this DAG level. The four explicitly listed statement-only inputs remain for later splitting. No Lean was written or compiled, no live repository or launcher file was changed, and no agents were started. Server dry-run and delivery results follow from the mandatory delivery command.
