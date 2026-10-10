# Stage-1 worker report

1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-flat-precompose-pus.json`: statement node, split with three formal mate-calculus steps; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement excerpts for every cited node in each proof step.
- `report.md`: this report.

2. Attachments: none.

3. WANTED: `literature/stacks-project/duality.tex`, Tag 0AA8 (Lemma 48.6.2), final compatibility sentence in case (1), for `lem-sc-flat-precompose-pus`; the repository contains only the citation index, so I checked the imported node statement and its blueprint place instead.

4. The imported item was unsplit and had the correct explicit two-map conclusion. The existing canonical base-change definition already expands the map `c` into unit, conjugate-mate inverse, and counit, while the existing global RHom adjunction states the natural Hom identifications needed to transport that composite. Creating a child node for mate calculus would duplicate a clause of the item, so the formal calculation remains in the proof steps. The Mathlib searches found only generic mate/pushforward declarations and no exact scheme-level theorem.

## Review by M1

I checked the item against the imported Tag 0AA8 case-(1) sentence and the blueprint ancestor `lem-sc-finite-duality`. The statement's square, affine hypotheses, right adjoints, beta isomorphism, object `M`, object `K`, and both explicitly listed morphism composites are unchanged. I opened `def-sc-duality-equation-base-change-map`: it states the exact unit/conjugate-of-beta/counit formula for `c`, which is the input used in Step 1 and the triangle-identity comparison in Step 2. I opened `lem-pc-global-hom-adjunction`: it states the natural global derived Hom adjunction for both `a` and `a'`, which is used in Steps 1--3 to move between the two RHom descriptions. Step 3 uses only the defining adjoint characterization of the algebraic RHom base-change map already named in the item; no claim that it is an isomorphism is introduced. The elementary marking is limited to the triangle-identity mate calculation in Step 2; the definition expansion and final transport through natural adjunctions remain non-elementary. I searched the whole DAG for mate/base-change compatibility and found no smaller existing statement, and ran LeanFinder, Loogle, and Mathlib grep searches for this item; the hits were generic only. I also checked the small identity-square case: beta and theta are identities, so both composites reduce to the ordinary RHom pullback comparison.

5. What I could not finish: the cited Stacks source file is not present in this checkout, so direct line-by-line source verification must be done by the second reader using the tag citation.

## Second reading by M1

- Item statement: checked against `duality.tex` Tag 0AA8 (Lemma 48.6.2), case (1) RHom comparison and final compatibility diagram; hypotheses and both composites agree, including affine bases and the assumed base-change isomorphism.
- Step 1: checked the expansion against the definition node and the source's unit/mate/counit construction; cited statements provide the displayed factors and adjunction identifications.
- Step 2: checked against the source's mate-calculus comparison and the cited definition/adjunction statements; the triangle-identity calculation is the only elementary portion.
- Step 3: checked against the source's final algebraic RHom base-change comparison; the cited adjunction and base-change-map definitions supply each transport.
- New nodes: none; the item is the sole statement node and no independent child lemma or Mathlib leaf is introduced.
- Changed `created.item` from the parent affine-basechange item to `lem-sc-flat-precompose-pus`, because delivery ownership must identify this item.
- Small cases checked: identity square reduces both maps to the ordinary RHom pullback comparison; zero objects and affine field base changes give the same zero/identity maps.
