# Stage-1 report: lem-sfb-closed-intersection-vertex-contraction

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-closed-intersection-vertex-contraction.json`: existing statement, now split into eight proof steps; no Mathlib match.
- `citations.json`: 20 step/node entries, quoting the cited statements verbatim.
- `report.md`: this report. `write_split.py` is a sandbox-only preparation script.

There are **0 new nodes and 0 Mathlib leaves**. The proof reuses the already existing arbitrary-ring open-closed and base-change results and writes the finite signed calculation directly. It does not replace a clause with a renamed new lemma.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and for closed intersections, insertion homotopies and contractions. The existing `AlgebraicGeometry.alternatingCechSheafAugmentation_restrict_homotopyEquivalence` in `AlgebraicGeometry/AlternatingCechSheafInsertionHomotopy.lean` is about structure-sheaf modules and **open** intersections; it does not state this item's pro-etale arbitrary-ring closed-restriction comparison. Thus it is not an attachment. No Lean was written or compiled.

## WANTED

None.

## Issues found and changes made

The item has no statement error requiring correction; its statement is unchanged. Its inherited proof was empty. I supplied the proof, including the finite-union check for quasi-compact complements of intersections, the actual unit normalization, local detection, the closed-base-change comparison on affine bases, and the signed insertion calculation at both endpoint degrees. In particular no covering assumption was added.

The nearest-blueprint-ancestor command prints `None`, consistent with the inherited `blueprint.from.node = null`. I retained that value and its detailed inherited `from.place` and `via` chain, and searched for equivalent blueprint statements before retaining `same_as = []`. I read the current `literature/blueprint/latest/.../sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3). It gives the higher open-direct-image route, rather than the technical finite closed support calculation; the latter is consequently marked agent-written. The corresponding inherited unit record is filed in `sec-six-functors`, while the item's chapter is `sec-six-functors-basics`; I changed neither record.

The item already carried searches made by its creating group. I retained those and added only searches actually run through `msearch.py` in this session. The logged second semantic phrasing returned the alternating coface-map complex and alternating constant complexes; the former, read in Mathlib/AlgebraicTopology/AlternatingFaceMapComplex.lean, constructs the alternating complex of a cosimplicial object, not the ordered finite closed-intersection diagram or its contraction. The other hits concern connected truncations and constant complexes. The first semantic query returned condensed constructions, presentations, limit sections and Nobeling exactness, none with this closed-unit conclusion. Loogle and the recorded grep returned zero hits. LeanSearch returned augmentation constructors and the Cech conerve, which also lack the closed comparisons. An exploratory logged search under `lem-sfb-closed-intersection-restriction-basechange` returned scheme pullback identities; no such node was created, since the existing arbitrary-ring mate node suffices.

## Unfinished work

None in this one-level split. The independent maintainer review remains part of the delivery workflow.

## Not duplicates

No new nodes were created, so there are no new/existing pairs. The DAG and whole-blueprint searches for closed intersections, closed base change and insertion homotopy led to reuse of existing statements. The existing open-intersection insertion identities have different coefficient categories and indices and were not cited as a substitute for this calculation.

## Review by Q27

I read AGENTS.md, GOAL.md, the three-level route rules in SETUP.md, the worker role, the stage-1 brief and stage document, and sections B through E of delivery-errors.md. I read the item, its parent finite-closed-cover-resolution statement, its chapter/unit records, the latest direct-images blueprint paragraph (3), and the actual Stacks proofs at Tags 09AA (`lemma-closed-immersion`), 09BM (`lemma-closed-immersion-complement-retrocompact-exact`) and 09AH (`lemma-ses-associated-to-open`) in proetale.tex. For the closed comparison I also read part (4) of the current blueprint `det-sf-open-closed-sequence-ring-sheaf.proof.md`. There are no new-node sources to review and no forbidden SGA source is used.

For step 1 I opened all five cited node statements. The affine closed-immersion characterization proves closure under composition from the composite of two surjective ring maps; I made that argument explicit. Closed-immersion base change applies to each iterated intersection. Finite unions of the complementary quasi-compact opens establish exactly the hypothesis of the ringed open-closed node; its arbitrary sheaf-of-rings coefficients are essential here. The quasi-compact base-change node applies to affine restriction and to each closed member without requiring X itself qcqs. Geometric inverse-image exactness explicitly covers transported inverse-image rings, so it proves exactness of the other half of each E, without assuming a flat scalar extension. The union and composite-exactness arguments are written in the step itself.

For step 2 I read the ordinary pro-etale pullback comparison definition, the composite-adjunction unit formula, and the conjugate-isomorphism unit equation. They respectively fix the comparison, identify a composite unit, and remove the ambiguity between two adjoint presentations. The step then writes the restriction composition identities and the pairwise opposite-sign cancellation proving d squared zero. It does not cite the narrower etale inverse-image composition theorem. This is finite matrix algebra from those formulas.

For step 3 I read the localization statement and the two normalization definitions cited. Localization identifies the underlying sites, while the arbitrary ring action is simply restricted on test objects; no assertion about a constant coefficient ring is substituted for the given A. The direct-image comparison is checked explicitly on T by the fibre-product identity, and the unit is checked on inverse-image unit sections. This proves compatibility of the actual arrows, rather than choosing abstract isomorphisms between their sources and targets.

For step 4 I checked the three generic algebra statements: the forgetful module functor gives sectionwise kernels and sheafified cokernels; localized-site restriction preserves both finite limits and finite colimits for a **sheaf** of rings; and an exact functor preserves homology. The cited pro-etale localization statement supplies the test objects. The rest is sheaf separatedness on the open cover T times_X V, explicitly written out. This neither assumes affine overlaps nor asserts exactness of global sections.

For step 5 I checked the precise hypotheses and conclusion of `lem-sf-ring-sheaf-base-change-mates`: its arbitrary-ring coefficient comparison is multiplicative and its beta has the stated counit transpose. Its qcqs hypotheses hold because V and its closed members are affine. The complement is quasi-compact by step 1. I checked the ringed open-closed counit and the ordinary pullback comparison/composite-adjunction formulas used to identify augmentation and faces. The face compatibility follows by transposing both arrows to the same square comparison followed by the same counit, using counit naturality and the composite-unit formula; the statement does not pretend that the mate node itself asserts sequence-arrow compatibility. The identity intersection after adjoining a vertex gives the invertible map via the triangle identity. The factorization Z_a through Z, not mere containment of point sets, is what identifies the degree minus one pullback.

Steps 6 and 7 cite no additional facts: they are the explicit construction and calculation from the maps already proved invertible. I checked the two cases a in J and a not in J, and in the latter wrote the commuting-square equality used to cancel each off-diagonal term. The sign exponents differ by one for b less than a as well as b greater than a. At degree minus one the composite is inverse(t_empty) times t_empty. At the top the full subset contains a and there is no outgoing differential. The singleton empty-output map is the actual closed counit after the augmentation comparison. Every map is linear, and the inverse of a natural isomorphism remains natural. These are the argument of the item itself, not a hidden comparison lemma relabeled as a new node.

Step 8 uses exactly the `j^{-1}i_*=0` clause of the ringed open-closed node. Its vanishing can be restricted further to the complement of Z since every intersection factors through Z. Naturality in M follows for each unit, counit and mate, and hence for their inverses, signed sums and composites. No new base-change hypothesis is used there.

I also checked the scalar signed matrices by Python for every vertex and degree for m=1 through 7; all satisfy dh+hd=1. This tests the signs and endpoint conventions, while the sheaf comparison argument is justified above.

For edge cases I checked m=1, empty X, empty closed members, repeated members, members contained scheme-theoretically in another, and a family that does not cover Z. The last case need not have globally exact augmentation, which is not claimed here: contraction is asserted only after restricting to one family member. Nilpotent scheme structures cause no change to the fibre-product identities used, because these are identities of monomorphisms, not replacements by their topological supports. All eight steps are shorter than 2000 characters. Their elementary parts are sectionwise identities, finite unions, finite signed-matrix cancellations or sheaf separatedness after the cited structural results; every structural non-elementary input has a cited statement and a verbatim citation entry.

The cross-unit statements are generic tools, recorded in split_report.tool_uses with the exact purpose. They do not replace the unit's direct-image route. I left the statement, source, creation history, inherited search results and all imported fields intact. The requested preflight checks are run only on the server by the provided delivery tools.
