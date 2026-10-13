## What changed

Proved `AlgebraicGeometry.exists_open_of_generic_fibre_partial_iso` with its original
signature and visibility. Added two proof imports, `GenericFibreAffineOpenLift` and
`GenericFibreIsoSpreadBaseOpen`, and updated its proof docstring and DAG proof to match.

Both new modules contain fully proved public supporting theorems. They construct the
cofiltered diagram of affine neighbourhoods of the generic point and identify its limit
with the spectrum of the generic residue field, using the existing proved
`Scheme.fromSpecStalk_limit_affine_neighbourhoods`. The affine-open theorem applies
`exists_isAffineOpen_preimage_eq` and transports the resulting open through the base
restriction. The isomorphism theorem applies the source library's
`exists_iso_of_isPullback`, the wrapper of morphism descent and eventual equality.
Their private helpers construct concrete diagrams and cones; the only choices are
unique universal-property maps inside proofs.

The main proof chooses one affine neighbourhood inside the partial-isomorphism source
and takes its image on both sides. It lifts these opens, descends their isomorphism,
and builds the desired open immersion and the explicit generic-point range witness.
No existing interface changed and no forced adaptations were needed.

Validation: all three modules compiled cleanly in dependency order (11.5 s, 12.9 s,
2.3 s in the final axiom-check run). `#print axioms` for all three public theorems
reported exactly `propext`, `Classical.choice`, and `Quot.sound`. Edge cases: the two
supporting theorems allow empty generic opens/fibres; only the main theorem needs
nonemptiness to choose its range witness. No integrality or reducedness is required
of X or Y, and no argument discards vertical components.

## Proved and sorry left

Closed the item's sole hole:
`AlgebraicGeometry.exists_open_of_generic_fibre_partial_iso`
(`lem-sbc-generic-fibre-partial-iso-spread-open`).

Also proved the two newly stated supporting theorems:
`AlgebraicGeometry.exists_affine_open_lift_of_generic_fibre`
(`lem-sbc-generic-fibre-affine-open-lift`) and
`AlgebraicGeometry.exists_base_open_iso_of_generic_fibre_iso`
(`lem-sbc-generic-fibre-iso-spread-base-open`).

No `sorry` remains in the item or any delivered module. No holes were added or split
off: this is one original hole closed, rather than a decomposition into new holes.
The axiom check confirms that no transitive `sorryAx` is used either.

## No longer needed

No original imports were removed, and the original node had no proof dependencies,
so no previously queued nodes or modules are newly pruned. The argument does not need
the original plan's independently chosen source and target principal charts and their
intersection: the image of a single affine chart is already affine. It also avoids
an explicit finite-generator denominator computation by using the proved limit API.
An exploratory `Mathlib.AlgebraicGeometry.FunctionField` import in the new modules
was removed before final compilation because it was unused.

## Where the brief, the DAG or earlier work was wrong

The original DAG supplied a valid prose argument but no proof dependency records.
The delivery records the actual reused limit and descent theorems, along with the
two generic-fibre specializations. The off-unit use of `thm-pd-spreading-out` is its
standard 01ZM morphism-descent/eventual-equality tool, implemented by the already
proved `exists_iso_of_isPullback`; it does not bypass the slicing unit's statement
or any realized unit step. No mathematical statement was disputed or weakened.

LeanSearch was attempted for both new statements but returned Internal Server Error.
The new nodes record these failures honestly together with successful LeanFinder,
Loogle and grep searches; local source reading located the general limit lemmas.

## New nodes

`lem-sbc-generic-fibre-affine-open-lift`, in
`lean/Sheaf/AlgebraicGeometry/GenericFibreAffineOpenLift.lean`: an affine generic-fibre
open lifts to an affine total-space open, together with an isomorphism respecting both
projections. This strictly smaller geometric step is fully proved. Source: Stacks
Tags 01Z4 and 01Z6, with the generic-point limit identified by the stalk theorem.

`lem-sbc-generic-fibre-iso-spread-base-open`, in
`lean/Sheaf/AlgebraicGeometry/GenericFibreIsoSpreadBaseOpen.lean`: a whole affine
finite-presentation generic-fibre isomorphism over the residue field descends over a
base neighbourhood. This strictly smaller descent step is fully proved. Source:
Stacks Tag 01ZM, parts (2) and (3). Both new nodes retain the original chapter/unit
and trace their origin through the item's common-open step to `sbc-lem-slicing`.
No change records are needed because no existing statement or definition changed.

## Second reading by T4

1. Compared the delivered item module with the repository version. The existing
   theorem signature is byte-for-byte unchanged; only its proof, proof imports and
   explanatory docstring changed. The two added modules are new supporting nodes.
   Verdict: pass.

2. Compiled all three delivered modules with `lcompile.py --all`. There are no
   `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations.
   The public declarations have only the permitted axioms (`propext`,
   `Classical.choice`, and `Quot.sound`) when checked with `#print axioms`.
   Verdict: pass.

3. Checked both split-off statements against their constructions and edge cases.
   The affine-lift statement permits empty affine opens and imposes no finite
   presentation assumption; the base-open isomorphism statement permits empty
   fibres and uses exactly the local finite-presentation hypotheses needed for
   descent. Neither duplicates an existing library declaration. Verdict: pass.

4. Read the proofs from the target downward. The target uses one affine chart,
   the affine generic-fibre lift, and the whole-fibre isomorphism descent. The
   imports are proof-only imports, and the DAG records the actual dependencies;
   no old proof dependency is unused. The realized unit route is retained through
   the common-open/slicing node. Verdict: pass.

5. Checked the three DAG nodes against the Lean declarations, including names,
   statements, proof steps, proof dependencies, origins, chapter and unit. The
   target node records the two helper nodes as its dependencies and no statement
   was weakened or strengthened. Verdict: pass.

Changed only this report section; no proof or statement repairs were necessary.
