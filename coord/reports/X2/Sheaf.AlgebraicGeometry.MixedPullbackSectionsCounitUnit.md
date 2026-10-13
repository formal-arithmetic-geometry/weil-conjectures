## What changed

Replaced the proof of `AlgebraicGeometry.mixedPullback_sections_counit_unit` with the
node's adjunction/naturality calculation. The supplied Hom-equivalence equation gives
the derived unit factorization. Naturality of sections and normalized Leray, followed
by Leray's defining unit equation, proves the homotopy identity. The ordinary adjunction
unit and scalar-restriction localization factors then identify it with the original
complex equation. A proved private helper `sectionsComplexUnit_eq` simplifies the
identity components of the quotient factors. No existing signature, definition,
visibility or import changed. The node copy records the actual calculation.

The mathematical inputs remain Stacks Tags [079W](https://stacks.math.columbia.edu/tag/079W)
and [0D5T](https://stacks.math.columbia.edu/tag/0D5T), and the already recorded normalized
Leray theorem. The formal argument uses no affine, boundedness, K-flatness or
invertibility hypothesis and keeps the two derived-localization universes independent.

## Proved and sorry left

Closed: `AlgebraicGeometry.mixedPullback_sections_counit_unit`
(`lem-sc-mixed-pullback-sections-counit-unit`), the sole original hole.
Added holes: none. Remaining holes in the delivered module: none.
The private helper is proved. Existing dependencies are reused without changing them;
this does not assert that their transitive proof dependencies are sorry-free.

## No longer needed

None. Both public imports supply objects appearing in the unchanged statement:
`MixedAffineSectionsComplexUnit` supplies the sections comparison and
`MixedGlobalSectionsDirectImageIso` supplies normalized Leray. The sole planned proof
dependency, `lem-sc-mixed-global-sections-direct-image-iso`, remains needed. No planned
node or module was bypassed, and no new proof dependency was imported.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped before formalizing the naturality calculation. Its sandbox
contained an unsuccessful direct `simpa` from the Hom-equivalence hypothesis, which
alone cannot prove an equality after applying sections and Leray. The completed proof
supplies those intervening naturalities and the complex-factor identifications.
No statement error was found. The unit record has no realized step bypassed by this
calculation. No new node or forced adaptation is required.

## Second reading by X2

1. Compared the delivered module and node against the repository versions. The theorem signature, definitions, visibility, and imports are unchanged; only the proof and its DAG proof route were updated. Verdict: pass.
2. Compiled the module with `lcompile.py`; the proof has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The private helper and target use only the permitted foundational axioms transitively. Verdict: pass.
3. Checked the target and proof dependencies with repository search and Mathlib/library declarations. No duplicate theorem or weaker restatement was introduced, and no new split-off statement was added. Verdict: pass.
4. The proof follows the unit route through the normalized Leray comparison, then performs the quotient-factor reduction. Removing the initial `dsimp only` shortens elaboration without changing the argument; all planned imports remain needed. Verdict: pass.
5. The node proof steps, `proof_deps`, and `proof_origin` now match the Lean proof, and the unit's realized route is preserved. Verdict: pass.

Changed only the proof elaboration by removing a redundant `dsimp only`; this reduces compilation below the delivery timeout. No statements, definitions, imports, nodes, or dependencies were otherwise changed.
