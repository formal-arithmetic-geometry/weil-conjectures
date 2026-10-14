## What changed

Proved `AlgebraicGeometry.schemeMV_composition_right_normalization` in
`Sheaf.AlgebraicGeometry.MayerVietorisCompositionRightNormalization` with its signature
and docstring unchanged. Added the proof-only import
`Sheaf.AlgebraicGeometry.MayerVietorisImageComponentCompositionFactor`.

The proof follows the existing node's plan: lift
`schemeMVImageIso_composition_factor` degreewise to a chain-map equality, apply
`DerivedCategory.Q`, and use naturality of `schemeMVDirectImageLocalization W.ι`.
After unfolding the two explicit localization composites, a proved private categorical
helper cancels the exact Y-restriction inverse/hom factors and assembles the result.
A second proved private helper rewrites termwise objects of composed functors before
elaboration. Neither helper assumes a scheme-specific normalization equation.

Explicit restriction additivity/zero-preservation witnesses, the generic categorical
helpers, and a documented heartbeat budget keep elaboration within the compile limit. The wall-clock compile limit is unchanged; the final local compile is clean (30.4 seconds). No existing
definition, public signature, visibility, or public import changed. The original
DAG proof and proof dependencies already describe this route and remain accurate.
The unit's route is preserved.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.schemeMV_composition_right_normalization`
(node `lem-pc-mayer-vietoris-composition-right-normalization`).

The private helpers `AlgebraicGeometry.complex_comp_obj` and
`AlgebraicGeometry.normalize_right` are also completely proved. No `sorry` remains in
the delivered module; no holes were added or split off. This is a proof, not a decomposition.

The argument has no cover, nonempty-open, or injectivity assumption. It applies unchanged
to empty/full opens and identity morphisms by the same functoriality, naturality, and
inverse-isomorphism identities.

## No longer needed

None. The original statement import is required, and the only added proof import is
used by the degreewise factorization. All four existing proof-dependency nodes remain
needed. No module or node is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The prescribed degreewise factorization is already
proved in the library. Its compiled module was absent from the initial local snapshot
and became available with the regular snapshot refresh. No dependency was copied,
modified, or restated to work around that delay.

## Second reading by N1

1. **Repository comparison.** Compared the delivered module with the repository version.
   The theorem signature, definitions, visibility, and existing declarations are unchanged;
   only a proof-only import, private proof helpers, and the theorem proof were added.
   Verdict: pass.
2. **Compilation and proof status.** Compiled the delivered file with `lcompile.py`.
   It compiles cleanly, contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`, and the private helpers are proved by categorical identities.
   Verdict: pass.
3. **Statements and split-offs.** No statements were split off and no new DAG nodes were
   added. The original target is proved directly using the existing image-component
   composition factorization; the private helpers are strictly internal reductions.
   Verdict: pass.
4. **Pruning and route.** The added import is used by the degreewise factorization, all
   original proof dependencies remain needed, and the unit route through image-component
   composition is preserved. No shorter unused import or dependency was found.
   Verdict: pass.
5. **DAG agreement.** The proof uses exactly the existing node's stated dependency and
   follows its degreewise/naturality/cancellation plan. The target statement and unit
   realization are unchanged.
   Verdict: pass.

No further changes were required by this second reading.
