## What changed

Added `Sheaf.Paper.AffineOpenSectionsCanonicalColimit`, isolating the affine-site
continuity argument as `affineOpenSections_exists_canonical_colimit` with one
named geometric hole. The target module imports it and proves
`affineOpenSections_cocone_isColimit` by applying the canonical result and
extensionality of natural transformations using `hν`.

## Proved and sorry left

`affineOpenSections_cocone_isColimit` is proved. The new theorem
`affineOpenSections_exists_canonical_colimit` remains `sorry`; its node is
`new-local-stalk-sections-canonical-colimit`.

## No longer needed

None; the target's existing imports remain required by its public statement.

## Where the brief, the DAG or earlier work was wrong

The DAG's geometric continuity step cannot be discharged from the available
Lean declarations in this session. It was split into the canonical-cocone
existence theorem, while the parent transport and uniqueness argument is fully
implemented.

## New nodes

`new-local-stalk-sections-canonical-colimit` records the isolated affine-site
continuity theorem and its source at Stacks Tag 03Q6.

## Second reading by T3

1. **No accidental interface changes.** Diffed `LocalStalkSectionsCoconeColimit.lean` against the repository version. The existing theorem signature and documentation are unchanged; only its proof and a proof-only import were added. The new canonical theorem is isolated in a separate module and node.

2. **Proof and compilation.** Compiled both delivered modules with `lcompile.py --all`; both compile without errors or warnings. The only remaining `sorry` is the named theorem `affineOpenSections_exists_canonical_colimit`, documented with its Stacks Tag 03Q6 source and represented by node `new-local-stalk-sections-canonical-colimit`. No forbidden declarations or hollow definitions were introduced.

3. **Split statement review.** The new theorem is a strict lower-level decomposition: it supplies existence of the canonical cocone and its colimit property, while the target additionally identifies an arbitrary supplied cocone by `hν`. Its component formula matches the target's required formula exactly, and the target proof uses extensionality to transport the colimit witness. It does not restate the target.

4. **Pruning and route.** The target's existing public imports remain needed for its signature; the canonical module is imported privately because only the proof uses it. No old proof dependency was removed, and the affine continuity route and its unit remain represented by the new node.

5. **DAG agreement.** The new node records the theorem's exact Lean statement, source, proof plan, dependencies, module and declaration. The target node's proof fields now describe the canonical existence step followed by natural-transformation extensionality and colimit transport.

Changed during second reading: added this review record only; no Lean declarations or statements required repair.
