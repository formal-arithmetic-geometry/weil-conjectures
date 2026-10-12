## What changed

Proved `localStalkSections_affine_vanishing` in
`lean/Sheaf/Paper/LocalStalkSectionsAffineVanishing.lean` without changing its signature or
visibility. The proof builds the cofiltered full subcategory of affine neighbourhoods,
transports the canonical spectrum-of-stalk limit property through `LocalStalkSections.openIso`,
and applies the existing `affineOpenSections_cocone_isColimit`. The concrete filtered-colimit
criterion turns equality of the images of `s` and `0` into vanishing after restriction.
The limit-cone construction follows the already compiled construction in
`Sheaf.Paper.LocalStalkSectionsDescentSections`, without importing that module.

Added proof-only imports of `Sheaf.Paper.LocalStalkSectionsCoconeColimit`,
`Sheaf.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods`,
`Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`, and
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`. Updated the existing node's proof,
proof dependencies, and proof origin to record the implemented route. No interface changes,
new modules, definitions, or nodes.

Validation: the item compiled with `lcompile.py`, without warnings. The delivery dry run
provides the additional static checks and axiom probe.

## Proved and sorry left

Closed the sole local hole: `localStalkSections_affine_vanishing`
(node `new-local-stalk-sections-affine-vanishing`). No `sorry` remains in the delivered module;
zero holes added or split off.

The proof uses the existing, still-sorry declaration `affineOpenSections_cocone_isColimit`
(node `new-local-stalk-sections-cocone-colimit`), which is not modified or delivered here.
This is a proof from existing stated dependencies, not a claim of a sorry-free transitive
axiom closure. `Scheme.fromSpecStalk_limit_affine_neighbourhoods` is already proved.

## No longer needed

No existing import, node, or module is pruned: the original module had only its required
public comparison-map import. Removed a trial explicit import of
`Mathlib.Algebra.Category.Grp.FilteredColimits`, already publicly available through the
existing `Mathlib.Algebra.Category.Grp.AB` import chain.

The proof needs no separate principal-open diagram, localization comparison, or new
adjunction-uniqueness lemma. Those parts of the original informal plan are already covered
by the existing affine-neighbourhood limit and affine-open cocone continuity declarations.
It does not import `WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity` or
`Sheaf.AlgebraicGeometry.EtaleSetSectionContinuity`; neither was an existing dependency to prune.

## Where the brief, the DAG or earlier work was wrong

The item's old proof plan had no named proof dependencies despite requiring non-elementary
continuity and a spectrum-of-stalk limit. Existing declarations already provide both, with
the exact coefficient universe and arbitrary supplied adjunction needed here. The node now
names these dependencies and records the actual limit-cone transport and filtered-colimit
argument. No statement correction is required; the unit's route is unchanged.

The zero-section case follows from the same additive-group argument. An affine neighbourhood
cannot be empty because it contains `x`; no global qcqs hypothesis is introduced.

## Second reading by M3

1. Compared the delivered Lean module and DAG node with the repository versions. The theorem
   signature and visibility are byte-for-byte unchanged; the node records only the implemented
   proof route and dependencies.
2. Compiled the module with `lcompile.py`; it succeeds without errors or warnings. The module
   contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declaration.
3. The sole theorem is a direct proof of the existing target statement. No split-off statements
   or new nodes were added, and the proof uses existing declarations rather than restating the
   target. The imported affine continuity theorem remains the only open dependency.
4. Checked the proof from the target downward: it uses the affine neighbourhood limit, transports
   its cone through `openIso`, applies `affineOpenSections_cocone_isColimit`, and finishes with
   the concrete filtered-colimit representative criterion. The unit route and its realized nodes
   are preserved; no shorter applicable library theorem was found.
5. The DAG `proof`, `proof_deps`, and `proof_origin` match the Lean proof. Imports are minimal
   for the declarations used; the attempted filtered-colimit import was removed because it was
   already available through the existing import chain.

No further changes were needed in the second reading.
