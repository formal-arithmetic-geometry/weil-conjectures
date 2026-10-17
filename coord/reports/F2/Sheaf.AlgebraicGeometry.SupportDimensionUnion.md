## What changed

Proved `AlgebraicGeometry.support_dimension_union` in
`Sheaf.AlgebraicGeometry.SupportDimensionUnion`, preserving its signature, visibility,
public imports, and existing docstrings. Added fully proved private helpers for dimension
of finite unions, the image-support bound, affine germ representatives, the open-immersion
adjunction unit, kernel sections, and the filtered-colimit comparison. No other Lean module
is changed, and there are no new public declarations or definition repairs.

The geometric argument follows the section-support route: represent a germ on an affine
etale neighbourhood; apply the existing zero-open lemma; cover the closed complement by
finitely many irreducible closed sets; bound the closures of their image generic points;
and lift the section through its support kernel. The categorical argument uses AB5 to
prove that the colimit comparison is monic, then stalk lifts and geometric-stalk
faithfulness to prove that it is epic by cancellation.

Added the proof-only import
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs` for the existing
restriction/upperStar isomorphism and its adjunction. Updated the existing node's proof,
proof dependencies and proof origin to describe the implementation; removed the two
obsolete top-level tool approvals listed below. The unit's realized statement and proof
steps are empty, so no unit-level route is bypassed.

The module compiles cleanly through `lcompile.py` (approximately five seconds), without
warnings. Search used leanfinder, loogle and Mathlib grep through `msearch.py`, plus source
searches in both library roots. No existing theorem directly supplied the complete result.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.support_dimension_union`
(node `lem-sc-support-dimension-union`). Proved 1 of 1 original sorries; added zero sorries;
zero split-offs. No `sorry` remains in any delivered Lean file.

This is a proof from existing library statements. In particular it still uses the existing
`AlgebraicGeometry.Scheme.etale_section_zero_open` and
`AlgebraicGeometry.topologicalKrullDim_closed_irreducible_eq_trdeg`; their modules are
retained. It does not claim that the target's entire dependency closure is now sorry-free.
Every new private helper, including the concrete restriction of irreducible closed sets,
is fully proved and contains no unproved data choice.

## No longer needed

Removed these direct proof-only imports:

- `Sheaf.AlgebraicGeometry.EtaleLfpAndFiniteType`.
- `Sheaf.AlgebraicGeometry.GeometricStalkColimits`.
- `WeilConjectures.AlgebraicGeometry.GeometricStalkColimits` (present in the current shared
  repository after synchronization).
- `Mathlib.Topology.NoetherianSpace` (available through the retained imports).
- `Mathlib.AlgebraicGeometry.Noetherian` (already publicly available through the
  retained geometric-point module; removed in the second reading).
- `Mathlib.AlgebraicGeometry.Properties` (available through the retained imports).
- `Mathlib.CategoryTheory.Sites.Point.Skyscraper`.
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact` (available through retained imports).

Removed proof-dependency edges to `lem-kun-etale-lfp`,
`lem-kun-stalks-commute-colimits`, and `prop-weil-pbc-geometric-stalks-exact`.
Removed the obsolete top-level `tool_uses` entries `lem-kun-etale-lfp` and
`lem-kun-stalks-commute-colimits`, preserving the remaining approval and its order.
The proof does not use these lemmas. This reports pruning of this item's route; other
parents or transitive imports may still need their modules.

Added the existing Mathlib-leaf dependency
`lem-weil-pbc-abelian-etale-sheaves-grothendieck`: its exact-filtered-colimit clause gives
monicity directly. No new node is needed for this established categorical input.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable definition was found. The original plan uses stronger
machinery than necessary in steps 3 and 7. For step 3, local finite type over the field
makes an affine etale neighbourhood locally Noetherian, and affineness supplies compactness;
no separate quasi-compact map to an affine base chart is needed. For step 7, AB5 and stalk
faithfulness avoid both stalk exactness and preservation of sheaf colimits by stalks.
The torsion hypothesis is unused, as the original proof already observed; it remains in
the theorem unchanged. The existing theorem docstring retains the original plan, while
inline comments, the node and this report explain the shorter implementation.

No new nodes, forced adaptations, statement changes, or change records are required.

## Second reading by F2

1. Compared the only delivered Lean module with the shared version. The complete
   `support_dimension_union` signature is byte-identical, as are its visibility, public
   imports and existing docstrings. The added declarations are private proof helpers;
   no public definition, statement or target meaning changes. Verdict: pass.
2. Read every helper and the main proof, then compiled the delivered module through
   `lcompile.py` without errors or warnings. A scratch copy prints axioms for all twelve
   private declarations and the main theorem. They use only `propext`, `Classical.choice`
   and `Quot.sound`, except that `section_zero_off_bounded` and the main theorem inherit
   `sorryAx` from the existing `etale_section_zero_open`. The dimension-image helper itself
   has only the three permitted axioms. No delivered declaration contains `sorry`, an
   axiom declaration, unsafe implementation, or unproved data choice. Verdict: pass as
   a reduction using the existing open dependency, not a sorry-free dependency closure.
3. There are no split-off statements or new nodes. Checked the actual private constructions:
   irreducible subsets are restricted by subtype preimage, closed supports are explicit
   finite unions of image-point closures, and kernel sections come from their universal
   property. Empty supports and empty schemes are allowed; the dimension induction starts
   with the empty set, and `a = 0` needs no positivity assumption. No arbitrary object is
   chosen from an unproved mere existence theorem. Verdict: pass.
4. Checked the proof from its conclusion downward: AB5 supplies monicity, stalk lifts
   supply epimorphic cancellation, and each lift comes from the section-support kernel.
   Repeated library searches by helper names and concepts and Mathlib searches through
   leanfinder, loogle and grep for dimension of finite closed unions. No theorem found
   replaces this result or the finite-union argument. Confirmed every removed old
   `proof_deps` edge is reported under `No longer needed`. Read the unit record and its
   source: its `realized.statement`, `realized.steps`, and source proof steps are empty;
   the compact-support base-change statement and its route are preserved. The retained
   private imports supply the dimension theorem, zero-open theorem, affine refinements,
   geometric-stalk faithfulness and restriction adjunction. Verdict: pass after removing
   one redundant direct import.
5. Opened the node and checked its proof against the Lean argument and the declarations
   of its dependencies. Its `proof_deps` is exactly the union of the steps' `uses`.
   The Grothendieck-abelian leaf supplies the AB5 input, and the geometric-stalk module
   supplies the jointly faithful variant of conservativity actually used. The only node
   fields changed are `proof`, `proof_deps`, `proof_origin`, and deletion of the two
   obsolete approved `tool_uses`; all other node fields remain identical. Verdict: pass.

Second-reading changes: removed the redundant proof-only import
`Mathlib.AlgebraicGeometry.Noetherian` and recorded it above. The proof is unchanged.
