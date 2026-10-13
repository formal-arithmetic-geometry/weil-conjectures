## What changed

Proved `AlgebraicGeometry.Scheme.picardDirectImageSectionMap_bijective` with its
signature and all existing public imports unchanged. The proof uses the existing
`isIso_derivedBaseChange_of_flat_invertible` on the iterated cartesian square,
`isIso_canonicalSinglePullbackMap`, and the proved source-library
`homologyFunctor_map_bijective_of_isLE_of_isGE`. It composes explicit Hom
bijections, evaluation at one, and the invertible restriction from inverse-image
top to top; `Functor.map_comp` identifies the composite with the fixed map.

Added proof imports:
- `Sheaf.AlgebraicGeometry.Picard.FlatInvertibleCanonicalDerivedBaseChange`
- `WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`
- `WeilConjectures.AlgebraicGeometry.Modules.Ext`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`

Updated the theorem docstring and its existing node's proof, proof_deps and
proof_origin to describe this argument. The three elaboration options are local
to the proof, preserving every file-wide command of the original module. There are no interface changes, forced
adaptations, new declarations or new nodes. The cube unit's statement and steps
are preserved; this is a shorter argument below the unit level. The base-change
result is used as a generic tool, not to replace a unit's statement or step.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.Scheme.picardDirectImageSectionMap_bijective`
(node `lem-sc-picard-direct-image-section-map-bijective`).

No sorry remains in the delivered module. No holes were added or split off.
The ordinary lcompile.py check passed without warnings. The delivery axiom probe
reported `SHEAF-PROBED 1`, with no SHEAF-AXIOM or SHEAF-SORRY findings.
This is a proof from existing declarations, not a claim that their entire
transitive dependency closure is sorry-free. No definitions or statements changed.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`
- `Sheaf.AlgebraicGeometry.DerivedAdjoint`

Removed direct proof dependencies:
- `lem-pc-rf-perfect-base-change`
- `lem-pc-ringed-spaces-derived-adjoint`

The proof does not need a perfectness witness, localized-open derived-category
instances, or a newly chosen derived adjunction. The existing flat-invertible
base-change theorem suffices. The canonical degree-zero mate-square theorem is
not applied; its module stays reachable through the section-map definition,
because it supplies `canonicalDirectImageH0Iso`. The existing single-pullback
comparison remains needed. Pruning these direct edges does not assert that the
removed modules leave the complete targets' import closure: other users may
still reach them. No public imports were removed.

## Where the brief, the DAG or earlier work was wrong

The planned perfect-direct-image application requests unnecessary perfectness
and extra localization/additivity instances. Existing canonical flat-invertible
base change handles this square directly. The last step can use the already
proved source-library homology bijection for a nonpositive source and a
nonnegative target instead of deriving a new adjunction identification.

The initial compile could not find the recently landed section-map module's
compiled file. The ordinary cache refresh supplied it; no dependency was copied,
recompiled, or replaced to bypass this transient failure.

The proof uses no chosen point or nonemptiness assumption, so empty schemes and
zero section groups require no exceptional cases. All choices of data already
occur in the fixed map (unique left-adjoint comparisons and inverses of proved
isomorphisms); this delivery creates no new data chosen from an existence hole.

Repair of the previous attempt: its three file-wide elaboration options were
classified as an interface change. Scoped
`backward.isDefEq.respectTransparency`,
`backward.isDefEq.respectTransparency.types`, and `maxRecDepth` inside the theorem's
proof instead. The theorem compiles without warnings through `lcompile.py`, and
`leanindex.interface_changes` reports an empty list. No lint was disabled and no
tool was edited. The launcher now excludes warnings from its generated probe and
allows a worker dry run whose only pending check is the independent second reading.
The second reader's section is intentionally left for that reader.

## Second reading by Q4

1. Interface: PASS. Read the complete repository/sandbox Lean diff and node diff.
   The existing theorem signature is byte for byte unchanged; there are no new
   declarations or changed definitions, public imports, visibility, or file-wide
   options. Only proof imports, the proof, and its explanatory docstring changed.
   No change record is needed. No open change record names this item.
2. Proof: PASS. Independently compiled the delivered module through lcompile.py
   without errors or warnings. A scratch copy with `#print axioms
   AlgebraicGeometry.Scheme.picardDirectImageSectionMap_bijective` compiled and
   reported exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The last is from existing open dependencies, not a new hole in this delivery.
   Checked the actual section-map definition: the coefficient comparison, source
   isomorphism, H0 comparison and restriction are the same maps; the final
   `change`, `Functor.map_comp`, associativity and `rfl` identify the composite.
   The delivered module has no sorry or forbidden declaration. The only chosen
   data in the proof are the same tensor-pullback adjunctions as in the fixed map;
   their left-adjoint comparisons are unique, not arbitrary existence witnesses.
3. Split statements: PASS (none). One original named hole is closed, zero holes
   are added, and no new node or theorem restates the item. The proof requires
   neither a point nor nonemptiness; empty schemes and zero section groups do not
   invalidate any of the categorical equivalences or the top-open restriction.
4. Route and pruning: PASS. Read the existing flat-invertible base-change theorem,
   degree-zero H0 comparison, source-library homology bijection and evaluation
   equivalence. Independent rg searches in both Lean roots and msearch grep for
   Hom congruence/homology bijections found the ingredients already used, with no
   shorter map-specific theorem. Each added proof import supplies a used result;
   all remain plain imports. Every old proof_deps entry is either retained or
   listed under No longer needed. The mate-square node remains because it owns
   canonicalDirectImageH0Iso, although its square theorem is not used. The cube
   unit's statement, steps and realized record are unchanged (the repository's
   realized lists are empty); this auxiliary reduction bypasses no unit step.
5. DAG: PASS. The node's four proof steps track invertibility/cartesianness,
   canonical base change and Hom conjugation, H0, and evaluation/restriction.
   proof_deps equals the union of their uses and points to the actual imported
   declarations/definitions; proof_origin describes the implemented route.
   All other node fields remain unchanged, and there are no new nodes to audit.

Second reading changed only this report, adding the independent review and axiom
result. No Lean or DAG repair was needed.
