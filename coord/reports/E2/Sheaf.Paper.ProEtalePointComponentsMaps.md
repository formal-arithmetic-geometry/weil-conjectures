## What changed

Proved `AlgebraicGeometry.ProEtale.proEtale_point_components_maps` in
`lean/Sheaf/Paper/ProEtalePointComponentsMaps.lean`, with its signature and visibility
unchanged. The proof reuses the already proved private
`profiniteLocallyConstantHomEquiv` from `ModuleObject.Basic` through a proof-only
`import all`. It transports that equivalence from prime spectra to affine schemes,
uses the defining pullback of `X[S]`, and factors continuous maps through connected
components. Private, fully proved helpers give the pointwise formula and both
naturality identities. The weak-contractibility hypotheses are unnecessary for this
stronger affine argument and remain in the public statement.

Updated the item's node to match this route. Added one definition node recording the
existing closed ring-map equivalence, so this reused tool has a DAG attachment.
No existing definition, statement, public import, or other module changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.proEtale_point_components_maps`
(`lem-weil-pbc-proetale-point-components-maps`). No holes remain in the module.
No holes were added, and no obligations were split off.

The complete file compiles without warnings using `lcompile.py` (about 3 seconds).
`#print axioms AlgebraicGeometry.ProEtale.proEtale_point_components_maps` reports
exactly `propext`, `Classical.choice`, and `Quot.sound`. In particular the reused
private equivalence has no reachable `sorry`. The constructions work without a
nonempty source, nonempty target, or nonzero coordinate ring; the original statement
retains every universe and weak-contractibility binder.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen`.
- `Mathlib.Topology.Spectral.Basic`.
- `Mathlib.AlgebraicGeometry.Properties` (second reading: redundant via `import all`).
- `WeilConjectures.Topology.SpectralSpace.ConnectedComponent` (second reading:
  redundant via `import all`).

The proof no longer uses `lem-galois-coproduct-copies-morphisms-clopen` or its finite
coproduct gluing argument. It also does not use the preservation-of-limits or finite
coproduct clauses of `lem-weil-pbc-profinite-test-object-functor`, nor the general
finite-quotient presentation, limit universal-property assembly, or finite-stage
naturality route. The public import `Sheaf.Paper.ProfiniteTestObjectFunctor` remains
unchanged as part of the existing statement interface; its theorem is not a proof
input. Thus all three old proof dependencies absent from the new proof are explicitly
accounted for: `lem-galois-coproduct-copies-morphisms-clopen`,
`lem-weil-pbc-profinite-test-object-functor`, and `def-weil-spectral-space`.
The separate `def-weil-spectral-space` proof edge was removed: the proof uses
the already proved component-space instances directly. The qcqs-scheme and component
clopen-intersection nodes remain as the topology inputs. No unit statement or unit
proof step is bypassed; this node is not among the unit's `realized` entries.

## Where the brief, the DAG or earlier work was wrong

The old finite-quotient plan is valid but unnecessarily long for this item. The landed
F2 proof in `ModuleObject.Basic` already supplied the core affine Hom equivalence as a
private definition. Lean's module-system `import all` makes it usable within this
proof without publishing it or adapting any consumer. The original theorem docstring
records the original plan; the updated DAG describes the actual compiled proof.

The reused equivalence did not have a DAG attachment. The added node records the
existing construction rather than introducing another definition. Its branch is
`sheaf-dag`: this helper was added in the adopted source-root library by the F2
landing, rather than being present in the original upstream snapshot. LeanSearch
returned an Internal Server Error; this is recorded as unavailable. Loogle,
LeanFinder, Mathlib grep, repository grep, and blueprint searches were also run.

## New nodes

`def-weil-pbc-profinite-locally-constant-hom-equiv` attaches the existing closed
`AlgebraicGeometry.ProEtale.profiniteLocallyConstantHomEquiv` in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`. It adds neither a Lean file
nor a proof obligation. It is the canonical equivalence constructed using
`LocallyConstant.liftPrimeSpectrum` and `profiniteSpectrumProjection`. The node
records its formulas, source, searches, and blueprint ancestry. No change record is
needed: all existing signatures, definitions, visibility, and public imports are
unchanged.

## Second reading by E2

1. **Interface: pass.** Read the repository/sandbox diff for the sole delivered Lean
   module. The bytes from `theorem proEtale_point_components_maps` through `:= by`
   agree exactly. All original universes, affine and weak-contractibility binders,
   the conjunction of three topological properties, the single family of
   equivalences, and both naturality identities remain. Existing docstrings and
   both public imports are unchanged. Only private helpers, proof imports and the
   proof were added or changed; there are no interface changes or adaptations.

2. **Proof and data: pass.** Independently compiled the delivered module with
   `lcompile.py`, without errors or warnings. A scratch copy with `#print axioms`
   for the public theorem and the reused private `profiniteLocallyConstantHomEquiv`
   reports exactly `propext`, `Classical.choice`, and `Quot.sound` for each. Read the
   latter's forward/inverse constructions and proofs in `ModuleObject.Basic`,
   lines 220–307, and `liftPrimeSpectrum` with its localization characterization in
   `RingTheory/Spectrum/Prime/LocallyConstant`, lines 317–423. The choices there
   determine their elements uniquely by equality in all prime localizations;
   the existence proofs are closed. Every new equivalence is explicitly composed
   or constructed, with proved inverse laws. No holes or forbidden declarations
   occur in the delivered module. In `relativeMapEquiv`, terminality supplies the
   pullback compatibility, and `f.w` supplies the second projection inverse law.
   The representative formula is checked after affine transport, so the target
   naturality calculation uses the same equivalence as source naturality.

3. **Split statements and reuse: pass.** No statement is split off and no hole is
   added. The new definition node records an existing, closed equivalence; it does
   not assert a missing version of this item. Checked its exact private signature
   and both directions against the source. Empty S gives the zero locally constant
   ring: maps to R exist exactly when R is zero, matching maps Spec R → empty S.
   For R zero both sides are singleton; for singleton S both sides are singleton.
   No nonempty or nontrivial instance is assumed anywhere. Independently searched
   Loogle for `"connectedComponentsLift"` and LeanFinder for the Stone-duality
   formulation of ring maps out of locally constant integer functions. Loogle
   supplies the lift and uniqueness lemmas already used here; LeanFinder supplies
   comap/evaluation operations, not the Hom equivalence. Direct `rg` on Mathlib,
   `lean/Sheaf`, the upstream geometry/topology modules, and DAG nodes found no
   duplicate closed correspondence or existing node for this private helper.

4. **Route, imports and pruning: pass after cleanup.** The public proof opens the
   original hole directly: the component-space instances prove its first conjunct;
   the closed ring correspondence, affine isomorphism and pullback universal
   property prove its second. The two pointwise naturality proofs are fully
   written. The finite-stage gluing route is therefore unnecessary. Checked all
   five old `proof_deps`: the qcqs-scheme and clopen-intersection inputs remain,
   and the other three are individually recorded above as no longer used.
   Read `dag/units/sk-thm-properbasechange.json`: its realized statement nodes are
   torsion assembly/bounded-below base change, and its three realized steps are
   projective-line PBC, reduction, and torsion assembly. This auxiliary Hom
   computation is none of them; replacing its internal route bypasses no unit
   statement or step. Tested removal of the direct Properties and ConnectedComponent
   proof imports in a scratch copy; it compiles because `import all Basic` already
   makes those dependencies available. Removed both from the delivered module.

5. **DAG: pass.** Diffed the existing node: only `proof`, `proof_deps`, and
   `proof_origin` change. Their five steps match the topology instances, ring-map
   equivalence/affine transport, relative pullback, target naturality and source
   naturality in Lean. The union of step uses is exactly `proof_deps`. The new
   definition node has the item's chapter and unit, blueprint ancestry, a source
   at the actual closed construction, search records, creation data, and the
   verbatim existing Lean signature. It adds no module or proof obligation.

Second reading changed only the two redundant proof imports, the complete pruning
account above, and this review section. The proof itself needed no repair.
