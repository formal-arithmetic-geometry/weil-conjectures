## What changed

Proved `AlgebraicGeometry.Scheme.affine_open_supported_model_exists` in
`Sheaf.AlgebraicGeometry.AffineOpenSupportedModelExists` without changing its signature.
Constructed the canonical chart/over-site equivalence explicitly, proved that its inverse
applied to the restricted shifted object has quasi-coherent homology, and used the existing
affine core derived equivalence. The two equivalence counits and a natural isomorphism
lifted through `DerivedCategory.Q` give the requested model.

The proof imports `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore` and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` privately.
The existing public import of `AffinePerfectModuleModel` stays. Updated the item's DAG
proof, proof dependencies and proof origin to this route. No new modules, declarations,
interfaces, change records or nodes are introduced. Exactness instances for the two
composite functors are supplied inside the proof; no file-level attribute is added.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.affine_open_supported_model_exists`
(node `new-affine-open-supported-model-exists`). No `sorry` remains in this module;
no hole is added. The proof uses the existing theorem
`AlgebraicGeometry.exists_affineQCohDerivedEquivalence_core` as a dependency.
This is a proof from existing declarations, not a decomposition into new holes.

## No longer needed

Removed the following proof imports and dependencies for this item:

- `Sheaf.AlgebraicGeometry.OpenDerivedRestrictionComparison`, node
  `lem-pc-open-derived-restriction-comparison`: its restriction/quasi-coherence clause is
  replaced by direct exact-functor homology comparison and Mathlib restriction of
  quasi-coherent modules; no localization adjunction, support or orthogonality is needed.
- `Sheaf.AlgebraicGeometry.AffineLocalizedSiteDerivedTransport`, node
  `lem-pc-affine-localized-site-derived-transport`: the canonical transport is constructed
  here so that its inverse can be identified explicitly with scheme restriction.
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`, node
  `lem-pc-affine-qcoh-derived-equivalence`: the existing smaller core theorem suffices.
  Its additional shift normalization and the module
  `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalenceShift`, node
  `new-affine-qcoh-derived-equivalence-shift`, are not needed along this item's route.

These are dependencies removed from this item's route, not claims that other target
branches never use them. The unit's statement and proof steps are preserved; this item
is not a realized unit statement or step in `dag/units/sk-thm-picard-duality.json`.

## Where the brief, the DAG or earlier work was wrong

The planned affine-site transport theorem supplies an unspecified equivalence and the
tilde comparison, but no assertion that its inverse preserves quasi-coherent cohomology.
Its signature is true and unchanged. Constructing the canonical equivalence explicitly
allows the needed quasi-coherence check without adding a bridge theorem.

Read Stacks Tags 06Z0 and 08EJ online because the local TeX copy is absent on this machine.
Tag 08EJ uses the affine D(A) equivalence before its separate support argument; this item
only supplies that model and does not need support, perfectness or boundedness. The proof
works uniformly for empty opens, the zero object and arbitrary integer shifts, with an
auxiliary standard localization on Spec A and the given localizations elsewhere.

Searches ran through msearch.py: LeanFinder for affine derived essential image found
ordinary affine-site/sheaf components, Loogle found Localization.liftNatIso, and grep
found Modules.isQuasicoherent_restrictFunctor. The existing project core equivalence
provides the affine derived result. The complete module compiled with lcompile.py without errors or warnings, including
after the final proof-local instance revision. `deliver3.py J2
Sheaf.AlgebraicGeometry.AffineOpenSupportedModelExists --no-push` printed OK for dry-run
commit `1bf309837b`: it compiles and passes preflight except for the second reading, which
the second reader writes. Nothing was pushed.
Its first attempt flagged file-level local instance attributes, which were replaced by
proof-local instances. The dry-run wrapper expressly allows the second-reading section
to be missing once it is the sole preflight issue; that section is left to the reader.

## Second reading by J2

1. Pass: compared the complete delivered Lean module against the repository version.
   The existing theorem signature is byte-for-byte identical, its docstring and public
   import are unchanged, and there are no new declarations or changed definitions.
   A parsed JSON comparison confirms that only `proof`, `proof_deps` and `proof_origin`
   change in the existing node. No change record is necessary.
2. Pass: compiled a scratch copy of the full module through `lcompile.py` with
   `#print axioms AlgebraicGeometry.Scheme.affine_open_supported_model_exists`.
   It compiled without errors or warnings and listed exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The delivered source has
   no `sorry`, forbidden declaration, or data definition. The model is the explicit
   inverse-equivalence image of the constructed restriction, not an arbitrary witness
   chosen in a definition from an unproved existence theorem.
3. Pass: no statements are split off, and there are no new holes or nodes to review.
   Checked the existing core equivalence signature and the restriction theorem in
   Mathlib. The latter applies because `isoSpec.inv ≫ U.ι` is an open immersion.
   Empty opens, zero objects, arbitrary integer shifts and unbounded complexes require
   no exceptional case in this argument.
4. Pass: read the proof from its conclusion through both counits, the localization
   comparison, affine inverse equivalence and homology quasi-coherence transport.
   Searched the library for affine derived equivalences and restriction comparisons,
   and repeated msearch grep with `derived.*equivalence|quasicoherent.*restrict`.
   No available theorem supplies a shorter complete argument with the required
   canonical inverse comparison. Each retained import is used: the public import
   supplies the statement's sheafification, and both private imports supply proof
   declarations. Every old proof dependency removed is listed under No longer needed.
   The unit record has no realized statement or step naming this node; its route is
   preserved. Checked the cited affine equivalence and its use before the support
   calculation in [Stacks 06Z0](https://stacks.math.columbia.edu/tag/06Z0) and
   [Stacks 08EJ](https://stacks.math.columbia.edu/tag/08EJ).
5. Pass: the node's three proof steps describe the Lean construction, and
   `proof_deps` is their union: the affine core equivalence and the existing
   affine-perfect-model node for the explicit sheafification. `proof_origin` identifies
   this proof accurately. Statement, source, unit, chapter and Lean record are unchanged.

Second reading changed only this report, adding the independent checks. No Lean or DAG
repair was needed. The node retains an older failed unqualified Loogle query; the sandbox
search log records the successful qualified query `CategoryTheory.Localization.liftNatIso`,
so the first worker's report of that search is correct. One original hole is closed and
zero holes are added.
