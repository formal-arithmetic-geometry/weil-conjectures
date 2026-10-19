## What changed

Proved `AlgebraicGeometry.ProEtale.constantModelConstructibleFiniteTor_wellDefined` in
`Sheaf.Paper.ConstantModelTorAmplitude`, with its signature unchanged. The proof transports
local-model presentations across restricted isomorphisms, transports boundedness and
constructible homology, and uses the existing generic Tor-amplitude isomorphism and retract
instances. The relative derived tensor's canonical shift and triangulated structures give
all-integer shift bounds and the extension bound. Zero, shifts and extensions after widening
to a common interval supply the triangulated property of finite Tor amplitude.

Added the proof-only import
`WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift`.
Updated the existing node's proof, proof dependencies and proof origin to match this route,
and removed its two obsolete tool approvals. No definitions, statements, public signatures,
or consumer modules changed. No new declarations or nodes.

The only additional module commands open `ZeroObject` and
`CategoryTheory.MonoidalCategory` for proof elaboration. The change record is
`coord/changes/G4-constant-model-tor-amplitude-proof-scope.md`; no declaration signature,
public import, definition, instance or exported attribute changes. No consumer needs an
adaptation. Validation on 2026-10-19: the item compiled cleanly in 25.7 seconds through
`lcompile.py`. A scratch copy with `#print axioms` compiled in 28.4 seconds and reports
exactly `propext`, `Classical.choice` and `Quot.sound`. The theorem signature is byte-identical
to the current shared source; no Lean line exceeds 100 characters. The initial dry-run
process ended during the interrupted session without a retained final result; its retry
is recorded in `scratchpad/dry-run-current.log`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.constantModelConstructibleFiniteTor_wellDefined`
(node `det-def-sfb-constructible-tor-amplitude`).
Added 0 holes. Remaining holes in the item and delivery: 0.

## No longer needed

The following planned proof dependencies are not needed by this proof:

- `def-weil-pbc-internal-abelian-sheaf-module-equivalence`
  (`Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`).
- `def-weil-sheaf-of-modules-category` (`Sheaf.CategoryTheory.RingedSiteModules`).
- `det-def-sfb-sheaf-tensor-structure` (`Sheaf.CategoryTheory.SheafTensorStructure`).
- `det-def-sfb-sheaf-tensor-closed` (`Sheaf.CategoryTheory.SheafTensorClosed`).
- `def-sfb-modobj-relative-tensor` (`WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`).
- `lem-pc-sites-sheaf-tensor-bilinear-universal`
  (`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`).
- `lem-weil-pbc-ringed-projection-mate-exact` (`Sheaf.Paper.ProjectionMateExact`).
- `lem-sf-derived-homology-long-exact`: its direct use is replaced by the existing
  canonical t-structure extension bounds `isGE₂` and `isLE₂`.

The definition already uses the internal relative derived tensor. Its existing generic
shift, exactness, isomorphism and retract APIs apply directly, so no sectionwise-module or
derived-equivalence comparison and no projection-mate theorem is required. The relative
module structure remains present through the existing definitions; this does not eliminate
its underlying mathematical construction. Both obsolete top-level `tool_uses` approvals
were withdrawn. Relative to the current shared sources, the seven module imports listed
above are removed, together with these two redundant proof-only imports:

- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel` (available through the statement import).
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom` (not used by the proof).

The two public imports are unchanged and provide the statement's objects and
triangulated-subcategory classes. The proof-only monoidal shift import supplies the
canonical shift and exactness API.

## Where the brief, the DAG or earlier work was wrong

The existing plan unnecessarily passed to sectionwise module sheaves and back. The landed
`torAmplitudeIn` definition already uses exactly the required relative tensor. The proof
keeps the unit's constructibility and Tor-amplitude route and proves every original clause,
including the affine-local convention and all nine well-definedness assertions. Empty
schemes, zero coefficients, degenerate intervals and zero retracts require no exceptions.

Searches performed with `msearch.py`: LeanFinder for finite Tor amplitude as a thick
triangulated subcategory (only general t-structure matches); Loogle for
`DerivedCategory.torAmplitudeIn` (unknown identifier in its Mathlib index); grep for
`commShiftTensorRight|isTriangulated_tensorRight` (no indexed matches). Direct source searches
found the generic Tor-amplitude invariance/retract instances and the canonical monoidal
shift API; the existing étale finite-Tor triangulated proof supplied the same generic
zero/shift/extension pattern.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
