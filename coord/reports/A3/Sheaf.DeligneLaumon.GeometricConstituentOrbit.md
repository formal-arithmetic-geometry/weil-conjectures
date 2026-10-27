## What changed

Replaced the body of `AlgebraicGeometry.WeilSheaf.exists_geometric_constituent_orbit` by a complete assembly proof with its original signature and public imports unchanged. All source-library files are unchanged.

The proof first reduces to a positive-dimensional support model, then proves geometric semisimplicity in the actual source sheaf category. The private `semisimple_quotient` is a finite induction: split off the final source summand, form the image of the preceding summands, and examine the induced map from the final simple summand to the cokernel. If it vanishes, the preceding image is the whole target. Otherwise the map is an isomorphism, supplies a section, and splits the short exact sequence. The public `exists_geometric_semisimple_decomposition` in `GeometricSemisimplicity` applies this result to the existing proved geometric-socle surjection `IsIrreducibleLisse.exists_epi_biproduct_desc`.

Added `ConstantFieldRestriction`: its functor is constructed from `ProEtaleWeilSheaf.transport` by restricting to constructible objects, using the actual pullback along the inverse geometric-fiber isomorphism to prove constructibility. Additivity, preservation of finite limits and colimits, and preservation of lissity are proved. `HasPointwisePowerTransport` is an explicit proposition about conjugate stalk operators, not an arbitrary functor assumption hidden in a definition. Its implication for reality is proved from the source characteristic-polynomial power theorem. `constantFieldRestrictionOfSquare` uses the existing canonical geometric-fiber isomorphism and its proved Frobenius intertwining equation.

The assembly proof constructs the composite functor and base-field algebra structure, transfers the geometric properties by the actual cartesian square, and lifts both marked points by finding finite points in the nonempty fibers over their finite residue fields. It composes the residue-degree exponents and proves the characteristic-polynomial identities using invariance under Frobenius conjugacy for every power. It proves reality for all coefficient embeddings and carries the summand orbit comparison through the composite scheme map.

The three remaining source arguments have separate modules and full proof docstrings: `SimpleLisseSupportModel`, `SemisimpleFrobeniusOrbitDescent`, and `ConstantFieldRestrictionStalk`. Their statements do not contain the entire original conclusion: respectively they omit decomposition and orbit data, assume a supplied geometric semisimple decomposition on an irreducible geometric fiber and omit local comparison with the original base, and assume no simplicity or lissity at all. The original proof genuinely combines them, including a proved semisimplicity argument between the first two.

The six modules were compiled with `lcompile.py --all` and the final main proof with `lcompile.py`; the main proof's profiled run reported about 2.5 seconds of tactic execution and 7.9 seconds overall. Profiling options were removed. The original existential isomorphism binder `v` is unused in the original conclusion, so its existing name is preserved and the unused-variable linter is disabled locally for that theorem only.

## Proved and sorry left

The original module has zero textual `sorry` left. The original hole at `AlgebraicGeometry.WeilSheaf.exists_geometric_constituent_orbit` is replaced by a proof from three named remaining obligations. This is a decomposition, not a complete proof without `sorryAx`: one original hole removed, three holes added, net minus two textual holes in the changed files.

The added holes, each with proof exactly `:= by sorry`, are:

- `AlgebraicGeometry.WeilSheaf.exists_simple_lisse_support_model`, node `lem-zl-simple-lisse-support-model`.
- `AlgebraicGeometry.WeilSheaf.exists_semisimple_frobenius_orbit_descent`, node `lem-zl-semisimple-frobenius-orbit-descent`.
- `AlgebraicGeometry.WeilSheaf.hasPointwisePowerTransport_constantFieldRestrictionOfSquare`, node `lem-zl-source-constant-field-restriction-stalk`.

There are no other new holes, no definition with postponed data, and no change to an existing declaration's type. The restriction functor, its exactness and lissity proofs, pointwise reality implication, geometric semisimplicity, finite-point lifting, and conjugacy calculation are proved without new holes. The existing source geometric-socle surjection is recorded by a new attachment node; its Lean file and proof are unchanged. The completed geometric-semisimplicity result also has its own node and module.

## No longer needed

No original import is removed, no module is withdrawn, and no global pruning is claimed. A provisional proof import of `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth` was removed: the argument only uses Mathlib's smooth base-change theorem. The proof imports `WeilConjectures.WeilSheaf.StalkUpperStar` for its finite-point mapping lemma.

The item no longer directly depends on `lem-zl-affine-geometric-components-finite-extension`, `lem-zl-geometric-constituents-any-base`, `def-weil-local-frobenius-trace`, or `lem-zl-point-weil-heart-flag`. Their corresponding mathematical steps remain needed by the new lower obligations, and their dependency edges are retained there. In particular, this does not bypass the unit's geometric-constituent and dimension-zero route.

`lem-zl-constant-extension-weil-heart-equivalence` and its module `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence` are unnecessary for this argument. The new restriction functor is built directly from the already constructed source pro-etale transport and canonical geometric-fiber comparison. No equivalence between the source category and the separate common-stage heart is assumed. This removes that proof dependency from this item's route only.

No direct proof import of the common-stage point flag, common-stage local Frobenius, or representation-theoretic Clifford module is needed by the completed assembly. The statements planned for the remaining obligations retain the appropriate existing unit dependencies.

## Where the brief, the DAG or earlier work was wrong

The recorded source Clifford declaration gives a stable filtration; it does not itself assert a direct sum of geometric simple source Weil sheaves or the orbit comparison at translated points. Likewise, the common-stage constant-extension theorem is not an interface for the source `WeilSheaf` category. The new source restriction definition resolves the functor and exactness part of that mismatch; its local comparison is isolated in the generic local-return obligation.

A useful existing proved source result was absent from this item's node: `IsIrreducibleLisse.exists_epi_biproduct_desc` in `GeometricConstituentMono`. The delivery uses it and records its attachment. Its conclusion is enough for the geometric semisimplicity induction, so that step no longer remains an unsupported assertion in the geometric-orbit construction.

Edge cases checked: the source quotient induction includes an empty sum and a zero quotient; support reduction excludes the zero object and empty support through the two nonzero stalk hypotheses; the same point can be used twice; the support-model statement explicitly handles dimension zero by an affine line. Constant-field restriction and local transport allow the zero sheaf and repeated powered eigenvalues. Orbit descent makes no semisimplicity assumption about local Frobenius; it uses semisimplicity only for the underlying geometric local system. Its prescribed constant model is cartesian, so it cannot choose an unrelated functor or unrelated scheme. The residue-degree exponents are multiplied in the assembly, and the orbit move preserves the second point's absolute residue cardinality.

## New nodes

`def-zl-source-constant-field-restriction` records the explicit source functor, canonical square specialization, and pointwise power-transport proposition, with proved exactness, lissity and reality consequences in `ConstantFieldRestriction`. Its data do not depend on any new unproved existence theorem.

`lem-zl-simple-lisse-support-model` isolates the clopen support/geometric-component and dimension-zero reductions. It contains no geometric summands or orbit claim.

`lem-zl-semisimple-frobenius-orbit-descent` takes the supplied semisimple geometric decomposition and isolates multiplicity-one/Frobenius-return descent on an actual finite constant model, with its summand orbit comparison. It provides no source-point Frobenius power comparison and does not establish semisimplicity.

`lem-zl-source-constant-field-restriction-stalk` isolates the generic residue-degree comparison for the already constructed functor. It has no irreducibility, lissity, reality, affine, smoothness or marked-point hypotheses.

`lem-zl-source-geometric-semisimplicity` records the proved `exists_geometric_semisimple_decomposition` in `GeometricSemisimplicity`, including the finite quotient-of-simples induction. It adds no hole.

`lem-zl-simple-geometric-socle-surjection` attaches the existing proved source theorem used by the semisimplicity argument. No new Lean declaration is introduced for this attachment.

All nodes record actual Mathlib searches and the current blueprint source. No statement or definition change record is required: existing interfaces are unchanged, and all new definitions are explicit constructions under `Sheaf`.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
