## What changed

Proved the eleven remaining theorem bodies in
`Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`, preserving all public
signatures and the existing public definitions. All new constructions and lemmas are private.
No source-library module was edited. A private irreducible identity isomorphism with a
proved unfolding equation is used in normalization proofs. The complex whiskering identity
is proved generically before specialization; normalization then uses explicit factorization
equations for the comparison maps. The final specialized normalization proof uses the
concrete functor names directly, avoiding expensive kernel matching of local aliases.

The proof assembles the existing exact inverse-image, proper direct-image and open-extension
functors into the proved compact-support formalism, identifies its maps with the specified
ordinary etale maps, and applies its coherence and pasting equations. Arbitrary-refinement
normalization is proved from the graph normalization on K-injective representatives, the
cartesian refinement case, and cancellation through the dense refinement. Bounded-below
restriction is proved for the actual derived units, exchange maps and compositors. Generic
categorical pasting lemmas combine these equations, including the inclusion comparisons of
composite functors and the tower associators, before specialization to module sheaves.

Updated the existing node's proof, proof dependencies, proof origin and obsolete top-level
tool approvals to describe this route. The statement, statement dependencies, Lean attachment
and the blueprint unit route are unchanged. There are no new nodes, statement changes,
withdrawals or forced adaptations. The administrative scope record is
`coord/changes/E2-unbounded-etale-compact-support-proof-scope.md`; it records the private
local instances, proof attributes and the unchanged interfaces of all 33 consumers.

Validation uses the full server compile through `lcompile.py` and the delivery axiom probe.
The packet audit confirmed all 24 public signatures, all nine public
definition bodies and the ordered public imports are unchanged; the module contains no
holes or forbidden constructs, all Lean lines meet the 100-character limit, and the
node's proof dependencies agree with its proof-step uses.

## Proved and sorry left

Closed 11 existing holes, by declaration (all in `AlgebraicGeometry.Etale`):

- `unboundedEtaleCompactSupport_comparison_coherence`
- `unboundedEtaleCompactSupport_refinement_normalization`
- `unboundedEtaleLowerShriekCompIso_tower`
- `unboundedEtaleLowerShriekCompIso_assoc`
- `unboundedEtaleLowerShriekCompIso_units`
- `unboundedEtaleCompactSupport_baseChange`
- `unboundedEtaleCompactSupport_baseChange_comp`
- `unboundedEtaleCompactSupport_baseChange_composition`
- `unboundedEtaleCompactSupport_comparison_plus`
- `unboundedEtaleCompactSupport_composition_plus`
- `unboundedEtaleCompactSupport_exchange_plus`

There are zero remaining `sorry`s in the delivered module and zero added holes. Every new
private helper is proved. Existing proved declarations remain proved. This is a proof from
existing library declarations, including their existing dependencies, not a claim that the
entire target import closure is already axiom-free.

## No longer needed

Removed these direct proof imports:

- `WeilConjectures.Compactification.CategoryBaseChange`
- `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`
- `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `Sheaf.Paper.CompactSupportStaircaseExpansion`

Removed these node proof dependencies because the corresponding separate geometric or
staircase argument is bypassed by the existing abstract formalism, the concrete
`ofComp`/`ofRestrict` tower construction, or the existing derived-functor API:

- `lem-amb-compact-support-staircase-expansion`
- `lem-amb-natural-transformation-whisker-exchange`
- `lem-cbc-compactifiable-compatible-tower`
- `lem-cbc-proper-open-interchange-coherence`
- `lem-pc-proper-base-change`
- `lem-weil-pbc-module-sheaves-enough-injectives`
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`
- `lem-weil-pbc-open-immersion-base-change`
- `prop-weil-pbc-inverse-image-modules-exact`

Removed these obsolete top-level tool approvals, preserving every remaining approval in
its original order:

- `lem-cbc-compactifiable-compatible-tower`
- `lem-cbc-proper-open-interchange-coherence`
- `lem-weil-pbc-module-sheaves-enough-injectives`
- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`
- `lem-weil-pbc-open-immersion-base-change`
- `lem-pc-proper-base-change`

No unit statement or unit proof step is bypassed.

Compared with the starting module, its transitive import closure no longer contains the
following modules. This is an item-closure comparison, not a claim that other target paths
cannot still use them; no files or declarations are withdrawn:

- `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`
- `Sheaf.AlgebraicGeometry.EtaleModuleAbelianRingedPresentation`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`
- `Sheaf.AlgebraicGeometry.ModuleAbelianKInjectiveDirectImageAcyclic`
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeGeometricNormalization`
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangePasting`
- `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange`
- `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChangeForgetful`
- `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChangeModN`
- `Sheaf.AlgebraicGeometry.TorsionAssembly`
- `Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison`
- `Sheaf.AlgebraicGeometry.UnboundedCoefficientForgetfulAux`
- `Sheaf.Paper.CompactSupportStaircaseExpansion`
- `Sheaf.Paper.DerivedCompactSupportCompositionCoherence`

The source-library declarations and public imports are all preserved. In particular,
pruning a dependency here does not delete an existing upstream proof that uses it.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan proposed separate staircase and compatible-tower arguments, although
the adopted library already proves the required abstract formalism identities and supplies
the concrete tower. Its bounded-below restriction step also has a direct derived-functor
API proof. The revised node records these shorter routes without changing any statement.

The main implementation issue was elaboration of large derived-adjunction and formalism
terms. Private wrappers give the native functor types of the actual maps, and generic
pasting lemmas perform the categorical calculations before specialization. Local
irreducibility keeps the existing derived-adjunction interfaces abstract during these
calculations. No definition was weakened, no arbitrary witness was used as mathematical
data, and no source-library repair was needed.

The `lem-kun-proper-base-change-torsion-ring` node still records a historical move to
`Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange`, while the current adopted source directly
contains its declared theorem
`isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring` in
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`. This delivery uses that existing
source theorem, retains the mathematical proof dependency, and removes the obsolete direct
Sheaf import; it does not withdraw or modify either module.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
