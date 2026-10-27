## What changed

The original theorem now proves the quotient geometry, constructs the cartesian closed-fibre square, verifies qcqs of both proper total spaces, pulls the weak Serre coproduct closure to the weakly etale test scheme, and applies the existing coefficient-transfer theorem. Two independent canonical comparison steps are stated separately with their sources and proofs in words.

The three generic evaluation constructions move verbatim to Sheaf.Paper.ClosedFibreModuleEvaluation, publicly reexported by the item. Their names, signatures, bodies, universes and visibility are unchanged. This removes the import cycle for the independent localization theorem. Change record: coord/changes/closed-fibre-evaluation-module.md. No consumer adaptation is needed.

## Proved and sorry left

Closed: AlgebraicGeometry.ProEtale.CondensedRing.proper_wContractible_closedFibre_rigidity (the item's original one hole), by a complete combination of named intermediate statements. This is a decomposition, not a complete proof of its mathematical dependency closure.

Added, exactly two holes, each a public theorem with proof exactly `:= by sorry`:

- AlgebraicGeometry.Etale.proper_wContractible_torsion_rigidity; node lem-sfb-proper-wcontractible-torsion-rigidity. This is torsion etale cohomology over a proper w-contractible base, independent of condensed coefficients and Serre closure.
- AlgebraicGeometry.ProEtale.CondensedRing.weaklyEtale_derived_evaluation_restriction_iff; node lem-sfb-weakly-etale-derived-evaluation-restriction. This is the canonical localization comparison for arbitrary unbounded modules, without properness, closedness or constructibility.

The geometry and constructible-pullback helpers are fully proved private theorems. No definitions contain holes. The extracted evaluation module has zero holes. The existing coefficient-transfer and henselian-lisse-rigidity obligations remain existing dependencies, with no new holes in those modules.

Validation: all four delivered Lean modules have compiled; the item compiles without warnings in 7.4 seconds. Its statement and the three extracted declaration blocks were compared verbatim with the live source and are unchanged. The launcher performs the final packet, consumer, node and axiom checks.

## No longer needed

Removed direct proof imports from the item:

- Sheaf.Topology.WLocalComponents
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType
- Sheaf.AlgebraicGeometry.ProEtale.WeaklyContractibleBasis
- Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison
- WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
- Sheaf.AlgebraicGeometry.ExactGlobalSectionsLeray
- Sheaf.AlgebraicGeometry.LerayBounded
- Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
- Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage
- Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
- Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
- Sheaf.Paper.SheafSliceDerivedComparison
- Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
- WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

These are removed as direct imports only. The geometric, Leray and localization dependencies needed by the two separate comparisons remain in their nodes; no claim is made to prune them from the library. The item's direct route uses finite-constant stratified pullback and Zariski locality rather than reproving scalar-matrix or stratification gluing. The affine qcqs and proper permanence facts are Mathlib instances. The broad ringed-slice comparison is used only by the separate localization argument. No upstream declaration is withdrawn and no unit route is bypassed.

The following nodes are removed from the item's direct `tool_uses`, in their original order:

- det-pe-wlocal-components
- sk-thm-pbc-henselian-h0
- sk-thm-pe-weakly-contractible-basis
- lem-cbc-abelian-etale-proetale-cohomology-comparison
- thm-weil-pbc-bounded-below
- def-weil-pbc-exact-global-sections-leray
- lem-weil-pbc-exact-functor-complex-cohomology
- lem-kun-leray-bdd
- lem-pur-scheme-constructible-preimage
- lem-sfb-scalar-matrix-inverse-image
- lem-weil-proetale-weakly-etale-localization
- lem-sfb-internal-module-operations-transport
- lem-sbc-ringed-topos-sheaf-slice-derived-comparison
- lem-weil-pbc-ring-sheaves-grothendieck
- lem-sfb-grothendieck-k-injective

The closed-point component theorem is replaced by henselian invariance of w-contractibility. The cohomology and localization tools belong to the two separate comparison nodes. The constructible-preimage and scalar-matrix tools are already encapsulated in the proved finite-stratification API. These are direct-route removals, not withdrawals of library modules.

## Where the brief, the DAG or earlier work was wrong

The listed dependencies provide proper base change, henselian H0, Leray and slice-derived comparison separately. None has a declaration that directly states the actual torsion cohomologyMap bijections or the internal-module derived-evaluation restriction comparison needed in Steps 5 and 8. The two new nodes record those precise missing glue results. They are strictly independent parts of the original argument, not renamed versions of the item.

Step 6 requires affine-local gluing when X is not qcqs. The proof explicitly chooses affine neighborhoods on X and T and uses the existing proved gluing and inverse-image composition lemmas. Compactness of Y alone does not supply quasi-separatedness of Y; the proof obtains qcqs of the two total spaces from properness over their affine bases.

The existing rework quarantine entry does not authorize withdrawal; the live module and its parent dependencies are preserved. The three evaluation definitions have their existing definition node, whose attachment follows the extraction.

## New nodes

lem-sfb-proper-wcontractible-torsion-rigidity records original Steps 3--5, with the actual torsion Ext pullback on an arbitrary proper cartesian closed fibre over Spec(R/J).

lem-sfb-weakly-etale-derived-evaluation-restriction records original Step 8, generalized to arbitrary weakly etale localization and arbitrary complexes. Its iff exactly identifies the two existing canonical arrows up to the invertible localization and composition comparisons.

The construction module has no new mathematical obligation: def-sfb-closed-fibre-module-evaluation already owns its three unchanged definitions. Its Lean module attachment is updated. The item node's proof, proof dependencies and proof origin follow the written reduction.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
