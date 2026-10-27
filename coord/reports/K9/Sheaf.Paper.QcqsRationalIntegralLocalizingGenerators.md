## What changed

Preserved both generator definitions, both existing theorem signatures, and all public imports.
Proved generator constructibility and finite Tor amplitude from the existing scalar-extension
CTF theorem. Assembled finite generation from integral leaf models and the existing finite-tree
reconstruction theorem. Proved the bounded-complex step with the existing degreewise bounded
devissage wrapper, finite extension-product addition, and integer shift stability. Derived the
ambient localizing assertion from the universal property of localizingClosure.

Added Sheaf.Paper.QcqsConstructibleIntegralLeafModels to bridge the two existing tree interfaces.
It only concerns constructible sheaves, lisse integral leaf models, and underived scalar maps.
This geometric assembly remains the one named split-off statement for the next round.
The actual scheme morphisms and canonical coefficient inclusions are retained. Both coefficient
cases include empty schemes, empty leaves, and zero ranks; fields may vary between closure leaves.
No derived complex or connecting morphism is descended to a common finite field.

## Proved and sorry left

The two original holes are closed from the stated dependencies, including the one new
sheaf-level assembly lemma:
AlgebraicGeometry.ProEtale.qcqs_rational_integral_localizing_generators and
AlgebraicGeometry.ProEtale.qcqs_algCl_integral_localizing_generators.
The only sorry added is AlgebraicGeometry.ProEtale.qcqs_constructible_integral_leaf_models
(node lem-sfb-qcqs-constructible-integral-leaf-models). Thus two original holes are reduced
to one strictly smaller sheaf-level geometric step. No sorry remains in the item module.
This is a decomposition with net one hole closed, not an independent proof of the new lemma.
The new helper module compiles. Both item theorem proofs are complete from this named
geometric step and the existing CTF and reconstruction declarations. The private derived
coefficient comparison proves existence of an isomorphism by eliminating equality.
No data is chosen from an unproved theorem.
Clean item compilation passed in 52.8 seconds with no warnings; the new module also
compiled. Delivery preflight performs the final signature, dependency and axiom checks.

## No longer needed

Removed these direct private proof imports:

- Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
- Sheaf.CategoryTheory.InternalSectionTensorComparison
- Sheaf.Paper.PadicIntegersInvertEll
- Sheaf.Paper.FiniteConstantModelResolution
- Sheaf.AlgebraicGeometry.CoefficientTorFlatModel
- Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
- Sheaf.SixFunctors.ConstructibleOpenClosedRefinement
- Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
- Sheaf.Paper.CoefficientFiniteDescentLisse
- Sheaf.Paper.StratifiedLatticeRank
- WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
- WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
- Sheaf.Paper.ContinuousLatticeSum
- Sheaf.Paper.ContinuousCoefficientRealizations
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
- Sheaf.AlgebraicGeometry.ProEtaleTorIntervalLocalDetection
- Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection
- WeilConjectures.CategoryTheory.TruncationTriangle
- Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
- Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
- Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
- Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
- Mathlib.Topology.Constructible

These are lower-level ingredients already encapsulated by the scalar-extension, lattice-tree,
and reconstruction interfaces; removing the direct imports does not assert they are globally
unused. Their existing declarations and modules are preserved. The old direct dependency on
lem-weil-pbc-truncation-triangle is replaced by the proved finite degreewise devissage node
lem-sfb-degreewise-bounded-devissage, which realizes the same finite Postnikov step. The original
constructible-tree and lisse-stratified-lattice nodes remain dependencies of the new leaf-model
assembly. The old tool_uses list described the original expanded fourteen-step plan; those
obsolete direct approvals are removed, while the actual lower ingredients remain attached to
the existing proof-dependency nodes. No Lean module is withdrawn.
A private finite-model isomorphism transport is proved directly,
so no private declarations of CoefficientHeartLisseExtensionConstructible are imported.

## Where the brief, the DAG or earlier work was wrong

The Lean docstrings retain the original fourteen-step plan, while the current DAG already
condenses the geometry into scalar-extension CTF, constructible refinement, lisse lattices,
and finite-tree reconstruction. The two latter tree interfaces use different inductive types:
SchemeRefinementTree versus QcqsOpenClosedTree. The new helper explicitly composes these
interfaces. This is a sheaf-level step, strictly smaller than either derived generation theorem.
The unit route is preserved; the finite Postnikov argument uses the proved source-library wrapper.
No statement, definition, target signature, or source-library declaration is altered.
Private proof imports use the same competing-coefficient-instance exclusion as the proved
reconstruction module. Local sheaf-colimit, scalar-extension monoidal, and tensor-colimit
instance priorities follow the existing source Colimit.TwoColimit module. This avoids a
divergent broad typeclass search without changing the chosen constructions.
The root module-object Tor predicate is qualified to avoid the
sheaf-Tor name exposed by that private import; its elaborated statement is unchanged.

## New nodes

lem-sfb-qcqs-constructible-integral-leaf-models: the paired finite-field and finite-valued closure
sheaf-level existence of a finite qcqs open/closed tree with integral lisse models. It uses the
existing constructible refinement and lisse-stratified-lattice results, actual pullback composition
and scalar pullback isomorphisms. Searches with LeanSearch, LeanFinder, Loogle, Mathlib/project grep,
and blueprint_refs found no direct duplicate. Its source is the parent geometric steps and the
current blueprint lattice proof; the new node records the source and full argument.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
