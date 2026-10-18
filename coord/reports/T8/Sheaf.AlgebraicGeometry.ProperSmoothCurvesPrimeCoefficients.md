## What changed

Replaced the item's single top-level hole by the Noetherian mixed-characteristic argument:
construct D(ell) and the full principal closed subscheme V(ell), prove the proper-base-change
identifications and preservation of fibre dimension, establish constructibility on both pieces,
and glue with the source library's proved open-closed theorem. The original theorem signature
is unchanged.

Added five fully proved supporting modules: finite geometric stalks in all degrees;
connected-fibre degree-zero constructibility; characteristic-prime vanishing above degree one;
constructibility of cyclic module sheaves from finite abelian charts; and compatibility of
module specialization with strict-local abelian specialization. The finiteness proof
uses the already proved curve calculation C5 and explicit Ext/derived and coefficient comparisons.
The degree-zero proof uses the existing connected-fibre section theorem on every etale base object.
The characteristic-prime vanishing proof uses Artin-Schreier on geometric fibres and stalk
conservativity. The coefficient upgrade uses the existing finite cyclic local-system comparison.

The invertible-prime case combines finite stalks with smooth proper specialization and the
finite-stalk criterion. Degree one in characteristic p uses a kernel realization and the existing
Frobenius-vector-bundle constructibility theorem. The remaining kernel obligation is recorded in a
new module, with complete proof explanations. All new objects appearing in definitions are
constructed; no arbitrary witness is chosen from an unproved mere-existence theorem in a definition.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.Etale.properSmoothCurves_prime_higherDirectImage_constructible` is removed.
This is a decomposition, not a complete proof: one upper hole closed, one lower hole added;
net zero before accounting for imported existing dependencies. The item itself has zero holes.

Fully proved new public declarations:

- `AlgebraicGeometry.Etale.prime_constant_stalk_finite`.
- `AlgebraicGeometry.Etale.higherDirectImage_zero_constant_constructible`.
- `AlgebraicGeometry.Etale.prime_higherDirectImage_zero_of_charP`.
- `AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_of_abelianIso`.
- `AlgebraicGeometry.Etale.bijective_moduleSpecialization_of_abelianIso`.

Sorries left in the delivery:

- `AlgebraicGeometry.Etale.exists_prime_curve_artinSchreier_kernel`, node
  `lem-weil-pbc-prime-curve-artin-schreier-kernel`. It remains to apply the derived exact segment
  to Artin-Schreier (transporting the tensor-unit coefficients by their natural coordinate
  isomorphism), identify R1 O with the specified finite locally free bundle, verify Frobenius
  semilinearity on raw cohomology classes and descend to sheaf sections. Its conclusion is the
  kernel identification, not constructibility; the main proof supplies constructibility using
  the independent vector-bundle kernel theorem.

The item and each supporting module compile through lcompile.py. The expensive derived
base-change construction is generic in a torsion coefficient ring and input sheaf.
It uses the componentwise unit theorem directly, without rewriting a functor-level
isomorphism. Constant coefficients use its isomorphism API, and the curve cohomology calculation also
keeps the coefficient ring generic. The explicitly constructed comparison isomorphisms
are irreducible, and
Noetherian and compactness instances on restrictions are supplied explicitly.
A fresh compilation of all seven modules and delivery validation are recorded by deliver3.py.

## No longer needed

The item's direct hand-built constructible-stratification assembly step is replaced by the
proved source-library open-closed gluing theorem. Its direct import and direct proof dependency
`Sheaf.AlgebraicGeometry.ConstructibleStratificationAssembly` /
`lem-weil-pbc-constructible-stratification-assembly` are removed, along with the obsolete direct
parent-node tool approval. That module remains reachable transitively through other proof
modules, so it is not claimed as a globally pruned module. The unit's own statement and
realized proof steps are retained. In particular the projective-line reduction theorem
`lemma-weil-pbc-prime-proper-base-change` remains needed: the bounded-below proper
base-change API is its componentwise consequence, so this unit step is not pruned.

Comparing the item's complete import closure before and after this delivery, the only old
module no longer reached is `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`.
Its source-library replacement was already a public import of the item. The six new modules
are all used. This is an item-closure calculation; the maintainer's ledger determines global
pruning across all targets. A direct comparison from both `Challenge` and `TargetsCheck`
shows no old module removed from their combined closure: other importers retain the wrapper.
Thus global module pruning is none.

Removed direct proof imports from the item (several remain needed inside supporting modules):

- `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`.
- `Sheaf.AlgebraicGeometry.ArtinSchreierSchemeSectionData`.
- `Sheaf.AlgebraicGeometry.ArtinSchreierSchemeSectionExact`.
- `Sheaf.AlgebraicGeometry.ConstructibleAbelianSheaf`.
- `Sheaf.AlgebraicGeometry.ConstructibleStratificationAssembly`.
- `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension`.
- `Sheaf.AlgebraicGeometry.EtaleSetSectionsFlatConnectedFibres`.
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`.
- `Sheaf.AlgebraicGeometry.GeometricFiberFinite`.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`.
- `Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages`.
- `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`.
- `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`.
- `WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations`.
- `WeilConjectures.AlgebraicGeometry.EtaleSetSectionsFlatConnectedFibres`.
- `WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor`.
- `WeilConjectures.ConstructibleSheaf.Defs`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`.

The Noetherian and immersion Mathlib dependencies are retained in the DAG: the proof explicitly
uses `LocallyOfFiniteType.isLocallyNoetherian`, and uses the open-subscheme Noetherian,
immersion finite-type and smooth-flat instances. These are not pruned.

Old planned proof dependencies not invoked as proof lemmas on the new route (source-library
instances and the proved open-closed API supply these steps; definitions used in signatures
remain available, and this list does not claim those definition modules are unreachable):

- `def-sbc-smooth-morphisms`.
- `def-weil-proper-morphism`.
- `lem-sfb-noetherian-space-compact-subsets`.
- `lem-weil-pbc-constructible-stratification-assembly`.
- `lem-weil-pbc-direct-image-left-exact`.
- `lem-weil-pbc-etale-sections-flat-qc-connected-fibres`.
- `lem-weil-pbc-exchange-forget-coefficients`.
- `lem-weil-pbc-inverse-image-composition`.
- `lem-weil-pbc-locally-noetherian-quasi-separated`.
- `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`.
- `lem-weil-pbc-site-sheaves-enough-injectives`.

## Where the brief, the DAG or earlier work was wrong

The brief suggests LeanFinder, Loogle and grep, but the preflight counts LeanFinder and
Loogle as one kind and additionally requires LeanSearch. All six new nodes now record actual
LeanSearch queries as well as the other searches.

The stated dependencies existed, but the interfaces did not directly compose. Smooth proper
specialization is stated for an abelian strict-local map; the finite-stalk criterion is stated
for the germ-characterized module specialization. The general comparison lemma records precisely
that interface. The finite abelian constructibility predicate also uses pullbacks to schemes,
whereas module constructibility uses localized-site charts; the proved chart upgrade handles
this mismatch, including empty charts.

The source library already proves open-closed gluing, curve cohomological finiteness C5,
Artin-Schreier curve vanishing, and the needed cohomology comparisons. Re-proving those planned
steps was unnecessary. No statement was weakened, and no existing definition was changed.

## New nodes

`lem-weil-pbc-connected-fibres-constant-degree-zero`: Degree-zero constant direct images under connected fibres. Its statement, source, proof explanation and search records are
attached to `Sheaf.AlgebraicGeometry.ConnectedFibresConstantDegreeZero`.

`lem-weil-pbc-constructible-cyclic-module-of-abelian`: Constructible cyclic module sheaves from finite abelian charts. Its statement, source, proof explanation and search records are
attached to `Sheaf.AlgebraicGeometry.ConstructibleCyclicModuleOfAbelian`.

`lem-weil-pbc-module-specialization-abelian-iso`: Compatibility of module and strict-local abelian specialization. Its statement, source, proof explanation and search records are
attached to `Sheaf.AlgebraicGeometry.ModuleSpecializationAbelianIso`.

`lem-weil-pbc-prime-curve-artin-schreier-kernel`: Degree-one prime coefficients as a Frobenius fixed-point kernel. Its statement, source, proof explanation and search records are
attached to `Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel`.

`lem-weil-pbc-prime-curve-charP-high-vanishing`: Characteristic-prime curve direct-image vanishing above degree one. Its statement, source, proof explanation and search records are
attached to `Sheaf.AlgebraicGeometry.PrimeCurveCharPHighVanishing`.

`lem-weil-pbc-prime-curve-geometric-stalks-finite`: Finite geometric stalks of prime-coefficient curve direct images. Its statement, source, proof explanation and search records are
attached to `Sheaf.AlgebraicGeometry.PrimeCurveGeometricStalkFinite`.

No change record is needed: existing public statements, definitions and module commands are
unchanged. New elaboration options and namespace opens are scoped to individual declarations.
The first dry run caught missing LeanSearch records and unscoped module commands; the search
records now include actual LeanSearch queries, and the module interface comparison is empty.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
