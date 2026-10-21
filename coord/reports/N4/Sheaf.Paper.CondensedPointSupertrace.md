## What changed

Repaired the invalid independent-choice split in Sheaf.Paper.CondensedPointSupertrace.
The exact original condensed_point_supertrace statement and all fields of
CondensedPointSupertraceData are preserved. The construction theorem now chooses its
realization, scalar action, finite based models, model identifications and normalized
tensor comparisons simultaneously. The parent proof unpacks these shared choices,
then uses the cohomology and compatible-matrix duality conclusions.

Proved condensed_point_scalar_exists from the simultaneous construction by copying its
fields with the explicit constructor: the scalar package does not depend on rho.
Added the proved module Sheaf.Paper.FiniteDimensionalComplexCohomology and used it as
the default frame_mem proof. The finite basis gives finite dimension and, off the
finite rank support, a subsingleton term. This default retains every existing class
field and its expanded type. The source canonical braiding is now synthesized
by a direct field-indexed instance; the old named specialization retains its type
and body as an instance-reducible definition. The target canonical braiding's priority
is 100. Unused automatic constructor-injectivity and SizeOf generation is disabled.
The finite-frame proof is stated as pointSupertraceFrame_mem with an ordinary field
parameter, and the class default applies that lemma. This avoids proving it in the
large realization-instance context. The differential and chain-map matrix formulas and the transported trace formula
are named propositions, and their class fields use these names with identical
expanded types. This keeps generated class declarations compact. The original
CondensedPointScalarData interface is preserved. Both delivery modules compiled
without warnings; the item took 36.6 seconds.

The substantive interface changes and all users are recorded in
coord/changes/CondensedPointConstructionCompatibility.md. The two quarantined parent
sources were read; neither uses a changed helper. Their archives are preserved.
No source-library declaration or Challenge declaration is modified.

## Proved and sorry left

The original module contained seven sorry declarations. One original statement is now
proved, AlgebraicGeometry.ProEtale.condensed_point_scalar_exists
(lem-zl-condensed-point-supertrace-scalars), from the strengthened construction theorem.
This is a reduction to the compatible construction, not an independent construction of
scalar data. No new sorry is added and no proof hole is hidden in a definition.

The false independent-choice obligations condensed_point_matrix_exists and
condensed_point_tensor_compatibility are withdrawn. The now-redundant separate
condensed_point_tensor_model_exists helper is also withdrawn. Their mathematical work is retained in the
simultaneous construction; removing them is a correction, not three theorems proved.
The ledger's syntactic reduction must not be mistaken for four completed mathematical
construction results.

Three public named sorry declarations remain, with full proofs in words:

- AlgebraicGeometry.ProEtale.condensed_point_realization_exists
  (lem-zl-condensed-point-supertrace-realization): simultaneous construction through
  the original argument's steps 1--8, with both tensor normalization equations.
- AlgebraicGeometry.ProEtale.condensed_point_cohomology_exists
  (lem-zl-condensed-point-supertrace-cohomology): cohomology and point evaluation;
  its signature is unchanged.
- AlgebraicGeometry.ProEtale.condensed_point_duality_exists
  (lem-zl-condensed-point-supertrace-duality): duality and supertrace for the compatible
  based matrix realization. The parent supplies its added matrix hypothesis.

DerivedCategory.pointFiniteDimensional_Q_of_finite_terms is proved without sorry,
using the existing ShortComplex.finiteDimensional_homology instance and the localization
homology comparison. Its proof includes empty term support and zero vector spaces.
AlgebraicGeometry.ProEtale.pointSupertraceFrame_mem proves the based-frame case and
is used by the class default. The parent assembly is complete Lean from the three
remaining construction statements.

## No longer needed

The obsolete separate Lean attachments of
lem-zl-condensed-point-supertrace-matrices,
lem-zl-condensed-point-supertrace-tensor-model, and
lem-zl-condensed-point-supertrace-tensor-laws are set to null. The DAG nodes themselves
are preserved, with their construction content recorded in the joint realization; their
statements are restated (reviewer fix) as the existential projections of that joint
construction, since the universally quantified readings are false.
The mathematical finite-matrix, flatness, tensor, cohomology and duality steps remain;
no unit route is bypassed. No module is withdrawn and no upstream declaration is pruned.

Removed these unused proof imports from the item:

- Sheaf.Paper.GeometricFieldProEtaleEvaluation
- WeilConjectures.CategoryTheory.ModuleObjects.Free
- Mathlib.Algebra.Module.Projective
- Mathlib.Algebra.Homology.DerivedCategory.KProjective
- Mathlib.Algebra.Homology.HomotopyCategory.KProjective
- Sheaf.Algebra.Homology.BoundedFreeProjectiveCohomologySplitting
- Sheaf.Paper.CondensedFiniteFreeTensorExact
- Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
- Sheaf.CategoryTheory.DerivedCategory.ChainSupertrace
- Sheaf.CategoryTheory.DerivedCategory.TraceFormalLaws
- Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
- WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def

Replaced the public import Sheaf.CategoryTheory.DerivedCategory.PerfectCategoricalTrace
with WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided. The three
local braiding definitions now use DerivedCategory.braidedCategory', whose body is the
same DerivedMonoidal.braidedCategory' construction. The broad trace package is not
needed for the statements or existing proof bodies. Neither quarantined parent uses
its re-exported perfect-trace declarations. This preserves their canonical braidings.

Also removed the unused public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite.
Replaced Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible by its definition API,
WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory. Removed the broad
public import Sheaf.CategoryTheory.InternalSectionTensorComparison: the two required
colimit/totalization properties are proved directly from the existing section-module
equivalence and coproduct universal properties; no extra proof import is needed
(reviewer fix: the unused plain import
WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful is removed, as is the
redundant import Mathlib.LinearAlgebra.FiniteDimensional.Defs of the new module
Sheaf.Paper.FiniteDimensionalComplexCohomology). Site size uses the
proved essentiallySmallSelf, with its coefficient universe explicit. The two archived
parents already import their own coefficient and constructibility interfaces.

These modules are not used by the current Lean proofs. The construction and duality
nodes still record the source lemmas their pending proofs need; these dependencies
are not claimed globally unnecessary. The scalar-existence helper is no longer needed
by the parent assembly but remains as a proved API theorem.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (repaired): the previous tensor compatibility statement asserted
normalization for every arbitrary tensor isomorphism T. Negating an isomorphism
preserves invertibility and negates its left matrix; for the degree-zero rank-one
complex the required coefficient is nonzero. Moreover rescaling all modelIso maps
by c preserves chain_map_descent but scales tensor descent's sides by c and c squared.
Thus merely changing tensor compatibility to an existential T would not fix the split:
the model identifications and the monoidal realization must be chosen together.

STATEMENT-DISPUTED (repaired): an arbitrary additive exact strong symmetric monoidal
realization need not preserve the independently specified E-scalar inclusion. Compose
the canonical realization with a nontrivial automorphism of a finite Galois coefficient
field E. On the unit, multiplication by a then has scalar and trace sigma(a), whereas
the old arbitrary-R matrix and duality statements demand a. Injectivity of epsilon
separates these values. The compatible matrix comparison is therefore essential.

The old component nodes each cited the parent comparison as their proof, while the
parent Lean proof applied all seven component holes. The revised proof dependencies
record the actual compatible construction and its cohomology/duality consequences.
The parent statement, all eleven mathematical steps and the unit route are retained.
The existing class/structure interface now has its own definition node,
def-zl-condensed-point-supertrace-data. The components cite that interface rather than
the parent existence conclusion. The repaired reachable DAG was checked for cycles.

## New nodes

lem-zl-point-finite-dimensional-complex-cohomology, in
lean/Sheaf/Paper/FiniteDimensionalComplexCohomology.lean, is the proved kernel/quotient
fact needed for finite-frame source membership. It is strictly a domain-membership
part of the matrix argument and introduces no admitted construction. Searches ran
with msearch (LeanFinder, Loogle, grep) and repository rg; the existing upstream
finite-dimensional homology instance was found and reused. Blueprint search found no
exact separate node. Change record: coord/changes/CondensedPointConstructionCompatibility.md.


def-zl-condensed-point-supertrace-data attaches the existing definitions in the item
to their own definition node. This is metadata separation, not a new mathematical
object or construction. It avoids an artificial cycle through the parent theorem
from all seven component statement dependencies. The parent statement is unchanged.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
