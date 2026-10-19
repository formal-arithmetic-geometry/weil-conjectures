## What changed

Completed all nine original proofs in Sheaf.AlgebraicGeometry.CohomologicalDimension.
Retained the substantial earlier sandbox work and checked it against current sources.
No public statement, definition, signature, visibility or public import changed.

The diagram laws use kernel uniqueness and factorization of scalar powers. A private
general-site proof identifies the canonical annihilator colimit with local prime-power
torsion, using sheafification, filtered-colimit representatives, AB5 and local kernel lifts.
The stalk criterion uses exactness and conservativity of geometric stalks. The existing
qcqs higher-image theorem then preserves prime-power torsion; the prime factorization
argument includes annihilator 1 and exponent zero.

The absolute and relative comparisons identify the permitted sheaves and nonvanishing
degree sets. Classicality is transported through the canonical forgetful pullback
comparison and its counit equation. Exact fully faithful inverse image preserves and
reflects the annihilator colimit. Generic source-library derived comparison isomorphisms
supply the cohomology and higher-image comparisons. Relative finiteness uses the existing
uniform torsion bound. Absolute finiteness combines that bound, preservation of prime-power
torsion and the existing Leray rectangle bound, with the Ext/derived cohomology comparison.

Repaired the last compiler error in the earlier work: the higher-image helper now proves
Nonempty of an isomorphism, and its witness is consumed only inside a proposition. It
therefore does not extract arbitrary definition data from a nonunique existence theorem.
The other private isomorphism definitions are explicit composites of canonical maps.

Updated sk-def-cd's proof, proof_deps and proof_origin to match these arguments and removed
obsolete tool_uses entries without adding or reordering maintainer approvals. No new node,
statement correction, definition repair, forced adaptation or change record is needed.

Added the direct proof import of PlusAdjunctionAcyclic after the resumed dry run found
that its derived-unit criterion is no longer transitively exposed. Its existing node
lem-cbc-derived-unit-injective-acyclicity is now cited explicitly in proof step 3; no new
statement is introduced.

Validation: lcompile.py compiled the complete file without errors or warnings (16.4 s). The final
deliver3.py dry run checks the complete proof, metadata and pruned imports before delivery. Only the authorized remote compiler was used.

## Proved and sorry left

Original holes: 9. Closed: 9. Added: 0. Split off: 0. Remaining in the item: 0.
All nine declarations are in AlgebraicGeometry.ProEtale and realize node sk-def-cd:

- ellPowerKernelMap_condition
- ellPowerKernelFunctor_map_id
- ellPowerKernelFunctor_map_comp
- ellPowerKernelCocone_naturality
- isEllPowerTorsion_iff_local
- cohomologicalDimension_eq_etaleCohomologicalDimension
- relativeCohomologicalDimension_eq_etale
- relativeCohomologicalDimension_lt_top_of_finiteType
- cohomologicalDimension_lt_top_of_finiteType

There are no sorry declarations in the delivery, including private helpers and definitions.
The proofs use existing library declarations, including proEtaleClassicalSheavesImage and
nonempty_sheafH_extDerivedIso; this is closure of the item's holes, not a claim that all imported
obligations or the project's targets are now proved. No existing hole was merely renamed,
repackaged or moved to a new statement.

## No longer needed

Removed direct proof imports (every public import is unchanged):

- Mathlib.Algebra.Category.ModuleCat.FilteredColimits
- Mathlib.Algebra.Homology.ShortComplex.ShortExact
- Mathlib.CategoryTheory.Sites.Point.Skyscraper
- Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
- Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
- Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
- Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension
- Sheaf.AlgebraicGeometry.TorsionEtaleSheaf
- WeilConjectures.AlgebraicGeometry.GeometricStalkColimits
- WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
- WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

The abelian-group filtered-colimit API replaces the module-coefficient API. The
classical-sheaf equivalence is obtained from the set-valued image theorem and the canonical
forgetful comparison, avoiding the larger module-coefficient equivalence theorem.
The generic derived comparison and injective-acyclicity API replaces the module-coefficient
bounded-below and direct-image wrappers. The direct-image comparison mathematical step
is retained, using nonempty_iso_comparisonUpperStar_comp_rightDerivedLowerStar; its extra
module wrapper coherence conclusions are unnecessary for equality of dimension suprema.
The absolute comparison is proved from the generic derived unit and derived-sections
factorization, rather than importing boundedBelowComparison.

Removed planned proof dependencies:

- def-weil-pbc-torsion-etale-sheaf
- det-pe-classical-sheaves-modules
- lem-kun-stalks-commute-colimits
- lem-weil-pbc-finite-type-over-noetherian
- lem-weil-pbc-module-sheaves-colimits-forgetful
- lem-weil-pbc-noetherian-open-subscheme-noetherian
- lem-weil-pbc-torsion-sheaf-characterizations
- sk-def-pe-site
- sk-prop-sf-comparison

The Noetherian-source facts come directly from Mathlib. Ordinary torsion is obtained
directly from the proved local criterion; no separate torsion-characterization wrapper is
needed. Abelian sheaf colimits and stalk colimits use the general Mathlib APIs, so the
module-sheaf colimit theorem and its specialized geometric-stalk wrapper are unnecessary.
The finite torsion dimension definition still enters through the public imports of
FiniteTorsionEtaleCohomologicalDimension; removing its redundant direct import, and that of
TorsionEtaleSheaf, does not remove those definitions from the route. The unit sk-def-cd
has no realized proof-step nodes to bypass; its statement and both comparison arguments
are retained. No Lean module is withdrawn, and global unreachability is not asserted for
any removed direct import.

The removed tool_uses entries are exactly the old entries absent from the new proof_deps;
all remaining approvals retain their original order. Added proof dependencies name the
existing set-valued classical-image, forgetful pullback, generic unit, acyclicity,
derived-sections factorization, exact-functor and Ext/derived comparison nodes actually used.

## Where the brief, the DAG or earlier work was wrong

The earlier report and proof_origin lagged behind the saved Lean proof: they claimed a
remaining relative comparison hole although its proof had been written. They now describe
the completed file. The last saved helper also attempted Prop-to-data elimination of
Nonempty; the repaired proposition-valued helper avoids both the compiler error and an
arbitrary nonunique choice of definition data.

The relative finite-type result does not need finite absolute prime-power dimension of
the field, as the original DAG already observed. Its hypothesis and full signature remain
unchanged. The absolute proof genuinely uses that hypothesis and does not replace it by
finite torsion dimension. Empty schemes, zero sheaves and exponent zero are included.

The original plan's module-coefficient wrappers contain substantially more than the
abelian-sheaf comparisons needed here. Their generic existing source-library versions,
combined with the explicit forgetful-counit argument, give a shorter route with the same
mathematical statements. No launcher or project script was changed.

## Second reading by T5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
