## What changed

Reduced WeilConjectures.zl_point_heart_finite_stage to four separate, strictly smaller
steps. The main proof now assembles those steps without any sorry in its body.
It proves finite dimensionality using the existing cohomology membership theorems,
uses coefficientQbarCohomology_changeStage for the seventh conjunct, and explicitly
constructs the fibre isomorphism and its normalization from the descended Weil
isomorphism and the prescribed zlPointWeilStageOmega.

Proved zlPointHeartExact_of_essentialImage in Sheaf.Paper.PointHeartExactness.
It factors a fully faithful point-heart functor with finite-dimensional essential
image through FGModuleCat, transports its abelian structure through the resulting
equivalence, and proves preservation/reflection of finite limits, finite colimits,
zero objects, and short exact sequences. The essential-image holes do not include
these exactness properties or finite-dimensionality proofs.

Moved the existing definitions to PointHeartFiniteStageData and publicly
re-exported them. The move is necessary to let the separate steps use the original
interface without importing the theorem which uses them. A structural text check
confirms that every original declaration signature is unchanged. All non-theorem
bodies are unchanged except that zlPointWeilStageOmega now passes the scheme and
prime-invertibility arguments explicitly to localQbarPullbackStageIso, preserving
its mathematical definition while avoiding expensive inference. The original
attributes and options are retained with the definitions.
No source-library file is changed and no target signature changes.

Change record: coord/changes/R7-point-heart-finite-stage-interface.md.

## Proved and sorry left

Closed the original hole in WeilConjectures.zl_point_heart_finite_stage by a complete
Lean reduction. This is a decomposition, not a net proof completion: 1 original
hole closed and 4 holes added. Also proved the new helper
WeilConjectures.zlPointHeartExact_of_essentialImage with no sorry.

The four remaining holes, each exactly `:= by sorry` in its own new module, are:

- WeilConjectures.zl_point_heart_essential_images
  (lem-zl-point-heart-essential-images): full faithfulness, additivity and essential
  image for the two specified heart functors; excludes all exactness properties.
- WeilConjectures.zl_point_heart_truncation_squares
  (lem-zl-point-heart-truncation-squares): canonical rational/common truncation
  comparisons and their scalar squares; excludes hearts and Weil descent.
- WeilConjectures.zl_point_heart_scalar_normalizations
  (lem-zl-point-heart-scalar-normalizations): only the identity and tower equations
  for the prescribed scalar comparison.
- WeilConjectures.zl_point_weil_simultaneous_descent
  (lem-zl-point-weil-simultaneous-descent): finite-stage carrier and Weil structure
  data, excluding geometric points and fibre normalization, which are constructed
  in the main theorem.

Each statement has its source, complete proof in words and DAG node. None is the
whole original theorem under another name, and no definition contains sorry.
The zero module, identity coefficient map, repeated fields and a raw representative
which need not itself be in the heart were checked against the mathematical plans.

## No longer needed

The assembly no longer directly imports these original proof-plan modules:
Sheaf.Paper.PointProEtaleSectionsExactOfUniverses,
Sheaf.CategoryTheory.TruncationsAndHomotopyColimits,
Sheaf.Paper.PointFdComplexes, Sheaf.Paper.ConstructibleTruncations,
Sheaf.Paper.PointFibreEquivalence,
Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison,
Sheaf.Paper.PointSectionsScalarExtension,
Sheaf.Paper.FieldCohomologyScalarExtension,
WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology,
Mathlib.Algebra.Module.LocalizedModule.Exact,
Mathlib.Algebra.Homology.ShortComplex.PreservesHomology,
Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful,
Mathlib.Algebra.Colimit.Module,
Sheaf.NumberTheory.Padics.FiniteCoefficientFields,
Mathlib.Algebra.Homology.DerivedCategory.Basic,
and Mathlib.LinearAlgebra.TensorProduct.Basic.

Mathlib.Algebra.Homology.DerivedCategory.TStructure is retained privately by the
shared interface. Original public prerequisites are retained there and re-exported.
The split-off mathematical steps still require the old plan's substantive
cohomology, fibre, truncation and colimit facts, so this is not a claim that those
nodes can be withdrawn globally. Their dependencies are retained in the new nodes.
All original top-level tool_uses entries are removed from the assembly node, whose
proof now uses the split-off steps; this does not withdraw those tools from their
new mathematical consumers. No module or DAG node is withdrawn. The unit's original
dimension-zero route and its parent lem-zl-point-weil-heart-flag are retained.

## Where the brief, the DAG or earlier work was wrong

The target's seventh conjunct is precisely the already proved
DerivedCategory.coefficientQbarCohomology_changeStage at degree zero; it does not
need a new argument. The old proof-plan imports did not themselves give a ready
restriction-to-hearts theorem with these specified realizations or the raw-target
finite-stage witness. The four holes isolate those substantive steps while the
assembly proves the available glue. No statement is disputed or weakened.

The advisory alternative PointRealizationStandardCohomology has no current source
file in the library, so it was not imported or duplicated. No absence of an importer
was used as an argument to withdraw anything.

## New nodes

- def-zl-point-heart-finite-stage-data records the existing interface moved
  into the shared data module and publicly re-exported by the original module.
- lem-zl-point-heart-exactness-from-image records the proved generic exactness
  argument through FGModuleCat.
- lem-zl-point-heart-essential-images isolates old steps 1--3 and 5--6, excluding
  exactness and finite-dimensionality that the main proof now supplies.
- lem-zl-point-heart-truncation-squares isolates the canonical comparison parts of
  old steps 1--2 and 4.
- lem-zl-point-heart-scalar-normalizations isolates the identity/tower part of old
  step 4.
- lem-zl-point-weil-simultaneous-descent isolates the finite carrier and structure
  data of old steps 5 and 8--9, excluding the constructed fibre clause of step 10.

The parent node's proof and proof_deps now follow the Lean assembly. Its Lean
attachment retains the original theorem; moved declarations are attached to the
shared interface node. The only change record is
coord/changes/R7-point-heart-finite-stage-interface.md.

The essential-image step uses the generic tools
lem-weil-point-proetale-sections-exact, prop-constructible-truncations,
lem-weil-point-fibre-equivalence, lem-pod-texact-truncation-comparison and
lem-weil-heart-short-exact-triangles as in the original reviewed plan. The truncation
step uses the generic truncation, fibre and scalar-comparison tools from that same
plan. The scalar-normalization step uses lem-weil-point-sections-scalar-extension
and lem-weil-cohomology-commutes-scalar-extension. These are tool uses for the
maintainer to record on the new nodes; they preserve the original argument rather
than changing a unit route.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
