## What changed

Factored the data declarations into ProjectiveBundleTautologicalData to allow independent
construction modules without an import cycle. Public names and signatures are preserved.
The frame-section composite is factored through a named frame vector; both composites
are irreducible and hidden across module boundaries with `@[no_expose]`.
A proved equation exposes the quotient step; a new proved IsIso lemma exposes
the frame-vector property that rank zero needs without unfolding the composite. This addresses the
retained attempt's elaboration timeout. The change record gives the definition change.

The original existence theorem now assembles frame models, base-change coherence and
coordinate geometry. Its private helpers prove pullback of fixed rank, properness and
invertibility. ProjectiveBundleRankZero has a complete proof body: its frame generator identifies
the quotient as an isomorphism on the rank-one frame cover, and open-cover reflection
makes it an isomorphism globally. The structural isomorphism uses projective zero-space.

Coordinate geometry now proves the affine chart with its coordinate-ratio equations,
Cartier regularity of every coordinate divisor, its associated line bundle O(1), and
containment of the coordinate intersection in the zeroth chart. The coordinate point is also fully proved: the quotient by all affine variables is
the coefficient ring, and the unique surviving subscheme chart identifies the structural
morphism as an isomorphism. The hyperplane identification is also proved in ProjectiveBundleCoordinateSubschemes.
The point isomorphism supplies reducedness. No target statement is changed.

All seven delivery modules and the seven direct consumers listed in the change record
compiled through lcompile.py; the direct consumers require no adaptations.
The mandatory downstream scan completed: 239 transitive downstream modules, and only
the item itself uses projectiveBundleFrameSection textually. No consumer is edited. A declaration-table comparison also confirms that all 22
existing declaration signatures match the shared source.

## Proved and sorry left

Closed the original hole AlgebraicGeometry.exists_projectiveBundleTautologicalGeometry.
This is a decomposition, not a proof free of sorry: one original hole becomes two
strictly partial construction holes. The original module contains zero sorry.

Also completed the proof bodies of AlgebraicGeometry.exists_projectiveBundleCoordinateSubschemes,
AlgebraicGeometry.exists_projectiveBundleCoordinateGeometry, and
AlgebraicGeometry.exists_projectiveBundleRankZero, completing the
coordinate-construction proof by proving its affine, ratio, divisor, line-bundle
and chart-containment clauses, as well as the complete scheme-theoretic coordinate point. No sorry occurs inside a definition or private theorem.

The axiom audit of exists_projectiveBundleRankZero still reports sorryAx because
ProjectiveBundleFrameChart itself depends on existing upstream holes. Its proof body
and frame-section equation have no local holes; this is not a claim of axiom-free
closure. The tensor-adjunction comparison, flat-cover reflection and projective
zero-space APIs individually use only propext, Classical.choice and Quot.sound.
The frame-section refactor recovers the original expanded composite after unfolding
the vector and reassociating composition by Category.assoc. The proved API equation
exposes the quotient factor without expanding that composite.

Exactly two sorry remain, each the entire proof of its named public theorem:

- AlgebraicGeometry.exists_projectiveBundleFrameModels
  (lem-pur-projective-bundle-frame-models): construct the affine symmetric
  gradings, glue the twist and tautological quotient, and normalize all frame charts
  (parent steps 1--4).
- AlgebraicGeometry.exists_projectiveBundleBaseChangeCoherence
  (lem-pur-projective-bundle-base-change-coherence): construct the graded
  pullback data and degree-one theta and prove identity/composition coherence
  (parent steps 6--9).

## No longer needed

The assembling proof no longer directly imports affine Proj scalar extension,
module-sheaf gluing, symmetric-algebra base change, module pullback affine sections,
relative-Proj functoriality, standard charts or symmetric grading. These remain planned dependencies of the lower residual construction nodes; their
modules are not claimed globally unnecessary.
The original public imports are retained in the item and also used by the extracted data module.
The removed original direct proof imports are:

- WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
- Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension
- Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
- Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
- Sheaf.CategoryTheory.SiteModuleSheafGluing
- WeilConjectures.RingTheory.SymmetricAlgebraBaseChange
- WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
- WeilConjectures.AlgebraicGeometry.ProjectiveSpace
- WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
- WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
- WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
- WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
- WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
- WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous

Removed obsolete direct tool approvals on the parent node (the corresponding
constructions now occur below the parent): def-nagata-effective-cartier-ideal, def-nagata-relative-proj, def-nagata-relative-projective-space, def-pc-divisor-line-bundle, def-pc-module-pullback, def-weil-pbc-proj-twisting-sheaf, lem-nagata-affine-proj-scalar-extension, lem-weil-pbc-dehomogenization-polynomial-ring, lem-weil-pbc-module-pullback-affine-sections, lem-weil-pbc-module-pullback-quasi-coherent, lem-weil-pbc-projective-space-standard-charts, lem-weil-pbc-quasi-coherent-symmetric-algebra, lem-weil-pbc-site-module-sheaf-gluing, lem-weil-pbc-symmetric-algebra-base-change, lem-weil-pbc-symmetric-algebra-graded, lemma-nagata-relative-proj-base-change-arbitrary, prop-nagata-proj-standard-open, prop-nagata-relative-proj-functoriality.

The coordinate proof does not need node lem-weil-pbc-projective-space-standard-charts
(module Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts) or the homogeneous-polynomial helper: it uses the existing proved CoordinateSectionChart,
ChartPolynomial APIs directly. The coordinate Cartier and dual-bundle
arguments need no new residual lemma. No blueprint unit or geometric clause is pruned.
The retained whole-system restatement is absent: it is not a valid reduction.

Unused proof imports removed from ProjectiveBundleFrameModels: WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded, WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality, Sheaf.CategoryTheory.SiteModuleSheafGluing, WeilConjectures.RingTheory.SymmetricAlgebraBaseChange, Mathlib.LinearAlgebra.SymmetricAlgebra.Basis. These imports were used only by the proposed construction in the docstring, not by the residual theorem proof.

Unused proof imports removed from ProjectiveBundleBaseChangeCoherence: WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded, WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections, WeilConjectures.RingTheory.SymmetricAlgebraBaseChange, Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension, Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction. These imports were used only by the proposed construction in the docstring, not by the residual theorem proof.

Removed the unused WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality import
from ProjectiveBundleCoordinateSubschemes. The proved hyperplane argument retains
WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartPolynomial for its chart-ring equations.

## Where the brief, the DAG or earlier work was wrong

The retained report incorrectly listed exists_projectiveBundleRankZero as a sorry,
called the extracted definitions verbatim despite the frame-vector factorization, and
reported an unsuccessful downstream scan. This report corrects all three: rank zero
is proved, the factorization is explicit in the change record, and the scan completed.
The retained coordinate hole is now closed by a complete proof body. The resumed
construction audit also corrects the earlier characterization of the quotient-geometry
theorem as a mere existence assertion: it includes a quotient universal property. The
remaining obstacle to that route is the extra affine twist-restriction normalization
and all-frame compatibility required by this item's interface. The original
statement and the blueprint unit's geometric route are preserved.


The earlier dry run exceeded its preflight subprocess budget after all seven modules
compiled. The retained frame-vector profile identified kernel expansion of the large
pullback-comparison composite (27.2 seconds for the rank-zero local lemma).
This session hides the frame vector and frame section with `@[no_expose]` and
provides the proved `projectiveBundleFrameVector_isIso` API. Rank zero uses this
API. The data module compiles in 16.0 seconds and rank zero in 8.4 seconds.
The exact delivery axiom probe passes on all seven modules: no disallowed axiom,
and direct sorry usage occurs only in the two named residual theorems above.
The probe reports its own generated long-line warning; delivered source files
have no such warnings. The required initial dry run stopped at the 72-minute
split-off budget rule before compiling or invoking preflight. The resumed dry run recognizes two remaining construction holes and stops at the
72-minute split-off reference before compilation. This is a policy refusal, not a tool failure.
The current budget start is 2026-10-19 17:51:23 UTC (attempt 1792432283), despite retained
work and compilation logs from 2026-10-18/19 and earlier attempt identifiers starting at
1792330854. This reset is reported without changing launcher metadata.
All seven modules compiled in the restored import-order check. The item also compiles
with its original public imports retained (29.6 seconds). The first completed preflight
found two node-record errors: a structure signature included `where`, and rank zero
lacked the required leansearch entry. Both records are corrected, with the actual
search results recorded. The axiom probe timed out on the data and item modules in
that dry run; the tool defers those probes to the merge, while their earlier probes passed.

## New nodes

- def-pur-projective-bundle-tautological-data: extracted data and the explicit frame-vector
  factorization, with its proved frame-section equation.
- lem-pur-projective-bundle-frame-models: frame-model construction, steps 1--4.
- lem-pur-projective-bundle-base-change-coherence: coherent pullback data, steps 6--9.
- lem-pur-projective-bundle-rank-zero: fully proved rank-zero consequences of frame charts.
- lem-pur-projective-bundle-coordinate-geometry: the assembled coordinate result, with
  direct proofs of affine charts, regular divisors, line bundles and chart containment.
- lem-pur-projective-bundle-coordinate-subschemes: proved coordinate-hyperplane
  identification, including the n=0 edge case. The proof constructs the graded deletion
  map, proves its kernel and image, checks radicality chartwise, compares closed embeddings,
  reindexes the remaining coordinates and applies the existing free-module comparison.

Every residual theorem has a sourced complete proof in words and a matching node.

Change record: coord/changes/K4-projective-bundle-tautological-data.md.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
