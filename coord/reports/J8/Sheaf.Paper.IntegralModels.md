## What changed

Sheaf.Paper.IntegralModels now assembles every conjunct of integral_models in Lean.
The opening equality uses localizingClosure_ctf_equals_bc. The pullback clause
uses integralModelsOperations, the exact inverse-image/left-derived comparison,
and constructibility repleteness. Tensor and extension by zero are direct
applications of integralModelsOperations. The last three clauses apply
integral_models_generators with the original lattice and positive reductions.
The two constructibility criteria combine the Stacks iff, pointwise completeness
iff and residue iff using transitivity and and_congr.

Three genuinely separate comparisons are stated in their own modules:
IntegralModelsEmbeddedCompletion, IntegralModelsEmbeddedStacksCriterion, and
IntegralModelsEmbeddedResidueComparison. Their docstrings give full proof arguments
and sources. They address arbitrary unbounded complexes, impose no extra hypothesis
on the main theorem, and each is strictly a part of its assertion.

IntegralModelsEmbedded extracts the original scalar constructions and predicates
without changing names, types or data. This avoids a comparison-helper/main-theorem
import cycle. It adds residueConstructible as the original residue conjunction;
stacksConstructible itself keeps its original body. All original public imports
and declaration availability are preserved. The extraction and all 46 consumer
checks are recorded in coord/changes/J8-integral-models-embedded-definitions.md.
No consumer is edited and there are no forced adaptations.

All 18 pre-existing extracted declaration signatures and bodies were compared
against the original after removing comments and whitespace; every comparison
matched. The main theorem statement was compared byte for byte and matched.

The parent DAG proof follows the actual assembly and the extracted definitions
have a separate attachment. The unit route is retained: completion and common
quotients, the Stacks criterion, field Tor bounds and etale comparison, operations,
and lattice generation all remain represented in the dependency graph.

## Proved and sorry left

Closed the sole original hole: AlgebraicGeometry.ProEtale.integral_models
(node sk-lem-integral-models). Its statement is byte-identical to the original.
There are zero sorry tokens in the item module and zero in the definition module.

Added three holes, each exactly a public named theorem with := by sorry:

- AlgebraicGeometry.ProEtale.integralModelsEmbeddedCompletion
  (lem-sfb-embedded-integral-completion).
- AlgebraicGeometry.ProEtale.integralModelsEmbeddedStacksCriterion
  (lem-sfb-embedded-integral-stacks-criterion).
- AlgebraicGeometry.ProEtale.integralModelsEmbeddedResidueComparison
  (lem-sfb-embedded-integral-residue-comparison).

This is a decomposition: one original hole closed and three separately stated
comparison holes added, for a packet net of minus two holes closed. It is not
claimed as a complete proof of the underlying coefficient comparisons. The main
assembly itself is complete and has compiled against these declarations.

The coefficient constructions use real constant sheafification, constant continuous
functions, actual quotient maps, exact scalar restriction and the original
intrinsic realization. No data is chosen from a new unproved existence theorem.

## No longer needed

Removed direct proof imports from IntegralModels:

- WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat.
- Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat.
- Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison.
- Sheaf.Paper.CartesianCoefficients.
- Sheaf.AlgebraicGeometry.IntegralConstantCompletion.

The direct flat-sheaf/K-flat proof steps
lem-pc-sites-modules-sheafification-flat and
lem-pc-bounded-above-flat-kflat-site are replaced by the already proved
lem-sfb-constant-field-tor-bounds. Their obsolete top-level tool_uses entries
are removed. The field-Tor lemma retains its own dependencies; no claim is made
that these modules disappear from the whole target closure.

The constructible comparison and integral completion are now used in the
corresponding separate comparison arguments. Cartesian exactness is already
provided through integralModelsOperations and its published exactness instance;
the main proof does not invoke cartesianCoefficients again. No mathematical
unit is bypassed. No modules are withdrawn or claimed pruned from target closure.
No source-library declarations are edited, deleted or replaced by sorry.

The source arguments were checked in literature/blueprint/latest and in the
Stacks proetale.tex section-derived-completion-noetherian (flatness, common
quotients and complete-category restriction), lemma-naive-completion (canonical
quotient-limit unit), and the definition and description of D_cons.

## Where the brief, the DAG or earlier work was wrong

The existing integral_models_stacks and integral_constant_completion declarations
use a field in the scheme universe and spectral integer coefficients. The assigned
statement instead uses a finite field embedded in PadicAlgCl in Type 0 and an
independent scheme universe. They cannot be applied by reflexivity: the spectral
norm/ring comparison, constant and continuous coefficient squares, small-site
transport, and uniformizer independence must be provided. Existing
integralCoefficientExtComparison gives an additive module equivalence preserving
constructible modules; it does not give the scalar/quotient square or completeness
transport needed here. The new lemmas isolate these precise gaps instead of
changing a universe or ambient category in the main theorem.

The originally repeated direct proof of residue-field flatness/K-flatness is
unnecessary given the existing constant-field Tor-bound theorem. The remaining
residue comparison must additionally identify the specified intrinsic realization
and bounded etale essential image; it is not merely a Tor-bound assertion.

Edge cases checked on the new statements: zero complex, empty Noetherian scheme,
arbitrary unbounded K, ell distinct from or equal to the residue characteristic of
the base, arbitrary associates pi generating the maximal ideal, and independent
coefficient/scheme universes. Only the outer main theorem keeps the given
finite-type field setting. The helper comparisons do not require it.

The interrupted compile was checked before any retry; no earlier delivery was
recorded. The resumed full compile succeeded for all five modules. Profiling
showed residue-statement elaboration below one second; its previous timeout did
not expose a slow definition in that statement. Profiling options were removed.

## New nodes

- def-sfb-embedded-integral-model-coefficients: attachment for the extracted actual
  scalar constructions, completeness predicates, Stacks predicate and first-residue
  etale-origin predicate, plus the named residue conjunction. No proof holes.
- lem-sfb-embedded-integral-completion: complete-object equivalence and pointwise
  preservation/reflection of completeness under the canonical restriction, with
  no boundedness assumption. Sources: unit first paragraph, Stacks 099I/099L/099M/0A07.
- lem-sfb-embedded-integral-stacks-criterion: universe-independent embedded version
  of the Stacks criterion, transported through normalized coefficient squares.
  Source: integral-models-stacks detail and Stacks 09C1.
- lem-sfb-embedded-integral-residue-comparison: finite constant first-reduction
  constructibility/Tor condition iff bounded constructible etale origin of the
  completed reduction under the specified intrinsic realization. Sources: unit
  first paragraph and Stacks 03ET/06YQ/09C1.

Change record: coord/changes/J8-integral-models-embedded-definitions.md.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
