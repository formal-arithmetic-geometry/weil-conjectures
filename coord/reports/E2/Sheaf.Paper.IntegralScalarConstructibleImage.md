## What changed

Replaced the sole proof hole in
`Sheaf.Paper.IntegralScalarConstructibleImage` by a complete Lean assembly from
ordinary integral-model and exact scalar-encoding comparisons. The assigned
statement, universes and all its hypotheses and conclusions are unchanged.

The proof explicitly constructs the coefficient isomorphism and proves every finite
residue normalization. It compares the given norm with the spectral norm, constructs
the actual/WithAbs and ULift continuous section charts, and uses the existing
normalized completion comparison and limiting residue cone. It applies
`integralStratifiedPerfectCharacterization`, retaining the completed object's actual
etale-origin property. Exact equivalences preserve cohomology and boundedness.
The ordinary scalar square is derived by uniqueness of the existing universal
left-derived functors; the existing bounded-constructible exact-scalar-extension
theorem supplies the rational image. The proved generic Serre helper applies to the
actual continuous field coefficients and supplies triangulation without introducing
an algebraic closure.

Added `ContinuousIntegralModelEncodingUniverses` and
`ContinuousScalarEncodingUniverses`, one ordinary comparison theorem per module.
These are strictly separate degree-zero arguments from the source; neither assumes
or concludes the assigned completed-derived scalar-image theorem. The scalar module
also constructs the actual internal integral inclusion and proves its ring-object
homomorphism instance.

Moved the seven existing continuous encoding declarations, with unchanged signatures
and bodies, to `ContinuousModuleEncodingUniverses`. The assigned module publicly
imports that module, preserving its API and avoiding an import cycle with the
ordinary comparison lemmas. The existing ownership record for the four continuous
encodings is retargeted; a definition node records the other three existing helpers.
No adopted `WeilConjectures` module, target statement or other group's module changes.
See `coord/changes/E2-continuous-module-encoding-universes.md`.

Validation: the main module compiled without errors in 22.3 seconds through
`lcompile.py`; the three helper modules have also compiled. All three retained
public declaration signatures are byte-identical to the shared source, and a
comment-stripped comparison verifies that all seven moved declarations are identical.
All delivered Lean lines have at most 100 characters. The unchanged direct consumer
compiled in 31.0 seconds. The axiom audit of the main theorem reports the expected
`propext`, `Classical.choice`, `Quot.sound` and `sorryAx`; the last reflects the
recorded unfinished comparison dependencies. Final delivery reruns packet checks.

## Proved and sorry left

Closed the original textual hole in
`AlgebraicGeometry.Scheme.integralScalarConstructibleImage`
(node `lem-weil-pbc-integral-scalar-constructible-image`). Its proof contains no
`sorry`. The private topology/ULift comparison, residue-normalized coefficient
construction and actual-field Serre/triangulation assembly are all proved.

Added exactly two holes, each the entire proof of its named public theorem:

- `AlgebraicGeometry.Scheme.continuousIntegralModelEncodingUniverses`, in
  `Sheaf.Paper.ContinuousIntegralModelEncodingUniverses`, node
  `lem-weil-pbc-continuous-integral-model-encoding-universes`.
- `AlgebraicGeometry.ProEtale.CondensedRing.continuousScalarEncodingUniverses`, in
  `Sheaf.Paper.ContinuousScalarEncodingUniverses`, node
  `lem-weil-pbc-continuous-scalar-encoding-universes`.

Thus this is a decomposition: one original hole closed, two strictly smaller
ordinary-comparison holes added, net -1 by textual hole counting. It is not an
axiom-free proof of the target. The assigned module has zero remaining textual
holes, and the whole packet has two. No hole is added to a definition or instance.
The seven relocated helpers retain their existing complete bodies, and the new
`continuousInternalScalarMapUniverses_isMonHom` instance is proved.

The model lemma isolates transport of finite scalar presentations through the
specified ordinary section equivalence, stratum inverse images and slice sites.
Its conclusion is degree-zero constructibility of one ordinary module. The scalar
lemma isolates exact localization and its ordinary extension comparison for
arbitrary modules. It contains no derived object, cohomology, completed-constructible
hypothesis, or triangulation assertion. The main proof supplies all those steps.
Both remaining statements have their source, a complete argument in words and edge
cases in the docstrings and matching DAG records. Zero modules, rank-zero finite
presentations, torsion scalar models and the empty base are included.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.Paper.ContinuousChartSchemeNaturality`.
- `Sheaf.Paper.ProfinitePointPullback`.
- `Sheaf.Paper.CompletedRealizationDerivedCohomology`.
- `Sheaf.AlgebraicGeometry.ProEtaleLocalDerivedRestrictionComparisons`.
- `Sheaf.Paper.ContinuousScalarDerivedEncoding`.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`.
- `Sheaf.CategoryTheory.SiteInverseImageTensor`.

The corresponding old direct proof dependencies are superseded as follows:

- `lem-weil-pbc-completed-realization-derived-cohomology` and
  `lem-weil-pbc-local-derived-restriction-comparisons`: the characterization gives
  cohomology models directly; the exact encoding's generic cohomology isomorphism
  handles the derived step.
- `lem-weil-pbc-continuous-scalar-derived-encoding`: the existing declaration fixes
  `E : Type`, whereas this item uses `E : Type u`. The new ordinary comparison uses
  the exact encodings of the assigned statement, and the derived comparison is
  proved in the main module by universal derived uniqueness.
- `lem-weil-pbc-left-exact-site-inverse-image-tensor` and
  `def-pur-sheaf-tensor-product`: the existing generic
  `lem-weil-pbc-bounded-constructible-exact-scalar-extension` handles preservation
  of internal presentations; no separate local derived tensor calculation is used.
- `def-weil-algebraic-closure`: generic Serre closure and local finite freeness
  apply directly to the specified continuous field ring.
- `lem-weil-pbc-profinite-point-pullback` and
  `def-sc-finitely-presented-module` are no longer separate direct dependencies of
  the main assembly. The latter remains needed by the new ordinary model lemma.
- `def-weil-pbc-continuous-coefficient-module-encoding`,
  `def-weil-pbc-internal-abelian-sheaf-module-equivalence`,
  `lem-weil-pbc-continuous-chart-scheme-naturality`, and
  `lem-weil-pbc-continuous-coefficients-immersion-restriction` are incorporated
  through the specified encoding and ordinary model interfaces, rather than being
  separate direct proof steps of the main theorem.
- `def-weil-pbc-condensed-e-module-category` remains a statement dependency but
  need not be a separate proof dependency.

The original public imports remain available, directly or via the public encoding
module. No module is withdrawn or claimed globally unreachable. Some removed direct
imports remain transitively needed by the ordinary comparison lemmas or other
library consumers; no declaration is removed from the adopted source library.

## Where the brief, the DAG or earlier work was wrong

The planned existing scalar-derived-encoding declaration is fixed to universe-zero
coefficients; it does not directly apply to this arbitrary-universe statement.
The normalized integral local-model interface elsewhere uses the spectral/WithAbs
completed-ring encoding, not this item's actual-norm continuous section-action
encoding. Applying it requires another substantial coefficient and local-model
comparison, rather than `exact` with that theorem. The new degree-zero statements
isolate those interface arguments without changing any coefficient convention.

The algebraic-closure passage in the old last proof step is unnecessary. The generic
proved Serre helper inside the existing module applies to the actual ring and its
finite-free local presentations. This avoids changing the field or its topology.

There is no disputed statement, no unit-route change, no source-library change and
no forced adaptation of another group's module. The moved encoding definitions
are mathematically identical to their original versions. No arbitrary data witness
is selected from a mere existence theorem.

## New nodes

`def-weil-pbc-completed-continuous-module-encoding-universes` records the relocated,
already constructed completed equivalence and the two already proved inverse
additivity instances. It has no proof hole. The four other encodings keep their
existing definition node, with only its Lean attachment moved.

`lem-weil-pbc-continuous-integral-model-encoding-universes` states the ordinary
transport from stratified finitely presented completed scalar models to the
archived internal finite-presentation condition. Its proof plan transports finite
presentations through exact reconstruction, inverse image and slice restriction.
It does not require finite cohomological bounds or a completed-derived object.

`lem-weil-pbc-continuous-scalar-encoding-universes` states exact ordinary
localization and the natural scalar-extension square for the actual integral
inclusion under the two specified arbitrary-universe encodings. The internal
scalar map is constructed and its ring-homomorphism property is proved. The
remaining ordinary comparison is separate from all derived-functor assembly.

The source is Bhatt--Scholze, Lemma 6.8.2, Definition 6.8.10, Proposition 6.8.11(3)
and the scalar construction of Proposition 6.8.14(2), with the section-action and
tensor adjunctions in Stacks Tags 00YV, 03EK and 03DA. Mathlib searches and blueprint
searches found no exact matching statement. Each new node records the source,
self-contained statement, full proof plan, searches and Lean attachment. The existing
main node's proof, proof dependencies and proof origin follow the implemented route.
Change record: `coord/changes/E2-continuous-module-encoding-universes.md`.

The first preflight rejected metadata only: a missing recorded LeanSearch query and
a new definition attachment incorrectly marked existing while giving a file. Added
the required search records and corrected the attachment. The original explicit
public coefficient-encoding import is retained as well as the new public import.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
