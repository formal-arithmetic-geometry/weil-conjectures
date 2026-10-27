# Q38: lem-sfb-space-fitting-ideal-calculus, stage 2

## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceFittingIdealCalculus` states
`AlgebraicGeometry.AlgebraicSpace.existsUnique_zerothFittingIdeal`, with the one
postponed proof `by sorry`. Its auxiliary real definition `IsZerothFittingIdeal`
is exactly the affine characterization used in this statement; it introduces no
second ring Fitting ideal, module category, quasi-coherence predicate, ideal
notion or pullback map. There is no data chosen from an existence theorem here.

The inherited BLOCKED result confused the already-reviewed stage-1 split with a
stage-2 statement delivery. The live node has `reviewed` PASS from Q32 but has no
`lean` or `reviewed_lean`; `coord/queue.tsv` assigns it to stage 2, and there is
no repair note for it. The stage-handoff rule in `coord/brief-stage2.md` section 0
therefore applies. I preserved the statement, all six accepted proof steps and
all proof dependencies. This delivery only adds `lean` and the already-landed
statement prerequisites for quasi-coherent ideal subobjects, the commutative
structure sheaf and the full-site sheafification instances. No mathematical
statement correction or new DAG node is needed.

Clause-by-clause reading:

- The base scheme is `{S : Scheme.{u}}`; the space is `(X : AlgebraicSpace S)`.
  The explicit `universe u` retains the recorded space framework: schemes,
  coefficient rings and sections in `u`, small-etale site objects in `u+1`, and
  its morphisms in `u`. `set_option autoImplicit false` is active. There is no
  added identification of site-object and section universes.
- A sheaf of modules on the small-etale structure sheaf is `(M : X.Modules)`.
  `(hM : M.IsFinitePresentation)` is Mathlib's local cokernel presentation by
  two finite coproducts of the ring. `(hqc : M.IsQuasicoherent)` is the recorded
  quasi-coherence predicate. Both hypotheses in the node are explicit, even
  though Mathlib derives quasi-coherence from finite presentation.
- `I : QuasiCoherentIdeal X` is the existing subtype of subobjects of
  `SheafOfModules.unit X.structureSheaf` whose underlying module is
  quasi-coherent. Thus it is an actual ideal inclusion, identified by an
  isomorphism commuting with that inclusion, rather than an abstract ideal
  module or an arbitrary monomorphism supplied as a new hypothesis.
- `IsZerothFittingIdeal M I` quantifies over **every** `U : X.EtaleSite` with
  `IsAffine (X.etaleForget.obj U)`. These are the affine etale charts of the
  node. The ring `X.commStructureSheaf.obj.obj (op U)` is exactly the ordinary
  commutative global-section ring of that scheme. `M.val.obj (op U)` is
  `M(Spec A)`. The existential `h : Module.Finite ...` supplies a proof of
  finite generation on that chart so the existing `LinearMap.fittingIdealZero`
  can be used; it is a conclusion, not a finiteness assumption on charts.
- The equality between `Set.range (I.val.arrow.val.app (op U))` and the carrier
  of `@LinearMap.fittingIdealZero ... h` identifies the ideal as a submodule
  of the same section ring. For quasi-coherent ideals, this section equality
  on every affine etale chart is exactly restriction to the associated ideal
  sheaf in Tag 0CZ3: the affine associated-sheaf equivalence determines both
  the module and its inclusion. It is not merely an unspecified isomorphism.
- The subsequent universal `n`, linear map `pi`, and `Function.Surjective pi`
  clause identifies the same section image with `pi.presentationFittingIdeal 0`
  for **every** finite free generating surjection. That recorded definition
  is the ideal of all maximal kernel-row determinants. Its branch `n <= 0`
  is the unit ideal, including the rank-zero surjection onto the zero module.
- `exists I, ...` gives existence. The separate clause
  `forall J : QuasiCoherentIdeal X, IsZerothFittingIdeal M J -> J = I` gives
  uniqueness among **all** ideals with the affine characterization, without
  assuming finite type or compatibility with pullback of the competitor.
- `(I.val : X.Modules).IsFiniteType` is precisely etale-local finite generation
  as defined by Mathlib's local generators. No Noetherian hypothesis appears.
- `forall (X' : AlgebraicSpace S) (g : X' -> X)` covers every space morphism.
  `((moduleTensorPullback g).obj M).IsFinitePresentation` and its
  `.IsQuasicoherent` conjunct state both required properties of `g^* M`.
- The final `exists I' : QuasiCoherentIdeal X'` with
  `IsZerothFittingIdeal ((moduleTensorPullback g).obj M) I'` identifies the
  Fitting ideal on the source, by the same affine characterization. Uniqueness
  of such ideals is already asserted universally by the theorem for every
  space and module.
- `I'.val = Subobject.mk (image.iota (idealTensorMap g I))` is an equality of
  ideal **subobjects of the structure module**. In Lean the source uses
  `image.ι`. The reused `idealTensorMap` is adjoint to the inclusion followed
  by the canonical regular-function structure map; its chart formula is
  multiplication `b tensor j` to `b rho(j)`. Taking its categorical image is
  the sheaf image, not the sectionwise image on arbitrary non-affine objects.
  No injectivity of this tensor map is claimed or assumed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `Scheme.Hom`, the recorded scheme and scheme-morphism declarations.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleForget`, `structureSheaf`, `Modules`; the full-subcategory definition
  of spaces and actual regular-function structure presheaf are retained.
- `def-weil-size-convention` is recorded as a metatheoretic convention, not
  as a declaration. Its role is the explicit universe above.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and its
  existing `SheafOfModules.IsQuasicoherent` predicate, with the named slice
  sheafification instances. The theorem uses the underlying module predicate.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `ModuleDirectImageModel`, `moduleDirectImage`, `moduleTensorPullback`,
  `moduleTensorAdjunction`. I read the full direct-image model signature,
  including all chart projections, its limit and both naturality conditions.
- `Sheaf.RingTheory.FittingIdealZero`: `LinearMap.fittingIdealZero`, with
  precisely the finite module instance supplied by the affine conclusion.
- `Sheaf.RingTheory.PresentationFittingIdeal`:
  `LinearMap.presentationFittingIdeal`, which gives the kernel-row formula,
  and its recorded independence/base-change theorem as a proof prerequisite.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal`:
  `QuasiCoherentIdeal`, `idealTensorMap`. These are reused without alteration.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentAlgebra`:
  `commStructureSheaf`, whose section rings retain commutativity.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceCommAlgebraSheaf`:
  `etaleAlgebraModulesHasSheafify` and the associated full-site module
  instances support categorical images in the original section universe.
- Mathlib's `Subobject.mk`, `image.ι`, the sheaf module limits API,
  `SheafOfModules.IsFinitePresentation` and `SheafOfModules.IsFiniteType`
  give the remaining existing constructions and predicates.

The available proof-dependency modules are imported non-publicly:
`SchemeZariskiEtaleQuasiCoherentEquivalence`, `AlgebraicSpaceAffineChartCalculus`,
`SpaceChartTensorRealization`, `AlgebraicSpaceAffineEtaleCover`,
`AlgebraicSpaceFibreProductsEtaleCovers`, `AlgebraicSpaceModulePullbackQuasiCoherent`,
and the upstream `WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections`.
`PresentationFittingIdeal` is already public through `FittingIdealZero` because
its presentation-ideal definition occurs in the statement. The ordinary finite
presentation and determinant Mathlib modules are imported for the corresponding
proof dependencies; the finite-presentation tensor base-change leaf is in the
former. The three proof-only nodes `lem-sfb-space-qcoh-cartesian-chart-family`,
`lem-trf-fitting-ideal-sheaf-pullback`, and
`lem-sfb-space-qcoh-kernels-colimits` have no Lean record and no upstream
closed declaration in their current nodes; consequently they have no module
to import. They are not missing notions needed to type this statement. Their
accepted roles remain in the theorem's complete six-step proof docstring.

Sources and edge cases:

I opened `literature/stacks-project/spaces-divisors.tex`, section-fitting-ideals,
lemma-base-change-fitting-ideal and lemma-fitting-ideal-of-finitely-presented
(Tags 0CZ3, 0CZ4 and 0CZ5). They give the affine-chart characterization, image
ideal under arbitrary base change, and finite type for finite presentation.
The node's six-step proof is reproduced in natural language in the theorem's
docstring, with every step's cited prerequisites, the finite determinant
expansion, unit-normalized local tensor calculation, and descent of equality.

I checked the zero module (unit ideal), a positive-rank free module (zero
zeroth Fitting ideal), `A/(a)` (ideal `(a)`), the zero ring, and the empty
space. A zero-rank presentation is explicitly included; the determinant ideal
uses its existing unit-ideal branch. No nonempty-space hypothesis, positive
rank, quasi-compactness, Noetherianity or flatness is imposed. For the nonflat
map `Z -> Z/2` and `M = Z/2`, the source ideal is `2Z`, its tensor pullback
is nonzero, and its map to `Z/2` is zero; its image is the zero Fitting ideal
of the rank-one free `Z/2` module. This confirms that using an image rather
than an inclusion of the tensor pullback is essential. Finite-type and finite
presentation predicates are the already-recorded local notions.

Searches for an existing exact statement:

- Prescribed `msearch.py leanfinder`: query `Zeroth Fitting ideal of a finitely
  presented quasicoherent module on an algebraic space is finite type and
  commutes with arbitrary pullback`. Eight results concerned local finite
  presentations, their quasi-coherence, and finite-type generators; no ideal
  construction, uniqueness or image-pullback result.
- Prescribed `msearch.py loogle`: query `"Fitting"`. Twelve results concerned
  Lie-module Fitting decompositions, not Fitting ideals of presentations.
- Prescribed `msearch.py grep`: query
  `fittingIdeal|FittingIdeal|fitting_ideal`. Zero Mathlib hits.
- `rg` in the upstream `lean/WeilConjectures` and in `lean/Sheaf` for Fitting
  ideals and the item ID: existing ring presentation ideals, zeroth ring
  ideal, and scheme Fitting-ideal modules were found and read; none states
  the algebraic-space result. The scheme construction's type is a scheme
  `IdealSheafData`, not an ideal subobject on an algebraic-space etale site.
- `rg` over Mathlib, upstream and project sources for
  `IsZerothFittingIdeal|existsUnique_zerothFittingIdeal`: no pre-existing
  declaration of either new name. No source module carries this blueprint ID.

Validation: the required `scompile.py Q38 lem-sfb-space-fitting-ideal-calculus`
compiled the delivered file as both a sandbox module and its library module
on the server (13.9 seconds and 3.0 seconds respectively), with no errors or
unexpected warnings. Every definition has real data; the only `sorry` is the
named theorem matching this DAG node. The JSON signature is extracted verbatim
from the theorem keyword up to its `:=`, and only `lean` and the authorized
landed-definition additions to `stmt_deps` differ from the base node.

## Second reading by Q38

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
