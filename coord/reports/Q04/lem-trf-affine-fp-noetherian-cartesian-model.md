## Worker report

The module `Sheaf.AlgebraicGeometry.AffineFpNoetherianCartesianModel` states
`AlgebraicGeometry.exists_affine_fp_noetherian_cartesian_model`, with its sole
proof `sorry`. No definitions, new nodes, dependency repairs or statement changes
are needed. The accepted five-step stage-1 split is preserved verbatim. The
inherited stage-1 stale-assignment refusal is inapplicable: brief-stage2 §0
explicitly makes a reviewed split the input to stage 2; the current node has no
Lean record and queue.tsv assigns stage 2.

The source read is `literature/stacks-project/algebra.tex`, Tag 00QJ,
`lemma-dimension-fibres-bounded-quasi-compact-open-upstairs`, especially the
finite-coefficient model paragraph at lines 31369–31380. It chooses the integer
subalgebra on the relation coefficients, the quotient by the same relations,
and the tensor identification. The module docstring reproduces each of the
node's five proof steps, including the canonical-map check and geometry.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| Commutative rings and the map R → B | `(R B : Type u) [CommRing R] [CommRing B] [Algebra R B]`; the map is `algebraMap R B`. Every ring map is represented by its induced algebra structure. |
| Finite presentation, the only finiteness hypothesis | `[Algebra.FinitePresentation R B]`. No Noetherianity, flatness, faithfulness, nonzero or characteristic restriction is assumed. |
| Existence of commutative rings R₀ and B₀ | `∃ (R₀ B₀ : CommRingCat.{u})`. These are arbitrary bundled commutative rings. |
| Maps R₀ → B₀ and R₀ → R | Existential `Algebra R₀ B₀` and `Algebra R₀ R`, with maps `algebraMap`. |
| Map B₀ → B and commutative ring square | `β : B₀ →+* B` and `β.comp (algebraMap R₀ B₀) = (algebraMap R B).comp (algebraMap R₀ R)`. |
| Finite type of R₀ over the integers | `(algebraMap ℤ R₀).FiniteType`, using the dependency's recorded `RingHom.FiniteType`. |
| Finite type of B₀ over R₀ | `(algebraMap R₀ B₀).FiniteType`. |
| Both model rings Noetherian | `IsNoetherianRing R₀ ∧ IsNoetherianRing B₀`. |
| R-algebra isomorphism B₀ ⊗[R₀] R ≅ B | The existential `e : @AlgEquiv R (B₀ ⊗[R₀] R) B ...` explicitly supplies `Algebra.TensorProduct.rightAlgebra`. Thus the R-action is via the right factor, not the left model ring. |
| Formula b ⊗ r ↦ β(b) φ(r) | `∀ (b : B₀) (r : R), e (b ⊗ₜ[R₀] r) = β b * algebraMap R B r`. |
| h and h₀ are the induced spectrum morphisms | `Spec.map (CommRingCat.ofHom (algebraMap R B))` and `Spec.map (CommRingCat.ofHom (algebraMap R₀ B₀)))`. |
| The displayed tensor isomorphism identifies h with base change of h₀ | Take `Spec.map` of the ring homomorphism underlying e and compose with `(pullbackSpecIso R₀ B₀ R).inv`. The statement gives its composition with each chosen pullback projection. This composite is an isomorphism because both factors are isomorphisms; no unrelated choice of geometric comparison is allowed. |
| Other projection q is induced by β | The first projection identity has right side `Spec.map (CommRingCat.ofHom β)`. |
| Identification is over Spec R | The second projection identity has right side `Spec.map (CommRingCat.ofHom (algebraMap R B))`. |
| h₀ locally of finite type | `LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R₀ B₀)))`. |
| q quasi-compact | `QuasiCompact (Spec.map (CommRingCat.ofHom β))`. |
| Spec B₀ locally Noetherian | `IsLocallyNoetherian (Spec B₀)`. |
| Spec B₀ quasi-compact | `CompactSpace (Spec B₀)`, with no separation axiom. |

The algebra structure implicit in `e.toRingEquiv` also needs the right-factor
instance. Both occurrences therefore spell out `@AlgEquiv.toRingEquiv` with that
same structure; there is no file-local instance or notation. `autoImplicit` is
false, and the universe and all ring, scalar and element variables are bound.

Dependency declarations, whose signatures and docstrings were read in the
current Mathlib sources:

- `def-weil-pbc-finitely-presented-algebra`:
  `Mathlib.RingTheory.FinitePresentation`, `Algebra.FinitePresentation`.
- `def-weil-pbc-finite-type-algebra`: `Mathlib.RingTheory.FiniteType`,
  `RingHom.FiniteType`. The algebra maps are deliberately passed to this
  recorded ring-homomorphism predicate.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` (all ideals finitely generated).
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`; its public imports expose
  `AlgebraicGeometry.QuasiCompact` from `Morphisms.QuasiCompact`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`.
- `def-weil-pbc-quasi-compact-scheme`: `Mathlib.Topology.Defs.Filter`,
  `CompactSpace`.
- The geometric comparison uses the already recorded proof leaf
  `lem-weil-pbc-fibre-product-affine-spectra`:
  `Mathlib.AlgebraicGeometry.Pullbacks`, `AlgebraicGeometry.pullbackSpecIso`.
- Tensor algebra structures use `Mathlib.RingTheory.TensorProduct.Maps`
  and its public `Basic` import, including
  `Algebra.TensorProduct.rightAlgebra`.

All remaining proof dependencies are imported from their recorded Mathlib
modules with plain `import`: multivariate polynomials, algebra homomorphisms
and quotient operations, presentation base change, affine morphisms and
separatedness, scheme limits and affine-scheme quasi-compactness. Finite-type
Noetherianity, tensor pushouts and the pointwise criterion are already exposed
by the statement imports. No dependency notion is recopied privately.

Edge cases checked before drafting: R may be the zero ring (then B is zero);
B may be zero with nonzero R (use the relation 1); a presentation may have
no variables or no relations; its set of coefficients may be empty (R₀ is
then the image of the integers); R may be non-Noetherian; there is no flatness
hypothesis. All corresponding spectra may be empty. The proof's coefficient
subalgebra and quotient fit in the same arbitrary universe u as the rings;
no finiteness of the underlying set, characteristic restriction or separate
smaller test universe is imposed. Both pure-tensor normalizations and
projection identities hold in these cases. No statement dispute or node
fault was found.

Searches for reuse were performed before writing, via the prescribed wrapper
and direct source searches. Exact wrapper queries and returned summaries:

- `leanfinder` query: `A finitely presented ring map admits a cartesian model over a finitely generated integer algebra with Noetherian source and target`. Result: 8 hits; `CommRingCat.isFinitelyPresentable_hom`, `AlgHom.FinitePresentation.of_finiteType`, `RingHom.FinitePresentation.of_finiteType`, `RingHom.FiniteType.of_finitePresentation`, `RingHom.FinitePresentation`, `AlgHom.FinitePresentation`, `Algebra.FinitePresentation.of_finiteType`, `Algebra.FinitePresentation.of_finitePresentation`.
- `leanfinder` query: `A finitely presented ring map admits a cartesian model over a finitely generated integer algebra with Noetherian source and target`. Result: 8 hits; `CommRingCat.isFinitelyPresentable_hom`, `AlgHom.FinitePresentation.of_finiteType`, `RingHom.FinitePresentation.of_finiteType`, `RingHom.FiniteType.of_finitePresentation`, `RingHom.FinitePresentation`, `AlgHom.FinitePresentation`, `Algebra.FinitePresentation.of_finiteType`, `Algebra.FinitePresentation.of_finitePresentation`.
- `grep` query: `exists.*(noetherian|Noetherian).*model|noetherian.*[Mm]odel|[Mm]odel.*[Nn]oetherian` in `AlgebraicGeometry`. Result: 0 hits; .
- `loogle` query: `Algebra.FinitePresentation, Algebra.FiniteType, IsNoetherianRing`. Result: 1 hits; `Algebra.FinitePresentation.of_finiteType`.
- `leansearch` query: `Every finitely presented algebra has a cartesian model over a finite type integer algebra with both model rings Noetherian`. Result: 8 hits; `AlgHom.FinitePresentation.of_finiteType`, `RingHom.FinitePresentation`, `Algebra.Presentation.finitePresentation_of_isFinite`, `Algebra.FinitePresentation.iff_quotient_mvPolynomial'`, `Algebra.FinitePresentation.iff`, `Module.finitePresentation_iff_finite`, `Algebra.Presentation.instFinitePresentationModelOfHasCoeffsOfFinite`, `Module.finitePresentation_of_finite`.
- `grep` query: `ModelOfHasCoeffs|exists_noetherian_model|noetherian_model` in `RingTheory`. Result: 10 hits; `Mathlib/RingTheory/Smooth/NoetherianDescent.lean`, `Mathlib/RingTheory/Smooth/NoetherianDescent.lean`, `Mathlib/RingTheory/Smooth/NoetherianDescent.lean`, `Mathlib/RingTheory/Smooth/NoetherianDescent.lean`, `Mathlib/RingTheory/Smooth/NoetherianDescent.lean`, `Mathlib/RingTheory/Extension/Presentation/Core.lean`, `Mathlib/RingTheory/Extension/Presentation/Core.lean`, `Mathlib/RingTheory/Extension/Presentation/Core.lean`.

The `leanfinder` query was repeated after an interrupted provider call; the
search log confirmed both results. No delivery or other mutation was repeated.
LeanFinder and LeanSearch locate finite-presentation criteria and presentation
model components, not the complete existential statement. Loogle returns only
`Algebra.FinitePresentation.of_finiteType`, which assumes an already Noetherian
base and constructs no model. The algebraic-geometry grep found no match.
The ring-theory grep found `Algebra.Presentation.ModelOfHasCoeffs`, its tensor
isomorphism and smooth-specific Noetherian descent. The presentation API's
full definitions and isomorphism formula were read in
`Mathlib/RingTheory/Extension/Presentation/Core.lean`; these are components of
the proof, not a theorem giving the complete node with its geometric clauses.

Direct `rg -n` searches of `lean/WeilConjectures` and `lean/Sheaf` used
`noetherian.*[Mm]odel|[Nn]oetherianCartesian|finitePresentation.*[Mm]odel|affineFpNoetherian`.
They locate smooth, flat, pointed or limit models with different hypotheses,
not this statement. In particular, the full signature of
`AlgebraicGeometry.exists_noetherian_model_with_section` in upstream
`SectionNoetherianDescent` requires a section and does not supply this affine
ring-and-tensor model. Searching the item id in `lean/WeilConjectures` gave
no match. Searching both source trees and `dag/lean_names_upstream.json` for
`exists_affine_fp_noetherian_cartesian_model|affine_fp_noetherian_cartesian`
gave no existing declaration. Consequently the delivery adds one theorem,
using the existing notions throughout.

Validation: every compiler invocation uses the prescribed `scompile.py` on
this single module. The initial compiler check found two missing right-factor
algebra instances in the projections; these were supplied explicitly. The
final compile and the required delivery preflight are recorded below.

Final validation: `scompile.py` successfully compiled both the sandbox module
and its actual library module (1.4 seconds each), with no errors or warnings.
`deliver2.py --no-push` returned `OK (dry run)` at `c45d68c6cdd`: preflight and
per-file compile passed. A local comparison confirmed that `lean` is the only
changed node field, its recorded signature is verbatim, all Lean lines are
at most 100 characters, and the sole theorem proof is `by sorry`.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
