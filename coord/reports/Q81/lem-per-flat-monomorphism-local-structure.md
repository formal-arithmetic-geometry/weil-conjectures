## Worker report

The module `Sheaf.AlgebraicGeometry.FlatMonomorphismLocalStructure` states
`AlgebraicGeometry.flat_monomorphism_local_structure`, with its only proof `by sorry`.
It introduces no definitions, helper axioms, or additional nodes. The accepted stage-1
statement, dependencies, and eight-step proof are preserved verbatim in the node;
only its `lean` field changes. The inherited unchanged-item failure concerned stage 1:
the current item is queued at stage 2 and has no Lean record or Lean review.
There is no released repair note for this item.

The source was read directly in ILO, Travaux de Gabber, VIII 2.1.12, 2.1.14 and
2.2.12, printed pages 88--91. Paragraph 2.1.12 gives injectivity and the actual local
ring isomorphisms (citing Raynaud); 2.1.14 gives ideal extension; 2.2.12 explicitly
calls flat monomorphisms regular. The node's proof explains the additional fibre
description and Noetherian consequence. The theorem docstring carries all eight
proof steps, including the exactness argument for extension of ideals.

Hypothesis and conclusion correspondence:

| Node text | Lean rendering |
| --- | --- |
| Schemes X, Y and f : Y to X | `{X Y : Scheme.{u}} (f : Y ⟶ X)` |
| f quasi-compact | `[QuasiCompact f]` |
| f flat | `[Flat f]`, the recorded Mathlib notion, equivalent to stalkwise flatness |
| The diagonal Y to Y times_X Y is an isomorphism | `(_hdiag : IsIso (pullback.diagonal f))`; no additional finite-presentation or surjectivity hypothesis |
| f injective on points | `Function.Injective f`, using the underlying-point-map coercion |
| Every induced local ring map is an isomorphism | `∀ y : Y, IsIso (f.stalkMap y)`; the actual induced ring morphism, not existence of an unspecified ring isomorphism |
| The scheme-theoretic fibre is empty or canonically Spec kappa(x) | `∀ x : X, IsEmpty (f.fiber x) ∨ IsIso (f.fiberToSpecResidueField x)` |
| The fibre is nonempty exactly on f(Y) | `Nonempty (f.fiber x) ↔ x ∈ Set.range f`, in the same quantifier as the fibre dichotomy |
| kappa(x) is the local ring modulo its maximal ideal | Mathlib's `X.residueField x`, defined as `CommRingCat.of (IsLocalRing.ResidueField (X.presheaf.stalk x))` |
| Flat with geometrically regular fibres, including the stated field-extension description | Original flatness is `[Flat f]`. For every `x`, every `K : Type u` with `[Field K]`, and every `ι : X.residueField x →+* K`, the actual pullback of `f.fiberToSpecResidueField x` along `Spec.map (CommRingCat.ofHom ι)` is empty or its second projection to Spec K is an isomorphism. Thus every nonempty extended fibre is canonically Spec K, as the node states; spectra of fields are regular. No replacement regularity predicate is introduced. |
| If X is Noetherian, Y is Noetherian | `IsNoetherian X → IsNoetherian Y` |
| Noetherian means a finite affine cover by spectra of Noetherian rings | Mathlib's `AlgebraicGeometry.IsNoetherian`, whose equivalence with precisely this condition is `isNoetherian_iff_of_finite_affine_openCover`; the Noetherian class here is not merely `IsLocallyNoetherian` |
| If X is reduced, Y is reduced | `IsReduced X → IsReduced Y`; the recorded sectionwise notion is equivalent to reduced stalks |
| Every conclusion after any base change T to X | `∀ (T : Scheme.{u}) (g : T ⟶ X), ...`, with source `pullback f g`, target T, and morphism `pullback.snd f g` |
| The base-changed morphism is regular | `Flat (pullback.snd f g)` and the repeated field-extension fibre dichotomy |
| Base-changed injectivity and induced local isomorphisms | `Function.Injective (pullback.snd f g)` and `∀ z : (pullback f g : Scheme.{u}), IsIso ((pullback.snd f g).stalkMap z)` |
| Base-changed canonical fibre description and exact image criterion | The repeated dichotomy for `(pullback.snd f g).fiber t` with its actual `fiberToSpecResidueField t`, and `Nonempty ... ↔ t ∈ Set.range (pullback.snd f g)` |
| Base-changed Noetherian and reduced conclusions conditional on T | `IsNoetherian T → IsNoetherian (pullback f g)` and `IsReduced T → IsReduced (pullback f g)` |

The universal field extensions and all schemes use the common explicitly bound universe
`u`; there is no independent smaller test-field universe. `set_option autoImplicit false`
forbids unbound variables. All pullbacks appearing as types of points or as arguments
of `IsEmpty` have explicit `Scheme.{u}` annotations: without those, type-directed
elaboration can select a pullback in the category of types instead of schemes.
There are no `let` or `show` binders in the statement, file-local notation, or private
definitions. The field-extension clause does not assert that an empty fibre is Spec K.

Dependency declarations read and used (all are the recorded declarations, not copies):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom` and `AlgebraicGeometry.Spec`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat`; `Flat.iff_flat_stalkMap` supplies its recorded stalkwise reading.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`; `AlgebraicGeometry.IsNoetherian` adds compactness,
  and `isNoetherian_iff_of_finite_affine_openCover` gives the finite-cover characterization.
- `def-pc-reduced-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsReduced`, with `isReduced_of_isReduced_stalk` and
  `isReduced_stalk_of_isReduced` verifying the local-ring interpretation.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and its recorded
  `AlgebraicGeometry.QuasiCompact` from `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
  Only the quasi-compact notion is a hypothesis; finite type is not assumed.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst` and `pullback.snd`.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`,
  `AlgebraicGeometry.Scheme.Hom.fiber`, `fiberι`, `fiberToSpecResidueField`.
  The canonical residue field and Spec map are those in the imported Mathlib interface.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, used by the finite-cover characterization. Its ideal-finite-generation
  reading is `isNoetherianRing_iff_ideal_fg`.

Statement dependency modules are public imports. Already stated proof dependencies have
plain imports: affine-open basis and stalk localization in `Mathlib.AlgebraicGeometry.AffineScheme`;
open factorization and monicity in `Mathlib.AlgebraicGeometry.OpenImmersion`;
`Mathlib.RingTheory.Localization.AtPrime.Basic`; local faithful flatness and tensor reflection
in `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra` and `.Basic`;
tensor pushout algebra in `Mathlib.RingTheory.TensorProduct.Basic` and `.Maps`;
`Mathlib.LinearAlgebra.TensorProduct.Defs`; exact tensoring in `Mathlib.RingTheory.Flat.Basic`.
Flat and quasi-compact base-change results are already included by the public imports.
The proof-only nodes `lem-sfb-monomorphism-into-field-coproduct` and
`lem-sfb-faithfully-flat-ring-epimorphism-isomorphism` have no recorded module or Mathlib
match in the read repository, so no import is invented for them. Their proof steps remain
in the docstring and DAG. They are not missing notions needed to type this statement.

Edge cases checked before writing:

- Empty Y: injectivity and stalk assertions are vacuous, all fibres are empty and all
  image tests are false. The empty scheme is reduced and Noetherian, including a finite
  empty affine cover. No global nonemptiness assumption appears.
- Identity f: the actual stalk maps, fibre maps, and field-extended structure maps are
  isomorphisms, with all image criteria true.
- The localization Spec Frac(Z) to Spec Z: quasi-compact flat monomorphism, not an open
  immersion or surjective morphism. The generic fibre is the residue-field spectrum and
  all other fibres are empty. The theorem adds neither of those stronger assumptions.
- Non-Noetherian or nonreduced X: the two permanence conclusions are implications;
  neither base property is silently required as a theorem hypothesis.
- Arbitrary field characteristic, the identity field extension, and nonalgebraic
  extensions are allowed; the field-extension binder requires neither finite degree
  nor algebraic closure. Zero rings cause empty spectra, not illicit field instances.
- Empty T, identity base change, and any nonflat base change g are allowed. Reducedness
  and Noetherianity after base change require the corresponding property of T itself.

Searches for an existing complete statement:

- `msearch.py leanfinder`: "A quasi-compact flat monomorphism of schemes induces
  isomorphisms on stalks, has empty or residue-field fibres, and preserves Noetherian and
  reduced schemes". Eight hits: closest `Flat.isIso_of_surjective_of_mono` requires
  surjectivity; `IsOpenImmersion.of_flat_of_mono` requires local finite presentation.
  Neither is the statement, and no combined theorem was found.
- `msearch.py loogle`: `AlgebraicGeometry.Flat, CategoryTheory.Mono`. Six hits: the two
  preceding theorems and four unrelated monicity-of-pushout-section lemmas.
- `msearch.py leansearch`: "quasi-compact flat monomorphism schemes local rings
  isomorphism Noetherian". Eight hits, including the same two restricted theorems,
  `Flat`, `QuasiCompact`, `quasiCompact_of_noetherianSpace_source`, and local criteria.
- `msearch.py grep`: `flat.*[Mm]ono|[Mm]ono.*flat` in `AlgebraicGeometry`. Eleven hits
  in FlatMono, Flat, and SchemeTheoreticallyDominant; no exact statement.
- `rg` in the project's `lean/WeilConjectures` and `lean/Sheaf` for the same concept,
  `flat_monomorphism`, `flatMonomorphism`, `flat_mono`, and the item id: only imports or
  uses of the restricted Mathlib FlatMono results, and unrelated flat tensor material.
  Exact proposed declaration name `flat_monomorphism_local_structure` has no hit in
  Mathlib or either project tree. The item id has no upstream name-index match.

No statement correction, missing statement notion, or mathematical dispute was found.
The source and all eight statement dependencies have usable interfaces.

Validation: every delivered Lean file is compiled with the prescribed server wrapper;
the only permitted diagnostic is the expected warning that the theorem uses `sorry`.
Delivery preflight and compilation are run by `deliver2.py --no-push` before pushing.

## Second reading by Q81

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
