## Worker report

The module `Sheaf.RingTheory.FlatNoetherianModelPrescribedElement` states
`Algebra.exists_flat_noetherian_model_prescribed_element`, with its sole proof
`sorry`. It introduces no definitions. The node's mathematical statement,
statement dependencies, and five-step proof are unchanged. Its docstring gives
that proof and identifies the Stacks sources and DAG dependencies.

Source checked: `literature/stacks-project/more-morphisms.tex`, Tag 056Y,
`lemma-slice-given-element`, second proof paragraph (lines 6188–6212).
The source first writes the base as a directed colimit of finite type integer
algebras, descends the flat finite presentation, and explicitly descends the
specified section `h` to `h₀`. The algebraic statement of this node expresses
exactly that step, with Noetherianity of both finite type model rings.

Clause-by-clause comparison:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| Commutative rings `A` and `B` | `{A : Type u} {B : Type v} [CommRing A] [CommRing B]` |
| Ring map `A → B` | `[Algebra A B]`, with ring map `algebraMap A B` |
| Flatness of this map | `[Module.Flat A B]`, equivalent to `RingHom.Flat (algebraMap A B)` by `RingHom.flat_algebraMap_iff` |
| Finite presentation over `A` | `[Algebra.FinitePresentation A B]` |
| Specified element `a ∈ B` | `(a : B)` |
| Existence of a subring of `A` containing the integer image | `∃ A₀ : Subalgebra ℤ A` |
| Finite generation over the integers | `Algebra.FiniteType ℤ A₀` |
| Existence of a commutative model algebra | `∃ (B₀ : Type (max u v)) (_ : CommRing B₀) (_ : Algebra A₀ B₀)` |
| Flatness over the actual model subring | `Module.Flat A₀ B₀` |
| Finite presentation of that algebra | `Algebra.FinitePresentation A₀ B₀` |
| Both model rings Noetherian | `IsNoetherianRing A₀ ∧ IsNoetherianRing B₀` |
| An element of the model algebra | `∃ (a₀ : B₀)` |
| An `A`-algebra isomorphism from the scalar extension to `B` | `(e : TensorProduct A₀ A B₀ ≃ₐ[A] B)` |
| The specified element descends through the isomorphism | `e (TensorProduct.tmul A₀ (1 : A) a₀) = a` |

`Subalgebra ℤ A` is precisely the requested subring with the integer image:
its `toSubring` is an actual subring of `A`, and `algebraMap_mem` includes each
integer. Conversely, every unital subring contains the integer image and is
closed under integer scalar multiplication, so it supplies such a subalgebra.
No injectivity of `ℤ → A` is required. The canonical instance
`Subalgebra.toAlgebra A₀` makes the map `A₀ → A` its inclusion; an arbitrary
replacement map is not quantified. `Algebra.FiniteType` is finite algebra
generation, not module finiteness or algebra finiteness.

The standard commutative algebra structure on `TensorProduct A₀ A B₀` is
Mathlib's algebra tensor product. Its left `A`-algebra structure is the one in
`e`. Both `a₀` and `e` are existential witnesses, with their exact value equation;
there is no choice construction or hollow definition. The universe variables
`u` and `v` are explicit and independent. A finite polynomial presentation over
`A₀` constructs a model in `Type u`; lifting its carrier to `Type (max u v)`
always supplies the displayed universe, so this choice excludes no case.

Dependency declarations read and used:

- `def-weil-pbc-flat-ring-map`: `Mathlib.RingTheory.RingHom.Flat`,
  `RingHom.Flat`, `Module.Flat`, and `RingHom.flat_algebraMap_iff`.
  The module-flatness definition was read in `Mathlib.RingTheory.Flat.Basic`.
- `def-weil-pbc-finitely-presented-algebra`:
  `Mathlib.RingTheory.FinitePresentation`, `Algebra.FinitePresentation`.
- `def-weil-pbc-module-tensor-product`: its Mathlib match `TensorProduct`
  and `TensorProduct.tmul` in `Mathlib.LinearAlgebra.TensorProduct.Defs`,
  with the algebra structure exposed by the public import
  `Mathlib.RingTheory.TensorProduct.Basic`. This Mathlib leaf needs no
  replacement node record.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`; its ideal-finiteness meaning is
  `isNoetherianRing_iff_ideal_fg`.
- `def-weil-pbc-category-colimit`: proof import
  `Mathlib.CategoryTheory.Limits.HasLimits`, `CategoryTheory.Limits.colimit`.
- `lem-weil-pbc-colimit-flat-ring-map`: proof import
  `WeilConjectures.RingTheory.ColimitFlatRingMap`,
  `RingHom.exists_eventually_flat_of_colimit_flat`. Its actual complete
  declaration and docstrings in that source were read.
- `lem-weil-pbc-finite-presentation-base-change-composition`: proof import
  `Mathlib.RingTheory.FiniteStability`, `Algebra.FinitePresentation.baseChange`;
  the other matched clause `Algebra.FinitePresentation.trans` is already
  exposed by `Mathlib.RingTheory.FinitePresentation`.
- `lem-weil-pbc-finite-type-algebra-noetherian`: proof import
  `Mathlib.RingTheory.FiniteType`, `Algebra.FiniteType.isNoetherianRing`.
  The signature's `Algebra.FiniteType` is already publicly exposed by
  `Mathlib.RingTheory.FinitePresentation`.

Edge cases checked mathematically before writing:

- If `A` is the zero ring, any unital `A`-algebra `B` is also the zero ring.
  The zero subring and zero model algebra satisfy the statement, with the
  unique possible element and isomorphism. No `Nontrivial` binder excludes it.
- If `B` is the zero ring over a nonzero `A`, take the prime subring and the
  zero model algebra. The zero module is flat and the zero algebra is finitely
  presented, as the quotient by `(1)`.
- In positive characteristic, the integer image is the prime subring, not a
  copy of `ℤ`; `Subalgebra ℤ A` correctly permits the noninjective integer map.
- For `A = ℚ` and `B = ℚ[t]/(t²)`, all elements have finitely many rational
  coefficients. Inverting their finitely many denominators in the model base
  gives the prescribed element over a free rank-two model algebra. This also
  checks that no smoothness or reducedness hypothesis was accidentally added.
- For `A = ℚ` and a presentation `B = ℚ[t]/(2t)`, the initial integer model
  `ℤ[t]/(2t)` is not flat. The existential subring permits adjoining `1/2`,
  after which the model is flat. The statement does not demand flatness of
  the initial coefficient model or freeze the integer subring.
- Zero chosen element, constants, and presentations with no variables or
  no relations are included. The conclusion does not require `a₀` to be
  nonzero, regular, or a generator.

Searches made on 2026-10-24:

- `msearch.py leanfinder`, query: "A flat finitely presented algebra and a
  prescribed element descend to a flat finitely presented algebra over a
  finite type integer subring with Noetherian model rings". Eight hits,
  led by `Algebra.Smooth.exists_finiteType`,
  `Algebra.Smooth.exists_subalgebra_finiteType`, and
  `Algebra.Smooth.exists_subalgebra_fg`. The descent theorems require
  smoothness and do not give the chosen-element equation. Their source
  signatures were inspected; none is this statement.
- `msearch.py loogle`, query: `Algebra.FinitePresentation, Module.Flat`.
  Five hits, all smoothness/etaleness criteria, including
  `Algebra.Etale.of_formallyUnramified_of_flat` and
  `Algebra.Smooth.of_formallySmooth_fiber`; no pointed model theorem.
- `msearch.py leansearch`, query: "A flat finitely presented algebra with a
  specified element descends to a flat finite presentation over a finitely
  generated integer subring, and both model rings are Noetherian".
  Eight hits: finite-presentation definitions and base change, module
  finiteness, presentations, and smooth flatness; no exact theorem.
- `msearch.py grep`, query: `noetherian.*model|model.*flat|descend.*element`,
  subdirectory `RingTheory`. One hit, the heading of
  `Mathlib/RingTheory/Smooth/NoetherianDescent.lean`; it concerns smoothness.
- Direct `rg` of the project and upstream ring-theory modules for flat model
  and prescribed-element terms, and of the entire upstream source for the
  blueprint id: no existing declaration of this node. Upstream
  `RingHom.exists_flat_finitePresentation_model` in
  `WeilConjectures.RingTheory.FlatFinitePresentationModel` was inspected:
  it supplies an abstract model base mapping to `A`, not a subring of `A`,
  and has no prescribed-element clause. Related flat-point and module-model
  statements also do not give the node's conclusion.
- Direct `rg` for the chosen declaration name and module name found no clash.
  The sibling DAG node `lem-trf-flat-subring-model-system` was checked: it
  has neither a current Lean record nor the specified-element/Noetherian
  statement, and is not a duplicate to record as `existing: true`.

No missing notion, unusable dependency, statement correction, or statement
reservation was found. No additional node or dependency module is delivered.

Validation: the prescribed `scompile.py` compiled both the sandbox form and
its library module form against the live server build with no errors or
warnings (6.4 s and 1.4 s respectively). The delivered module contains no
probe commands, local notation, local instances, auto-bound universes, or
definitions using postponed data.

The required `deliver2.py --no-push` dry run also passed the current server
preflight and per-file compilation. Exactly the module, the item's node record,
and this worker report are delivered; the only changed field of the node is
`lean`. Independent review is performed by the maintainer after delivery, as
specified in this dispatch; no second worker reading is claimed here.

## Second reading by Q124

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
