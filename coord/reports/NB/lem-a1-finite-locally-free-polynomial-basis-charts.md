## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteLocallyFreePolynomialBasisCharts` states
`AlgebraicGeometry.finiteLocallyFree_polynomial_basis_charts`, with its proof `sorry`.
It introduces no definitions, helper axioms, additional nodes or dependency repairs.
The node's mathematical statement and dependency lists are unchanged.

Source read: Stacks `exercises.tex`, exercise-trace-det-rings, Tag 02DV(3), lines
1605 onward, and `morphisms.tex`, lemma-base-change-finite-locally-free, Tag 02KD,
lines 12420 onward, together with the item's complete eight-step proof.

Hypotheses, clause by clause:

- Commutative rings and a unital map: `{A B : Type u} [CommRing A] [CommRing B]
  [Algebra A B]`. The named map is `algebraMap A B`. For commutative rings an
  algebra structure is exactly a unital ring map with its induced scalar action;
  every map in the node is represented, via `RingHom.toAlgebra`.
- Nonnegative degree and finite cover size: `(r m : ℕ)`.
- `Spec B → Spec A` finite locally free of degree r: binder `h` uses precisely
  `Scheme.Hom.IsFiniteLocallyFreeOfDegree r` on the spectrum of this map. Its
  inherited conditions are finite, flat, locally of finite presentation; its
  degree is the dimension of global sections of every scheme-theoretic fibre.
- The given f_i and the unit-ideal cover: `(f : Fin m → A)` and
  `hf : Ideal.span (Set.range f) = ⊤`.
- The specified r-element local bases: `(e : (i : Fin m) → @Module.Basis ... )`.
  Its scalar ring is `Localization.Away (f i)` and module is the underlying
  module of `Localization.Away (algebraMap A B (f i))`. Its module structure is
  explicitly `Algebra.toModule` of the algebra induced by
  `IsLocalization.Away.map ... (algebraMap A B) (f i)`. This is the canonical
  localized coefficient map, with no arbitrary scalar action. Ring localization
  is the ring model of the module localization B_{f_i}; the recorded module
  localization definition and its `IsLocalizedModule` characterization agree
  with it (Mathlib `Algebra.Module.LocalizedModule.IsLocalization`).

Conclusions, in their Lean order:

1. The displayed canonical tensor ring isomorphism is the existing
   `(polyEquivTensor A B).symm`, an A-algebra equivalence. Its value on every
   `b ⊗ₜ[A] P` is stated explicitly as
   `P.sum (fun n a ↦ Polynomial.monomial n (b * algebraMap A B a))`.
   Thus the isomorphism is the node's specified map, including every coefficient.
2. `IsPullback` on the four spectrum maps states that the polynomial square is
   cartesian. Its first projection is `Spec(C : B →+* Polynomial B)`, its second
   is `Spec(Polynomial.mapRingHom (algebraMap A B))`, and its lower maps are
   `Spec(algebraMap A B)` and `Spec(C : A →+* Polynomial A)`. This is exactly the
   base change along `Spec A[T] → Spec A`, with both projections identified.
   The preceding formula identifies the tensor inclusions with these maps;
   the universal property makes this the same identification as the chosen
   fibre product, without choosing another unnamed isomorphism.
3. The polynomial spectrum map has `IsFiniteLocallyFreeOfDegree r`.
4. Its structure-sheaf pushforward is explicitly
   `(Scheme.Modules.pushforward ...).obj (SheafOfModules.unit ...ringCatSheaf)`.
   Its `IsQuasicoherent` property is stated.
5. The identical pushforward has
   `SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} ... r`, exactly the
   dependency's open-cover notion of constant rank r.
6. `Ideal.span (Set.range (fun i : Fin m ↦ Polynomial.C (f i))) = ⊤`
   says the g_i generate the unit ideal.
7. For each i, ring equivalences `α` and `β` have source A[T]_{C(f_i)} and
   B[T] localized at the image of C(f_i), and target A_{f_i}[T] and B_{f_i}[T].
   The latter source is written with the literal image
   `(Polynomial.mapRingHom (algebraMap A B)) (Polynomial.C (f i))`, equal to
   `Polynomial.C (algebraMap A B (f i))` by `Polynomial.map_C`. This spelling
   lets localization's map interface use the actual image without a cast.
8. The first two equations following `∃ α β` specify their restrictions on
   every polynomial: applying either isomorphism to a localization numerator
   equals coefficientwise localization. These equations characterize the maps
   uniquely by localization's universal property; neither equivalence is arbitrary.
9. The `∀ z` equation states the entire compatibility diagram: β after the
   canonical localized polynomial coefficient map equals the polynomial extension
   of the localized coefficient map after α. Compatibility with further
   localizations follows from the specified numerator formulas and uniqueness of
   maps from a localization; it does not require selecting further maps.
10. Finally `∃ E : @Module.Basis ... , ∀ j : Fin r, E j = Polynomial.C (e i j)`
    asserts that the particular constant polynomials are a basis. Its module
    action is explicitly the polynomial extension of the canonical local map.
    By the compatibility equation this transports to the original localized
    polynomial rings with exactly their original coefficient action.

Recorded statement dependencies and declarations used:

- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`; signatures/docstrings read.
- `def-pc-finite-locally-free`:
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`,
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` and
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree`; full class bodies read.
- `def-weil-ring-localization-away`: `Mathlib.GroupTheory.MonoidLocalization.Away`,
  `Localization.Away`; used through `Mathlib.RingTheory.Localization.Away.Basic`,
  which additionally supplies the existing canonical `IsLocalization.Away.map`.
- `def-weil-pbc-module-localization-away`:
  `Mathlib.Algebra.Module.LocalizedModule.Basic`, `LocalizedModule.Away`,
  `LocalizedModule.mkLinearMap`, `IsLocalizedModule.lift`; their declarations were
  read. Here B_f is its canonical ring-localization model rather than a second
  definition or a chosen abstract module.
- `def-weil-pbc-free-module`: `Mathlib.LinearAlgebra.FreeModule.Basic`,
  `Module.Free`; the specified bases use `Module.Basis` from its recorded match.
  The class and the full `Module.Basis` signature/docstring were read.
- `def-weil-polynomial-ring`: `Mathlib.Algebra.Polynomial.Basic`, `Polynomial`;
  the recorded structure and constant/coefficientwise ring maps were read.
- `def-weil-module-base-change`: `Mathlib.LinearAlgebra.TensorProduct.Tower`,
  `TensorProduct`, `TensorProduct.mk`, `LinearMap.baseChange`. The tensor product
  in the displayed equivalence is the node's B tensor_A A[T], in its exact order.
- `def-amb-finite-locally-free-module`:
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`,
  `SheafOfModules.IsFiniteLocallyFreeOfRank`; its complete class body was read.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `pullback` and
  its projections. The statement uses its universal-property form `IsPullback`
  on the specified square, as permitted by the project convention. The chosen
  pullback and projection declarations were read.

All nine recorded dependency modules are publicly available from the imports;
proof-only modules are plain imports. Their paths are read from the dependency
records or their Mathlib matches, including the affine tensor-spectrum, finite/
flat/finite-presentation base-change, rank, tilde, localization-open and basis
base-change components. The declaration docstring carries every proof step,
including the common-denominator argument and all degenerate cases.

Edge cases checked mathematically before the statement was written:

- A=0 forces B=0 by unitality. The spectra are empty and all rank/degree claims
  are vacuous; no `Nontrivial` assumption appears.
- m=0 is allowed by `Fin 0`: hf says the zero ideal equals the unit ideal, so
  exactly the zero-ring empty-cover case occurs.
- r=0 is allowed by `Fin 0`; an empty local basis means the localized module is
  zero. The empty determinant issue is irrelevant here, and the local freeness
  statement is exactly rank zero.
- f_i=0 or nilpotent gives zero localizations and empty principal charts. No
  denominator is cancelled and no f_i is assumed nonzero or regular.
- A=B and the identity map in rank one gives the usual constant basis, and the
  compatibility equation has the correct variance and order of composition.

Searches performed with msearch.py (group NB, this item):

- LeanFinder: `Polynomial base change of a finite locally free algebra preserves
  degree and its localized bases extend to constant polynomial bases`: eight hits,
  including `IsBaseChange.of_fintype_basis` and submersive presentation base change;
  none gives this combined scheme/localization/specified-basis statement.
- Loogle: `Polynomial, Module.Basis`: twelve hits, including charpoly matrix,
  AdjoinRoot power bases and polynomial sequences; none is this assertion.
- grep: `polyEquivTensor|polynomial.*[Bb]asis|[Bb]asis.*[Pp]olynomial|isLocalization`
  with subdirectory `RingTheory/PolynomialAlgebra`: zero hits (that query named a
  file stem rather than a directory). Repeated a focused directory search below.
- LeanSearch: `Polynomial extension commutes with localization and extends a finite
  module basis to a basis of constant polynomials`: eight hits, including
  `Polynomial.isLocalization` and `Module.Basis.localizationLocalization_apply`.
  These are components, not the combined assertion.
- grep: `polyEquivTensor|Polynomial.isLocalization` in `RingTheory`: 22 hits,
  notably `Mathlib/RingTheory/PolynomialAlgebra.lean` and
  `Mathlib/RingTheory/Localization/Algebra.lean`. Read the complete tensor
  equivalence and the localization theorem; use the former directly.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for polynomial/basis and
  `polyEquivTensor` found component constructions and the existing parent norm
  theorem, but no theorem for this item. An item-id search in upstream sources
  found no declaration. The exact proposed declaration name was also searched in
  both source trees and `dag/lean_names_upstream.json`, with no collision.

No statement fault or disputed clause was found. There is no statement correction.
Compilation: the prescribed scompile.py compiled the sandbox module and its final
library module separately, both cleanly; no non-sorry warning or error remained.
The first compile identified a non-definitional equality between `map C(f_i)` and
`C(φ(f_i))` in localization's type-class input. Writing the actual image in β's
source fixes that elaboration issue without changing the mathematical statement.

## Second reading by NB

The dispatcher explicitly prohibits starting another agent and assigns the
independent reading to the maintainer. This section records the worker's separate
second pass through the node and finished file, not an independent-agent review.

I checked each binder against the node: the algebra map is fully general; r and m
include zero; hf is exactly ideal generation; each e is a basis of the canonical
localized B-algebra over the localized A-ring. I checked the tensor equivalence
formula coefficient by coefficient and the order of the four maps in `IsPullback`.
I checked that both sheaf clauses concern the identical polynomial map and the
structure sheaf, with exactly rank r. I checked the polynomial cover, both
localization equivalence directions, their numerator normalizations, the full
coefficient-map commuting equation, and the precise e-to-C(e) basis equality.
All objects and hypotheses match. No algebra structure is selected existentially
or assumed as extra input. There are no local notations, local instances, hidden
let binders, unbound universes, or nonzero assumptions. No mathematical mismatch
was found. The only change during this pass was wrapping a long docstring line;
the map-image spelling was the earlier compile repair described above.
