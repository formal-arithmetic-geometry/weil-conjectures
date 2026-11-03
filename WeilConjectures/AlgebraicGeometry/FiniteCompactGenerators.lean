/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Compact generators for finite-coefficient localizing closures

Source: blueprint `literature/blueprint/latest/blueprint/`,
`part-six-operations/sec-six-functors-basics/sec-ctf-finite-foundations/`,
`sk-prop-ctf-finite-compact/sk-prop-ctf-finite-compact-generators.md` and its
corresponding `.proof.md`; standing conventions in `sec-introduction/prose-01-01.md`.

Let `A` be a finite `ℓ`-primary coefficient ring and let `X` be a separated
finite-type scheme over a finite or algebraically closed field of characteristic
prime to `ℓ`.  The bounded constructible finite-Tor subcategory is thick and
essentially small; a small skeleton is a set of compact generators of its
localizing closure, and those are exactly the compact objects of the closure.

The proof follows the finite-coefficient compactness argument in the blueprint:
smallness and thickness, orthogonal generation by a skeleton, the telescope
construction, compact-Hom factorization, and finite thick factorization.
(blueprint: det-ctf-finite-compact-generators)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

/-- The compact objects of the finite-coefficient pro-etale localizing closure are
exactly the bounded constructible finite-Tor complexes, and a small skeleton of
that subcategory is a set of compact generators.

The coefficient ring is finite and killed by a power of `ℓ`; the base field is
finite or algebraically closed of characteristic different from `ℓ`; and `X` is
separated, quasi-compact, and locally of finite type over that field.  Put
`S = Dctf(X,A)` and `L = Loc(S)`.  The first paragraph of the blueprint proof
uses the finite-coefficient smallness theorem to show that `S` is thick and
essentially small.  The second paragraph takes a small skeleton `G` of `S`.
For an object orthogonal to every shifted member of `G`, the left orthogonal is
localizing and contains `S`, hence contains `L`; its identity map is zero, so
`G` generates.  The compactness theorem makes every member of `G` compact.

For the converse compact-object assertion, the telescope construction writes a
compact `K` as a sequential homotopy colimit of coproducts of shifts of members
of `G`.  Compactness of the Hom functor represents the identity of `K` at a
finite stage.  The finite-thick-factorization theorem factors this stage map
through an object in the thick closure of a finite sum of skeleton objects.
Since `S` is thick and replete, that factor object lies in `S`; the resulting
retract shows `K ∈ S`.  Conversely all objects of `S` are compact.  Thus
`Lᶜ = S`, and the thick closure of `G` is `S`.

The argument is the statement of the blueprint node and uses Stacks Tags 09SM,
09SN, 094A, and 09SP. (blueprint: det-ctf-finite-compact-generators) -/
theorem finiteCompactGenerators
    (ℓ : ℕ) {p : ℕ} [Fact ℓ.Prime]
    {k : Type u} [Field k] [CharP k p]
    (hK : Finite k ∨ IsAlgClosed k) (hℓ : p ≠ ℓ)
    {X : Scheme.{u}} (aX : X ⟶ Spec (CommRingCat.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A]
    (hA : ∃ r : ℕ, ∀ a : A, (ℓ ^ r) • a = 0) :
    let Λ := Profinite.continuousMapRingObj.{u} A
    let S := constantModelBoundedConstructible Λ X ⊓
      fun K ↦ DerivedCategory.finiteTorAmplitude _ K
    let L := localizingClosureProEtale Λ X
    ∃ hTri : L.IsTriangulated,
      letI := hTri
      ∃ hSums : HasCoproducts.{u + 1} L.FullSubcategory,
        letI := hSums
        S.IsTriangulated ∧
          S.IsClosedUnderIsomorphisms ∧
          S.IsStableUnderRetracts ∧
          ObjectProperty.EssentiallySmall.{u + 1} S ∧
          (∃ (G : Type (u + 1)) (hCat : Category.{u + 1} G),
            letI := hCat
            ∃ (e : G ≌ S.FullSubcategory),
              (∀ g g' : G, Nonempty (g ≅ g') → g = g') ∧
              ∃ hL : ∀ g : G, L (e.functor.obj g).obj,
                (∀ g : G,
                  @CategoryTheory.IsCompactObject _ _ _ hSums
                    (ObjectProperty.FullSubcategory.mk (e.functor.obj g).obj (hL g))) ∧
                  (let E : G → L.FullSubcategory := fun g ↦
                    (ObjectProperty.FullSubcategory.mk (e.functor.obj g).obj (hL g) :
                      L.FullSubcategory)
                  letI : HasCoproducts.{u + 1} L.FullSubcategory := hSums
                  IsTriangulatedGeneratingFamily E)) ∧
          (∀ K : L.FullSubcategory,
            @CategoryTheory.IsCompactObject _ _ _ hSums K ↔ S K.obj) := by
  sorry

end AlgebraicGeometry.ProEtale
