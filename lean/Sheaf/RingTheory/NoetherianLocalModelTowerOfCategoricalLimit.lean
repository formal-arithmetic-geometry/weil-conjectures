/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.RingTheory.NoetherianLocalModelTower
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.RingTheory.EssentialFiniteness

@[expose] public section

universe u v w t

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Module

/-- Convert an already specified categorical limit system into a Noetherian local model tower.
There is no finite-presentation hypothesis and no assertion constructing a categorical system.
Source: Stacks Project, Algebra, proof of Tag 00R7, first two paragraphs, using
Tags 00QU, 00QV and 00QX for the supplied categorical system.
(blueprint: lem-weil-pbc-noetherian-local-model-tower-categorical-conversion).

Proof: retain the index preorder and the three stage rings and stage modules of the supplied
system. Use the natural transformations for stage algebra structures and compose these maps
for the base-to-top algebra structure; restrict module scalars along them. The local structures
are supplied. Each base ring is essentially of finite type over the Noetherian ring of integers;
the middle and top rings are essentially of finite type over their preceding stages, so all
three are Noetherian. Use functor maps for transitions and compose the cocone maps with
`ULift.down` for maps into the original rings. Functor laws give the directed-system laws;
naturality gives the commutation and semilinearity clauses. The forgetful functors from
commutative rings and abelian groups to sets preserve filtered colimits. Thus every element
of each limit has a representative and equality of two representatives at one stage holds
at a later stage; composing with the lift equivalences gives the eight elementwise clauses.
The fibre transition and module transition are supplied. For the base transition, first
base-change the middle-ring transition localization along the top-stage ring, then compose
with the top-ring transition localization; tensor associativity identifies the resulting
source with the required base-to-top tensor product. For the base localization at the limit,
use tensor symmetry and the canonical module equivalence from a ring localization to its
localized module, restricting scalars to the original base ring. For module localization put
`E = S ⊗[Sᵢ] Tᵢ`, acting on `L = S ⊗[Sᵢ] Nᵢ` by the tensor action. Tensor symmetry and
transport through `ULift.down` make the supplied top-ring limit map a localization `E → S'`.
For its inverted submonoid U, localization-tensor compatibility identifies `LocalizedModule U L`
with `S' ⊗[E] L`. Tensor associativity identifies the latter with `S' ⊗[Tᵢ] Nᵢ`, and the supplied
module base-change equivalence identifies it with M. Restrict scalars to S in these equivalences.
All scalar-tower laws follow from composition and the supplied commuting squares. -/
theorem noetherian_localModelTower_of_categoricalLimit
    (R : Type u) (S : Type v) (S' : Type w) (M : Type t)
    [CommRing R] [CommRing S] [CommRing S'] [AddCommGroup M]
    [Algebra R S] [Algebra S S'] [Module S' M] [Module S M]
    [IsScalarTower S S' M] (s t : ℕ)
    (h :
      let R₁ := ULift.{max u v w} R
      let S₁ := ULift.{max u v w} S
      let T₁ := ULift.{max u v w} S'
      let α : R₁ →+* S₁ := (algebraMap R S).ulift
      let β : S₁ →+* T₁ := (algebraMap S S').ulift
      ∃ (Λ : Type (max u v w)) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
        (A Bs C : Λ ⥤ CommRingCat.{max u v w}) (ρ : A ⟶ Bs) (σ : Bs ⟶ C)
        (π : A ⟶ (Functor.const Λ).obj (CommRingCat.of R₁))
        (κ : Bs ⟶ (Functor.const Λ).obj (CommRingCat.of S₁))
        (κ' : C ⟶ (Functor.const Λ).obj (CommRingCat.of T₁))
        (D : Λ ⥤ AddCommGrpCat.{t})
        (ν : D ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M))
        (_ : ∀ i : Λ, Module (C.obj i) (D.obj i)),
        -- local rings and local homomorphisms
        (∀ i, IsLocalRing (A.obj i)) ∧ (∀ i, IsLocalRing (Bs.obj i)) ∧
        (∀ i, IsLocalRing (C.obj i)) ∧
        (∀ i, IsLocalHom (ρ.app i).hom) ∧ (∀ i, IsLocalHom (σ.app i).hom) ∧
        (∀ (i j : Λ) (h : i ≤ j), IsLocalHom (A.map (homOfLE h)).hom) ∧
        (∀ (i j : Λ) (h : i ≤ j), IsLocalHom (Bs.map (homOfLE h)).hom) ∧
        (∀ (i j : Λ) (h : i ≤ j), IsLocalHom (C.map (homOfLE h)).hom) ∧
        (∀ i, IsLocalHom (@CommRingCat.Hom.hom _ (CommRingCat.of R₁) (π.app i))) ∧
        (∀ i, IsLocalHom (@CommRingCat.Hom.hom _ (CommRingCat.of S₁) (κ.app i))) ∧
        (∀ i, IsLocalHom (@CommRingCat.Hom.hom _ (CommRingCat.of T₁) (κ'.app i))) ∧
        -- the maps to `R₁, S₁, T₁` commute with `α, β`
        (∀ i, ρ.app i ≫ κ.app i = π.app i ≫ CommRingCat.ofHom α) ∧
        (∀ i, σ.app i ≫ κ'.app i = κ.app i ≫ CommRingCat.ofHom β) ∧
        -- semilinearity of the module maps
        (∀ (i j : Λ) (h : i ≤ j) (y : C.obj i) (x : D.obj i),
          (D.map (homOfLE h)).hom (y • x) =
            (C.map (homOfLE h)).hom y • (D.map (homOfLE h)).hom x) ∧
        (∀ i (y : C.obj i) (x : D.obj i),
          (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) (y • x) =
            (@CommRingCat.Hom.hom _ (CommRingCat.of T₁) (κ'.app i)) y •
              (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x) ∧
        -- (1) the colimits
        Nonempty (IsColimit (Cocone.mk (CommRingCat.of R₁) π)) ∧
        Nonempty (IsColimit (Cocone.mk (CommRingCat.of S₁) κ)) ∧
        Nonempty (IsColimit (Cocone.mk (CommRingCat.of T₁) κ')) ∧
        Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M) ν)) ∧
        -- (2) essential finite type
        (∀ i, (algebraMap ℤ (A.obj i)).EssFiniteType) ∧
        (∀ i, (ρ.app i).hom.EssFiniteType) ∧
        (∀ i, (σ.app i).hom.EssFiniteType) ∧
        -- (3) finite generation, indeed cokernels of `t × s` matrices
        (∀ i, Module.Finite (C.obj i) (D.obj i)) ∧
        (∀ i, ∃ H₀ : (Fin s → C.obj i) →ₗ[C.obj i] (Fin t → C.obj i),
          Nonempty (((Fin t → C.obj i) ⧸ LinearMap.range H₀) ≃ₗ[C.obj i] D.obj i)) ∧
        -- (4) transition base changes
        (∀ (i j : Λ) (h : i ≤ j),
          letI := (ρ.app i).hom.toAlgebra
          letI := (A.map (homOfLE h)).hom.toAlgebra
          ∃ φ : Bs.obj i ⊗[A.obj i] A.obj j →+* Bs.obj j,
            (∀ (x : Bs.obj i) (y : A.obj j),
              φ (x ⊗ₜ[A.obj i] y) = (Bs.map (homOfLE h)).hom x * (ρ.app j).hom y) ∧
            (letI := φ.toAlgebra
             ∃ U : Submonoid (Bs.obj i ⊗[A.obj i] A.obj j), IsLocalization U (Bs.obj j))) ∧
        (∀ (i j : Λ) (h : i ≤ j),
          letI := (σ.app i).hom.toAlgebra
          letI := (Bs.map (homOfLE h)).hom.toAlgebra
          ∃ φ : C.obj i ⊗[Bs.obj i] Bs.obj j →+* C.obj j,
            (∀ (x : C.obj i) (y : Bs.obj j),
              φ (x ⊗ₜ[Bs.obj i] y) = (C.map (homOfLE h)).hom x * (σ.app j).hom y) ∧
            (letI := φ.toAlgebra
             ∃ U : Submonoid (C.obj i ⊗[Bs.obj i] Bs.obj j), IsLocalization U (C.obj j))) ∧
        (∀ (i j : Λ) (h : i ≤ j),
          letI := (C.map (homOfLE h)).hom.toAlgebra
          ∃ e : C.obj j ⊗[C.obj i] D.obj i ≃ₗ[C.obj j] D.obj j,
            ∀ (y : C.obj j) (x : D.obj i),
              e (y ⊗ₜ[C.obj i] x) = y • (D.map (homOfLE h)).hom x) ∧
        -- (5) base changes to the limit
        (∀ i,
          letI := (ρ.app i).hom.toAlgebra
          letI := (@CommRingCat.Hom.hom _ (CommRingCat.of R₁) (π.app i)).toAlgebra
          ∃ φ : Bs.obj i ⊗[A.obj i] R₁ →+* S₁,
            (∀ (x : Bs.obj i) (y : R₁),
              φ (x ⊗ₜ[A.obj i] y) =
                (@CommRingCat.Hom.hom _ (CommRingCat.of S₁) (κ.app i)) x * α y) ∧
            (letI := φ.toAlgebra
             ∃ U : Submonoid (Bs.obj i ⊗[A.obj i] R₁), IsLocalization U S₁)) ∧
        (∀ i,
          letI := (σ.app i).hom.toAlgebra
          letI := (@CommRingCat.Hom.hom _ (CommRingCat.of S₁) (κ.app i)).toAlgebra
          ∃ φ : C.obj i ⊗[Bs.obj i] S₁ →+* T₁,
            (∀ (x : C.obj i) (y : S₁),
              φ (x ⊗ₜ[Bs.obj i] y) =
                (@CommRingCat.Hom.hom _ (CommRingCat.of T₁) (κ'.app i)) x * β y) ∧
            (letI := φ.toAlgebra
             ∃ U : Submonoid (C.obj i ⊗[Bs.obj i] S₁), IsLocalization U T₁)) ∧
        (∀ i,
          letI := (@CommRingCat.Hom.hom _ (CommRingCat.of T₁) (κ'.app i)).toAlgebra
          ∃ e : T₁ ⊗[C.obj i] D.obj i ≃ₗ[T₁] M,
            ∀ (y : T₁) (x : D.obj i),
              e (y ⊗ₜ[C.obj i] x) =
                y • (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x)) :
    Nonempty (NoetherianLocalModelTower R S S' M) := by sorry

end Module
