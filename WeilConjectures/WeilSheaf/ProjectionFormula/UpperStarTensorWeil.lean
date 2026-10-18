/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ProjectionFormula.UpperStarTensorCompat

/-!
# Pullback commutes with tensor products of sheaves with structure isomorphisms

For automorphisms `a` of `T₁` and `b` of `T₂` and a morphism `j : T₁ ⟶ T₂` with
`a ≫ j = j ≫ b`, the pullback `j^*` transports `ℓ`-adic sheaves with a structure isomorphism
`(b⁻¹)_* K ≅ K` to sheaves with a structure isomorphism `(a⁻¹)_* j^* K ≅ j^* K` along the exchange
isomorphism. It commutes with the tensor products of such sheaves,
`j^*(- ⊗ A) ≅ j^*(-) ⊗ j^* A`
(`AlgebraicGeometry.ProEtale.isoAlgebraTensorFunctorCompMapOfNatIsoIso`): the comparison of the
underlying sheaves (`AlgebraicGeometry.ProEtale.adicUpperStarTensorLeftIso`) is compatible with
the structure isomorphisms (`AlgebraicGeometry.ProEtale.adicUpperStarTensorLeftIso_tensorStr_comm`).
For `a` and `b` the geometric Frobenii, these are pro-étale Weil sheaves.

## Implementation notes

The exchange isomorphism enters as a variable `e` together with an equation
`e = adicUpperStarExchange l j a b c`: comparing its components at definitionally equal but
syntactically different objects otherwise makes the kernel unfold it.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Endofunctor

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {T T₁ T₂ : Scheme.{u}}

section IsoAlgebra

variable (l) in
/-- The tensor product `B ⊗ A` of `ℓ`-adic sheaves with structure isomorphisms
`(a⁻¹)_* A ≅ A` and `(a⁻¹)_* B ≅ B` for an automorphism `a`, with the structure isomorphism
`(a⁻¹)_* (B ⊗ A) ≅ (a⁻¹)_* B ⊗ (a⁻¹)_* A ≅ B ⊗ A`. For `a` the geometric Frobenius, this is the
tensor product of pro-étale Weil sheaves (`AlgebraicGeometry.ProEtaleWeilSheaf.tensor`). -/
noncomputable def isoAlgebraTensor (a : T ≅ T) (A B : IsoAlgebra (a.inv)_*ᵃ[l]) :
    IsoAlgebra (a.inv)_*ᵃ[l] :=
  IsoAlgebra.mk ((Mod.tensorLeft A.carrier).obj B.carrier)
    ((adicLowerStarTensorLeftIso l a.inv A.carrier).app B.carrier ≪≫
      (Mod.tensorLeftMapIso A.str).app _ ≪≫ (Mod.tensorLeft A.carrier).mapIso B.str)

lemma isoAlgebraTensor_obj_str (a : T ≅ T) (A B : IsoAlgebra (a.inv)_*ᵃ[l]) :
    (isoAlgebraTensor l a A B).obj.str =
      (adicLowerStarTensorLeftIso l a.inv A.carrier).hom.app B.carrier ≫
        (Mod.tensorLeftMap A.obj.str).app _ ≫ (Mod.tensorLeft A.carrier).map B.obj.str :=
  rfl

lemma isoAlgebraTensor_map_comm (a : T ≅ T) (A : IsoAlgebra (a.inv)_*ᵃ[l])
    {B B' : IsoAlgebra (a.inv)_*ᵃ[l]} (f : B ⟶ B') :
    (a.inv)_*ᵃ[l].map ((Mod.tensorLeft A.carrier).map f.hom.f) ≫
        (isoAlgebraTensor l a A B').obj.str =
      (isoAlgebraTensor l a A B).obj.str ≫ (Mod.tensorLeft A.carrier).map f.hom.f := by
  rw [isoAlgebraTensor_obj_str, isoAlgebraTensor_obj_str]
  have h₁ := (adicLowerStarTensorLeftIso l a.inv A.carrier).hom.naturality f.hom.f
  have h₂ := (Mod.tensorLeftMap A.obj.str).naturality ((a.inv)_*ᵃ[l].map f.hom.f)
  simp only [Functor.comp_map] at h₁ h₂
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, ← Functor.map_comp, ← Functor.map_comp]
  congr 3
  exact f.hom.h

variable (l) in
/-- The tensor product `- ⊗ A` with an `ℓ`-adic sheaf with structure isomorphism, as a functor. -/
noncomputable def isoAlgebraTensorFunctor (a : T ≅ T) (A : IsoAlgebra (a.inv)_*ᵃ[l]) :
    IsoAlgebra (a.inv)_*ᵃ[l] ⥤ IsoAlgebra (a.inv)_*ᵃ[l] where
  obj B := isoAlgebraTensor l a A B
  map f := ObjectProperty.homMk ⟨(Mod.tensorLeft A.carrier).map f.hom.f,
    isoAlgebraTensor_map_comm a A f⟩
  map_id _ := IsoAlgebra.hom_ext ((Mod.tensorLeft A.carrier).map_id _)
  map_comp _ _ := IsoAlgebra.hom_ext ((Mod.tensorLeft A.carrier).map_comp _ _)

/-- The structure isomorphism of a transport along `e : j^* ⋙ (a⁻¹)_* ≅ (b⁻¹)_* ⋙ j^*`. -/
lemma mapOfNatIso_obj_obj_str (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂)
    (e : (j)^*ᵃ[l] ⋙ (a.inv)_*ᵃ[l] ≅ (b.inv)_*ᵃ[l] ⋙ (j)^*ᵃ[l]) (K : IsoAlgebra (b.inv)_*ᵃ[l]) :
    ((IsoAlgebra.mapOfNatIso e).obj K).obj.str = e.hom.app K.carrier ≫ (j)^*ᵃ[l].map K.obj.str := by
  rw [← IsoAlgebra.str_hom, IsoAlgebra.mapOfNatIso_obj_str]
  rfl

/-- `AlgebraicGeometry.ProEtale.adicUpperStarTensorLeftIso_tensorStr_comm` for an isomorphism `e`
equal to the exchange isomorphism. Keeping `e` abstract avoids unfolding the exchange isomorphism
when comparing its components at definitionally equal objects. -/
lemma adicUpperStarTensorLeftIso_tensorStr_comm_of_eq (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁)
    (b : T₂ ≅ T₂) (c : a.hom ≫ j = j ≫ b.hom)
    (e : (j)^*ᵃ[l] ⋙ (a.inv)_*ᵃ[l] ≅ (b.inv)_*ᵃ[l] ⋙ (j)^*ᵃ[l])
    (he : e = adicUpperStarExchange l j a b c) (P M : AdicSheaf l T₂)
    (sM : (b.inv)_*ᵃ[l].obj M ⟶ M) (sP : (b.inv)_*ᵃ[l].obj P ⟶ P) :
    (a.inv)_*ᵃ[l].map ((adicUpperStarTensorLeftIso l j M).hom.app P) ≫
        (adicLowerStarTensorLeftIso l a.inv ((j)^*ᵃ[l].obj M)).hom.app ((j)^*ᵃ[l].obj P) ≫
        (Mod.tensorLeftMap (e.hom.app M ≫ (j)^*ᵃ[l].map sM)).app _ ≫
        (Mod.tensorLeft _).map (e.hom.app P ≫ (j)^*ᵃ[l].map sP) =
      e.hom.app ((Mod.tensorLeft M).obj P : AdicSheaf l T₂) ≫
        (j)^*ᵃ[l].map ((adicLowerStarTensorLeftIso l b.inv M).hom.app P ≫
          (Mod.tensorLeftMap sM).app _ ≫ (Mod.tensorLeft M).map sP) ≫
        (adicUpperStarTensorLeftIso l j M).hom.app P := by
  subst he
  exact adicUpperStarTensorLeftIso_tensorStr_comm j a b c P M sM sP

/-- The comparison `j^*(B ⊗ A) ≅ j^* B ⊗ j^* A` is compatible with the structure isomorphisms
transported along an isomorphism `e` equal to the exchange isomorphism. -/
lemma adicUpperStarTensorLeftIso_isoAlgebraTensor_comm (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁)
    (b : T₂ ≅ T₂) (c : a.hom ≫ j = j ≫ b.hom)
    (e : (j)^*ᵃ[l] ⋙ (a.inv)_*ᵃ[l] ≅ (b.inv)_*ᵃ[l] ⋙ (j)^*ᵃ[l])
    (he : e = adicUpperStarExchange l j a b c) (A B : IsoAlgebra (b.inv)_*ᵃ[l]) :
    (a.inv)_*ᵃ[l].map ((adicUpperStarTensorLeftIso l j A.carrier).hom.app B.carrier) ≫
        (isoAlgebraTensor l a ((IsoAlgebra.mapOfNatIso e).obj A)
          ((IsoAlgebra.mapOfNatIso e).obj B)).obj.str =
      ((IsoAlgebra.mapOfNatIso e).obj (isoAlgebraTensor l b A B)).obj.str ≫
        (adicUpperStarTensorLeftIso l j A.carrier).hom.app B.carrier := by
  rw [isoAlgebraTensor_obj_str, mapOfNatIso_obj_obj_str, mapOfNatIso_obj_obj_str,
    mapOfNatIso_obj_obj_str, isoAlgebraTensor_obj_str, Category.assoc]
  exact adicUpperStarTensorLeftIso_tensorStr_comm_of_eq j a b c e he B.carrier A.carrier
    A.obj.str B.obj.str

variable (l) in
/-- **Pullback commutes with tensor products of sheaves with structure isomorphisms**:
`j^*(- ⊗ A) ≅ j^*(-) ⊗ j^* A`, the structure isomorphisms being transported along an
isomorphism `e` equal to the exchange isomorphism. -/
noncomputable def isoAlgebraTensorFunctorCompMapOfNatIsoIso (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁)
    (b : T₂ ≅ T₂) (c : a.hom ≫ j = j ≫ b.hom)
    (e : (j)^*ᵃ[l] ⋙ (a.inv)_*ᵃ[l] ≅ (b.inv)_*ᵃ[l] ⋙ (j)^*ᵃ[l])
    (he : e = adicUpperStarExchange l j a b c) (A : IsoAlgebra (b.inv)_*ᵃ[l]) :
    isoAlgebraTensorFunctor l b A ⋙ IsoAlgebra.mapOfNatIso e ≅
      IsoAlgebra.mapOfNatIso e ⋙ isoAlgebraTensorFunctor l a ((IsoAlgebra.mapOfNatIso e).obj A) :=
  NatIso.ofComponents
    (fun B ↦ IsoAlgebra.isoMk ((adicUpperStarTensorLeftIso l j A.carrier).app B.carrier)
      (adicUpperStarTensorLeftIso_isoAlgebraTensor_comm j a b c e he A B))
    fun f ↦ IsoAlgebra.hom_ext ((adicUpperStarTensorLeftIso l j A.carrier).hom.naturality f.hom.f)

@[simp]
lemma isoAlgebraTensorFunctorCompMapOfNatIsoIso_hom_app_hom_f (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁)
    (b : T₂ ≅ T₂) (c : a.hom ≫ j = j ≫ b.hom)
    (e : (j)^*ᵃ[l] ⋙ (a.inv)_*ᵃ[l] ≅ (b.inv)_*ᵃ[l] ⋙ (j)^*ᵃ[l])
    (he : e = adicUpperStarExchange l j a b c) (A B : IsoAlgebra (b.inv)_*ᵃ[l]) :
    ((isoAlgebraTensorFunctorCompMapOfNatIsoIso l j a b c e he A).hom.app B).hom.f =
      (adicUpperStarTensorLeftIso l j A.carrier).hom.app B.carrier :=
  rfl

end IsoAlgebra

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

set_option hygiene false in
local notation "𝐒" => Spec (CommRingCat.of k₀)

set_option hygiene false in
local notation "Fr[" T "]" => Scheme.Hom.geometricGaloisFrobenius (T ↘ Spec (CommRingCat.of k₀))

set_option hygiene false in
local notation "bc[" f "]" =>
  Scheme.Hom.geometricFiberMap f (comp_over f (Spec (CommRingCat.of k₀)))

set_option hygiene false in
local notation "EX[" φ "]" => adicUpperStarExchange l (bc[φ]) (Fr[X]) (Fr[Y])
        (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ (comp_over φ 𝐒)).symm

lemma tensorFunctor_eq_isoAlgebraTensorFunctor (A : ProEtaleWeilSheaf k₀ l X) :
    tensorFunctor k₀ l X A = isoAlgebraTensorFunctor l (Fr[X]) A :=
  rfl

lemma upperStar_eq_mapOfNatIso (φ : X ⟶ Y) [φ.IsOver 𝐒] :
    upperStar k₀ l φ = IsoAlgebra.mapOfNatIso (EX[φ]) := by
  rw [← adicUpperStarGeometricFiberMapCompFrobeniusIso_eq_exchange]
  rfl

/-- **Pullback of pro-étale Weil sheaves commutes with tensor products**:
`φ^*(- ⊗ A) ≅ φ^*(-) ⊗ φ^* A`, through the comparison
`AlgebraicGeometry.ProEtale.adicUpperStarTensorLeftIso` of the underlying sheaves
(`AlgebraicGeometry.ProEtale.isoAlgebraTensorFunctorCompMapOfNatIsoIso`). -/
theorem nonempty_tensorFunctorCompUpperStarIso (φ : X ⟶ Y) [φ.IsOver 𝐒]
    (A : ProEtaleWeilSheaf k₀ l Y) :
    Nonempty (tensorFunctor k₀ l Y A ⋙ upperStar k₀ l φ ≅
      upperStar k₀ l φ ⋙ tensorFunctor k₀ l X ((upperStar k₀ l φ).obj A)) := by
  rw [upperStar_eq_mapOfNatIso, tensorFunctor_eq_isoAlgebraTensorFunctor,
    tensorFunctor_eq_isoAlgebraTensorFunctor]
  exact ⟨isoAlgebraTensorFunctorCompMapOfNatIsoIso l (bc[φ]) (Fr[X]) (Fr[Y])
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ (comp_over φ 𝐒)).symm
    (EX[φ]) rfl A⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
