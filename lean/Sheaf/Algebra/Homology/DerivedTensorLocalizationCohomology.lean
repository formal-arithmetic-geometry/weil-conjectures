/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import WeilConjectures.Algebra.Homology.RingTensorCohomology
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelMap
import WeilConjectures.Algebra.Homology.DerivedTensorFirstLocalizationModels
import WeilConjectures.Algebra.Homology.DerivedTensorBaseSecondLocalizationModels

/-! # Localization of cohomology of a derived tensor

Source: Stacks Project, perfect.tex, Tag 0DJ8, the affine proof of
lemma-single-complex-base-change-condition
(blueprint: lem-pc-derived-tensor-localization-cohomology).

The existing cohomology models specify the derived universal property, coefficient
algebra action and comparison maps. The theorem is independent of the choices of models.
`P` is a functorial A-K-flat resolution; `J` is localization of A-complexes. The ordinary
complex on the comparison's target therefore computes the A-derived tensor, both before
and after localization. Naturality is expressed using maps between cohomology models:
their equations identify them with the maps induced by a complex morphism and the unique
counit-compatible comparison between the two derived functors.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology

/-- Changing equal scalar maps gives the identity on pure tensors. -/
private noncomputable def equalScalarComplexIso
    (S T : Type u) [CommRing S] [CommRing T] (f g : S →+* T) (h : f = g)
    (Q : CochainComplex (ModuleCat.{u} S) ℤ) :
    ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj Q ≅
      ((ModuleCat.extendScalars g).mapHomologicalComplex (.up ℤ)).obj Q :=
  eqToIso (congrArg
    (fun k : S →+* T ↦ ((ModuleCat.extendScalars k).mapHomologicalComplex (.up ℤ)).obj Q) h)

private theorem equalScalarComplexIso_tmul
    (S T : Type u) [CommRing S] [CommRing T] (f g : S →+* T) (h : f = g)
    (Q : CochainComplex (ModuleCat.{u} S) ℤ) (j : ℤ) (d : T) (x : Q.X j) :
    (equalScalarComplexIso S T f g h Q).hom.f j (d ⊗ₜ[S, f] x) = d ⊗ₜ[S, g] x := by
  subst g
  rfl

private theorem equalScalarComplexIso_inv_tmul
    (S T : Type u) [CommRing S] [CommRing T] (f g : S →+* T) (h : f = g)
    (Q : CochainComplex (ModuleCat.{u} S) ℤ) (j : ℤ) (d : T) (x : Q.X j) :
    (equalScalarComplexIso S T f g h Q).inv.f j (d ⊗ₜ[S, g] x) = d ⊗ₜ[S, f] x := by
  subst g
  rfl

variable (R A B Rp Aq Bp D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Rp] [CommRing Aq]
  [CommRing Bp] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra R Rp] [Algebra A Aq] [Algebra B Bp]
  [Algebra R Aq] [Algebra R Bp] [Algebra Rp Aq] [Algebra Rp Bp]
  [tRA : IsScalarTower R A Aq] [tRpA : IsScalarTower R Rp Aq]
  [tRB : IsScalarTower R B Bp] [tRpB : IsScalarTower R Rp Bp]
  [Algebra (A ⊗[R] B) D] [Algebra (Aq ⊗[Rp] Bp) D]
  [Algebra A D] [Algebra B D] [Algebra Aq D] [Algebra Bp D]
  [tAD : IsScalarTower A (A ⊗[R] B) D]
  [tBD : IsScalarTower B (A ⊗[R] B) D]
  [tAqD : IsScalarTower Aq (Aq ⊗[Rp] Bp) D]
  [tBpD : IsScalarTower Bp (Aq ⊗[Rp] Bp) D]
  [tAAqD : IsScalarTower A Aq D] [tBBpD : IsScalarTower B Bp D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Rp)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Bp)]

set_option quotPrecheck false in
local notation "P" => resolution A
set_option quotPrecheck false in
local notation "J" => extend A Aq
set_option quotPrecheck false in
local notation "ML" => fun M => ModuleCat.BaseDerivedTensorCohomologyModel R A B ((P).obj M) D
set_option quotPrecheck false in
local notation "MR" => fun M => ModuleCat.BaseDerivedTensorCohomologyModel Rp Aq Bp
  ((J).obj ((P).obj M)) D
set_option quotPrecheck false in
local notation "EL" => ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)
set_option quotPrecheck false in
local notation "ER" => ModuleCat.extendScalars (algebraMap (Aq ⊗[Rp] Bp) D)

include tRA tRpA tRB tRpB tAD tBD tAqD tBpD tAAqD tBBpD in
/-- Localization of derived tensor cohomology, with naturality and comparison compatibility.
Source: Stacks Project, perfect.tex, Tag 0DJ8, affine displayed localization identity
(blueprint: lem-pc-derived-tensor-localization-cohomology).

Proof: construct the intermediate coefficient map `Aq tensor_R B -> D` by the
universal property of the tensor product and the given scalar towers. Apply
`derivedTensor_first_localization_models` to `P(M)` and
`derivedTensor_base_second_localization_models` to `J(P(M))`, using the same
intermediate cohomology model. Compose their D-linear isomorphisms. The universal
counit and the coefficient-action equations characterize this intermediate model
up to the cohomology isomorphisms used in the composition.

For comparison compatibility, the two maps from Aq to D agree by the scalar tower
equations. Their equality induces a complex isomorphism fixing pure tensors.
Compose the two comparison squares and cancel this isomorphism on homology.
For naturality, `exists_baseDerivedTensorCohomologyModelMap` supplies the
counit-compatible morphism between intermediate models and its tensor-linear
cohomology map. Compose the two smaller naturality equations by associativity.
The two localization lemmas separately retain the coefficient actions and
comparison maps in the affine identity of Tag 0DJ8. -/
theorem derivedTensor_localization_cohomology
    (q' : Ideal (A ⊗[R] B)) [q'.IsPrime]
    (q : Ideal A) [q.IsPrime] (p' : Ideal B) [p'.IsPrime]
    (p : Ideal R) [p.IsPrime]
    (hq : q = q'.comap (algebraMap A (A ⊗[R] B)))
    (hp' : p' = q'.comap Algebra.TensorProduct.includeRight.toRingHom)
    (hp : p = q.comap (algebraMap R A))
    [IsLocalization.AtPrime Rp p] [IsLocalization.AtPrime Aq q]
    [IsLocalization.AtPrime Bp p'] [IsLocalization.AtPrime D q'] :
    ∀ i : ℤ, ∃ e : ∀ (M : CochainComplex (ModuleCat.{u} A) ℤ)
        (L : (ML) M) (K : (MR) M),
        (EL).obj (L.cohomology i) ≅ (ER).obj (K.cohomology i),
      (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ) (L : (ML) M) (K : (MR) M)
          (τ :
            ((ModuleCat.extendScalars ((algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj ((P).obj M) ≅
            ((ModuleCat.extendScalars ((algebraMap (Aq ⊗[Rp] Bp) D).comp
              (algebraMap Aq (Aq ⊗[Rp] Bp)))).mapHomologicalComplex (.up ℤ)).obj
                ((J).obj ((P).obj M))),
          (∀ (j : ℤ) (d : D) (x : ((P).obj M).X j),
            τ.hom.f j (d ⊗ₜ[A, (algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B))] x) =
              d ⊗ₜ[Aq, (algebraMap (Aq ⊗[Rp] Bp) D).comp
                (algebraMap Aq (Aq ⊗[Rp] Bp))] ((1 : Aq) ⊗ₜ[A, algebraMap A Aq] x)) →
          L.localizedComparison i ≫ HomologicalComplex.homologyMap τ.hom i =
            (e M L K).hom ≫ K.localizedComparison i) ∧
      (∀ (M N : CochainComplex (ModuleCat.{u} A) ℤ) (f : M ⟶ N)
          (L : (ML) M) (K : (MR) M) (L' : (ML) N) (K' : (MR) N)
          (δ : L.derived ⟶ L'.derived) (ε : K.derived ⟶ K'.derived)
          (g : L.cohomology i ⟶ L'.cohomology i)
          (h : K.cohomology i ⟶ K'.cohomology i),
        Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} R)) δ ≫ L'.counit = L.counit →
        Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} Rp)) ε ≫ K'.counit = K.counit →
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map g ≫
                (L'.cohomologyIso i).hom =
          (L.cohomologyIso i).hom ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
            (L.derived.map (DerivedCategory.Qh.map ((HomotopyCategory.quotient (ModuleCat.{u} R)
                (.up ℤ)).map
              ((restrict R A).map ((P).map f))))) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map (δ.app
                (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
              ((restrict R A).obj ((P).obj N))))) →
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeRight : Bp →ₐ[Rp] Aq ⊗[Rp] Bp).toRingHom).map h ≫
                (K'.cohomologyIso i).hom =
          (K.cohomologyIso i).hom ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} Bp) i).map
            (K.derived.map (DerivedCategory.Qh.map ((HomotopyCategory.quotient (ModuleCat.{u} Rp)
                (.up ℤ)).map
              ((restrict Rp Aq).map ((J).map ((P).map f)))))) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} Bp) i).map (ε.app
                (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (ModuleCat.{u} Rp) (.up ℤ)).obj
              ((restrict Rp Aq).obj ((J).obj ((P).obj N)))))) →
        (EL).map g ≫ (e N L' K').hom = (e M L K).hom ≫ (ER).map h) := by
  classical
  have _ := hq
  have _ := hp'
  have _ := hp
  let : Algebra R D :=
    ((algebraMap (A ⊗[R] B) D).comp (algebraMap R (A ⊗[R] B))).toAlgebra
  let : IsScalarTower R (A ⊗[R] B) D :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R A D := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R (A ⊗[R] B) D,
      IsScalarTower.algebraMap_eq R A (A ⊗[R] B),
      IsScalarTower.algebraMap_eq A (A ⊗[R] B) D]
    rfl)
  let : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R (A ⊗[R] B) D,
      IsScalarTower.algebraMap_eq R B (A ⊗[R] B),
      IsScalarTower.algebraMap_eq B (A ⊗[R] B) D]
    rfl)
  let : IsScalarTower R Aq D := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R A D, IsScalarTower.algebraMap_eq A Aq D,
      IsScalarTower.algebraMap_eq R A Aq]
    rfl)
  let φ : (Aq ⊗[R] B) →ₐ[R] D := Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom R Aq D) (IsScalarTower.toAlgHom R B D)
      (fun _ _ ↦ Commute.all _ _)
  let : Algebra (Aq ⊗[R] B) D := φ.toRingHom.toAlgebra
  let : IsScalarTower Aq (Aq ⊗[R] B) D :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change algebraMap Aq D x = φ (x ⊗ₜ[R] (1 : B))
      simp [φ])
  let : IsScalarTower B (Aq ⊗[R] B) D :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change algebraMap B D x = φ ((1 : Aq) ⊗ₜ[R] x)
      simp [φ])
  intro i
  obtain ⟨e₁, c₁, n₁⟩ :=
    derivedTensor_first_localization_models R A B Aq D q.primeCompl i
  obtain ⟨e₂, c₂, n₂⟩ :=
    derivedTensor_base_second_localization_models R Aq B Rp Bp D p.primeCompl p'.primeCompl i
  let T : ∀ M : CochainComplex (ModuleCat.{u} A) ℤ,
      ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((J).obj ((P).obj M)) D :=
    fun M ↦ Classical.choice
      (ModuleCat.nonempty_baseDerivedTensorCohomologyModel R Aq B ((J).obj ((P).obj M)) D)
  refine ⟨fun M L K ↦ e₁ ((P).obj M) L (T M) ≪≫ e₂ ((J).obj ((P).obj M)) (T M) K,
    ?_, ?_⟩
  · intro M L K τ hτ
    let f₀ := (algebraMap (Aq ⊗[R] B) D).comp (algebraMap Aq (Aq ⊗[R] B))
    let f₂ := (algebraMap (Aq ⊗[Rp] Bp) D).comp (algebraMap Aq (Aq ⊗[Rp] Bp))
    have hf : f₂ = f₀ := by
      dsimp [f₂, f₀]
      rw [← IsScalarTower.algebraMap_eq Aq (Aq ⊗[Rp] Bp) D,
        ← IsScalarTower.algebraMap_eq Aq (Aq ⊗[R] B) D]
    let τ₀ := equalScalarComplexIso Aq D f₂ f₀ hf ((J).obj ((P).obj M))
    let τ₁ := τ ≪≫ τ₀
    have hc₁ := c₁ ((P).obj M) L (T M) τ₁ (by
      intro j d x
      change τ₀.hom.f j (τ.hom.f j _) = _
      rw [hτ, equalScalarComplexIso_tmul])
    have hc₂ := c₂ ((J).obj ((P).obj M)) (T M) K τ₀.symm (by
      intro j d x
      change (equalScalarComplexIso Aq D f₂ f₀ hf _).inv.f j _ = _
      exact equalScalarComplexIso_inv_tmul Aq D f₂ f₀ hf _ j d x)
    have hcomp : τ₁.hom ≫ τ₀.inv = τ.hom := by simp [τ₁]
    change L.localizedComparison i ≫ HomologicalComplex.homologyMap τ.hom i =
      (e₁ ((P).obj M) L (T M)).hom ≫
        (e₂ ((J).obj ((P).obj M)) (T M) K).hom ≫ K.localizedComparison i
    rw [← hcomp, HomologicalComplex.homologyMap_comp, ← Category.assoc, hc₁,
      Category.assoc]
    exact congrArg (fun k ↦ (e₁ ((P).obj M) L (T M)).hom ≫ k) hc₂
  · intro M N f L K L' K' δ ε g h hδ hε hg hh
    obtain ⟨δ₀, g₀, hδ₀, hg₀⟩ := exists_baseDerivedTensorCohomologyModelMap
      R Aq B D ((J).obj ((P).obj M)) ((J).obj ((P).obj N))
      ((J).map ((P).map f)) (T M) (T N) i
    have hn₁ := n₁ ((P).obj M) ((P).obj N) ((P).map f)
      L (T M) L' (T N) δ δ₀ g g₀ hδ hg hδ₀ hg₀
    have hn₂ := n₂ ((J).obj ((P).obj M)) ((J).obj ((P).obj N))
      ((J).map ((P).map f)) (T M) K (T N) K' δ₀ ε g₀ h hδ₀ hg₀ hε hh
    change (EL).map g ≫
        ((e₁ ((P).obj N) L' (T N)).hom ≫
          (e₂ ((J).obj ((P).obj N)) (T N) K').hom) =
      ((e₁ ((P).obj M) L (T M)).hom ≫
        (e₂ ((J).obj ((P).obj M)) (T M) K).hom) ≫ (ER).map h
    rw [← Category.assoc, hn₁, Category.assoc, hn₂, Category.assoc]

end RingTensorCohomology
