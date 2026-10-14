/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module
public import Sheaf.RingTheory.LimitModuleRingData
/-!
# Polynomial-quotient descent with localization base change
Source: Stacks Project, Algebra, Tag 00QV, as used in Tag 00QX.
(blueprint: lem-limit-module-localization-ring-data)
-/
@[expose] public section
universe u p
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace RingHom
/-- Descend a localized finitely presented algebra with its ring base-change properties.
Source: Stacks Project, Algebra, Tag 00QV (proof) and Tag 00QX (ring construction).
Proof: Replace the given localization of P by localization at the inverse image of
T's maximal ideal; since T is local this gives the same ring. Write P as a finite
polynomial quotient. Lift the finitely many coefficients of its defining relations
along the given colimit to a common index i₀. At each later index take that polynomial
quotient over F(i), and localize it at the inverse image of T's maximal ideal.
The contraction to F(i) is maximal because the maps F(i) → c.pt → T are local.
Hence these rings and their structure, transition and limit maps are local; their
structure maps are essentially of finite type. Maps of polynomials carry the lifted
relations to the later relations and induce the required naturality and composition.
Polynomial and quotient base change give the unlocalized scalar-extension identities.
Base change of localization followed by localization at the contracted prime proves
both displayed localization predicates, with the canonical pure-tensor formulas.
For the ring colimit, lift the finitely many numerator and denominator coefficients
of any element to a stage; denominators outside the prime remain outside its inverse
image. A fraction mapping to zero has a finite ideal-membership witness after
multiplication by a denominator. Lift that witness and its finitely many equalities
to a later stage, so the fraction is zero there. These two properties give the
colimit universal property. The tail is cofinal by directedness.
(blueprint: lem-limit-module-localization-ring-data) -/
theorem exists_limit_module_localization_ring_data
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    [∀ i : I, IsLocalRing (F.obj i)] [IsLocalRing c.pt]
    (hF : ∀ (i j : I) (h : i ≤ j), IsLocalHom (F.map (homOfLE h)).hom)
    (hcLocal : ∀ i : I, IsLocalHom (c.ι.app i).hom)
    (T : CommRingCat.{u}) [IsLocalRing T] (τ : c.pt →+* T) [IsLocalHom τ]
    (P : Type p) [CommRing P] [Algebra c.pt P] [Algebra.FinitePresentation c.pt P]
    (W : Submonoid P) (f : P →+* T)
    (hf : f.comp (algebraMap c.pt P) = τ)
    (hT : letI := f.toAlgebra; IsLocalization W T) :
    ∃ i₀ : I,
      ∃ (B : {i : I // i₀ ≤ i} ⥤ CommRingCat.{u}) (β : B ⟶ (Functor.const _).obj T),
        Nonempty (IsColimit (Cocone.mk T β)) ∧
        ∃ (κ : ∀ i : {i : I // i₀ ≤ i}, B.obj i →+* T),
          (∀ i, ∀ x : B.obj i, κ i x = (β.app i).hom x) ∧
          (∀ i, IsLocalRing (B.obj i)) ∧ (∀ i, IsLocalHom (κ i)) ∧
          (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
            IsLocalHom (B.map (homOfLE h)).hom) ∧
          ∃ (τ₀ : ∀ i : {i : I // i₀ ≤ i}, F.obj i.1 →+* B.obj i),
            (∀ i, IsLocalHom (τ₀ i)) ∧ (∀ i, (τ₀ i).EssFiniteType) ∧
            (∀ i, (κ i).comp (τ₀ i) = τ.comp (c.ι.app i.1).hom) ∧
            (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
              (B.map (homOfLE h)).hom.comp (τ₀ i) =
                (τ₀ j).comp (F.map (homOfLE h)).hom) ∧
            (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
              letI := (τ₀ i).toAlgebra
              letI := (F.map (homOfLE h)).hom.toAlgebra
              (∃ φ : B.obj i ⊗[F.obj i.1] F.obj j.1 →+* B.obj j,
                (∀ (x : B.obj i) (y : F.obj j.1),
                  φ (x ⊗ₜ[F.obj i.1] y) =
                    (B.map (homOfLE h)).hom x * τ₀ j y) ∧
                (letI := φ.toAlgebra
                 ∃ U : Submonoid (B.obj i ⊗[F.obj i.1] F.obj j.1),
                   IsLocalization U (B.obj j)))) ∧
            (∀ i : {i : I // i₀ ≤ i},
              letI := (τ₀ i).toAlgebra
              letI : Algebra (F.obj i.1) c.pt := (c.ι.app i.1).hom.toAlgebra
              (∃ φ : B.obj i ⊗[F.obj i.1] c.pt →+* T,
                (∀ (x : B.obj i) (y : c.pt),
                  φ (x ⊗ₜ[F.obj i.1] y) = κ i x * τ y) ∧
                (letI := φ.toAlgebra
                 ∃ U : Submonoid (B.obj i ⊗[F.obj i.1] c.pt), IsLocalization U T))) := by
  sorry
end RingHom
