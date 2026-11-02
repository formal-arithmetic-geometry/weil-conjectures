/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RetractedSupport.RetractedSupportKernelCounitMap
public import WeilConjectures.AlgebraicGeometry.RetractedSupport.RetractedSupportRepresentability
import WeilConjectures.CategoryTheory.RestrictedCoyonedaRigidity
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedExteriorProduct

/-! # Rigidity identifies the supplied support isomorphism with the kernel map

Source: the second assertion of `lem-pur-gysin-structure.proof.md`
(blueprint: lem-pur-retracted-support-kernel-class).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.PurityFiniteSetting

namespace AlgebraicGeometry.ProEtale.RetractedSupport

private theorem representedEndomorphism_rigidity
    {C : Type*} [Category C] {D : Type*} [Category.{u} D]
    {E : Type*} [Category E]
    (F : C ⥤ D) [F.Full] [F.Faithful] (G : E ⥤ D) [G.Full]
    {A B : C} (q : A ⟶ B) [Epi q] (R : E) (e : G.obj R ≅ F.obj B)
    (T H : E ⥤ Type u) (ρ : T ≅ G ⋙ coyoneda.obj (op (F.obj B)))
    (v : T ⟶ H) (ζ : ∀ K : E, H.obj K → (F.obj A ⟶ G.obj K))
    (hv : ∀ (K : E) (x : T.obj K),
      ζ K (v.app K x) = F.map q ≫ ρ.hom.app K x)
    (α : T ⟶ T) (hα : ∀ (K : E) (x : T.obj K), v.app K (α.app K x) = v.app K x) :
    ∀ (K : E) (x : T.obj K), α.app K x = x := by
  let t (K : E) (f : F.obj B ⟶ G.obj K) := ρ.hom.app K (α.app K (ρ.inv.app K f))
  have ht {K L : E} (g : K ⟶ L) (f : F.obj B ⟶ G.obj K) :
      t L (f ≫ G.map g) = t K f ≫ G.map g := by
    have hi := ConcreteCategory.congr_hom (ρ.inv.naturality g) f
    change ρ.inv.app L (f ≫ G.map g) = T.map g (ρ.inv.app K f) at hi
    dsimp only [t]
    rw [hi]
    have ha := ConcreteCategory.congr_hom (α.naturality g) (ρ.inv.app K f)
    change α.app L (T.map g (ρ.inv.app K f)) =
      T.map g (α.app K (ρ.inv.app K f)) at ha
    rw [ha]
    exact ConcreteCategory.congr_hom (ρ.hom.naturality g) (α.app K (ρ.inv.app K f))
  have hq : F.map q ≫ t R e.inv = F.map q ≫ e.inv := by
    dsimp only [t]
    rw [← hv R (α.app R (ρ.inv.app R e.inv)), hα,
      hv R (ρ.inv.app R e.inv)]
    have he := ConcreteCategory.congr_hom (ρ.inv_hom_id_app R) e.inv
    change ρ.hom.app R (ρ.inv.app R e.inv) = e.inv at he
    rw [he]
  have h := CategoryTheory.restrictedCoyoneda_rigidity F G q R e t (fun g f => ht g f) hq
  intro K x
  have hx := h K (ρ.hom.app K x)
  have he := ConcreteCategory.congr_hom (ρ.hom_inv_id_app K) x
  change ρ.inv.app K (ρ.hom.app K x) = x at he
  dsimp only [t] at hx
  rw [he] at hx
  have he' := ConcreteCategory.congr_hom (ρ.hom_inv_id_app K) (α.app K x)
  change ρ.inv.app K (ρ.hom.app K (α.app K x)) = α.app K x at he'
  exact he'.symm.trans ((congrArg (fun f => ρ.inv.app K f) hx).trans he)

/-- The arbitrary natural support comparison agrees with the class of the normalized
closed counit, on every bounded-below ordinary etale input and in each fixed degree.
Source: `lem-pur-gysin-structure.proof.md`, supported-Hom identification; Milne,
Etale Cohomology, Theorem 9.4 and Example 9.5
(blueprint: lem-pur-retracted-support-kernel-class).

Proof:
1. Compute the ordinary closed right adjoint on a bounded-below injective representative
   of B. Exact closed direct image makes this adjoint preserve injectives. The kernel of
   restriction to the complementary open is the direct image of this closed value, and
   its inclusion is the ordinary counit. Global evaluation identifies its sections with
   the ordinary supported-section kernel.
2. Derive this kernel comparison, using the right-derived units on the representatives.
   Transport along the finite etale/pro-etale comparison and along the retraction
   collapse. The resulting comparison of cohomology is normalized by the forget-support
   map. The specified exceptional comparison and image comparison give precisely the
   displayed six-factor morphism; the supported derived adjunction constructs its class.
3. Work naturally in all bounded-below inputs B before evaluating on the given m.
   In degree q, both cohomology functors are represented by the closed direct image
   of the constant object shifted by minus q. The supplied comparison's global_first
   equation says that its ratio with the kernel comparison fixes forgetting support.
4. Represent the ratio by an endomorphism of this shifted single object. Deshift and
   lift the endomorphism through the fully faithful single-object functor. Forgetting
   support is precomposition by the quotient from the ambient constant sheaf to the
   closed constant direct image. That quotient is epic in the sheaf category, so its
   lift is the identity. The restrictedCoyoneda_rigidity lemma gives identity on every
   test input; no shift compatibility of the arbitrary family supportIso is assumed.
5. Evaluate this equality on the global unit class of m. Naturality of global-class
   evaluation moves m through the canonical kernel comparison. The derived adjunction
   class is exactly the right side. Zero morphisms and empty closed supports are covered
   by the same kernel and adjunction constructions. -/
theorem kernel_support_class
    (P : WeilConjectures.PurityFiniteSetting.{u}) (h : P.ramificationIndex ∣ P.level)
    (T : Scheme.{u}) [IsLocallyNoetherian (Line T)]
    (c : Comparison P (lineProjection T) (zeroSection T) (openImmersion T)
      (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) T))
    (hb : DerivedCategory.TStructure.t.plus (P.boundaryEtaleValue h T))
    (eK : (nu P T).obj (P.boundaryEtaleValue h T) ≅ P.gysinValue h T)
    (d : (nu P (Line T)).obj
        ((Etale.lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.obj
          (P.boundaryEtaleValue h T)) ≅
      (lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.obj
        ((nu P T).obj (P.boundaryEtaleValue h T)))
    (heK : eK.hom = P.boundaryExceptionalComparison h T)
    (hd : d.hom = P.boundaryImageComparison T ⟨P.boundaryEtaleValue h T, hb⟩)
    (m : P.derivedSheaf h T false ⟶ P.gysinValue h T) :
    ((c.supportIso 2).hom.app (P.gysinEtaleInput h T)) (P.gysinGlobalClass T 2 m) =
      supportedHomPairAdjunctionClass P (zeroSection T) (P.gysinInput h T) 2
          (((lowerStar (Modules P) (zeroSection T)).mapDerivedCategorySingleFunctor 0).inv.app
          (P.constant T) ≫
        (lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map m ≫
        (lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map eK.inv ≫
        d.inv ≫ (nu P (Line T)).map (P.boundaryEtaleCounit h T) ≫
        ((nu P (Line T)).commShiftIso (2 : ℤ)).hom.app (P.gysinEtaleInput h T).obj) := by
  have hfirstIso (L : DerivedCategory.Plus (EtSheaves P (Line T))) :
      IsIso (firstComparison P (lineProjection T) (zeroSection T)
        (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) T) L) := by
    obtain ⟨v, hv, _, _⟩ := c.transport L
    rw [← hv]
    infer_instance
  have hfirst (L : DerivedCategory.Plus (EtSheaves P (Line T))) :
      firstComparison P (lineProjection T) (zeroSection T)
        (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) T) L ≫ c.first.app L =
        (nu P T).map ((Etale.lowerStar (Modules P) (lineProjection T)).rightDerivedFunctor.map
          ((Adjunction.ofIsLeftAdjoint
            (Etale.lowerStar (Modules P) (zeroSection T)).rightDerivedFunctor).counit.app L.obj)) ≫
          imageComparison P (lineProjection T) L := by
    obtain ⟨v, hv, hw, _⟩ := c.transport L
    have h := v.hom.comm₁
    rw [hv, hw] at h
    exact h.symm
  obtain ⟨κ, hκ, hm⟩ := kernelCounitClassNaturalMap P h T
    c.first hfirstIso hfirst
  obtain ⟨M⟩ := supportRepresentability_exists P (zeroSection T) 2
  let σ := c.supportIso 2
  let α : supportValues P (zeroSection T) 2 ⟶ supportValues P (zeroSection T) 2 :=
    Functor.whiskerRight (σ.inv ≫ κ) (forget (Modules P))
  have hα (L : DerivedCategory.Plus (EtSheaves P (Line T)))
      (x : (supportValues P (zeroSection T) 2).obj L) :
      (supportForgetValues P (zeroSection T) 2).app L (α.app L x) =
        (supportForgetValues P (zeroSection T) 2).app L x := by
    have h := ConcreteCategory.congr_hom
      ((c.global_first L 2).symm.trans (hκ L)) (σ.inv.app L x)
    have hi := ConcreteCategory.congr_hom (σ.inv_hom_id_app L) x
    change σ.hom.app L (σ.inv.app L x) = x at hi
    change (supportForgetValues P (zeroSection T) 2).app L (σ.hom.app L (σ.inv.app L x)) =
      (supportForgetValues P (zeroSection T) 2).app L (α.app L x) at h
    rw [hi] at h
    exact h.symm
  let C := supportClosedCoefficient P (zeroSection T)
  let R := (DerivedCategory.Plus.singleFunctor (EtSheaves P (Line T)) 2).obj C
  let eR : (supportTests P (X := (Line T)) 2).obj R ≅ (supportSingle P).obj C :=
    ((DerivedCategory.singleFunctors (EtSheaves P (Line T))).shiftIso 2 0 2 (add_zero 2)).app C
  have : Epi (Etale.supportedCoefficientQuotient P.Coefficient (zeroSection T)
      (ModuleCat.of P.Coefficient P.Coefficient)) :=
    Etale.coefficientQuotient_epi P.Coefficient (zeroSection T) _
  have hr := representedEndomorphism_rigidity
    (supportSingle P) (supportTests P (X := (Line T)) 2)
    (Etale.supportedCoefficientQuotient P.Coefficient (zeroSection T)
      (ModuleCat.of P.Coefficient P.Coefficient)) R eR
    (supportValues P (zeroSection T) 2) (supportAmbientValues P (X := (Line T)) 2) M.supported
    (supportForgetValues P (zeroSection T) 2) (fun L => M.ambient.hom.app L) M.forget_eq α hα
  let B := P.gysinEtaleInput h T
  have hx := hr B (σ.hom.app B (P.gysinGlobalClass T 2 m))
  change κ.app B (σ.inv.app B (σ.hom.app B (P.gysinGlobalClass T 2 m))) =
    σ.hom.app B (P.gysinGlobalClass T 2 m) at hx
  have hi := ConcreteCategory.congr_hom (σ.hom_inv_id_app B) (P.gysinGlobalClass T 2 m)
  change σ.inv.app B (σ.hom.app B (P.gysinGlobalClass T 2 m)) =
    P.gysinGlobalClass T 2 m at hi
  rw [hi] at hx
  exact hx.symm.trans (hm hb eK d heK hd m)

end AlgebraicGeometry.ProEtale.RetractedSupport
