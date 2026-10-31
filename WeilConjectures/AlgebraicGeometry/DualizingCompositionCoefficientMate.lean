/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.SixFunctorDatum
public import WeilConjectures.AlgebraicGeometry.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.SixFunctorDualNotation
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The constructible dualizing composition mate

Source: main-20261015, sec-six-functors/sk-thm-sf-verdier-exchange/
thm-sf-verdier-exchange.proof.md, Step 1 (composition mate) and Step 3
(its A5 coefficient compatibility)
(blueprint: lem-sf-dualizing-composition-coefficient-mate).

The restricted exceptional functors use the datum's recorded finite-Tor predicates
and the preservation fields of A1. The intrinsic condensed finite-Tor interface is
re-exported from the current dependency; no Tor predicate is defined here.
Dualizing notation is `SixFunctorDualityData.dualizing` as in `def-sf-pf`.
The composition mate is the already recorded right-adjoint composition, restricted
to those full categories. Its Hom normalization determines it
uniquely. The coefficient equation uses precisely the adjunction comparisons of A5.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w v' w'

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

section Restricted

variable {D : FiniteFieldDatum.{u}}
  {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
  {S : SixFunctorPushStage D B} {P : ∀ X, ObjectProperty (B X)}

/-- Restrict the supplied exceptional functor to its actual finite-Tor domain.
Source: A1, finite-Tor domain of def-sf-datum
(blueprint: lem-sf-dualizing-composition-coefficient-mate). -/
def dualizingCompositionExceptional (H : SixFunctorCoherentStage S P)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (cf : Compactification f.hom.left) :
    (P Y).FullSubcategory ⥤ (P X).FullSubcategory :=
  (P X).lift ((P Y).ι ⋙ S.exceptional f cf)
    (fun K ↦ H.exceptionalDomain f cf K.obj K.property)

/-- The existing composition mate, restricted through the full finite-Tor inclusions.
Source: Step 1, conjugate of the supplied A4 compositor
(blueprint: lem-sf-dualizing-composition-coefficient-mate). -/
def dualizingCompositionMate (H : SixFunctorCoherentStage S P)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) :
    dualizingCompositionExceptional H g cg ⋙ dualizingCompositionExceptional H f cf ≅
      dualizingCompositionExceptional H (f ≫ g) cfg :=
  NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk (P X)
      ((sixFunctorExceptionalComposition S f g cf cg cfg).symm.app K.obj))
    (fun t ↦ ObjectProperty.hom_ext (P X)
      ((sixFunctorExceptionalComposition S f g cf cg cfg).inv.naturality t.hom))

/-- The full Hom chain, with precomposition by alpha rather than its inverse.
Source: Step 1, the displayed A1 Hom characterization
(blueprint: lem-sf-dualizing-composition-coefficient-mate). -/
def DualizingCompositionHomFormula (H : SixFunctorCoherentStage S P)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left)
    (c : dualizingCompositionExceptional H g cg ⋙
      dualizingCompositionExceptional H f cf ≅
        dualizingCompositionExceptional H (f ≫ g) cfg) : Prop :=
  ∀ (K : (P X).FullSubcategory) (L : (P Z).FullSubcategory)
    (t : K ⟶ (dualizingCompositionExceptional H g cg ⋙
      dualizingCompositionExceptional H f cf).obj L),
    (t ≫ c.hom.app L).hom =
      (S.exceptionalAdjunction (f ≫ g) cfg).homEquiv K.obj L.obj
        ((S.composition f g cf cg cfg).hom.app K.obj ≫
          ((S.exceptionalAdjunction g cg).homEquiv
            ((S.support f cf).obj K.obj) L.obj).symm
            (((S.exceptionalAdjunction f cf).homEquiv K.obj
              ((S.exceptional g cg).obj L.obj)).symm t.hom))

/-- The normalization and uniqueness clauses for one coefficient stage.
Source: Step 1, natural isomorphism and uniqueness
(blueprint: lem-sf-dualizing-composition-coefficient-mate). -/
def DualizingCompositionNormalized (H : SixFunctorCoherentStage S P) : Prop :=
  ∀ (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left]
    [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (cf : Compactification f.hom.left)
    (cg : Compactification (sixFunctorStructure Y).hom.left)
    (cfg : Compactification (f ≫ sixFunctorStructure Y).hom.left),
    DualizingCompositionHomFormula H f (sixFunctorStructure Y) cf cg cfg
      (dualizingCompositionMate H f (sixFunctorStructure Y) cf cg cfg) ∧
    ∀ c, DualizingCompositionHomFormula H f (sixFunctorStructure Y) cf cg cfg c →
      c = dualizingCompositionMate H f (sixFunctorStructure Y) cf cg cfg

end Restricted

private theorem normalized_stage
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {P : ∀ X, ObjectProperty (B X)}
    (H : SixFunctorCoherentStage S P) : DualizingCompositionNormalized H := by
  intro X Y _ _ f _ _ _ cf cg cfg
  have hformula :
      DualizingCompositionHomFormula H f (sixFunctorStructure Y) cf cg cfg
        (dualizingCompositionMate H f (sixFunctorStructure Y) cf cg cfg) := by
    intro K L t
    have hobj :
        ((dualizingCompositionExceptional H (sixFunctorStructure Y) cg ⋙
          dualizingCompositionExceptional H f cf).obj L).obj =
          (S.exceptional (sixFunctorStructure Y) cg ⋙ S.exceptional f cf).obj L.obj := by
      rfl
    let t' : K.obj ⟶ (S.exceptional (sixFunctorStructure Y) cg ⋙
        S.exceptional f cf).obj L.obj := t.hom ≫ eqToHom hobj
    have hambient :
        t' ≫ (sixFunctorExceptionalComposition S f (sixFunctorStructure Y)
            cf cg cfg).inv.app L.obj =
          (S.exceptionalAdjunction (f ≫ sixFunctorStructure Y) cfg).homEquiv
            K.obj L.obj
            ((S.composition f (sixFunctorStructure Y) cf cg cfg).hom.app K.obj ≫
              ((S.exceptionalAdjunction (sixFunctorStructure Y) cg).homEquiv
                ((S.support f cf).obj K.obj) L.obj).symm
                (((S.exceptionalAdjunction f cf).homEquiv K.obj
                  ((S.exceptional (sixFunctorStructure Y) cg).obj L.obj)).symm t')) := by
      let a := ((S.exceptionalAdjunction f cf).comp
        (S.exceptionalAdjunction (sixFunctorStructure Y) cg)).ofNatIsoLeft
          (S.composition f (sixFunctorStructure Y) cf cg cfg).symm
      have hu :
          ((S.exceptionalAdjunction (f ≫ sixFunctorStructure Y) cfg).homEquiv K.obj
            L.obj).symm
              (t' ≫ ((S.exceptionalAdjunction (f ≫ sixFunctorStructure Y) cfg).rightAdjointUniq
                a).inv.app L.obj) =
            (a.homEquiv K.obj L.obj).symm t' := by
        simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
          Adjunction.rightAdjointUniq_inv_app,
          Adjunction.rightAdjointUniq_hom_app_counit]
      have hmain := congrArg
        ((S.exceptionalAdjunction (f ≫ sixFunctorStructure Y) cfg).homEquiv K.obj L.obj) hu
      have ha :
          (a.homEquiv K.obj L.obj).symm t' =
            (S.composition f (sixFunctorStructure Y) cf cg cfg).hom.app K.obj ≫
              ((S.exceptionalAdjunction (sixFunctorStructure Y) cg).homEquiv
                ((S.support f cf).obj K.obj) L.obj).symm
                (((S.exceptionalAdjunction f cf).homEquiv K.obj
                  ((S.exceptional (sixFunctorStructure Y) cg).obj L.obj)).symm t') := by
        have h := Adjunction.homEquiv_ofNatIsoLeft_symm_apply
          ((S.exceptionalAdjunction f cf).comp
            (S.exceptionalAdjunction (sixFunctorStructure Y) cg))
          (S.composition f (sixFunctorStructure Y) cf cg cfg).symm t'
        rw [Adjunction.comp_homEquiv] at h
        simpa [a] using h
      rw [ha] at hmain
      simpa only [Equiv.apply_symm_apply, sixFunctorExceptionalComposition] using hmain
    simpa [t', dualizingCompositionMate] using hambient
  refine ⟨hformula, ?_⟩
  intro c hc
  apply Iso.ext
  ext L
  have hcL := hc ((dualizingCompositionExceptional H (sixFunctorStructure Y) cg ⋙
      dualizingCompositionExceptional H f cf).obj L) L (𝟙 _)
  have hmL := hformula ((dualizingCompositionExceptional H (sixFunctorStructure Y) cg ⋙
      dualizingCompositionExceptional H f cf).obj L) L (𝟙 _)
  simpa only [Category.id_comp] using hcL.trans hmL.symm

/-- The four coefficient stages have exactly the normalized unique composition mate.
Its value at the coefficient unit is the indicated dualizing isomorphism, since
`SixFunctorDualityData.dualizing` is exceptional inverse image of that unit.

Source: main-20261015, thm-sf-verdier-exchange.proof.md, Step 1
(blueprint: lem-sf-dualizing-composition-coefficient-mate).

Proof: (1) the pasted adjunction `(F ⊣ U).comp (G ⊣ V)` transported along the
inverse of the A4 compositor alpha (def-weil-pbc-composite-adjunction) is a
second left adjoint structure for `H ⊣ W`; the recorded composition mate is the
right-adjoint uniqueness isomorphism between them (def-weil-pbc-adjunction-conjugate),
so its counit identity turns the H-Hom bijection of `t ≫ c` into the pasted Hom
bijection of `t`, i.e. alpha followed by the two inverse Hom bijections
(def-weil-pbc-adjunction-mate). (2) The restricted functors agree objectwise with
the ambient ones; morphisms are transported through the full finite-Tor
inclusions. (3) Uniqueness: test a competing map on the identity of the composite
right-adjoint object, where both formulas give the same value. The same argument
applies to each of the four coherent stages. No biduality is used. -/
theorem dualizingComposition_normalized
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorDatum D C E n hn) :
    DualizingCompositionNormalized S.finiteCoherence ∧
    DualizingCompositionNormalized S.integralCoherence ∧
    DualizingCompositionNormalized S.rationalCoherence ∧
    DualizingCompositionNormalized S.commonCoherence := by
  exact ⟨normalized_stage S.finiteCoherence, normalized_stage S.integralCoherence,
    normalized_stage S.rationalCoherence, normalized_stage S.commonCoherence⟩

section Coefficients

variable {D : FiniteFieldDatum.{u}}
  {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
  {B' : SixFunctorSpace D → Type v'} [∀ X, Category.{w'} (B' X)]

/-- The composition mate evaluated at the coefficient unit, hence the dualizing iso.
Source: Step 1, the particular isomorphism f^! omega_Y = omega_X
(blueprint: lem-sf-dualizing-composition-coefficient-mate). -/
def dualizingCompositionUnitIso (S : SixFunctorPushStage D B)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (cf : Compactification f.hom.left)
    (cg : Compactification (sixFunctorStructure Y).hom.left)
    (cfg : Compactification (f ≫ sixFunctorStructure Y).hom.left)
    (one : B (sixFunctorPoint D)) :
    (S.exceptional f cf).obj ((S.exceptional (sixFunctorStructure Y) cg).obj one) ≅
      (S.exceptional (f ≫ sixFunctorStructure Y) cfg).obj one :=
  (sixFunctorExceptionalComposition S f (sixFunctorStructure Y) cf cg cfg).symm.app one

/-- The A5 dualizing-object comparison: beta followed by exceptional image of u.
Here the chosen source structure map is literally `a_Y f`, as in the node.
Source: Step 3, definition of kappa
(blueprint: lem-sf-dualizing-composition-coefficient-mate). -/
def dualizingCompositionKappa
    {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
    {T : ∀ X, B X ⥤ B' X} (A : SixFunctorCoefficientComparison S S' T)
    {X Z : SixFunctorSpace D} (a : X ⟶ Z) (ca : Compactification a.hom.left)
    {one : B Z} {one' : B' Z} (unit : (T Z).obj one ≅ one') :
    (T X).obj ((S.exceptional a ca).obj one) ≅ (S'.exceptional a ca).obj one' :=
  ((A.supportAdjunction a ca).right.app one) ≪≫
    (S'.exceptional a ca).mapIso unit

private theorem coefficient_exchange_at
    {C₁ C₂ C₃ C₄ : Type v} {D₁ D₂ D₃ D₄ : Type v'}
    [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃] [Category.{w} C₄]
    [Category.{w'} D₁] [Category.{w'} D₂] [Category.{w'} D₃] [Category.{w'} D₄]
    {U : C₁ ⥤ C₂} {R : C₂ ⥤ C₁} {V : C₃ ⥤ C₄} {S : C₄ ⥤ C₃}
    {Ue : D₁ ⥤ D₂} {Re : D₂ ⥤ D₁} {Ve : D₃ ⥤ D₄} {Se : D₄ ⥤ D₃}
    (a : U ⊣ R) (b : V ⊣ S) (ae : Ue ⊣ Re) (be : Ve ⊣ Se)
    {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄} {Ge : D₁ ⥤ D₃} {He : D₂ ⥤ D₄}
    {T₁ : C₁ ⥤ D₁} {T₂ : C₂ ⥤ D₂} {T₃ : C₃ ⥤ D₃} {T₄ : C₄ ⥤ D₄}
    (θ : G ⋙ V ⟶ U ⋙ H) (θe : Ge ⋙ Ve ⟶ Ue ⋙ He)
    (K : C₂)
    (B : (R ⋙ G).obj K ⟶ (H ⋙ S).obj K)
    (Be : (Re ⋙ Ge).obj (T₂.obj K) ⟶ (He ⋙ Se).obj (T₂.obj K))
    (hB : V.map B ≫ b.counit.app (H.obj K) =
      θ.app (R.obj K) ≫ H.map (a.counit.app K))
    (hBe : Ve.map Be ≫ be.counit.app (He.obj (T₂.obj K)) =
      θe.app (Re.obj (T₂.obj K)) ≫ He.map (ae.counit.app (T₂.obj K)))
    (αU : U ⋙ T₂ ≅ T₁ ⋙ Ue) (αV : V ⋙ T₄ ≅ T₃ ⋙ Ve)
    (αG : G ⋙ T₃ ⟶ T₁ ⋙ Ge) (αH : H ⋙ T₄ ⟶ T₂ ⋙ He)
    (δ : T₁.obj (R.obj K) ⟶ Re.obj (T₂.obj K))
    (δ' : T₃.obj (S.obj (H.obj K)) ⟶ Se.obj (T₄.obj (H.obj K)))
    (hδ : Ue.map δ ≫ ae.counit.app (T₂.obj K) =
      αU.inv.app (R.obj K) ≫ T₂.map (a.counit.app K))
    (hδ' : Ve.map δ' ≫ be.counit.app (T₄.obj (H.obj K)) =
      αV.inv.app (S.obj (H.obj K)) ≫ T₄.map (b.counit.app (H.obj K)))
    (hcube : T₄.map (θ.app (R.obj K)) ≫ αH.app (U.obj (R.obj K)) ≫
        He.map (αU.hom.app (R.obj K)) =
      αV.hom.app (G.obj (R.obj K)) ≫ Ve.map (αG.app (R.obj K)) ≫
        θe.app (T₁.obj (R.obj K))) :
    αG.app (R.obj K) ≫ Ge.map δ ≫ Be =
      T₃.map B ≫ δ' ≫ Se.map (αH.app K) := by
  apply (be.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_symm_apply, Functor.map_comp, Category.assoc]
  rw [hBe]
  have hn := θe.naturality (δ)
  rw [reassoc_of% hn, ← Functor.map_comp, hδ]
  have hn' := be.counit.naturality (αH.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hn'
  rw [hn', reassoc_of% (hδ')]
  rw [reassoc_of% (αV.inv.naturality (B)), ← Functor.map_comp_assoc, hB]
  simp only [Functor.map_comp, Category.assoc]
  have hnH := αH.naturality (a.counit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at hnH
  rw [hnH]
  have hc := congrArg (fun z ↦ αV.inv.app (G.obj (R.obj K)) ≫ z ≫
    He.map (αU.inv.app (R.obj K))) hcube
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at hc
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at hc
  simp only [Functor.comp_obj] at hc
  simpa [Category.assoc] using congrArg
    (fun z ↦ z ≫ He.map (T₂.map (a.counit.app K))) hc.symm


/-- The generic composition mate calculation.
The composite mate has the composite counit equation by naturality of the first counit.
Apply pointwise coefficient exchange to the two adjunction compositors and remove the
identity horizontal functors. Source: Step 3, compatibility with exceptional
composition (blueprint: lem-sf-dualizing-composition-coefficient-mate). -/
private theorem coefficientMate_composition
    {C₀ C₁ C₂ : Type v} {D₀ D₁ D₂ : Type v'}
    [Category.{w} C₀] [Category.{w} C₁] [Category.{w} C₂]
    [Category.{w'} D₀] [Category.{w'} D₁] [Category.{w'} D₂]
    {Lf : C₀ ⥤ C₁} {Rf : C₁ ⥤ C₀} {Lg : C₁ ⥤ C₂} {Rg : C₂ ⥤ C₁}
    {Lh : C₀ ⥤ C₂} {Rh : C₂ ⥤ C₀}
    {Lf' : D₀ ⥤ D₁} {Rf' : D₁ ⥤ D₀} {Lg' : D₁ ⥤ D₂} {Rg' : D₂ ⥤ D₁}
    {Lh' : D₀ ⥤ D₂} {Rh' : D₂ ⥤ D₀}
    {Q₀ : C₀ ⥤ D₀} {Q₁ : C₁ ⥤ D₁} {Q₂ : C₂ ⥤ D₂}
    (af : Lf ⊣ Rf) (ag : Lg ⊣ Rg) (ah : Lh ⊣ Rh)
    (bf : Lf' ⊣ Rf') (bg : Lg' ⊣ Rg') (bh : Lh' ⊣ Rh')
    (p : Lf ⋙ Lg ≅ Lh) (p' : Lf' ⋙ Lg' ≅ Lh')
    (qf : Lf ⋙ Q₁ ≅ Q₀ ⋙ Lf') (qg : Lg ⋙ Q₂ ≅ Q₁ ⋙ Lg')
    (qh : Lh ⋙ Q₂ ≅ Q₀ ⋙ Lh')
    (K : C₂)
    (δf : Q₀.obj (Rf.obj (Rg.obj K)) ⟶ Rf'.obj (Q₁.obj (Rg.obj K)))
    (δg : Q₁.obj (Rg.obj K) ⟶ Rg'.obj (Q₂.obj K))
    (δh : Q₀.obj (Rh.obj K) ⟶ Rh'.obj (Q₂.obj K))
    (hδf : Lf'.map δf ≫ bf.counit.app (Q₁.obj (Rg.obj K)) =
      qf.inv.app (Rf.obj (Rg.obj K)) ≫ Q₁.map (af.counit.app (Rg.obj K)))
    (hδg : Lg'.map δg ≫ bg.counit.app (Q₂.obj K) =
      qg.inv.app (Rg.obj K) ≫ Q₂.map (ag.counit.app K))
    (hδh : Lh'.map δh ≫ bh.counit.app (Q₂.obj K) =
      qh.inv.app (Rh.obj K) ≫ Q₂.map (ah.counit.app K))
    (hc : Q₂.map (p.hom.app (Rh.obj K)) ≫ qh.hom.app (Rh.obj K) =
      qg.hom.app (Lf.obj (Rh.obj K)) ≫ Lg'.map (qf.hom.app (Rh.obj K)) ≫
        p'.hom.app (Q₀.obj (Rh.obj K))) :
    Q₀.map ((conjugateIsoEquiv ah (af.comp ag) p).hom.app K) ≫
        δf ≫ Rf'.map (δg) =
      δh ≫ (conjugateIsoEquiv bh (bf.comp bg) p').hom.app (Q₂.obj K) := by
  let qp : (Lf ⋙ Lg) ⋙ Q₂ ≅ Q₀ ⋙ (Lf' ⋙ Lg') :=
    Functor.associator Lf Lg Q₂ ≪≫ Functor.isoWhiskerLeft Lf qg ≪≫
      (Functor.associator Lf Q₁ Lg').symm ≪≫ Functor.isoWhiskerRight qf Lg' ≪≫
        Functor.associator Q₀ Lf' Lg'
  have hp :
      (Lf' ⋙ Lg').map (δf ≫ Rf'.map (δg)) ≫
        (bf.comp bg).counit.app (Q₂.obj K) =
      qp.inv.app ((Rg ⋙ Rf).obj K) ≫ Q₂.map ((af.comp ag).counit.app K) := by
    have hn := bf.counit.naturality (δg)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hn
    have hn' := congrArg Lg'.map hn
    simp only [Functor.map_comp] at hn'
    simp only [Functor.comp_map, Functor.comp_obj, Functor.map_comp,
      Adjunction.comp_counit_app, Category.assoc]
    rw [reassoc_of% hn', ← Lg'.map_comp_assoc, hδf, Lg'.map_comp,
      Category.assoc, hδg]
    have hq := qg.inv.naturality (af.counit.app (Rg.obj K))
    dsimp only [Functor.comp_map, Functor.comp_obj] at hq
    simp only [qp, Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc]
    rw [reassoc_of% hq]
  have hcube : Q₂.map (p.hom.app (Rh.obj K)) ≫ qh.hom.app (Rh.obj K) =
      qg.hom.app (Lf.obj (Rh.obj K)) ≫ Lg'.map (qf.hom.app (Rh.obj K)) ≫
        p'.hom.app (Q₀.obj (Rh.obj K)) := hc
  have hh := coefficient_exchange_at (G := 𝟭 C₀) (H := 𝟭 C₂)
    (Ge := 𝟭 D₀) (He := 𝟭 D₂) (T₁ := Q₀) (T₂ := Q₂) (T₃ := Q₀) (T₄ := Q₂)
    ah (af.comp ag) bh (bf.comp bg)
    p.hom p'.hom K ((conjugateEquiv ah (af.comp ag) p.hom).app K)
    ((conjugateEquiv bh (bf.comp bg) p'.hom).app (Q₂.obj K))
    (conjugateEquiv_counit ah (af.comp ag) p.hom K)
    (conjugateEquiv_counit bh (bf.comp bg) p'.hom (Q₂.obj K))
    qh qp (Q₀.leftUnitor.hom ≫ Q₀.rightUnitor.inv)
    (Q₂.leftUnitor.hom ≫ Q₂.rightUnitor.inv) δh
    (δf ≫ Rf'.map (δg)) hδh hp (by
      simpa [qp] using hcube)
  have hi₀ : (Q₀.leftUnitor.hom ≫ Q₀.rightUnitor.inv).app (Rh.obj K) =
      𝟙 (Q₀.obj (Rh.obj K)) := by simp
  have hi₂ : (Q₂.leftUnitor.hom ≫ Q₂.rightUnitor.inv).app K = 𝟙 (Q₂.obj K) := by simp
  rw [hi₀, hi₂, (Rg' ⋙ Rf').map_id (Q₂.obj K), Functor.id_map] at hh
  have he := Category.id_comp
    (δh ≫ (conjugateEquiv bh (bf.comp bg) p'.hom).app (Q₂.obj K))
  have he' := Category.comp_id
    (Q₀.map ((conjugateEquiv ah (af.comp ag) p.hom).app K) ≫ (δf ≫ Rf'.map δg))
  have hh' := he.symm.trans (hh.trans ((Category.assoc _ _ _).symm.trans he'))
  simpa only [conjugateIsoEquiv_apply_hom] using hh'.symm


private theorem coefficient_exceptional_composition
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {B' : SixFunctorSpace D → Type v'} [∀ X, Category.{w'} (B' X)]
    (S : SixFunctorPushStage D B) (S' : SixFunctorPushStage D B')
    (T : ∀ X, B X ⥤ B' X) (A : SixFunctorCoefficientComparison S S' T)
    (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left]
    [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (cf : Compactification f.hom.left)
    (cg : Compactification (sixFunctorStructure Y).hom.left)
    (cfg : Compactification (f ≫ sixFunctorStructure Y).hom.left)
    (one : B (sixFunctorPoint D)) :
    (T X).map ((sixFunctorExceptionalComposition S f (sixFunctorStructure Y)
        cf cg cfg).inv.app one) ≫
      (A.supportAdjunction (f ≫ sixFunctorStructure Y) cfg).right.hom.app one =
    (A.supportAdjunction f cf).right.hom.app
        ((S.exceptional (sixFunctorStructure Y) cg).obj one) ≫
      (S'.exceptional f cf).map
        ((A.supportAdjunction (sixFunctorStructure Y) cg).right.hom.app one) ≫
      (sixFunctorExceptionalComposition S' f (sixFunctorStructure Y)
        cf cg cfg).inv.app ((T (sixFunctorPoint D)).obj one) := by
  let af := S.exceptionalAdjunction f cf
  let ag := S.exceptionalAdjunction (sixFunctorStructure Y) cg
  let ah := S.exceptionalAdjunction (f ≫ sixFunctorStructure Y) cfg
  let bf := S'.exceptionalAdjunction f cf
  let bg := S'.exceptionalAdjunction (sixFunctorStructure Y) cg
  let bh := S'.exceptionalAdjunction (f ≫ sixFunctorStructure Y) cfg
  let p := (S.composition f (sixFunctorStructure Y) cf cg cfg).symm
  let p' := (S'.composition f (sixFunctorStructure Y) cf cg cfg).symm
  let qf := (A.supportAdjunction f cf).left
  let qg := (A.supportAdjunction (sixFunctorStructure Y) cg).left
  let qh := (A.supportAdjunction (f ≫ sixFunctorStructure Y) cfg).left
  let δf := (A.supportAdjunction f cf).right.hom.app
      ((S.exceptional (sixFunctorStructure Y) cg).obj one)
  let δg := (A.supportAdjunction (sixFunctorStructure Y) cg).right.hom.app one
  let δh := (A.supportAdjunction (f ≫ sixFunctorStructure Y) cfg).right.hom.app one
  let qp := Functor.associator (S.support f cf) (S.support (sixFunctorStructure Y) cg)
      (T (sixFunctorPoint D)) ≪≫
    Functor.isoWhiskerLeft (S.support f cf) qg ≪≫
      (Functor.associator (S.support f cf) (T Y)
        (S'.support (sixFunctorStructure Y) cg)).symm ≪≫
      Functor.isoWhiskerRight qf (S'.support (sixFunctorStructure Y) cg) ≪≫
      Functor.associator (T X) (S'.support f cf)
        (S'.support (sixFunctorStructure Y) cg)
  have hcomp := A.composition f (sixFunctorStructure Y) cf cg cfg
      ((S.exceptional (f ≫ sixFunctorStructure Y) cfg).obj one)
  have hc : (T (sixFunctorPoint D)).map
      (p.hom.app ((S.exceptional (f ≫ sixFunctorStructure Y) cfg).obj one)) ≫
      qh.hom.app ((S.exceptional (f ≫ sixFunctorStructure Y) cfg).obj one) =
      qg.hom.app ((S.support f cf).obj
        ((S.exceptional (f ≫ sixFunctorStructure Y) cfg).obj one)) ≫
        (S'.support (sixFunctorStructure Y) cg).map
          (qf.hom.app ((S.exceptional (f ≫ sixFunctorStructure Y) cfg).obj one)) ≫
        p'.hom.app ((T X).obj
          ((S.exceptional (f ≫ sixFunctorStructure Y) cfg).obj one)) := by
    have h := congrArg (fun z ↦
      (T (sixFunctorPoint D)).map
          (p.hom.app ((S.exceptional (f ≫ sixFunctorStructure Y) cfg).obj one)) ≫ z ≫
        p'.hom.app ((T X).obj ((S.exceptional (f ≫ sixFunctorStructure Y) cfg).obj one))) hcomp
    simpa [p, p', qf, qg, qh, af, ag, ah, bf, bg, bh, Category.assoc] using h.symm
  have hm := coefficientMate_composition af ag ah bf bg bh p p' qf qg qh one
    δf δg δh
    (by
      simpa [δf, qf, af, bf, Category.assoc] using
        (A.supportAdjunction f cf).counit
          ((S.exceptional (sixFunctorStructure Y) cg).obj one))
    (by
      simpa [δg, qg, ag, bg, Category.assoc] using
        (A.supportAdjunction (sixFunctorStructure Y) cg).counit one)
    (by
      simpa [δh, qh, ah, bh, Category.assoc] using
        (A.supportAdjunction (f ≫ sixFunctorStructure Y) cfg).counit one)
    (by
      simpa [qp, Category.assoc] using hc)
  have hi := congrArg (fun z ↦
      (T X).map ((conjugateIsoEquiv ah (af.comp ag) p).inv.app one) ≫ z ≫
        (conjugateIsoEquiv bh (bf.comp bg) p').inv.app
          ((T (sixFunctorPoint D)).obj one)) hm
  have ep : (conjugateIsoEquiv ah (af.comp ag) p).inv.app one =
      (sixFunctorExceptionalComposition S f (sixFunctorStructure Y)
        cf cg cfg).inv.app one := by
    apply (cancel_epi ((sixFunctorExceptionalComposition S f
      (sixFunctorStructure Y) cf cg cfg).hom.app one)).1
    simp only [Functor.comp_obj, sixFunctorExceptionalComposition,
      Adjunction.rightAdjointUniq, conjugateIsoEquiv, Equiv.coe_fn_mk, Iso.refl_hom,
      Iso.refl_inv, conjugateEquiv_apply_app, Adjunction.ofNatIsoLeft_unit,
      Adjunction.comp_unit, Iso.symm_hom, Category.assoc, NatTrans.comp_app,
      Functor.id_obj, Functor.whiskerRight_app, Functor.rightUnitor_inv_app,
      Functor.whiskerLeft_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.comp_map, Category.id_comp, NatTrans.id_app,
      Iso.symm_inv, Adjunction.comp_counit_app, Functor.map_comp,
      Adjunction.ofNatIsoLeft_counit, p]
    aesop_cat
  have ep' : (conjugateIsoEquiv bh (bf.comp bg) p').inv.app
      ((T (sixFunctorPoint D)).obj one) =
      (sixFunctorExceptionalComposition S' f (sixFunctorStructure Y)
        cf cg cfg).inv.app ((T (sixFunctorPoint D)).obj one) := by
    simp only [Functor.comp_obj, conjugateIsoEquiv, Equiv.coe_fn_mk, Iso.symm_hom,
      Iso.symm_inv, conjugateEquiv_apply_app, Adjunction.comp_counit_app,
      Functor.map_comp, sixFunctorExceptionalComposition, Adjunction.rightAdjointUniq,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
      Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Functor.id_obj,
      Functor.whiskerLeft_app, p']
    aesop_cat
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Iso.hom_inv_id_app] at hi
  rw [ep, ep'] at hi
  simpa [Category.assoc] using hi.symm

/-- Coefficient equation for an allowed A5 comparison, with its supplied unit map.
This is stated in the faithful bounded-constructible presentation of the full
finite-Tor categories; all arrows and their order are unchanged by the inclusion.
`S,S'` are the stages of that comparison, not additional exceptional adjoints on
ambient derived categories. A comparison is supplied only where A5 defines it;
this theorem neither constructs nor assumes any field-to-finite reduction.

Source: main-20261015, thm-sf-verdier-exchange.proof.md, Step 3,
with coefficient compatibility supplied by def-sf-datum A5
(blueprint: lem-sf-dualizing-composition-coefficient-mate).

Proof plan: (1) A.supportAdjunction is exactly the A5 unit/counit square, so its
right comparison is the mate of the inverse left comparison by
def-weil-pbc-adjunction-mate. (2) A.composition is the A5 compositor square.
Rearrange that square and apply lem-weil-pbc-mate-pasting: clause 2 pastes the
f and a_Y comparisons, and clauses 3a and 3b change the two adjunctions via alpha
and alpha'. (3) The two equal left squares have equal mates, giving the equation
at arbitrary L. (4) Put L equal to the coefficient unit, postcompose by the
exceptional image of unit, and use naturality of the target composition mate.
This gives exactly kappa_X T_X(c_f) = c'_f f'^!(kappa_Y) beta_f. -/
theorem dualizingComposition_coefficient
    (S : SixFunctorPushStage D B) (S' : SixFunctorPushStage D B')
    (T : ∀ X, B X ⥤ B' X) (A : SixFunctorCoefficientComparison S S' T)
    (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left]
    [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (cf : Compactification f.hom.left)
    (cg : Compactification (sixFunctorStructure Y).hom.left)
    (cfg : Compactification (f ≫ sixFunctorStructure Y).hom.left)
    (one : B (sixFunctorPoint D)) (one' : B' (sixFunctorPoint D))
    (unit : (T (sixFunctorPoint D)).obj one ≅ one') :
    (T X).map
        (dualizingCompositionUnitIso S f cf cg cfg one).hom ≫
      (dualizingCompositionKappa A (f ≫ sixFunctorStructure Y) cfg unit).hom =
    (A.supportAdjunction f cf).right.hom.app
        ((S.exceptional (sixFunctorStructure Y) cg).obj one) ≫
      (S'.exceptional f cf).map
        (dualizingCompositionKappa A (sixFunctorStructure Y) cg unit).hom ≫
      (dualizingCompositionUnitIso S' f cf cg cfg one').hom := by
  have h := coefficient_exceptional_composition S S' T A X Y f cf cg cfg one
  have h' := congrArg (fun z ↦ z ≫
    (S'.exceptional (f ≫ sixFunctorStructure Y) cfg).map unit.hom) h
  simp only [Category.assoc] at h'
  rw [← (sixFunctorExceptionalComposition S' f (sixFunctorStructure Y)
      cf cg cfg).inv.naturality unit.hom] at h'
  convert h' using 1 <;>
    simp [dualizingCompositionUnitIso, dualizingCompositionKappa,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
      Functor.comp_obj, Category.assoc]

end Coefficients
end WeilConjectures
