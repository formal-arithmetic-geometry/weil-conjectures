/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H6
-/
module

public import Sheaf.Paper.SectionsScalarCochainCoherence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import all Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction

/-! # Ordinary sections and scalar towers with independent coefficient universes

Source: Stacks 03EK, 03CZ, 03CY; the ordinary part of the sections-scalar coherence
argument (blueprint: lem-weil-sections-scalar-ordinary-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe z x y v w a r uC vC
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory.ScalarTower

variable {I : Type z} [Preorder I]
  (S : I → Type x) (M : I → Type y)
  [∀ i, Category.{v} (S i)] [∀ i, Category.{w} (M i)]
  (T : ∀ i j, i ≤ j → S i ⥤ S j) (t : ∀ i j, i ≤ j → M i ⥤ M j)

/-- The four kinds of ordinary scalar coherence isomorphisms.
Source: Stacks 03EK (blueprint: lem-weil-sections-scalar-ordinary-tower). -/
structure OrdinaryMaps where
  sheafComp : ∀ i j k (h : i ≤ j) (g : j ≤ k), T i j h ⋙ T j k g ≅ T i k (h.trans g)
  moduleComp : ∀ i j k (h : i ≤ j) (g : j ≤ k), t i j h ⋙ t j k g ≅ t i k (h.trans g)
  sheafUnit : ∀ i, T i i le_rfl ≅ 𝟭 (S i)
  moduleUnit : ∀ i, t i i le_rfl ≅ 𝟭 (M i)

variable {S M T t}
  (G : ∀ i, S i ⥤ M i)
  (θ : ∀ i j h, G i ⋙ t i j h ≅ T i j h ⋙ G j)

/-- The four equations that are transported to derived categories.
Source: Stacks 03EK and 04VG (blueprint: lem-weil-sections-scalar-ordinary-tower). -/
structure Coherent (O : OrdinaryMaps S M T t) : Prop where
  square : ∀ i j k h g (X : S i),
    (t j k g).map ((θ i j h).hom.app X) ≫
      (θ j k g).hom.app ((T i j h).obj X) ≫ (G k).map ((O.sheafComp i j k h g).hom.app X) =
    (O.moduleComp i j k h g).hom.app ((G i).obj X) ≫ (θ i k (h.trans g)).hom.app X
  unit : ∀ i (X : S i),
    (θ i i le_rfl).hom.app X ≫ (G i).map ((O.sheafUnit i).hom.app X) =
      (O.moduleUnit i).hom.app ((G i).obj X)
  sheaf_tower : ∀ i j k n h g q (X : S i),
    (T k n q).map ((O.sheafComp i j k h g).hom.app X) ≫
      (O.sheafComp i k n (h.trans g) q).hom.app X =
    (O.sheafComp j k n g q).hom.app ((T i j h).obj X) ≫
      (O.sheafComp i j n h (g.trans q)).hom.app X
  module_tower : ∀ i j k n h g q (X : M i),
    (t k n q).map ((O.moduleComp i j k h g).hom.app X) ≫
      (O.moduleComp i k n (h.trans g) q).hom.app X =
    (O.moduleComp j k n g q).hom.app ((t i j h).obj X) ≫
      (O.moduleComp i j n h (g.trans q)).hom.app X

section Normalization
variable {C₁ C₂ N₁ N₂ : Type*}
  [Category C₁] [Category C₂] [Category N₁] [Category N₂]
  (F F' : C₁ ⥤ N₁) (H H' : C₂ ⥤ N₂) (U : C₁ ⥤ C₂) (V : N₁ ⥤ N₂)

/-- Equal coefficient identifications transport a comparison without changing its value.
Source: substitution of equal functors
(blueprint: lem-weil-sections-scalar-ordinary-tower). -/
theorem comparison_exists_heq (hF : F' = F) (hH : H' = H) (η : F ⋙ V ≅ U ⋙ H) :
    ∃ η' : F' ⋙ V ≅ U ⋙ H', HEq η' η := by
  subst F'
  subst H'
  exact ⟨η, HEq.rfl⟩
end Normalization

end CategoryTheory.ScalarTower

namespace CategoryTheory.SectionsScalarOrdinaryTower

variable {I : Type z} [Preorder I] {C : Type uC} [Category.{vC} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max a r} RingCat.{max a r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max a r}]
  [HasWeakSheafify J AddCommGrpCat.{max a r}]
  (s : C) (R : I → Sheaf J CommRingCat.{max a r}) (A : I → CommRingCat.{a})
  (f : ∀ i j (_h : i ≤ j), R i ⟶ R j)
  (a : ∀ i j (_h : i ≤ j), A i ⟶ A j)

set_option linter.checkUnivs false in
/-- Module sheaves in the common section universe.
Source: Stacks 03D7 (blueprint: lem-weil-sections-scalar-ordinary-tower). -/
abbrev S (i : I) := SectionsScalarCochain.modules (R i)
/-- Ordinary coefficient modules in the common section universe.
Source: Stacks 03EK (blueprint: lem-weil-sections-scalar-ordinary-tower). -/
abbrev M (i : I) := ModuleCat.{max a r} (A i)
/-- Ordinary extension along an edge of the coefficient tower.
Source: Stacks 03EK (blueprint: lem-weil-sections-scalar-ordinary-tower). -/
abbrev t (i j : I) (h : i ≤ j) := ModuleCat.extendScalars.{a, a, max a r} (a i j h).hom
/-- The pure tensor in the actual extended module.
Source: Stacks 03EK (blueprint: lem-weil-sections-scalar-ordinary-tower). -/
def modulePure (i j : I) (h : i ≤ j) (N : M.{z, a, r} A i) (b : A j) (n : N) :
    (t.{z, a, r} A a i j h).obj N := b ⊗ₜ[A i,(a i j h).hom] n
/-- Sections with the specified coefficient action.
Source: Stacks 03EK (blueprint: lem-weil-sections-scalar-ordinary-tower). -/
abbrev G (lam : ∀ i, A i →+* (R i).obj.obj (op s)) (i : I) :
    S.{z, a, r, uC, vC} R i ⥤ M.{z, a, r} A i :=
  SheafOfModules.evaluation.{max a r}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (R i)) (op s) ⋙
    ModuleCat.restrictScalars (lam i)

section Pure
variable {C' : Type x} [Category.{v} C'] {J' : GrothendieckTopology C'}
  [J'.HasSheafCompose (forget₂ CommRingCat.{y} RingCat.{y})]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{y}]
  [HasWeakSheafify J' AddCommGrpCat.{y}]

/-- Pure scalar tensors transported by the module morphism from the object equality.
Source: Stacks 03EK, 03CY (blueprint: lem-weil-sections-scalar-ordinary-tower). -/
def pure {R S : Sheaf J' CommRingCat.{y}} (f : R ⟶ S)
    (T : SectionsScalarCochain.modules R ⥤ SectionsScalarCochain.modules S)
    (e : ∀ F, T.obj F = SheafOfModules.changeOfRings f F)
    (F : SectionsScalarCochain.modules R) U (b : S.obj.obj U) (x : F.val.obj U) :
    (T.obj F).val.obj U :=
  (eqToHom (e F).symm).val.app U
    ((toSheafify J' (SheafOfModules.changeOfRingsPresheaf f F).presheaf).app U
      (b ⊗ₜ[R.obj.obj U,(f.hom.app U).hom] x))
end Pure

variable (T : ∀ i j, i ≤ j → S.{z, a, r, uC, vC} R i ⥤ S.{z, a, r, uC, vC} R j)
  (e : ∀ i j h F, (T i j h).obj F = SheafOfModules.changeOfRings (f i j h) F)
  (lam : ∀ i, A i →+* (R i).obj.obj (op s))
  (θ : ∀ i j h, G.{z, a, r, uC, vC} s R A lam i ⋙
    t.{z, a, r} A a i j h ≅ T i j h ⋙ G.{z, a, r, uC, vC} s R A lam j)

/-- Tensor normalizations, including inverses and identity coefficients.
Source: Stacks 03EK and 03CZ (blueprint: lem-weil-sections-scalar-ordinary-tower). -/
structure Formula
    (O : ScalarTower.OrdinaryMaps (S.{z, a, r, uC, vC} R) (M.{z, a, r} A) T
      (t.{z, a, r} A a)) : Prop where
  sheaf_formula : ∀ i j k h g (F : S.{z, a, r, uC, vC} R i) U b c x,
    ((O.sheafComp i j k h g).hom.app F).val.app U
      (pure (f j k g) (T j k g) (e j k g) ((T i j h).obj F) U c
        (pure (f i j h) (T i j h) (e i j h) F U b x)) =
    pure (f i k (h.trans g)) (T i k (h.trans g))
      (e i k (h.trans g)) F U ((f j k g).hom.app U b * c) x
  sheaf_inverse : ∀ i j k h g (F : S.{z, a, r, uC, vC} R i) U c x,
    ((O.sheafComp i j k h g).inv.app F).val.app U
      (pure (f i k (h.trans g)) (T i k (h.trans g))
        (e i k (h.trans g)) F U c x) =
    pure (f j k g) (T j k g) (e j k g) ((T i j h).obj F) U c
      (pure (f i j h) (T i j h) (e i j h) F U 1 x)
  module_formula : ∀ i j k h g (N : M.{z, a, r} A i) (b : A j) (c : A k) (n : N),
    (O.moduleComp i j k h g).hom.app N
      (modulePure.{z, a, r} A a j k g ((t.{z, a, r} A a i j h).obj N) c
        (modulePure.{z, a, r} A a i j h N b n)) =
    modulePure.{z, a, r} A a i k (h.trans g) N ((a j k g) b * c) n
  module_inverse : ∀ i j k h g (N : M.{z, a, r} A i) (c : A k) (n : N),
    (O.moduleComp i j k h g).inv.app N (modulePure.{z, a, r} A a i k (h.trans g) N c n) =
    modulePure.{z, a, r} A a j k g ((t.{z, a, r} A a i j h).obj N) c
      (modulePure.{z, a, r} A a i j h N 1 n)
  sheaf_unit_formula : ∀ i (F : S.{z, a, r, uC, vC} R i) U b x,
    ((O.sheafUnit i).hom.app F).val.app U
      (pure (f i i le_rfl) (T i i le_rfl) (e i i le_rfl) F U b x) =
      @SMul.smul _ _ (F.val.obj U).isModule.toSMul b x
  module_unit_formula : ∀ i (N : M.{z, a, r} A i) (b : A i) (n : N),
    (O.moduleUnit i).hom.app N (modulePure.{z, a, r} A a i i le_rfl N b n) = b • n

private theorem section_transport
    {C' : Type x} [Category.{v} C'] {J' : GrothendieckTopology C'}
    {Q : Sheaf J' RingCat.{y}}
    (F N : SheafOfModules.{y} Q) (h : F = N) (U : C'ᵒᵖ) (x : N.val.obj U) :
    Eq.ndrec (motive := fun P : SheafOfModules.{y} Q ↦
      (P.val.obj U : Type y)) x h.symm = (eqToHom h.symm).val.app U x := by
  cases h
  rfl

/-- The pure tensor uses exactly the object-identification transport.
Source: Stacks 03EK (blueprint: lem-weil-sections-scalar-ordinary-tower). -/
theorem pure_transport (i j : I) (h : i ≤ j) (F : S.{z, a, r, uC, vC} R i) U b x :
    pure (f i j h) (T i j h) (e i j h) F U b x =
      (eqToHom (e i j h F).symm).val.app U
        ((toSheafify J (SheafOfModules.changeOfRingsPresheaf (f i j h) F).presheaf).app U
          (b ⊗ₜ[(R i).obj.obj U,((f i j h).hom.app U).hom] x)) := by rfl

private def extensionComparison (i j : I) (h : i ≤ j)
    (hm : ∀ {F N} (v : F ⟶ N), (T i j h).map v = eqToHom (e i j h F) ≫
      SheafOfModules.changeOfRingsHom (f i j h) F v ≫ eqToHom (e i j h N).symm) :
    T i j h ≅ SheafOfModules.CoefficientOrdinaryProof.tensorFunctor (f i j h) :=
  NatIso.ofComponents (fun F ↦ eqToIso (e i j h F)) (by
    intro F N v
    change (T i j h).map v ≫ eqToHom (e i j h N) =
      eqToHom (e i j h F) ≫ SheafOfModules.changeOfRingsHom (f i j h) F v
    rw [hm]
    simp)

private theorem extensionAdjunction (i j : I) (h : i ≤ j)
    (hm : ∀ {F N} (v : F ⟶ N), (T i j h).map v = eqToHom (e i j h F) ≫
      SheafOfModules.changeOfRingsHom (f i j h) F v ≫ eqToHom (e i j h N).symm) :
    ∃ adj : T i j h ⊣ SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map (f i j h)),
      ∀ F U (x : F.val.obj U), (adj.unit.app F).val.app U x =
        pure (f i j h) (T i j h) (e i j h) F U 1 x := by
  let q := extensionComparison R f T e i j h hm
  let adj := (SheafOfModules.CoefficientOrdinaryProof.tensorAdjunction
    (f i j h)).ofNatIsoLeft q.symm
  refine ⟨adj, ?_⟩
  intro F U x
  rw [pure_transport.{z, a, r, uC, vC}]
  rfl

private theorem pure_smul (i j : I) (h : i ≤ j)
    (F : S.{z, a, r, uC, vC} R i) U b x :
    pure (f i j h) (T i j h) (e i j h) F U b x =
      b • pure (f i j h) (T i j h) (e i j h) F U 1 x := by
  rw [pure_transport.{z, a, r, uC, vC}, pure_transport.{z, a, r, uC, vC}]
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (R j)).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf (f i j h) F)
  let q := (eqToHom (e i j h F).symm).val.app U
  change q (η.app U (b ⊗ₜ[(R i).obj.obj U, ((f i j h).hom.app U).hom] x)) =
    b • q (η.app U ((1 : (R j).obj.obj U) ⊗ₜ[(R i).obj.obj U,
      ((f i j h).hom.app U).hom] x))
  rw [← q.hom.map_smul, ← (η.app U).hom.map_smul]
  congr 2
  symm
  exact (ModuleCat.ExtendScalars.smul_tmul (f := ((f i j h).hom.app U).hom) b 1 x).trans
    (by rw [mul_one])

private theorem transpose_tmul (i j : I) (h : i ≤ j)
    (adj : T i j h ⊣ SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map (f i j h)))
    (hn : ∀ F U (x : F.val.obj U), (adj.unit.app F).val.app U x =
      pure (f i j h) (T i j h) (e i j h) F U 1 x)
    (F : S.{z, a, r, uC, vC} R i) (N : S.{z, a, r, uC, vC} R j)
    (v : (T i j h).obj F ⟶ N) U b x :
    v.val.app U (pure (f i j h) (T i j h) (e i j h) F U b x) =
      b • (show N.val.obj U from (adj.homEquiv F N v).val.app U x) := by
  rw [pure_smul.{z, a, r, uC, vC}, ← hn, Adjunction.homEquiv_unit]
  exact (v.val.app U).hom.map_smul b _

private theorem sheaf_associator
    (hm : ∀ i j h {F N} (v : F ⟶ N), (T i j h).map v = eqToHom (e i j h F) ≫
      SheafOfModules.changeOfRingsHom (f i j h) F v ≫ eqToHom (e i j h N).symm)
    (i j k : I) (h : i ≤ j) (g : j ≤ k) (hc : f i j h ≫ f j k g = f i k (h.trans g)) :
    ∃ α : T i j h ⋙ T j k g ≅ T i k (h.trans g),
      ∀ F U b c x, (α.hom.app F).val.app U
        (pure (f j k g) (T j k g) (e j k g) ((T i j h).obj F) U c
          (pure (f i j h) (T i j h) (e i j h) F U b x)) =
        pure (f i k (h.trans g)) (T i k (h.trans g))
          (e i k (h.trans g)) F U ((f j k g).hom.app U b * c) x := by
  obtain ⟨aa, ha⟩ := extensionAdjunction.{z, a, r, uC, vC} R f T e i j h (hm i j h)
  obtain ⟨ab, hb⟩ := extensionAdjunction.{z, a, r, uC, vC} R f T e j k g (hm j k g)
  obtain ⟨ac, hd⟩ := extensionAdjunction.{z, a, r, uC, vC} R f T e i k (h.trans g)
    (hm i k (h.trans g))
  let res : SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map (f j k g)) ⋙
      SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map (f i j h)) ≅
      SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map (f i k (h.trans g))) :=
    NatIso.ofComponents (fun N ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        (ModuleCat.restrictScalarsComp'App ((f i j h).hom.app U).hom
          ((f j k g).hom.app U).hom ((f i k (h.trans g)).hom.app U).hom
          (by rw [← hc]; rfl) (N.val.obj U)).symm)
        (by intros; ext x; rfl))) (by intros; ext U x; rfl)
  let α := Adjunction.leftAdjointUniq ((aa.comp ab).ofNatIsoRight res) ac
  refine ⟨α, ?_⟩
  intro F U b c x
  let v := α.hom.app F
  have hh := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((aa.comp ab).ofNatIsoRight res) ac F
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at hh
  have hx := congrArg (fun q ↦ q.val.app U x) hh
  change (aa.homEquiv F _ (ab.homEquiv _ _ v)).val.app U x =
    (ac.unit.app F).val.app U x at hx
  change v.val.app U _ = _
  erw [transpose_tmul.{z, a, r, uC, vC} R f T e j k g ab hb
    ((T i j h).obj F) ((T i k (h.trans g)).obj F)
    v U c (pure (f i j h) (T i j h) (e i j h) F U b x)]
  erw [transpose_tmul.{z, a, r, uC, vC} R f T e i j h aa ha F _ (ab.homEquiv _ _ v) U b x, hx, hd]
  rw [pure_smul.{z, a, r, uC, vC} R f T e i k (h.trans g) F U ((f j k g).hom.app U b * c) x,
    mul_comm ((f j k g).hom.app U b) c]
  exact (mul_smul c ((f j k g).hom.app U b)
    (pure (f i k (h.trans g)) (T i k (h.trans g))
      (e i k (h.trans g)) F U 1 x)).symm

private theorem extension_hom_ext (i j : I) (h : i ≤ j)
    (adj : T i j h ⊣ SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map (f i j h)))
    (hn : ∀ F U (x : F.val.obj U), (adj.unit.app F).val.app U x =
      pure (f i j h) (T i j h) (e i j h) F U 1 x)
    (F : S.{z, a, r, uC, vC} R i) (N : S.{z, a, r, uC, vC} R j)
    (v w : (T i j h).obj F ⟶ N)
    (hv : ∀ U x, v.val.app U
      (pure (f i j h) (T i j h) (e i j h) F U 1 x) =
      w.val.app U (pure (f i j h) (T i j h) (e i j h) F U 1 x)) :
    v = w := by
  apply (adj.homEquiv F N).injective
  ext U x
  change ((adj.unit.app F) ≫
      (SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map (f i j h))).map v).val.app U x =
    ((adj.unit.app F) ≫
      (SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map (f i j h))).map w).val.app U x
  change v.val.app U ((adj.unit.app F).val.app U x) =
    w.val.app U ((adj.unit.app F).val.app U x)
  rw [hn]
  exact hv U x

private theorem associator_inverse (i j k : I) (h : i ≤ j) (g : j ≤ k)
    (α : T i j h ⋙ T j k g ≅ T i k (h.trans g))
    (hn : ∀ F U b c x, (α.hom.app F).val.app U
        (pure (f j k g) (T j k g) (e j k g) ((T i j h).obj F) U c
          (pure (f i j h) (T i j h) (e i j h) F U b x)) =
        pure (f i k (h.trans g)) (T i k (h.trans g))
          (e i k (h.trans g)) F U ((f j k g).hom.app U b * c) x)
    (F : S.{z, a, r, uC, vC} R i) U c x :
    (α.inv.app F).val.app U
      (pure (f i k (h.trans g)) (T i k (h.trans g))
        (e i k (h.trans g)) F U c x) =
    pure (f j k g) (T j k g) (e j k g) ((T i j h).obj F) U c
      (pure (f i j h) (T i j h) (e i j h) F U 1 x) := by
  have hx := hn F U 1 c x
  simp only [map_one, one_mul] at hx
  rw [← hx]
  have hh := congrArg (fun q ↦ q.val.app U
    (pure (f j k g) (T j k g) (e j k g) ((T i j h).obj F) U c
      (pure (f i j h) (T i j h) (e i j h) F U 1 x)))
    (α.hom_inv_id_app F)
  exact hh

private theorem sheaf_unitor
    (hm : ∀ i j h {F N} (v : F ⟶ N), (T i j h).map v = eqToHom (e i j h F) ≫
      SheafOfModules.changeOfRingsHom (f i j h) F v ≫ eqToHom (e i j h N).symm)
    (i : I) (hi : f i i le_rfl = 𝟙 (R i)) :
    ∃ ε : T i i le_rfl ≅ 𝟭 (S.{z, a, r, uC, vC} R i),
      ∀ F U b x, (ε.hom.app F).val.app U
        (pure (f i i le_rfl) (T i i le_rfl)
          (e i i le_rfl) F U b x) =
      @SMul.smul _ _ (F.val.obj U).isModule.toSMul b x := by
  obtain ⟨adj, hn⟩ := extensionAdjunction.{z, a, r, uC, vC} R f T e i i le_rfl
    (hm i i le_rfl)
  let res : SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map (f i i le_rfl)) ≅
      𝟭 (S.{z, a, r, uC, vC} R i) :=
    NatIso.ofComponents (fun N ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        ModuleCat.restrictScalarsId'App ((f i i le_rfl).hom.app U).hom
          (by rw [hi]; rfl) (N.val.obj U)) (by intros; ext x; rfl)))
      (by intros; ext U x; rfl)
  let ε := Adjunction.leftAdjointUniq (adj.ofNatIsoRight res)
    (Adjunction.id : 𝟭 (S.{z, a, r, uC, vC} R i) ⊣ 𝟭 _)
  refine ⟨ε, ?_⟩
  intro F U b x
  have hh := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (adj.ofNatIsoRight res) (Adjunction.id : 𝟭 (S.{z, a, r, uC, vC} R i) ⊣ 𝟭 _) F
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at hh
  have hx := congrArg (fun q ↦ q.val.app U x) hh
  change (adj.homEquiv F F (ε.hom.app F)).val.app U x = x at hx
  exact (transpose_tmul.{z, a, r, uC, vC} R f T e i i le_rfl adj hn F F
    (ε.hom.app F) U b x).trans (congrArg (fun y ↦ b • y) hx)

private theorem map_pure (i j : I) (h : i ≤ j)
    (adj : T i j h ⊣ SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map (f i j h)))
    (hn : ∀ F U (x : F.val.obj U), (adj.unit.app F).val.app U x =
      pure (f i j h) (T i j h) (e i j h) F U 1 x)
    {F N : S.{z, a, r, uC, vC} R i} (v : F ⟶ N) U b x :
    ((T i j h).map v).val.app U
      (pure (f i j h) (T i j h) (e i j h) F U b x) =
      pure (f i j h) (T i j h) (e i j h) N U b (v.val.app U x) := by
  have hx := congrArg (fun q ↦ q.val.app U x) (adj.unit.naturality v)
  change (adj.unit.app N).val.app U (v.val.app U x) =
    ((T i j h).map v).val.app U ((adj.unit.app F).val.app U x) at hx
  rw [hn, hn] at hx
  rw [pure_smul.{z, a, r, uC, vC} R f T e i j h F U b x,
    (((T i j h).map v).val.app U).hom.map_smul, hx.symm,
    ← pure_smul.{z, a, r, uC, vC} R f T e i j h N U b (v.val.app U x)]

private theorem double_extension_hom_ext (i j k : I) (h : i ≤ j) (g : j ≤ k)
    (aa : T i j h ⊣ SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map (f i j h)))
    (ha : ∀ F U (x : F.val.obj U), (aa.unit.app F).val.app U x =
      pure (f i j h) (T i j h) (e i j h) F U 1 x)
    (ab : T j k g ⊣ SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map (f j k g)))
    (hb : ∀ F U (x : F.val.obj U), (ab.unit.app F).val.app U x =
      pure (f j k g) (T j k g) (e j k g) F U 1 x)
    (F : S.{z, a, r, uC, vC} R i) (N : S.{z, a, r, uC, vC} R k)
    (v w : (T j k g).obj ((T i j h).obj F) ⟶ N)
    (hv : ∀ U x, v.val.app U
      (pure (f j k g) (T j k g) (e j k g) ((T i j h).obj F) U 1
        (pure (f i j h) (T i j h) (e i j h) F U 1 x)) =
      w.val.app U
      (pure (f j k g) (T j k g) (e j k g) ((T i j h).obj F) U 1
        (pure (f i j h) (T i j h) (e i j h) F U 1 x))) : v = w := by
  apply (ab.homEquiv _ _).injective
  apply extension_hom_ext.{z, a, r, uC, vC} R f T e i j h aa ha
  intro U x
  change v.val.app U ((ab.unit.app _).val.app U _) =
    w.val.app U ((ab.unit.app _).val.app U _)
  rw [hb]
  exact hv U x

private theorem module_map_pure (i j : I) (h : i ≤ j)
    {N N' : M.{z, a, r} A i} (v : N ⟶ N') (b : A j) (n : N) :
    (t.{z, a, r} A a i j h).map v (modulePure A a i j h N b n) =
      modulePure A a i j h N' b (v n) := rfl

private theorem modulePure_smul (i j : I) (h : i ≤ j)
    (N : M.{z, a, r} A i) (b : A j) (n : N) :
    modulePure A a i j h N b n = b • modulePure A a i j h N 1 n := by
  change b ⊗ₜ[A i, (a i j h).hom] n =
    b • ((1 : A j) ⊗ₜ[A i, (a i j h).hom] n : (ModuleCat.extendScalars (a i j h).hom).obj N)
  exact ((ModuleCat.ExtendScalars.smul_tmul (f := (a i j h).hom)
    (M := N) b 1 n).trans (by rw [mul_one])).symm

private theorem module_associator (i j k : I) (h : i ≤ j) (g : j ≤ k)
    (hc : a i j h ≫ a j k g = a i k (h.trans g)) :
    ∃ α : t.{z, a, r} A a i j h ⋙ t.{z, a, r} A a j k g ≅
        t.{z, a, r} A a i k (h.trans g),
      ∀ (N : M.{z, a, r} A i) b c n, α.hom.app N
        (modulePure A a j k g ((t A a i j h).obj N) c (modulePure A a i j h N b n)) =
        modulePure A a i k (h.trans g) N ((a j k g) b * c) n := by
  let aa := ModuleCat.extendRestrictScalarsAdj (a i j h).hom
  let ab := ModuleCat.extendRestrictScalarsAdj (a j k g).hom
  let ac := ModuleCat.extendRestrictScalarsAdj (a i k (h.trans g)).hom
  let res : ModuleCat.restrictScalars (a j k g).hom ⋙
      ModuleCat.restrictScalars (a i j h).hom ≅
      ModuleCat.restrictScalars (a i k (h.trans g)).hom :=
    (ModuleCat.restrictScalarsComp' (a i j h).hom (a j k g).hom
      (a i k (h.trans g)).hom (by rw [← hc]; rfl)).symm
  let α := Adjunction.leftAdjointUniq ((aa.comp ab).ofNatIsoRight res) ac
  refine ⟨α, ?_⟩
  intro N b c n
  have hh := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((aa.comp ab).ofNatIsoRight res) ac N
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at hh
  have hx := congrArg (fun q ↦ q n) hh
  change α.hom.app N (modulePure A a j k g _ 1 (modulePure A a i j h N 1 n)) =
    modulePure A a i k (h.trans g) N 1 n at hx
  let v := ab.homEquiv _ _ (α.hom.app N)
  have hv (y : (t.{z, a, r} A a i j h).obj N) :
      α.hom.app N (modulePure A a j k g _ c y) = c • v y := by
    rw [modulePure_smul A a, map_smul]
    rfl
  rw [hv]
  have hb : modulePure A a i j h N b n = b • modulePure A a i j h N 1 n := by
    exact modulePure_smul A a i j h N b n
  rw [hb, map_smul]
  change c • ((a j k g).hom b •
    α.hom.app N (modulePure A a j k g _ 1 (modulePure A a i j h N 1 n))) = _
  rw [hx, smul_smul, modulePure_smul A a i k (h.trans g) N ((a j k g) b * c) n]
  rw [mul_comm c]

private theorem module_unitor (i : I) (hi : a i i le_rfl = 𝟙 (A i)) :
    ∃ ε : t.{z, a, r} A a i i le_rfl ≅ 𝟭 (M.{z, a, r} A i),
      ∀ (N : M.{z, a, r} A i) b n,
        ε.hom.app N (modulePure A a i i le_rfl N b n) = b • n := by
  let adj := ModuleCat.extendRestrictScalarsAdj (a i i le_rfl).hom
  let res := ModuleCat.restrictScalarsId' (a i i le_rfl).hom (by rw [hi]; rfl)
  let ε := Adjunction.leftAdjointUniq (adj.ofNatIsoRight res)
    (Adjunction.id : 𝟭 (M.{z, a, r} A i) ⊣ 𝟭 _)
  refine ⟨ε, ?_⟩
  intro N b n
  have hh := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (adj.ofNatIsoRight res) (Adjunction.id : 𝟭 (M.{z, a, r} A i) ⊣ 𝟭 _) N
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at hh
  have hx := congrArg (fun q ↦ q n) hh
  change ε.hom.app N (modulePure A a i i le_rfl N 1 n) = n at hx
  rw [modulePure_smul A a i i le_rfl N b n, map_smul, hx]

attribute [local irreducible] pure

/-- Ordinary scalar coherence for a tower of sheaves and its normalized sections map.
Source: Stacks 03EK, 03CZ, 03CY; the ordinary parts of
lem-weil-sections-scalar-cochain-coherence, proof steps 1--4 and 6--8.
(blueprint: lem-weil-sections-scalar-ordinary-tower).

Proof: restriction of scalars composes by the given coefficient equations. Its left
adjoints therefore have unique normalized associators; the adjunction unit inserts
1 tensor x. Transposing twice gives c tensor (b tensor x) mapped to f(b)c tensor x.
Transposing the inverse gives insertion of 1. The identity adjunction gives the
multiplication unit. The identical module adjunction gives the module maps. To prove
the sections square, evaluate on c tensor (b tensor n); compatibility of lam and the
normalized theta formula give lam(f(b)c) tensor n on both sides. Module tensors are
generated by pure tensors. For sheaf equalities use the extension/restriction
adjunction repeatedly, so no global tensor-generation claim is needed. The unit
square follows by the same calculation with the identity coefficient. Both routes
in a four-stage tower multiply the three coefficients in the same order, and
associativity proves equality. These generator and adjunction arguments also prove
uniqueness of every natural associator and unit. The argument is local to each
finite tower, so it applies to any indexing preorder and includes repeated indices. -/
theorem coherence
    (_hs : IsTerminal s)
    (_fid : ∀ i, f i i le_rfl = 𝟙 (R i))
    (_fcomp : ∀ i j k h g, f i j h ≫ f j k g = f i k (h.trans g))
    (_aid : ∀ i, a i i le_rfl = 𝟙 (A i))
    (_acomp : ∀ i j k h g, a i j h ≫ a j k g = a i k (h.trans g))
    (_hm : ∀ i j h {F N} (v : F ⟶ N), (T i j h).map v = eqToHom (e i j h F) ≫
      SheafOfModules.changeOfRingsHom (f i j h) F v ≫ eqToHom (e i j h N).symm)
    (_compat : ∀ i j h,
      ((f i j h).hom.app (op s)).hom.comp (lam i) = (lam j).comp (a i j h).hom)
    (_normalized : ∀ i j h (F : S.{z, a, r, uC, vC} R i) (b : A j)
      (n : (G.{z, a, r, uC, vC} s R A lam i).obj F),
      (θ i j h).hom.app F
        (modulePure.{z, a, r} A a i j h ((G.{z, a, r, uC, vC} s R A lam i).obj F) b n) =
        pure (f i j h) (T i j h) (e i j h) F (op s) (lam j b) n) :
    ∃! O : ScalarTower.OrdinaryMaps (S.{z, a, r, uC, vC} R) (M.{z, a, r} A) T (t.{z, a, r} A a),
      Formula.{z, a, r, uC, vC} R A f a T e O ∧
        ScalarTower.Coherent (G.{z, a, r, uC, vC} s R A lam) θ O := by
  classical
  choose sc hsc using fun i j k h g ↦ sheaf_associator.{z, a, r, uC, vC} R f T e _hm i j k h g
    (_fcomp i j k h g)
  choose su hsu using fun i ↦ sheaf_unitor.{z, a, r, uC, vC} R f T e _hm i (_fid i)
  choose mc hmc using fun i j k h g ↦ module_associator.{z, a, r} A a i j k h g
    (_acomp i j k h g)
  choose mu hmu using fun i ↦ module_unitor.{z, a, r} A a i (_aid i)
  choose adj hadj using fun i j h ↦ extensionAdjunction.{z, a, r, uC, vC} R f T e i j h (_hm i j h)
  let O : ScalarTower.OrdinaryMaps (S.{z, a, r, uC, vC} R) (M.{z, a, r} A) T
      (t.{z, a, r} A a) := ⟨sc, mc, su, mu⟩
  have hF : Formula.{z, a, r, uC, vC} R A f a T e O := by
    refine ⟨hsc, ?_, hmc, ?_, hsu, hmu⟩
    · exact fun i j k h g ↦ associator_inverse.{z, a, r, uC, vC} R f T e i j k h g (sc i j k h g)
        (hsc i j k h g)
    · intro i j k h g N c n
      have hx := hmc i j k h g N 1 c n
      simp only [map_one, one_mul] at hx
      rw [← hx]
      exact congrArg (fun q ↦ q
        (modulePure.{z, a, r} A a j k g ((t.{z, a, r} A a i j h).obj N) c
          (modulePure.{z, a, r} A a i j h N 1 n))) ((mc i j k h g).hom_inv_id_app N)
  have hC : ScalarTower.Coherent (G.{z, a, r, uC, vC} s R A lam) θ O := by
    constructor
    · intro i j k h g F
      apply ((ModuleCat.extendRestrictScalarsAdj (a j k g).hom).homEquiv _ _).injective
      apply ModuleCat.ExtendScalars.hom_ext
      intro n
      change ((sc i j k h g).hom.app F).val.app (op s)
        ((θ j k g).hom.app ((T i j h).obj F)
          ((t.{z, a, r} A a j k g).map ((θ i j h).hom.app F)
            (modulePure.{z, a, r} A a j k g _ 1 (modulePure.{z, a, r} A a i j h _ 1 n)))) =
        (θ i k (h.trans g)).hom.app F
          ((mc i j k h g).hom.app ((G.{z, a, r, uC, vC} s R A lam i).obj F)
            (modulePure.{z, a, r} A a j k g _ 1 (modulePure.{z, a, r} A a i j h _ 1 n)))
      rw [module_map_pure A a]
      rw [_normalized]
      have hn := _normalized j k g ((T i j h).obj F) 1
        ((θ i j h).hom.app F (modulePure A a i j h _ 1 n))
      have hi := _normalized i j h F 1 n
      rw [hi] at hn
      erw [hn, hsc, hmc, _normalized]
      simp only [map_one, one_mul]
    · intro i F
      apply ModuleCat.ExtendScalars.hom_ext
      intro n
      change ((su i).hom.app F).val.app (op s)
        ((θ i i le_rfl).hom.app F (modulePure.{z, a, r} A a i i le_rfl _ 1 n)) =
        (mu i).hom.app ((G.{z, a, r, uC, vC} s R A lam i).obj F)
          (modulePure.{z, a, r} A a i i le_rfl _ 1 n)
      rw [_normalized, hsu, hmu, map_one, one_smul]
      exact @one_smul ((R i).obj.obj (op s)) (F.val.obj (op s)) _
        (F.val.obj (op s)).isModule.toMulAction n
    · intro i j k n h g q F
      apply ((adj k n q).homEquiv _ _).injective
      apply double_extension_hom_ext.{z, a, r, uC, vC} R f T e i j k h g (adj i j h) (hadj i j h)
        (adj j k g) (hadj j k g)
      intro U x
      change (((T k n q).map ((sc i j k h g).hom.app F) ≫
        (sc i k n (h.trans g) q).hom.app F).val.app U)
          ((adj k n q).unit.app _ |>.val.app U
            (pure (f j k g) (T j k g) (e j k g)
              ((T i j h).obj F) U 1
              (pure (f i j h) (T i j h) (e i j h) F U 1 x))) =
        (((sc j k n g q).hom.app ((T i j h).obj F) ≫
          (sc i j n h (g.trans q)).hom.app F).val.app U)
          ((adj k n q).unit.app _ |>.val.app U
            (pure (f j k g) (T j k g) (e j k g)
              ((T i j h).obj F) U 1
              (pure (f i j h) (T i j h) (e i j h) F U 1 x)))
      simp only [hadj]
      change ((sc i k n (h.trans g) q).hom.app F).val.app U
        (((T k n q).map ((sc i j k h g).hom.app F)).val.app U _) =
        ((sc i j n h (g.trans q)).hom.app F).val.app U
          (((sc j k n g q).hom.app ((T i j h).obj F)).val.app U _)
      erw [map_pure.{z, a, r, uC, vC} R f T e k n q (adj k n q) (hadj k n q),
        hsc, hsc, hsc, hsc]
      simp only [map_one, one_mul]
    · intro i j k n h g q N
      apply ((ModuleCat.extendRestrictScalarsAdj (a k n q).hom).homEquiv _ _).injective
      apply ((ModuleCat.extendRestrictScalarsAdj (a j k g).hom).homEquiv _ _).injective
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      change (mc i k n (h.trans g) q).hom.app N
        ((t.{z, a, r} A a k n q).map ((mc i j k h g).hom.app N)
          (modulePure.{z, a, r} A a k n q _ 1
            (modulePure.{z, a, r} A a j k g _ 1 (modulePure.{z, a, r} A a i j h N 1 x)))) =
        (mc i j n h (g.trans q)).hom.app N
          ((mc j k n g q).hom.app ((t.{z, a, r} A a i j h).obj N)
            (modulePure.{z, a, r} A a k n q _ 1
              (modulePure.{z, a, r} A a j k g _ 1 (modulePure.{z, a, r} A a i j h N 1 x))))
      rw [module_map_pure A a, hmc, hmc, hmc, hmc]
      simp only [map_one, one_mul]
  refine ⟨O, ⟨hF, hC⟩, ?_⟩
  intro Z hZ
  have hzs : Z.sheafComp = sc := by
    funext i j k h g
    apply Iso.ext
    apply NatTrans.ext
    funext F
    apply double_extension_hom_ext.{z, a, r, uC, vC} R f T e i j k h g (adj i j h) (hadj i j h)
      (adj j k g) (hadj j k g)
    intro U x
    exact (hZ.1.sheaf_formula i j k h g F U 1 1 x).trans
      (hsc i j k h g F U 1 1 x).symm
  have hzm : Z.moduleComp = mc := by
    funext i j k h g
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply ((ModuleCat.extendRestrictScalarsAdj (a j k g).hom).homEquiv _ _).injective
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change (Z.moduleComp i j k h g).hom.app N
      (modulePure.{z, a, r} A a j k g _ 1 (modulePure.{z, a, r} A a i j h N 1 x)) =
      (mc i j k h g).hom.app N
        (modulePure.{z, a, r} A a j k g _ 1 (modulePure.{z, a, r} A a i j h N 1 x))
    rw [hZ.1.module_formula, hmc]
  have hzu : Z.sheafUnit = su := by
    funext i
    apply Iso.ext
    apply NatTrans.ext
    funext F
    apply extension_hom_ext.{z, a, r, uC, vC} R f T e i i le_rfl (adj i i le_rfl) (hadj i i le_rfl)
    intro U x
    rw [hZ.1.sheaf_unit_formula, hsu]
  have hzv : Z.moduleUnit = mu := by
    funext i
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change (Z.moduleUnit i).hom.app N (modulePure.{z, a, r} A a i i le_rfl N 1 x) =
      (mu i).hom.app N (modulePure.{z, a, r} A a i i le_rfl N 1 x)
    rw [hZ.1.module_unit_formula, hmu]
  cases Z
  change ScalarTower.OrdinaryMaps.mk _ _ _ _ = ScalarTower.OrdinaryMaps.mk _ _ _ _
  congr

end CategoryTheory.SectionsScalarOrdinaryTower
