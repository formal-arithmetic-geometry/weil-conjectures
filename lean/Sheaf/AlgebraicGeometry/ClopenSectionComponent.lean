/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleOpenTensor
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# The clopen component description for a section of an open immersion

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-sf-operations,
lem-weil-pbc-clopen-section-direct-image.proof.md, disjoint-open-cover description
and displayed section formula; Stacks Project, `proetale.tex`, Tags 098K and 09AE
(blueprint: lem-sp-clopen-section-component).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme

/-- The open complement of a closed-range open immersion, with the closed immersion
instance obtained canonically from its open-immersion and closed-range hypotheses.
Source: Stacks Project, Definition 098K and Weil blueprint
(blueprint: lem-sp-clopen-section-component). -/
noncomputable def clopenComplement {X V : Scheme.{u}} (s : X ⟶ V)
    [IsOpenImmersion s] (hclosed : IsClosed (Set.range s.base)) : V.Opens :=
  @openComplementOfIsClosedImmersion V X s
    (IsClosedImmersion.of_isPreimmersion s hclosed)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The inclusion of the section component of `W ×[X] V`. Its projections are
`𝟙 W` and `W.hom ≫ s`, so it identifies that component with `W` over `X`.
Source: blueprint main-20261015, clopen-section-direct-image proof, displayed section formula
(blueprint: lem-sp-clopen-section-component). -/
noncomputable def clopenSectionComponentArrow {X V : Scheme.{u}} (q : V ⟶ X)
    (s : X ⟶ V) [IsOpenImmersion s] (hsection : s ≫ q = 𝟙 X) (W : X.ProEt) :
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale s)).obj W ⟶
      (proEtaleBaseChange q).obj W :=
  MorphismProperty.Over.homMk
    (pullback.lift (𝟙 W.left) (W.hom ≫ s)
      (by
        change (𝟙 W.left) ≫ W.hom = (W.hom ≫ s) ≫ q
        exact (Category.id_comp W.hom).trans
          ((Category.comp_id W.hom).symm.trans
            ((congrArg (fun f : X ⟶ X ↦ W.hom ≫ f) hsection).symm.trans
              (Category.assoc W.hom s q).symm))))
    (by simp) trivial

/-- Sectionwise normalization of the comparison `q_* s_! → 𝟭`. On scalar-unit
sections, after the canonical realization counit, its composite with the open unit
is precisely restriction along `W → W ×[X] V`. The open unit identifies
`s^* s_! M` with `M`. Scalar-unit sections locally generate the intrinsic module
sheaf, so this equation fixes the comparison on all sections, with no arbitrary
coefficient identification.
Source: blueprint main-20261015, clopen-section-direct-image proof, displayed section formula
(blueprint: lem-sp-clopen-section-component). -/
def ClopenSectionComparisonOnSections {X V : Scheme.{u}} (q : V ⟶ X)
    (s : X ⟶ V) [IsOpenImmersion s] (hsection : s ≫ q = 𝟙 X)
    (A : Type u) [CommRing A] [Finite A]
    (e : sfIntrinsicExtensionByZero s A ⋙ proEtaleConstantModuleDirectImage q A ⟶
      𝟭 (proEtaleRingModules X (proEtaleConstantRing X A))) : Prop :=
  ∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)) (W : X.ProEtᵒᵖ)
    (m : (((sfIntrinsicModuleEquivalence V A).inverse.obj
      ((sfIntrinsicExtensionByZero s A).obj M)).obj.obj
        ((proEtaleBaseChange q).op.obj W))),
    ((sfIntrinsicExtensionByZeroAdjunction s A).unit.app M).val.app W
      ((e.app M).val.app W
        (((proEtaleConstantModuleDirectImage q A).map
          ((sfIntrinsicModuleEquivalence V A).counitIso.hom.app
            ((sfIntrinsicExtensionByZero s A).obj M))).val.app W
          (sfIntrinsicRealizationUnit V A
            ((sfIntrinsicModuleEquivalence V A).inverse.obj
              ((sfIntrinsicExtensionByZero s A).obj M))
            ((proEtaleBaseChange q).op.obj W) m))) =
      sfIntrinsicRealizationUnit X A
        ((ProEtale.openImmersionRestriction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) s).obj
            ((sfIntrinsicModuleEquivalence V A).inverse.obj
              ((sfIntrinsicExtensionByZero s A).obj M))) W
        ((((sfIntrinsicModuleEquivalence V A).inverse.obj
          ((sfIntrinsicExtensionByZero s A).obj M)).obj.map
            (clopenSectionComponentArrow q s hsection W.unop).op) m)

attribute [local instance] preservesBinaryBiproduct_of_preservesBiproduct
section Generic

universe v

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [HasBinaryBiproducts C]

private theorem pair_equivalence (F : C ⥤ D) (G : C ⥤ E)
    (L : D ⥤ C) (R : E ⥤ C) (a : L ⊣ F) (b : R ⊣ G)
    [F.Additive] [G.Additive] [L.Full] [L.Faithful] [R.Full] [R.Faithful]
    (hFL : ∀ M, IsZero (G.obj (L.obj M)))
    (hGR : ∀ N, IsZero (F.obj (R.obj N)))
    (hconservative : ∀ {M N : C} (f : M ⟶ N),
      IsIso (F.map f) → IsIso (G.map f) → IsIso f) :
    (F.prod' G).IsEquivalence := by
  let P := F.prod' G
  let Q : D × E ⥤ C :=
    { obj := fun MN ↦ L.obj MN.1 ⊞ R.obj MN.2
      map := fun f ↦ biprod.map (L.map f.1) (R.map f.2)
      map_id := by intro MN; ext <;> simp
      map_comp := by intro MN MN' MN'' f g; ext <;> simp }
  let c : P ⋙ Q ⟶ 𝟭 C :=
    { app := fun M ↦ biprod.desc (a.counit.app M) (b.counit.app M)
      naturality := by
        intro M N f
        dsimp [Q, P]
        apply biprod.hom_ext' <;> simp }
  have hcF (M : C) : IsIso (F.map (c.app M)) := by
    let e := F.mapBiprod (L.obj (F.obj M)) (R.obj (G.obj M))
    let z := isoBiprodZero (X := F.obj (L.obj (F.obj M))) (hGR (G.obj M))
    have he : F.map (c.app M) = e.hom ≫ z.inv ≫ F.map (a.counit.app M) := by
      apply (cancel_epi e.inv).1
      apply biprod.hom_ext'
      · simp [e, z, c, ← Functor.map_comp]
      · exact (hGR (G.obj M)).eq_of_src _ _
    rw [he]
    infer_instance
  have hcG (M : C) : IsIso (G.map (c.app M)) := by
    let e := G.mapBiprod (L.obj (F.obj M)) (R.obj (G.obj M))
    let z := isoZeroBiprod (Y := G.obj (R.obj (G.obj M))) (hFL (F.obj M))
    have he : G.map (c.app M) = e.hom ≫ z.inv ≫ G.map (b.counit.app M) := by
      apply (cancel_epi e.inv).1
      apply biprod.hom_ext'
      · exact (hFL (F.obj M)).eq_of_src _ _
      · simp [e, z, c, ← Functor.map_comp]
    rw [he]
    infer_instance
  have : IsIso c := by
    have (M : C) : IsIso (c.app M) := hconservative _ (hcF M) (hcG M)
    exact NatIso.isIso_of_isIso_app c
  let d : Q ⋙ P ⟶ 𝟭 (D × E) :=
    { app := fun MN ↦
        (F.map biprod.fst ≫ (asIso a.unit).inv.app MN.1,
          G.map biprod.snd ≫ (asIso b.unit).inv.app MN.2)
      naturality := by
        intro MN MN' f
        apply Prod.ext
        · dsimp [Q, P]
          simp only [← Category.assoc, ← F.map_comp, biprod.map_fst]
          rw [F.map_comp, Category.assoc]
          simpa only [Functor.comp_map, Functor.id_map, asIso, NatIso.isIso_inv_app, Category.assoc]
            using congrArg (fun k ↦ F.map (biprod.fst : L.obj MN.1 ⊞ R.obj MN.2 ⟶ _) ≫ k)
            ((asIso a.unit).inv.naturality f.1)
        · dsimp [Q, P]
          simp only [← Category.assoc, ← G.map_comp, biprod.map_snd]
          rw [G.map_comp, Category.assoc]
          simpa only [Functor.comp_map, Functor.id_map, asIso, NatIso.isIso_inv_app, Category.assoc]
            using congrArg (fun k ↦ G.map (biprod.snd : L.obj MN.1 ⊞ R.obj MN.2 ⟶ _) ≫ k)
            ((asIso b.unit).inv.naturality f.2) }
  have : IsIso d := by
    have (MN : D × E) : IsIso (d.app MN) := by
      apply (isIso_prod_iff _ _).2
      constructor
      · change IsIso (F.map biprod.fst ≫ (asIso a.unit).inv.app MN.1)
        have he : F.map (biprod.fst : L.obj MN.1 ⊞ R.obj MN.2 ⟶ _) =
            (F.mapBiprod _ _).hom ≫ (isoBiprodZero (hGR MN.2)).inv := by
          simp
        rw [he]
        infer_instance
      · change IsIso (G.map biprod.snd ≫ (asIso b.unit).inv.app MN.2)
        have he : G.map (biprod.snd : L.obj MN.1 ⊞ R.obj MN.2 ⟶ _) =
            (G.mapBiprod _ _).hom ≫ (isoZeroBiprod (hFL MN.1)).inv := by
          simp
        rw [he]
        infer_instance
    exact NatIso.isIso_of_isIso_app d
  exact (CategoryTheory.Equivalence.mk P Q (asIso c).symm (asIso d)).isEquivalence_functor

end Generic

/-- The categorical component decomposition used by `clopenSectionComponent`.
Source: the disjoint-open-cover argument in the blueprint proof
(blueprint: lem-sp-clopen-section-component). -/
private theorem clopenSectionComponentCore {X V : Scheme.{u}} (q : V ⟶ X) (s : X ⟶ V)
    [IsOpenImmersion s] (hclosed : IsClosed (Set.range s.base))
    (hsection : s ≫ q = 𝟙 X) (A : Type u) [CommRing A] [Finite A] :
    ((Functor.prod'
        (sfIntrinsicOpenRestriction s A)
        (sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A)).IsEquivalence ∧
      PreservesFiniteLimits
        (Functor.prod'
          (sfIntrinsicOpenRestriction s A)
          (sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A)) ∧
      PreservesFiniteColimits
        (Functor.prod'
          (sfIntrinsicOpenRestriction s A)
          (sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A))) := by
  have _ := hsection
  let Z := clopenComplement s hclosed
  let F := sfIntrinsicOpenRestriction s A
  let G := sfIntrinsicOpenRestriction Z.ι A
  let L := sfIntrinsicExtensionByZero s A
  let R := sfIntrinsicExtensionByZero Z.ι A
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let eV := sfIntrinsicModuleEquivalence V A
  let eX := sfIntrinsicModuleEquivalence X A
  let eZ := sfIntrinsicModuleEquivalence Z.toScheme A
  have : L.Full := by dsimp [L, sfIntrinsicExtensionByZero]; infer_instance
  have : L.Faithful := by dsimp [L, sfIntrinsicExtensionByZero]; infer_instance
  have : R.Full := by dsimp [R, sfIntrinsicExtensionByZero]; infer_instance
  have : R.Faithful := by dsimp [R, sfIntrinsicExtensionByZero]; infer_instance
  have hjk : Set.range s.base ∩ Set.range Z.ι.base = ∅ := by
    rw [Z.range_ι]
    exact Set.inter_compl_self _
  have hz₁ (M : proEtaleRingModules X (proEtaleConstantRing X A)) :
      IsZero (G.obj (L.obj M)) := by
    let S := ProEtale.openImmersionLowerShriek B s
    let T := ProEtale.openImmersionRestriction B Z.ι
    have hz : IsZero (T.obj (S.obj (eX.inverse.obj M))) := by
      let hi := ProEtale.isInitial_openImmersionRestriction_openImmersionLowerShriek
        B s Z.ι hjk (eX.inverse.obj M)
      exact (isZero_zero _).of_iso (hi.uniqueUpToIso HasZeroObject.zeroIsInitial)
    exact (eZ.functor.map_isZero hz).of_iso
      (eZ.functor.mapIso (T.mapIso (eV.unitIso.symm.app (S.obj (eX.inverse.obj M)))))
  have hz₂ (M : proEtaleRingModules Z.toScheme (proEtaleConstantRing Z.toScheme A)) :
      IsZero (F.obj (R.obj M)) := by
    let S := ProEtale.openImmersionLowerShriek B Z.ι
    let T := ProEtale.openImmersionRestriction B s
    have hz : IsZero (T.obj (S.obj (eZ.inverse.obj M))) := by
      let hi := ProEtale.isInitial_openImmersionRestriction_openImmersionLowerShriek
        B Z.ι s (by rw [Set.inter_comm]; exact hjk) (eZ.inverse.obj M)
      exact (isZero_zero _).of_iso (hi.uniqueUpToIso HasZeroObject.zeroIsInitial)
    exact (eX.functor.map_isZero hz).of_iso
      (eX.functor.mapIso (T.mapIso (eV.unitIso.symm.app (S.obj (eZ.inverse.obj M)))))
  have hc : ∀ {M N : proEtaleRingModules V (proEtaleConstantRing V A)} (f : M ⟶ N),
      IsIso (F.map f) → IsIso (G.map f) → IsIso f := by
    intro M N f hF hG
    have hF' : IsIso ((ProEtale.openImmersionRestriction B s).map (eV.inverse.map f)) := by
      have : IsIso (eX.functor.map
          ((ProEtale.openImmersionRestriction B s).map (eV.inverse.map f))) := hF
      exact isIso_of_reflects_iso _ eX.functor
    have hG' : IsIso ((ProEtale.openImmersionRestriction B Z.ι).map (eV.inverse.map f)) := by
      have : IsIso (eZ.functor.map
          ((ProEtale.openImmersionRestriction B Z.ι).map (eV.inverse.map f))) := hG
      exact isIso_of_reflects_iso _ eZ.functor
    let g : ∀ i, ![X, Z.toScheme] i ⟶ V :=
      Fin.cons s (Fin.cons Z.ι fun i ↦ i.elim0)
    have : ∀ i, IsOpenImmersion (g i) :=
      Fin.cases (inferInstanceAs (IsOpenImmersion s))
        (Fin.cases (inferInstanceAs (IsOpenImmersion Z.ι)) fun i ↦ i.elim0)
    have hsurj : ∀ x, ∃ i, x ∈ Set.range (g i).base := fun x ↦ by
      by_cases hx : x ∈ Set.range s.base
      · exact ⟨0, hx⟩
      · exact ⟨1, Z.range_ι.ge hx⟩
    have hcover : Presieve.ofArrows _ g ∈ Scheme.proetalePrecoverage V :=
      Scheme.zariskiPrecoverage_le_proetalePrecoverage _
        ((Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨hsurj, fun i ↦ this i⟩)
    have : IsIso (eV.inverse.map f) :=
      ProEtale.isIso_of_isIso_localizationRestriction B _ g hcover
        (Fin.cases hF' (Fin.cases hG' fun i ↦ i.elim0))
    exact isIso_of_reflects_iso f eV.inverse
  have : (F.prod' G).IsEquivalence :=
    pair_equivalence F G L R (sfIntrinsicExtensionByZeroAdjunction s A)
      (sfIntrinsicExtensionByZeroAdjunction Z.ι A) hz₁ hz₂ hc
  exact ⟨this, inferInstance, inferInstance⟩

section Generic

universe v

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  [Preadditive C] [Preadditive D] [Preadditive E]
private theorem pair_homotopy (F : C ⥤ D) (G : C ⥤ E) [F.Additive] [G.Additive]
    [(F.prod' G).Full] [(F.prod' G).Faithful]
    {K L : CochainComplex C ℤ} (f g : K ⟶ L)
    (h : Homotopy ((F.mapHomologicalComplex (.up ℤ)).map f)
      ((F.mapHomologicalComplex (.up ℤ)).map g))
    (k : Homotopy ((G.mapHomologicalComplex (.up ℤ)).map f)
      ((G.mapHomologicalComplex (.up ℤ)).map g)) : Nonempty (Homotopy f g) := by
  let P := F.prod' G
  let a (i j : ℤ) : K.X i ⟶ L.X j := P.preimage (h.hom i j, k.hom i j)
  have ha (i j : ℤ) : P.map (a i j) = (h.hom i j, k.hom i j) := P.map_preimage _
  have ha₁ (i j : ℤ) : F.map (a i j) = h.hom i j := congrArg Prod.fst (ha i j)
  have ha₂ (i j : ℤ) : G.map (a i j) = k.hom i j := congrArg Prod.snd (ha i j)
  refine ⟨{ hom := a, zero := ?_, comm := ?_ }⟩
  · intro i j hij
    apply P.map_injective
    apply Prod.ext
    · exact (ha₁ i j).trans ((h.zero i j hij).trans (F.map_zero _ _).symm)
    · exact (ha₂ i j).trans ((k.zero i j hij).trans (G.map_zero _ _).symm)
  · intro i
    apply P.map_injective
    apply Prod.ext
    · simpa only [P, Functor.prod'_map, Functor.map_add, Functor.map_comp, ha₁,
        dNext, prevD, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.mk'_apply,
        Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_map_f] using h.comm i
    · simpa only [P, Functor.prod'_map, Functor.map_add, Functor.map_comp, ha₂,
        dNext, prevD, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.mk'_apply,
        Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_map_f] using k.comm i

private theorem pair_complex_equivalence (F : C ⥤ D) (G : C ⥤ E)
    [F.Additive] [G.Additive] [(F.prod' G).IsEquivalence] :
    ((F.mapHomologicalComplex (.up ℤ)).prod'
      (G.mapHomologicalComplex (.up ℤ))).IsEquivalence := by
  let P := F.prod' G
  let Q := (F.mapHomologicalComplex (.up ℤ)).prod' (G.mapHomologicalComplex (.up ℤ))
  have hfaithful : Q.Faithful := ⟨fun {K L} f g h ↦ by
    ext n
    apply P.map_injective
    apply Prod.ext
    · exact congrArg (fun a ↦ a.f n) (congrArg Prod.fst h)
    · exact congrArg (fun a ↦ a.f n) (congrArg Prod.snd h)⟩
  have hfull : Q.Full := ⟨fun {K L} f ↦ by
    let a : K ⟶ L :=
      { f := fun n ↦ P.preimage (f.1.f n, f.2.f n)
        comm' := by
          intro i j hij
          apply P.map_injective
          apply Prod.ext
          · simp only [Functor.map_comp, P.map_preimage, prod_comp]
            exact f.1.comm i j
          · simp only [Functor.map_comp, P.map_preimage, prod_comp]
            exact f.2.comm i j }
    refine ⟨a, ?_⟩
    apply Prod.ext <;> ext n
    · exact congrArg Prod.fst (P.map_preimage (f.1.f n, f.2.f n))
    · exact congrArg Prod.snd (P.map_preimage (f.1.f n, f.2.f n))⟩
  have hess : Q.EssSurj := ⟨fun KL ↦ by
    let Z (n : ℤ) := P.objPreimage (KL.1.X n, KL.2.X n)
    let e (n : ℤ) := P.objObjPreimageIso (KL.1.X n, KL.2.X n)
    let d (i j : ℤ) : Z i ⟶ Z j :=
      P.preimage ((e i).hom ≫ (KL.1.d i j, KL.2.d i j) ≫ (e j).inv)
    have hd (i j : ℤ) : P.map (d i j) =
        (e i).hom ≫ (KL.1.d i j, KL.2.d i j) ≫ (e j).inv := P.map_preimage _
    let K : CochainComplex C ℤ :=
      { X := Z
        d := d
        shape := by
          intro i j hij
          apply P.map_injective
          apply Prod.ext
          · change F.map (d i j) = F.map 0
            have h := congrArg Prod.fst (hd i j)
            dsimp [P] at h
            rw [h, KL.1.shape i j hij, zero_comp,
              comp_zero, F.map_zero]
          · change G.map (d i j) = G.map 0
            have h := congrArg Prod.snd (hd i j)
            dsimp [P] at h
            rw [h, KL.2.shape i j hij, zero_comp,
              comp_zero, G.map_zero]
        d_comp_d' := by
          intro i j k hij hjk
          apply P.map_injective
          apply Prod.ext
          · change F.map (d i j ≫ d j k) = F.map 0
            have h := congrArg Prod.fst (hd i j)
            have h' := congrArg Prod.fst (hd j k)
            dsimp [P] at h h'
            rw [F.map_comp, h, h', F.map_zero]
            have he := congrArg Prod.fst (Iso.inv_hom_id (e j))
            dsimp at he
            simp only [Category.assoc]
            rw [← Category.assoc (e j).inv.1, he, Category.id_comp,
              ← Category.assoc (KL.1.d i j), KL.1.d_comp_d,
              zero_comp, comp_zero]
          · change G.map (d i j ≫ d j k) = G.map 0
            have h := congrArg Prod.snd (hd i j)
            have h' := congrArg Prod.snd (hd j k)
            dsimp [P] at h h'
            rw [G.map_comp, h, h', G.map_zero]
            have he := congrArg Prod.snd (Iso.inv_hom_id (e j))
            dsimp at he
            simp only [Category.assoc]
            rw [← Category.assoc (e j).inv.2, he, Category.id_comp,
              ← Category.assoc (KL.2.d i j), KL.2.d_comp_d,
              zero_comp, comp_zero] }
    let e₁ : (F.mapHomologicalComplex (.up ℤ)).obj K ≅ KL.1 :=
      HomologicalComplex.Hom.isoOfComponents
        (fun n ↦ (CategoryTheory.Prod.fst D E).mapIso (e n)) (by
          intro i j hij
          have h := congrArg Prod.fst (hd i j)
          dsimp [P] at h
          change (e i).hom.1 ≫ KL.1.d i j = F.map (d i j) ≫ (e j).hom.1
          rw [h]
          have he := congrArg Prod.fst (Iso.inv_hom_id (e j))
          dsimp at he
          simp only [Category.assoc, he, Category.comp_id])
    let e₂ : (G.mapHomologicalComplex (.up ℤ)).obj K ≅ KL.2 :=
      HomologicalComplex.Hom.isoOfComponents
        (fun n ↦ (CategoryTheory.Prod.snd D E).mapIso (e n)) (by
          intro i j hij
          have h := congrArg Prod.snd (hd i j)
          dsimp [P] at h
          change (e i).hom.2 ≫ KL.2.d i j = G.map (d i j) ≫ (e j).hom.2
          rw [h]
          have he := congrArg Prod.snd (Iso.inv_hom_id (e j))
          dsimp at he
          simp only [Category.assoc, he, Category.comp_id])
    exact ⟨K, ⟨e₁.prod e₂⟩⟩⟩
  exact ⟨hfaithful, hfull, hess⟩

end Generic

/-- The complex-level component decomposition used by `clopenSectionComponent`.
Source: the componentwise complex argument in the blueprint proof
(blueprint: lem-sp-clopen-section-component). -/
private theorem clopenSectionComponentComplex {X V : Scheme.{u}} (q : V ⟶ X) (s : X ⟶ V)
    [IsOpenImmersion s] (hclosed : IsClosed (Set.range s.base))
    (hsection : s ≫ q = 𝟙 X) (A : Type u) [CommRing A] [Finite A] :
    (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)),
      Nonempty
        ((Functor.prod'
            (sfIntrinsicOpenRestriction s A)
            (sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A)).obj
          ((sfIntrinsicExtensionByZero s A).obj M) ≅
          ((M, 0) :
            proEtaleRingModules X (proEtaleConstantRing X A) ×
              proEtaleRingModules (clopenComplement s hclosed).toScheme
                (proEtaleConstantRing (clopenComplement s hclosed).toScheme A)))) ∧
    (Functor.prod'
      ((sfIntrinsicOpenRestriction s A).mapHomologicalComplex (.up ℤ))
      ((sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A).mapHomologicalComplex
        (.up ℤ))).IsEquivalence ∧
    (∀ (K : CochainComplex
        (proEtaleRingModules V (proEtaleConstantRing V A)) ℤ),
      HomologicalComplex.Acyclic K ↔
        (HomologicalComplex.Acyclic
            (((sfIntrinsicOpenRestriction s A).mapHomologicalComplex (.up ℤ)).obj K) ∧
          HomologicalComplex.Acyclic
            (((sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A).mapHomologicalComplex
              (.up ℤ)).obj K))) ∧
    (∀ {E F : CochainComplex
        (proEtaleRingModules V (proEtaleConstantRing V A)) ℤ} (f g : E ⟶ F),
      Nonempty (Homotopy f g) ↔
        (Nonempty (Homotopy
            (((sfIntrinsicOpenRestriction s A).mapHomologicalComplex (.up ℤ)).map f)
            (((sfIntrinsicOpenRestriction s A).mapHomologicalComplex (.up ℤ)).map g)) ∧
          Nonempty (Homotopy
            (((sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A).mapHomologicalComplex
              (.up ℤ)).map f)
            (((sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A).mapHomologicalComplex
              (.up ℤ)).map g)))) := by
  let F := sfIntrinsicOpenRestriction s A
  let G := sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A
  let L := sfIntrinsicExtensionByZero s A
  have hcore := (clopenSectionComponentCore q s hclosed hsection A).1
  have : (F.prod' G).IsEquivalence := hcore
  refine ⟨?_, pair_complex_equivalence F G, ?_, ?_⟩
  · intro M
    let eX := sfIntrinsicModuleEquivalence X A
    let eV := sfIntrinsicModuleEquivalence V A
    let eZ := sfIntrinsicModuleEquivalence (clopenComplement s hclosed).toScheme A
    let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
    let R := ProEtale.openImmersionRestriction B (clopenComplement s hclosed).ι
    let S := ProEtale.openImmersionLowerShriek B s
    have : L.Full := by dsimp [L, sfIntrinsicExtensionByZero]; infer_instance
    have : L.Faithful := by dsimp [L, sfIntrinsicExtensionByZero]; infer_instance
    have : IsIso ((sfIntrinsicExtensionByZeroAdjunction s A).unit.app M) :=
      inferInstance
    let e₁ : F.obj (L.obj M) ≅ M :=
      (asIso ((sfIntrinsicExtensionByZeroAdjunction s A).unit.app M)).symm
    have hz : IsZero (R.obj (S.obj (eX.inverse.obj M))) := by
      let hi := ProEtale.isInitial_openImmersionRestriction_openImmersionLowerShriek
        B s (clopenComplement s hclosed).ι (by
          rw [(clopenComplement s hclosed).range_ι]
          change Set.range s.base ∩ (Set.range s.base)ᶜ = ∅
          exact Set.inter_compl_self _) (eX.inverse.obj M)
      exact (isZero_zero _).of_iso (hi.uniqueUpToIso HasZeroObject.zeroIsInitial)
    let e₂ : G.obj (L.obj M) ≅ 0 :=
      ((eZ.functor.map_isZero hz).of_iso
        (eZ.functor.mapIso (R.mapIso (eV.unitIso.symm.app
          (S.obj (eX.inverse.obj M)))))).isoZero
    exact ⟨e₁.prod e₂⟩
  · intro K
    have : F.PreservesHomology := by dsimp [F]; infer_instance
    have : G.PreservesHomology := by dsimp [G]; infer_instance
    constructor
    · intro h
      constructor
      · intro n
        apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
        exact (F.map_isZero (h n).isZero_homology).of_iso
          ((K.sc n).mapHomologyIso F)
      · intro n
        apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
        exact (G.map_isZero (h n).isZero_homology).of_iso
          ((K.sc n).mapHomologyIso G)
    · rintro ⟨hF, hG⟩ n
      apply (K.exactAt_iff_isZero_homology n).2
      have hzF : IsZero (F.obj (K.homology n)) :=
        (hF n).isZero_homology.of_iso ((K.sc n).mapHomologyIso F).symm
      have hzG : IsZero (G.obj (K.homology n)) :=
        (hG n).isZero_homology.of_iso ((K.sc n).mapHomologyIso G).symm
      apply (IsZero.iff_id_eq_zero _).2
      apply (F.prod' G).map_injective
      apply Prod.ext
      · change F.map (𝟙 _) = F.map 0
        rw [F.map_id, F.map_zero]
        exact hzF.eq_of_src _ _
      · change G.map (𝟙 _) = G.map 0
        rw [G.map_id, G.map_zero]
        exact hzG.eq_of_src _ _
  · intro E H f g
    constructor
    · rintro ⟨h⟩
      exact ⟨⟨F.mapHomotopy h⟩, ⟨G.mapHomotopy h⟩⟩
    · rintro ⟨⟨h⟩, ⟨k⟩⟩
      exact pair_homotopy F G f g h k

private noncomputable def fixedSectionRestriction {X V : Scheme.{u}} (q : V ⟶ X)
    (s : X ⟶ V) [IsOpenImmersion s] (hsection : s ≫ q = 𝟙 X)
    (A : Type u) [CommRing A] :
    ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) q ⟶
      ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) s where
  app M :=
    { hom :=
        { app := fun W ↦ M.obj.map (clopenSectionComponentArrow q s hsection W.unop).op
          naturality := by
            intro W W' f
            change M.obj.map ((proEtaleBaseChange q).op.map f) ≫ _ =
              _ ≫ M.obj.map
                ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale s)).op.map f)
            change M.obj.map (((proEtaleBaseChange q).map f.unop).op) ≫ _ =
              _ ≫ M.obj.map (((MorphismProperty.Over.map ⊤
                (inferInstance : WeaklyEtale s)).map f.unop).op)
            rw [← M.obj.map_comp, ← M.obj.map_comp, ← op_comp, ← op_comp]
            congr 1
            apply congrArg Quiver.Hom.op
            apply MorphismProperty.Over.Hom.ext
            change pullback.lift (𝟙 _) (_ ≫ s) _ ≫ pullback.map _ _ _ _
              f.unop.left (𝟙 V) (𝟙 X)
                (by simp) (by simp) =
                f.unop.left ≫ pullback.lift (𝟙 _) (_ ≫ s) _
            apply pullback.hom_ext <;> simp only [Category.assoc, limit.lift_π,
              PullbackCone.mk_π_app,
              limit.lift_π_assoc, cospan_left, Category.comp_id]
            · exact Category.id_comp _
            · exact (congrArg (fun k ↦ k ≫ s)
                (MorphismProperty.Over.w f.unop)).symm.trans
                  (Category.assoc _ _ _) } }
  naturality M N f := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    exact (f.hom.naturality _).symm

private noncomputable def fixedClopenSectionIso {X V : Scheme.{u}} (q : V ⟶ X)
    (s : X ⟶ V) [IsOpenImmersion s] (hclosed : IsClosed (Set.range s.base))
    (hsection : s ≫ q = 𝟙 X) (A : Type u) [CommRing A] :
    ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) s ⋙
      ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) q ≅
        𝟭 (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  have := ProEtale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range B s hclosed
  exact Functor.isoWhiskerRight (asIso (ProEtale.openImmersionLowerShriekToLowerStar B s))
      (ProEtale.lowerStar B q) ≪≫ ProEtale.lowerStarComp B s q ≪≫
    ProEtale.lowerStarCongr B hsection ≪≫ ProEtale.lowerStarId B X

private theorem restriction_star_comp_counit {X V : Scheme.{u}} (q : V ⟶ X)
    (s : X ⟶ V) [IsOpenImmersion s] (hsection : s ≫ q = 𝟙 X)
    (A : Type u) [CommRing A]
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    (fixedSectionRestriction q s hsection A).app
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) s).obj M) ≫
      (ProEtale.openImmersionRestrictionLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) s).counit.app M =
      (ProEtale.lowerStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) s q ≪≫
        ProEtale.lowerStarCongr (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) hsection ≪≫
        ProEtale.lowerStarId (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).hom.app M := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  change ((fixedSectionRestriction q s hsection A).app _).hom.app W ≫
    ((ProEtale.openImmersionRestrictionLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) s).counit.app M).hom.app W = _
  change M.obj.map _ ≫ _ = _
  simp only [Iso.trans_hom, NatTrans.comp_app]
  change _ = ((ProEtale.lowerStarComp
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) s q).hom.app M).hom.app W ≫
      ((ProEtale.lowerStarCongr
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) hsection).hom.app M).hom.app W ≫
      ((ProEtale.lowerStarId
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).hom.app M).hom.app W
  simp only [
    ProEtale.lowerStarComp_hom_app_hom_app,
    ProEtale.lowerStarCongr_hom_app_hom_app,
    ProEtale.lowerStarId_hom_app_hom_app]
  change _ ≫ M.obj.map
    ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ s
      (inferInstance : WeaklyEtale s) trivial).unit.app W.unop).op = _
  rw [← M.obj.map_comp, ← M.obj.map_comp, ← M.obj.map_comp]
  apply congrArg M.obj.map
  simp only [← op_comp]
  apply congrArg Quiver.Hom.op
  apply MorphismProperty.Over.Hom.ext
  simp only [Quiver.Hom.unop_op, Functor.op_map]
  change (pullback.lift (𝟙 W.unop.left) W.unop.hom _) ≫
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ s).map
      (clopenSectionComponentArrow q s hsection W.unop)).left = _
  simp only [MorphismProperty.Over.pullback_map_left]
  apply pullback.hom_ext
  · apply pullback.hom_ext <;>
      simp [clopenSectionComponentArrow, Category.assoc,
        proEtaleBaseChange, MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
        MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp]
  · simp [clopenSectionComponentArrow, Category.assoc,
      proEtaleBaseChange, MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp]


private theorem fixedSectionRestriction_isIso {X V : Scheme.{u}} (q : V ⟶ X)
    (s : X ⟶ V) [IsOpenImmersion s] (hclosed : IsClosed (Set.range s.base))
    (hsection : s ≫ q = 𝟙 X) (A : Type u) [CommRing A]
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    IsIso ((fixedSectionRestriction q s hsection A).app
      ((ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) s).obj M)) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let r := fixedSectionRestriction q s hsection A
  let c := (ProEtale.openImmersionLowerShriekToLowerStar B s).app M
  let T := ProEtale.openImmersionRestriction B s
  let D := ProEtale.lowerStar B q
  let b := ProEtale.openImmersionRestrictionLowerStarAdjunction B s
  have := ProEtale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range B s hclosed
  have he : r.app ((ProEtale.openImmersionLowerShriek B s).obj M) ≫
      T.map c ≫ b.counit.app M = (fixedClopenSectionIso q s hclosed hsection A).hom.app M := by
    rw [← Category.assoc, ← r.naturality, Category.assoc]
    rw [restriction_star_comp_counit q s hsection A M]
    rfl
  have : IsIso (r.app ((ProEtale.openImmersionLowerShriek B s).obj M) ≫
      T.map c ≫ b.counit.app M) := by
      dsimp only [B, Functor.comp_obj, Functor.id_obj] at he ⊢
      rw [he]
      infer_instance
  exact IsIso.of_isIso_comp_right _ (T.map c ≫ b.counit.app M)


private noncomputable def intrinsicSectionRestriction {X V : Scheme.{u}} (q : V ⟶ X)
    (s : X ⟶ V) [IsOpenImmersion s] (hsection : s ≫ q = 𝟙 X)
    (A : Type u) [CommRing A] [Finite A] :
    proEtaleConstantModuleDirectImage q A ⟶ sfIntrinsicOpenRestriction s A :=
  let eV := sfIntrinsicModuleEquivalence V A
  let eX := sfIntrinsicModuleEquivalence X A
  let D := proEtaleConstantModuleDirectImage q A
  (Functor.leftUnitor D).inv ≫
    Functor.whiskerRight eV.counitIso.inv D ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft eV.inverse (sfIntrinsicDirectImageComparison q A).hom ≫
    Functor.whiskerLeft eV.inverse
      (Functor.whiskerRight (fixedSectionRestriction q s hsection A) eX.functor)

private theorem intrinsicSectionRestriction_isIso {X V : Scheme.{u}} (q : V ⟶ X)
    (s : X ⟶ V) [IsOpenImmersion s] (hclosed : IsClosed (Set.range s.base))
    (hsection : s ≫ q = 𝟙 X) (A : Type u) [CommRing A] [Finite A]
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) :
    IsIso ((intrinsicSectionRestriction q s hsection A).app
      ((sfIntrinsicExtensionByZero s A).obj M)) := by
  let eV := sfIntrinsicModuleEquivalence V A
  let eX := sfIntrinsicModuleEquivalence X A
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let S := ProEtale.openImmersionLowerShriek B s
  let r := fixedSectionRestriction q s hsection A
  let N := S.obj (eX.inverse.obj M)
  have := fixedSectionRestriction_isIso q s hclosed hsection A (eX.inverse.obj M)
  have hr : IsIso (r.app (eV.inverse.obj (eV.functor.obj N))) := by
    have he := r.naturality (eV.unitIso.hom.app N)
    have : IsIso ((ProEtale.lowerStar B q).map (eV.unitIso.hom.app N) ≫
        r.app (eV.inverse.obj (eV.functor.obj N))) := by
      dsimp only [B, Functor.comp_obj, Functor.id_obj] at he ⊢
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((ProEtale.lowerStar B q).map (eV.unitIso.hom.app N)) _
  have hr' : IsIso (eX.functor.map (r.app (eV.inverse.obj (eV.functor.obj N)))) :=
    inferInstance
  simp only [intrinsicSectionRestriction, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Category.id_comp]
  change IsIso (_ ≫ _ ≫ eX.functor.map (r.app (eV.inverse.obj (eV.functor.obj N))))
  infer_instance

private theorem realizationUnit_naturality (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A]
    {M N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))}
    (f : M ⟶ N) (W : T.ProEtᵒᵖ) (m : M.obj.obj W) :
    (((sfIntrinsicModuleEquivalence T A).functor.map f).val.app W)
        (sfIntrinsicRealizationUnit T A M W m) =
      sfIntrinsicRealizationUnit T A N W ((f.hom.app W) m) := by
  let P := ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1, u} A)
  have h := (PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap T A)).unit.naturality (P.map f.hom)
  exact (congrArg (fun k ↦ k.app W m) h).symm

private theorem intrinsicSectionRestriction_normalized {X V : Scheme.{u}} (q : V ⟶ X)
    (s : X ⟶ V) [IsOpenImmersion s] (hsection : s ≫ q = 𝟙 X)
    (A : Type u) [CommRing A] [Finite A]
    (N : proEtaleRingModules V (proEtaleConstantRing V A)) (W : X.ProEtᵒᵖ)
    (m : (((sfIntrinsicModuleEquivalence V A).inverse.obj N).obj.obj
      ((proEtaleBaseChange q).op.obj W))) :
    ((intrinsicSectionRestriction q s hsection A).app N).val.app W
        (((proEtaleConstantModuleDirectImage q A).map
          ((sfIntrinsicModuleEquivalence V A).counitIso.hom.app N)).val.app W
            (sfIntrinsicRealizationUnit V A
              ((sfIntrinsicModuleEquivalence V A).inverse.obj N)
              ((proEtaleBaseChange q).op.obj W) m)) =
      sfIntrinsicRealizationUnit X A
        ((ProEtale.openImmersionRestriction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) s).obj
            ((sfIntrinsicModuleEquivalence V A).inverse.obj N)) W
        ((((sfIntrinsicModuleEquivalence V A).inverse.obj N).obj.map
          (clopenSectionComponentArrow q s hsection W.unop).op) m) := by
  let eV := sfIntrinsicModuleEquivalence V A
  let eX := sfIntrinsicModuleEquivalence X A
  let D := proEtaleConstantModuleDirectImage q A
  let H := eV.inverse.obj N
  let c := sfIntrinsicDirectImageComparison q A
  let r := fixedSectionRestriction q s hsection A
  have he : D.map (eV.counitIso.hom.app N) ≫
      (intrinsicSectionRestriction q s hsection A).app N =
      c.hom.app H ≫ eX.functor.map (r.app H) := by
    simp [intrinsicSectionRestriction, c, H, r, eX, eV, D]
  change ((D.map (eV.counitIso.hom.app N) ≫
    (intrinsicSectionRestriction q s hsection A).app N).val.app W) _ = _
  rw [he]
  change ((eX.functor.map (r.app H)).val.app W)
    ((c.hom.app H).val.app W (sfIntrinsicRealizationUnit V A H _ m)) = _
  have hc := (sfIntrinsicDirectImageComparison_existsUnique q A).exists.choose_spec H W m
  exact (congrArg (fun x ↦ ((eX.functor.map (r.app H)).val.app W) x) hc).trans
    (realizationUnit_naturality X A (r.app H) W m)

/-- The direct-image comparison before passing to complexes.
Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-sf-operations,
lem-weil-pbc-clopen-section-direct-image.proof.md, displayed section formula
(blueprint: lem-sp-clopen-section-component).

Proof: For a test object W over X, the pullback W ×[X] V splits into the component
W given by the section and the complementary open. Extension by zero vanishes on
that complement. Restriction along clopenSectionComponentArrow therefore gives a
bijection from its sections to the sections over W in the section component. Compose
with the inverse of the open adjunction unit. This is additive and commutes with the
constant scalars. The canonical coefficient realization extends the same action to
locally constant scalars, so the bijection is a module isomorphism in intrinsic
coefficients. Its inverse glues a section with zero on the complementary open.
The sheaf uniqueness clause proves the two inverse laws. Restriction commutes with
restriction along the component arrow, and morphisms of sheaves commute with it as
well. These identities make the sectionwise isomorphisms a natural isomorphism.
Evaluating its definition on the realization unit gives exactly the stated equation. -/
private theorem clopenSectionComparison {X V : Scheme.{u}} (q : V ⟶ X) (s : X ⟶ V)
    [IsOpenImmersion s] (hclosed : IsClosed (Set.range s.base))
    (hsection : s ≫ q = 𝟙 X) (A : Type u) [CommRing A] [Finite A] :
    ∃ e : sfIntrinsicExtensionByZero s A ⋙ proEtaleConstantModuleDirectImage q A ≅
        𝟭 (proEtaleRingModules X (proEtaleConstantRing X A)),
      ClopenSectionComparisonOnSections q s hsection A e.hom := by
  let L := sfIntrinsicExtensionByZero s A
  let a := sfIntrinsicExtensionByZeroAdjunction s A
  let r := intrinsicSectionRestriction q s hsection A
  have : L.Full := by dsimp [L, sfIntrinsicExtensionByZero]; infer_instance
  have : L.Faithful := by dsimp [L, sfIntrinsicExtensionByZero]; infer_instance
  have : IsIso (Functor.whiskerLeft L r) := by
    have (M : proEtaleRingModules X (proEtaleConstantRing X A)) :
        IsIso ((Functor.whiskerLeft L r).app M) :=
      intrinsicSectionRestriction_isIso q s hclosed hsection A M
    exact NatIso.isIso_of_isIso_app _
  let e := asIso (Functor.whiskerLeft L r) ≪≫ (asIso a.unit).symm
  refine ⟨e, ?_⟩
  intro M W m
  have he : e.hom.app M ≫ a.unit.app M = r.app (L.obj M) := by simp [e]
  change ((e.hom.app M ≫ a.unit.app M).val.app W) _ = _
  rw [he]
  exact intrinsicSectionRestriction_normalized q s hsection A (L.obj M) W m

/-- The K-injective and direct-image tail of the clopen component calculation.
Source: the componentwise K-injective and section formula argument in the blueprint
proof (blueprint: lem-sp-clopen-section-component). -/
private theorem clopenSectionComponentTail {X V : Scheme.{u}} (q : V ⟶ X) (s : X ⟶ V)
    [IsOpenImmersion s] (hclosed : IsClosed (Set.range s.base))
    (hsection : s ≫ q = 𝟙 X) (A : Type u) [CommRing A] [Finite A] :
    (∀ (I : CochainComplex
        (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ),
      CochainComplex.IsKInjective I →
        CochainComplex.IsKInjective
          (((sfIntrinsicExtensionByZero s A).mapHomologicalComplex (.up ℤ)).obj I)) ∧
    (∃ e : sfIntrinsicExtensionByZero s A ⋙ proEtaleConstantModuleDirectImage q A ≅
        𝟭 (proEtaleRingModules X (proEtaleConstantRing X A)),
      ClopenSectionComparisonOnSections q s hsection A e.hom ∧
      ∃ eC : (sfIntrinsicExtensionByZero s A).mapHomologicalComplex (.up ℤ) ⋙
          (proEtaleConstantModuleDirectImage q A).mapHomologicalComplex (.up ℤ) ≅
        𝟭 (CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ),
        (∀ (K : CochainComplex
            (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ) (n : ℤ),
          (eC.hom.app K).f n = e.hom.app (K.X n)) ∧
        (∀ {E F : CochainComplex
            (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ} (f : E ⟶ F),
          ((sfIntrinsicExtensionByZero s A).mapHomologicalComplex (.up ℤ) ⋙
              (proEtaleConstantModuleDirectImage q A).mapHomologicalComplex (.up ℤ)).map f ≫
            eC.hom.app F = eC.hom.app E ≫ f) ∧
        (∀ {E F : CochainComplex
            (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ}
            {f g : E ⟶ F} (h : Homotopy f g) (i j : ℤ),
          (sfIntrinsicExtensionByZero s A ⋙ proEtaleConstantModuleDirectImage q A).map
              (h.hom i j) ≫ e.hom.app (F.X j) =
            e.hom.app (E.X i) ≫ h.hom i j)) := by
  constructor
  · intro I hI
    let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
    have := hI
    have : (ProEtale.openImmersionRestriction B s).PreservesHomology := by
      have : PreservesLimitsOfSize.{0, 0} (ProEtale.openImmersionRestriction B s) :=
        (ProEtale.openImmersionLowerShriekAdjunction B s).rightAdjoint_preservesLimits
      have : PreservesColimitsOfSize.{0, 0} (ProEtale.openImmersionRestriction B s) :=
        (ProEtale.openImmersionRestrictionLowerStarAdjunction B s).leftAdjoint_preservesColimits
      infer_instance
    have := (ProEtale.openImmersionRestrictionLowerStarAdjunction B s).preservesKInjectiveComplexes
    have := ProEtale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range B s hclosed
    have := Functor.preservesKInjectiveComplexes_of_iso
      (asIso (ProEtale.openImmersionLowerShriekToLowerStar B s)).symm
    change CochainComplex.IsKInjective
      (((((sfIntrinsicModuleEquivalence X A).inverse ⋙
        ProEtale.openImmersionLowerShriek B s) ⋙
        (sfIntrinsicModuleEquivalence V A).functor).mapHomologicalComplex (.up ℤ)).obj I)
    infer_instance
  · obtain ⟨e, he⟩ := clopenSectionComparison q s hclosed hsection A
    let eC := Functor.mapHomologicalComplexCompIso e (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ (.up ℤ)
    refine ⟨e, he, eC, ?_, ?_, ?_⟩
    · intro K n
      rfl
    · intro E F f
      exact eC.hom.naturality f
    · intro E F f g h i j
      exact e.hom.naturality (h.hom i j)

/-- For a clopen section, module sheaves, complexes, K-injectives and direct images split
into the section component and its open complement.
Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-sf-operations,
lem-weil-pbc-clopen-section-direct-image.proof.md, disjoint-open-cover description
and displayed section formula; Stacks Project, `proetale.tex`, Tags 098K and 09AE
(blueprint: lem-sp-clopen-section-component).

Proof plan, following all eight DAG steps:
1. Open-immersion base change splits every test object into the section and complementary
   opens. Weakly-etale base change and localization identify their pro-etale sites
   (`lem-weil-pbc-open-immersion-base-change`,
   `lem-weil-pbc-weakly-etale-composition-base-change`,
   `lem-weil-proetale-weakly-etale-localization`, `sk-def-pe-site`).
2. The sheaf equalizer for this two-open cover gives the sectionwise product decomposition:
   cross intersections are empty and the empty-cover condition gives zero sections there.
   The restriction maps are additive, linear, and natural (`def-weil-pbc-sites-and-cohomology`).
3. Glue a pair by `G(M,N)(W) = M(W_X) × N(W_Z)` with scalar action through coefficient
   restrictions. Matching families glue coordinatewise. Restriction and gluing are inverse
   on objects and morphisms (`def-weil-sheaf-of-modules-category`).
4. Kernels and cokernels in the product are coordinatewise. The equivalence preserves
   their universal properties, hence is exact; so are both coordinate restrictions.
5. In the product, insertion `(M,0)` is left adjoint to the first restriction. Uniqueness
   of left adjoints identifies the recorded extension by zero with that insertion, and its
   unit with the canonical component identification (`lem-weil-extension-by-zero-adjunction`).
6. Apply the additive equivalence in every integer degree. Differentials, chain maps,
   kernels/images and homotopy equations are componentwise; thus acyclicity and homotopies
   are componentwise (`def-pc-cochain-complex-modules`, `def-pc-acyclic-complex-modules`).
7. A map from an acyclic complex to the inserted K-injective has components `(a_X,0)`.
   A null homotopy of `a_X` extends by the zero homotopy on the complement. This proves
   K-injectivity without a degree bound (`def-pur-kinjective-complex`).
8. For `W → X`, direct image evaluates at `W ×[X] V`. The section component is `W`
   since `s ≫ q = 𝟙 X`. Restrict along `clopenSectionComponentArrow`, then use the inverse
   open unit. This is exactly `ClopenSectionComparisonOnSections`: the realization
   counit and scalar-unit maps express the same restriction in intrinsic coefficients.
   The coefficient composite is the identity on constant sections and hence on the
   sheafification, so the map is linear. Restriction and maps of sheaves commute with
   it, giving the natural isomorphism (`def-weil-proetale-module-direct-image`). Apply
   that same map in every degree; its naturality gives the differential, chain-map
   and degree-minus-one homotopy compatibilities displayed in the conclusion.
-/
theorem clopenSectionComponent {X V : Scheme.{u}} (q : V ⟶ X) (s : X ⟶ V)
    [IsOpenImmersion s] (hclosed : IsClosed (Set.range s.base))
    (hsection : s ≫ q = 𝟙 X) (A : Type u) [CommRing A] [Finite A] :
    ((Functor.prod'
        (sfIntrinsicOpenRestriction s A)
        (sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A)).IsEquivalence ∧
      PreservesFiniteLimits
        (Functor.prod'
          (sfIntrinsicOpenRestriction s A)
          (sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A)) ∧
      PreservesFiniteColimits
        (Functor.prod'
          (sfIntrinsicOpenRestriction s A)
          (sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A))) ∧
      (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)),
        Nonempty
          ((Functor.prod'
              (sfIntrinsicOpenRestriction s A)
              (sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A)).obj
            ((sfIntrinsicExtensionByZero s A).obj M) ≅
            ((M, 0) :
              proEtaleRingModules X (proEtaleConstantRing X A) ×
                proEtaleRingModules (clopenComplement s hclosed).toScheme
                  (proEtaleConstantRing (clopenComplement s hclosed).toScheme A)))) ∧
      (Functor.prod'
        ((sfIntrinsicOpenRestriction s A).mapHomologicalComplex (.up ℤ))
        ((sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A).mapHomologicalComplex
          (.up ℤ))).IsEquivalence ∧
      (∀ (K : CochainComplex
          (proEtaleRingModules V (proEtaleConstantRing V A)) ℤ),
        HomologicalComplex.Acyclic K ↔
          (HomologicalComplex.Acyclic
              (((sfIntrinsicOpenRestriction s A).mapHomologicalComplex (.up ℤ)).obj K) ∧
            HomologicalComplex.Acyclic
              (((sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A).mapHomologicalComplex
                (.up ℤ)).obj K))) ∧
      (∀ {E F : CochainComplex
          (proEtaleRingModules V (proEtaleConstantRing V A)) ℤ} (f g : E ⟶ F),
        Nonempty (Homotopy f g) ↔
          (Nonempty (Homotopy
              (((sfIntrinsicOpenRestriction s A).mapHomologicalComplex (.up ℤ)).map f)
              (((sfIntrinsicOpenRestriction s A).mapHomologicalComplex (.up ℤ)).map g)) ∧
            Nonempty (Homotopy
              (((sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A).mapHomologicalComplex
                (.up ℤ)).map f)
              (((sfIntrinsicOpenRestriction (clopenComplement s hclosed).ι A).mapHomologicalComplex
                (.up ℤ)).map g)))) ∧
      (∀ (I : CochainComplex
          (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ),
        CochainComplex.IsKInjective I →
          CochainComplex.IsKInjective
            (((sfIntrinsicExtensionByZero s A).mapHomologicalComplex (.up ℤ)).obj I)) ∧
      (∃ e : sfIntrinsicExtensionByZero s A ⋙ proEtaleConstantModuleDirectImage q A ≅
          𝟭 (proEtaleRingModules X (proEtaleConstantRing X A)),
        ClopenSectionComparisonOnSections q s hsection A e.hom ∧
        ∃ eC : (sfIntrinsicExtensionByZero s A).mapHomologicalComplex (.up ℤ) ⋙
            (proEtaleConstantModuleDirectImage q A).mapHomologicalComplex (.up ℤ) ≅
          𝟭 (CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ),
          (∀ (K : CochainComplex
              (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ) (n : ℤ),
            (eC.hom.app K).f n = e.hom.app (K.X n)) ∧
          (∀ {E F : CochainComplex
              (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ} (f : E ⟶ F),
            ((sfIntrinsicExtensionByZero s A).mapHomologicalComplex (.up ℤ) ⋙
                (proEtaleConstantModuleDirectImage q A).mapHomologicalComplex (.up ℤ)).map f ≫
              eC.hom.app F = eC.hom.app E ≫ f) ∧
          (∀ {E F : CochainComplex
              (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ}
              {f g : E ⟶ F} (h : Homotopy f g) (i j : ℤ),
            (sfIntrinsicExtensionByZero s A ⋙ proEtaleConstantModuleDirectImage q A).map
                (h.hom i j) ≫ e.hom.app (F.X j) =
              e.hom.app (E.X i) ≫ h.hom i j)) := by
  obtain ⟨hcore, hlimits, hcolimits⟩ :=
    clopenSectionComponentCore q s hclosed hsection A
  obtain ⟨hM, hcomplex, hacyclic, hhomotopy⟩ :=
    clopenSectionComponentComplex q s hclosed hsection A
  obtain ⟨hkinj, hexists⟩ := clopenSectionComponentTail q s hclosed hsection A
  exact ⟨⟨hcore, hlimits, hcolimits⟩, hM, hcomplex, hacyclic, hhomotopy, hkinj, hexists⟩

end AlgebraicGeometry.Scheme
