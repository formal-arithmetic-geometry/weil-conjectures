/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.LeftDerivedEquivalence
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Transport of a normalized left derived adjunction

Source: Stacks Project, Derived Categories, Tags 05RR and 0FND;
Cohomology on Sites, Tag 07A6.
-/

@[expose] public section
set_option autoImplicit false
universe a b a' b' av bv av' bv' da db da' db'
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem transportKanExtension
    {C₀ C₁ D₀ D₁ H₀ H₁ : Type*}
    [Category* C₀] [Category* C₁] [Category* D₀] [Category* D₁]
    [Category* H₀] [Category* H₁]
    (P : C₀ ≌ C₁) (D : D₀ ≌ D₁) (G : H₀ ≌ H₁)
    (Q : C₀ ⥤ D₀) (Q' : C₁ ⥤ D₁) (F : C₀ ⥤ H₀) (F' : C₁ ⥤ H₁)
    (K : D₀ ⥤ H₀) (ε : Q ⋙ K ⟶ F) [K.IsRightKanExtension ε]
    (k : Q ⋙ D.functor ≅ P.functor ⋙ Q')
    (f : F ⋙ G.functor ≅ P.functor ⋙ F') :
    ∃ (K' : D₁ ⥤ H₁) (ε' : Q' ⋙ K' ⟶ F')
      (c : D.functor ⋙ K' ≅ K ⋙ G.functor),
      K'.IsRightKanExtension ε' ∧
      ∀ X : C₀, K'.map (k.hom.app X) ≫ ε'.app (P.functor.obj X) =
        c.hom.app (Q.obj X) ≫ G.functor.map (ε.app X) ≫ f.hom.app X := by
  let K' := D.inverse ⋙ K ⋙ G.functor
  let c : D.functor ⋙ K' ≅ K ⋙ G.functor :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight D.unitIso.symm (K ⋙ G.functor) ≪≫ Functor.leftUnitor _
  let εp := (Functor.associator Q K G.functor).inv ≫
    Functor.whiskerRight ε G.functor
  have hεp : (K ⋙ G.functor).IsRightKanExtension εp :=
    Functor.isRightKanExtension_comp_of_isEquivalence K ε G.functor
  let α := Functor.whiskerLeft Q c.hom ≫ εp ≫ f.hom
  have hα : (D.functor ⋙ K').IsRightKanExtension α :=
    (Functor.isRightKanExtension_iff_of_iso₂ εp α f c.symm (by
      ext X
      simp [α])).1 hεp
  let β : P.functor ⋙ (Q' ⋙ K') ⟶ P.functor ⋙ F' :=
    (Functor.associator _ _ _).inv ≫ (Functor.isoWhiskerRight k K').inv ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft Q c.hom ≫ εp ≫ f.hom
  let W := (Functor.whiskeringLeft C₀ C₁ H₁).obj P.functor
  let ε' : Q' ⋙ K' ⟶ F' := W.preimage β
  have heq : Functor.whiskerLeft P.functor ε' = β := W.map_preimage β
  have hβ : K'.IsRightKanExtension
      ((Functor.associator P.functor Q' K').hom ≫ β) := by
    apply (Functor.isRightKanExtension_iff_postcomp₁ D.functor k _).2
    convert hα using 1
    ext X
    simp [α, β]
  have hε' : K'.IsRightKanExtension ε' := by
    apply (Functor.isRightKanExtension_iff_precomp K' P.functor ε').2
    simpa only [heq] using hβ
  refine ⟨K', ε', c, hε', ?_⟩
  intro X
  have ht := NatTrans.congr_app heq X
  change ε'.app (P.functor.obj X) = β.app X at ht
  rw [ht]
  simp [β, εp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem transportAdjunction
    {A₀ A₁ B₀ B₁ : Type*} [Category* A₀] [Category* A₁]
    [Category* B₀] [Category* B₁]
    (D : A₀ ≌ A₁) (G : B₀ ≌ B₁)
    (L : A₀ ⥤ B₀) (U : B₀ ⥤ A₀) (L' : A₁ ⥤ B₁) (U' : B₁ ⥤ A₁)
    (a : L ⊣ U) (c : D.functor ⋙ L' ≅ L ⋙ G.functor)
    (d : U ⋙ D.functor ≅ G.functor ⋙ U') :
    ∃ a' : L' ⊣ U', ∀ X : A₀,
      D.functor.map (a.unit.app X) ≫ d.hom.app (L.obj X) =
        a'.unit.app (D.functor.obj X) ≫ U'.map (c.hom.app X) := by
  let z : D.inverse ⋙ (L ⋙ G.functor) ≅ L' :=
    Functor.isoWhiskerLeft D.inverse c.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight D.counitIso L' ≪≫ Functor.leftUnitor _
  let a₀ := (D.symm.toAdjunction.comp (a.comp G.toAdjunction)).ofNatIsoLeft z
  let V := (G.inverse ⋙ U) ⋙ D.functor
  let α := TwoSquare.mk D.functor L L' G.functor c.hom
  let β := (mateEquiv a a₀ α).natTrans
  let : IsIso α.natTrans := inferInstanceAs (IsIso c.hom)
  let : IsIso β := isIso_mateEquiv_of_isEquivalence a a₀ α
  let W := (Functor.whiskeringLeft B₀ B₁ A₁).obj G.functor
  let v : W.obj V ≅ W.obj U' := (asIso β).symm ≪≫ d
  let w : V ≅ U' := W.preimageIso v
  have hw : Functor.whiskerLeft G.functor w.hom = v.hom := W.map_preimage v.hom
  have hd (Y : B₀) : β.app Y ≫ w.hom.app (G.functor.obj Y) = d.hom.app Y := by
    have hh := NatTrans.congr_app hw Y
    change w.hom.app (G.functor.obj Y) = (inv β).app Y ≫ d.hom.app Y at hh
    rw [hh]
    simp
  let a' := a₀.ofNatIsoRight w
  refine ⟨a', ?_⟩
  intro X
  have ht := unit_mateEquiv a a₀ α X
  change D.functor.map (a.unit.app X) ≫ β.app (L.obj X) =
    a₀.unit.app (D.functor.obj X) ≫ V.map (c.hom.app X) at ht
  change D.functor.map (a.unit.app X) ≫ d.hom.app (L.obj X) =
    (a₀.unit.app (D.functor.obj X) ≫ w.hom.app (L'.obj (D.functor.obj X))) ≫
      U'.map (c.hom.app X)
  rw [Category.assoc, ← w.hom.naturality, ← Category.assoc, ← ht, Category.assoc]
  simpa only [Functor.comp_obj] using
    congrArg (fun t ↦ D.functor.map (a.unit.app X) ≫ t) (hd (L.obj X)).symm

private theorem homotopyEquivalence
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive] :
    (e.functor.mapHomotopyCategory (.up ℤ)).IsEquivalence := by
  let F := e.functor.mapHomotopyCategory (.up ℤ)
  let : F.Full := inferInstanceAs (e.functor.mapHomotopyCategory (.up ℤ)).Full
  let : F.Faithful := inferInstanceAs (e.functor.mapHomotopyCategory (.up ℤ)).Faithful
  let : F.EssSurj := ⟨fun K ↦ by
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    let ec := e.mapHomologicalComplex (.up ℤ)
    refine ⟨(HomotopyCategory.quotient _ _).obj (ec.inverse.obj L), ⟨?_⟩⟩
    exact (e.functor.mapHomotopyCategoryFactors (.up ℤ)).app _ ≪≫
      (HomotopyCategory.quotient _ _).mapIso (ec.counitIso.app L)⟩
  exact ⟨inferInstance, inferInstance, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
private theorem homotopyComp_hom
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    (F : C ⥤ D) (G : D ⥤ E) (T : C ⥤ E)
    [F.Additive] [G.Additive] [T.Additive] (r : F ⋙ G ≅ T)
    (H : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso r (.up ℤ)).hom.app H =
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app H ≫
        (NatTrans.mapHomotopyCategory r.hom (.up ℤ)).app H := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
  change (HomotopyCategory.quotient E (.up ℤ)).map _ =
    (HomotopyCategory.quotient E (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient E (.up ℤ)).map _
  rw [← Functor.map_comp]
  congr 1
  apply HomologicalComplex.hom_ext
  intro n
  change r.hom.app (K.X n) = 𝟙 _ ≫ r.hom.app (K.X n)
  rw [Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact additive equivalences transport a universal left derived pair and its normalized
adjunction. The right comparison is prescribed by localization of the ordinary right square.

Source: Stacks Project, Derived Categories, Tags 05RR and 0FND;
Cohomology on Sites, Tag 07A6.
(blueprint: lem-pbc-normalized-derived-adjunction-transport).

Proof:
1. Put `LM = DR.inverse ⋙ LS ⋙ DS.functor`. Compose the source counit with the two
localization comparisons, the equivalence unit and counit, and the ordinary left square.
Precomposition and postcomposition by equivalences are equivalences of categories of
right Kan extensions. Thus this counit makes LM the universal left derived functor.
The equivalence unit gives c, and the definition of the counit gives its factorization.
2. Localize the ordinary right square. Compose the two exact-functor localization
comparisons and their inverses to obtain d. Its factorization is the displayed formula.
3. Transport the source adjunction along DR and DS. The left comparison c and the right
comparison d identify its functors with LM and the exact derived right functor. Transport
along these isomorphisms gives aM; the unit formula for transport is the last equation.
4. Evaluate that formula on a localized homotopy representative and compose with the
ordinary right functor of the transported counit. Use the counit factorization from step 1,
the right factorization from step 2, and the source normalized unit. Naturality cancels
the adjacent localization comparisons. The remaining equality is exactly the assumed
ordinary unit square, mapped degreewise and localized. Essential surjectivity of the
homotopy equivalence proves the ordinary normalization on every representative.
The argument requires no exactness of either left adjoint. -/
theorem normalizedDerivedAdjunctionTransport
    {A : Type a} {B : Type b} {A' : Type a'} {B' : Type b'}
    [Category.{av} A] [Category.{bv} B] [Category.{av'} A'] [Category.{bv'} B']
    [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
    [HasDerivedCategory.{da} A] [HasDerivedCategory.{db} B]
    [HasDerivedCategory.{da'} A'] [HasDerivedCategory.{db'} B']
    (e : A ≌ A') (g : B ≌ B') [e.functor.Additive] [e.inverse.Additive]
    [g.functor.Additive] [g.inverse.Additive]
    (L : A ⥤ B) (U : B ⥤ A) (L' : A' ⥤ B') (U' : B' ⥤ A')
    [L.Additive] [U.Additive] [L'.Additive] [U'.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits U'] [PreservesFiniteColimits U']
    (a : L ⊣ U) (a' : L' ⊣ U')
    (s : L ⋙ g.functor ≅ e.functor ⋙ L')
    (r : U ⋙ e.functor ≅ g.functor ⋙ U')
    (hu : ∀ X : A, e.functor.map (a.unit.app X) ≫ r.hom.app (L.obj X) ≫
      U'.map (s.hom.app X) = a'.unit.app (e.functor.obj X))
    (LS : DerivedCategory A ⥤ DerivedCategory B)
    (εS : DerivedCategory.Qh ⋙ LS ⟶ L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hLS : LS.IsLeftDerivedFunctor εS (HomotopyCategory.quasiIso A (.up ℤ)))
    (aS : LS ⊣ U.mapDerivedCategory)
    (hn : ∀ H : HomotopyCategory A (.up ℤ),
      aS.unit.app (DerivedCategory.Qh.obj H) ≫ U.mapDerivedCategory.map (εS.app H) ≫
        U.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj H) =
      DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app H)) :
    let DR := e.mapDerivedCategory
    let DS := g.mapDerivedCategory
    let kR := e.functor.mapDerivedCategoryFactorsh
    let kS := g.functor.mapDerivedCategoryFactorsh
    let sH := Functor.mapHomotopyCategoryCompIso s (.up ℤ) ≪≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (e.functor ⋙ L')) (.up ℤ)).symm
    let rH := Functor.mapHomotopyCategoryCompIso r (.up ℤ) ≪≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (g.functor ⋙ U')) (.up ℤ)).symm
    ∃ (LM : DerivedCategory A' ⥤ DerivedCategory B')
      (εM : DerivedCategory.Qh ⋙ LM ⟶ L'.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
      (c : DR.functor ⋙ LM ≅ LS ⋙ DS.functor)
      (d : U.mapDerivedCategory ⋙ DR.functor ≅ DS.functor ⋙ U'.mapDerivedCategory)
      (aM : LM ⊣ U'.mapDerivedCategory),
      LM.IsLeftDerivedFunctor εM (HomotopyCategory.quasiIso A' (.up ℤ)) ∧
      (∀ H : HomotopyCategory A (.up ℤ),
        LM.map (kR.hom.app H) ≫ εM.app ((e.functor.mapHomotopyCategory (.up ℤ)).obj H) =
          c.hom.app (DerivedCategory.Qh.obj H) ≫ DS.functor.map (εS.app H) ≫
            kS.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj H) ≫
            DerivedCategory.Qh.map (sH.hom.app H)) ∧
      (∀ H : HomotopyCategory B (.up ℤ),
        d.hom.app (DerivedCategory.Qh.obj H) =
          DR.functor.map (U.mapDerivedCategoryFactorsh.hom.app H) ≫
            kR.hom.app ((U.mapHomotopyCategory (.up ℤ)).obj H) ≫
            DerivedCategory.Qh.map (rH.hom.app H) ≫
            U'.mapDerivedCategoryFactorsh.inv.app
              ((g.functor.mapHomotopyCategory (.up ℤ)).obj H) ≫
            U'.mapDerivedCategory.map (kS.inv.app H)) ∧
      (∀ H : HomotopyCategory A' (.up ℤ),
        aM.unit.app (DerivedCategory.Qh.obj H) ≫ U'.mapDerivedCategory.map (εM.app H) ≫
          U'.mapDerivedCategoryFactorsh.hom.app ((L'.mapHomotopyCategory (.up ℤ)).obj H) =
        DerivedCategory.Qh.map ((a'.mapHomotopyCategory (.up ℤ)).unit.app H)) ∧
      (∀ K : DerivedCategory A,
        DR.functor.map (aS.unit.app K) ≫ d.hom.app (LS.obj K) =
          aM.unit.app (DR.functor.obj K) ≫ U'.mapDerivedCategory.map (c.hom.app K))  := by
  classical
  dsimp only
  let DR := e.mapDerivedCategory
  let DS := g.mapDerivedCategory
  let : (e.functor.mapHomotopyCategory (.up ℤ)).IsEquivalence := homotopyEquivalence e
  let : (g.functor.mapHomotopyCategory (.up ℤ)).IsEquivalence := homotopyEquivalence g
  let P := (e.functor.mapHomotopyCategory (.up ℤ)).asEquivalence
  let sH := Functor.mapHomotopyCategoryCompIso s (.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (e.functor ⋙ L')) (.up ℤ)).symm
  let f : (L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ⋙ DS.functor ≅
      P.functor ⋙ (L'.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ g.functor.mapDerivedCategoryFactorsh ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight sH DerivedCategory.Qh ≪≫ Functor.associator _ _ _
  let : LS.IsLeftDerivedFunctor εS (HomotopyCategory.quasiIso A (.up ℤ)) := hLS
  let : LS.IsRightKanExtension εS :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension LS εS
      (HomotopyCategory.quasiIso A (.up ℤ))
  obtain ⟨LM, εM, c, hLM, hc⟩ := transportKanExtension P DR DS
    DerivedCategory.Qh DerivedCategory.Qh
    (L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (L'.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    LS εS e.functor.mapDerivedCategoryFactorsh f
  have hLM' : LM.IsLeftDerivedFunctor εM (HomotopyCategory.quasiIso A' (.up ℤ)) := by
    rw [Functor.isLeftDerivedFunctor_iff_isRightKanExtension]
    exact hLM
  have hc' (H : HomotopyCategory A (.up ℤ)) :
      LM.map (e.functor.mapDerivedCategoryFactorsh.hom.app H) ≫
        εM.app ((e.functor.mapHomotopyCategory (.up ℤ)).obj H) =
      c.hom.app (DerivedCategory.Qh.obj H) ≫ DS.functor.map (εS.app H) ≫
        g.functor.mapDerivedCategoryFactorsh.hom.app
          ((L.mapHomotopyCategory (.up ℤ)).obj H) ≫
          DerivedCategory.Qh.map (sH.hom.app H) := by
    simpa [f, P, DR, Functor.asEquivalence, Equivalence.mapDerivedCategory,
      Category.assoc] using hc H
  let : PreservesFiniteLimits (U ⋙ e.functor) := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits (U ⋙ e.functor) := comp_preservesFiniteColimits _ _
  let : PreservesFiniteLimits (g.functor ⋙ U') := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits (g.functor ⋙ U') := comp_preservesFiniteColimits _ _
  let d : U.mapDerivedCategory ⋙ DR.functor ≅ DS.functor ⋙ U'.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso U e.functor).symm ≪≫
      Functor.mapDerivedCategoryNatIso r ≪≫
      Functor.mapDerivedCategoryCompIso g.functor U'
  obtain ⟨aM, hunit⟩ := transportAdjunction DR DS LS U.mapDerivedCategory
    LM U'.mapDerivedCategory aS c d
  let rH := Functor.mapHomotopyCategoryCompIso r (.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (g.functor ⋙ U')) (.up ℤ)).symm
  have hd (H : HomotopyCategory B (.up ℤ)) :
      d.hom.app (DerivedCategory.Qh.obj H) ≫
        U'.mapDerivedCategory.map (g.functor.mapDerivedCategoryFactorsh.hom.app H) ≫
        U'.mapDerivedCategoryFactorsh.hom.app
          ((g.functor.mapHomotopyCategory (.up ℤ)).obj H) =
      DR.functor.map (U.mapDerivedCategoryFactorsh.hom.app H) ≫
        e.functor.mapDerivedCategoryFactorsh.hom.app
          ((U.mapHomotopyCategory (.up ℤ)).obj H) ≫
        DerivedCategory.Qh.map (rH.hom.app H) := by
    apply (cancel_mono (DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso
        (Iso.refl (g.functor ⋙ U')) (.up ℤ)).hom.app H))).1
    simp only [d, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
    rw [Functor.mapDerivedCategoryCompIso_fach,
      Functor.mapDerivedCategoryNatIso_fach]
    rw [← Functor.mapDerivedCategoryCompIso_fach U e.functor]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    simp [rH, homotopyComp_hom U e.functor _ r H, Functor.map_comp, Category.assoc]
    rfl
  have huH (H : HomotopyCategory A (.up ℤ)) :
      (e.functor.mapHomotopyCategory (.up ℤ)).map
          ((a.mapHomotopyCategory (.up ℤ)).unit.app H) ≫
        rH.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj H) ≫
        (U'.mapHomotopyCategory (.up ℤ)).map (sH.hom.app H) =
      (a'.mapHomotopyCategory (.up ℤ)).unit.app
        ((e.functor.mapHomotopyCategory (.up ℤ)).obj H) := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
    change _ = (a'.mapHomotopyCategory (.up ℤ)).unit.app
      ((HomotopyCategory.quotient A' (.up ℤ)).obj
        ((e.functor.mapHomologicalComplex (.up ℤ)).obj K))
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient,
      Adjunction.mapHomotopyCategory_unit_app_quotient]
    dsimp only [rH, sH, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    simp only [Functor.map_comp, Category.assoc]
    change (HomotopyCategory.quotient A' (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient A' (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient A' (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient A' (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient A' (.up ℤ)).map _ =
      (HomotopyCategory.quotient A' (.up ℤ)).map _
    simp only [← Functor.map_comp]
    congr 1
    apply HomologicalComplex.hom_ext
    intro n
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Adjunction.mapHomologicalComplex_unit_app_f,
      Functor.mapHomologicalComplexCompIso_hom_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f,
      Iso.refl_inv, NatTrans.id_app]
    change e.functor.map (a.unit.app (K.X n)) ≫
      r.hom.app (L.obj (K.X n)) ≫ 𝟙 _ ≫
        U'.map (s.hom.app (K.X n) ≫ 𝟙 _) = a'.unit.app (e.functor.obj (K.X n))
    simp only [Category.id_comp, Category.comp_id]
    exact hu (K.X n)
  have hnP (H : HomotopyCategory A (.up ℤ)) :
      aM.unit.app (DerivedCategory.Qh.obj
          ((e.functor.mapHomotopyCategory (.up ℤ)).obj H)) ≫
        U'.mapDerivedCategory.map
          (εM.app ((e.functor.mapHomotopyCategory (.up ℤ)).obj H)) ≫
        U'.mapDerivedCategoryFactorsh.hom.app
          ((L'.mapHomotopyCategory (.up ℤ)).obj
            ((e.functor.mapHomotopyCategory (.up ℤ)).obj H)) =
      DerivedCategory.Qh.map ((a'.mapHomotopyCategory (.up ℤ)).unit.app
        ((e.functor.mapHomotopyCategory (.up ℤ)).obj H)) := by
    dsimp only [DR, DS, Equivalence.mapDerivedCategory, Equivalence.mk] at *
    change U.mapDerivedCategory ⋙ e.functor.mapDerivedCategory ≅
      g.functor.mapDerivedCategory ⋙ U'.mapDerivedCategory at d
    change e.functor.mapDerivedCategory ⋙ LM ≅ LS ⋙ g.functor.mapDerivedCategory at c
    apply (cancel_epi (e.functor.mapDerivedCategoryFactorsh.hom.app H)).1
    have hη := aM.unit.naturality (e.functor.mapDerivedCategoryFactorsh.hom.app H)
    simp only [Functor.id_map, Functor.comp_map] at hη
    erw [reassoc_of% hη]
    erw [← Functor.map_comp_assoc, hc']
    simp only [Functor.map_comp, Category.assoc]
    have hunitH := hunit (DerivedCategory.Qh.obj H)
    change _ = aM.unit.app
      (e.functor.mapDerivedCategory.obj (DerivedCategory.Qh.obj H)) ≫
      U'.mapDerivedCategory.map (c.hom.app (DerivedCategory.Qh.obj H)) at hunitH
    erw [← reassoc_of% hunitH]
    erw [← d.hom.naturality_assoc]
    have hκ := U'.mapDerivedCategoryFactorsh.hom.naturality (sH.hom.app H)
    simp only [Functor.comp_map] at hκ
    erw [hκ]
    erw [reassoc_of% hd ((L.mapHomotopyCategory (.up ℤ)).obj H)]
    erw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    simp only [Category.assoc]
    erw [hn]
    erw [e.functor.mapDerivedCategoryFactorsh.hom.naturality_assoc]
    simp only [Functor.comp_map, Functor.id_obj]
    erw [← Functor.map_comp_assoc, ← Functor.map_comp]
    simpa only [Category.assoc] using congrArg
      (fun t ↦ e.functor.mapDerivedCategoryFactorsh.hom.app H ≫ DerivedCategory.Qh.map t)
      (huH H)
  let τ₁ : DerivedCategory.Qh (C := A') ⟶
      (L'.mapHomotopyCategory (.up ℤ) ⋙ U'.mapHomotopyCategory (.up ℤ)) ⋙
        DerivedCategory.Qh :=
    DerivedCategory.Qh.leftUnitor.inv ≫ Functor.whiskerLeft DerivedCategory.Qh aM.unit ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight εM U'.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ U'.mapDerivedCategoryFactorsh.hom ≫
      (Functor.associator _ _ _).inv
  let τ₂ : DerivedCategory.Qh (C := A') ⟶
      (L'.mapHomotopyCategory (.up ℤ) ⋙ U'.mapHomotopyCategory (.up ℤ)) ⋙
        DerivedCategory.Qh :=
    DerivedCategory.Qh.leftUnitor.inv ≫
      Functor.whiskerRight (a'.mapHomotopyCategory (.up ℤ)).unit DerivedCategory.Qh
  have hτ : τ₁ = τ₂ := by
    apply ((Functor.whiskeringLeft _ _ _).obj P.functor).map_injective
    ext H
    simpa [τ₁, τ₂, P, Functor.asEquivalence, Category.assoc] using hnP H
  refine ⟨LM, εM, c, d, aM, hLM', hc', ?_, ?_, hunit⟩
  · intro H
    let j := U'.mapDerivedCategory.mapIso (g.functor.mapDerivedCategoryFactorsh.app H) ≪≫
      U'.mapDerivedCategoryFactorsh.app ((g.functor.mapHomotopyCategory (.up ℤ)).obj H)
    have hj : d.hom.app (DerivedCategory.Qh.obj H) ≫ j.hom =
        DR.functor.map (U.mapDerivedCategoryFactorsh.hom.app H) ≫
        e.functor.mapDerivedCategoryFactorsh.hom.app
          ((U.mapHomotopyCategory (.up ℤ)).obj H) ≫
        DerivedCategory.Qh.map (rH.hom.app H) := by
      convert hd H using 1
      rfl
    have hh := (Iso.eq_comp_inv j).2 hj
    convert hh using 1 <;> first
      | rfl
      | (simp only [j, Iso.trans_inv, Functor.mapIso_inv, Category.assoc]; rfl)
  · intro H
    simpa [τ₁, τ₂, Category.assoc] using NatTrans.congr_app hτ H

end CategoryTheory
