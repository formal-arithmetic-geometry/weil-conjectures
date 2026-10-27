/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Sheaf.Algebra.Homology.KFlatTensorQuasiIso
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturality
import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIso
import WeilConjectures.Algebra.Homology.QuasiIsoOfSections
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap

/-!
# Derived Hom computed by a bounded-above projective resolution

Source: Stacks Project, More on Algebra, Tag 0A5W, Lemma 15.75.2;
Derived Categories Tag 06XR (blueprint: lem-sc-derived-hom-projective-resolution).

The ring `A` is the structure ring of the one-point ringed site
(`CochainComplex.onePointRingSheaf A`), so `A`-modules are the sheaves of modules
on that site and `R Hom_A` is the landed `derivedInternalHom` there.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace CategoryTheory

private theorem over_projective {A : Type u} [CommRing A]
    (U : Discrete PUnit.{u + 1}) :
    (SheafOfModules.overFunctor.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A)) U).PreservesProjectiveObjects := by
  let R := (sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (CochainComplex.onePointRingSheaf A)
  let adj := SheafOfModules.overPushforwardOverAdj.{u} (R := R) U
  have hu (M) : IsIso (adj.unit.app M) := by
    rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf R),
      ← isIso_iff_of_reflects_iso _ (sheafToPresheaf ⊥ AddCommGrpCat.{u})]
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    change IsIso (M.val.presheaf.map ((Over.forgetAdjStar U).counit.app V.unop).op)
    infer_instance
  have hc (M) : IsIso (adj.counit.app M) := by
    rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf (R.over U)),
      ← isIso_iff_of_reflects_iso _
        (sheafToPresheaf ((⊥ : GrothendieckTopology (Discrete PUnit.{u + 1})).over U)
          AddCommGrpCat.{u})]
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    have : IsIso ((Over.forgetAdjStar U).unit.app V.unop) := by
      apply isIso_of_reflects_iso _ (Over.forget U)
    change IsIso (M.val.presheaf.map ((Over.forgetAdjStar U).unit.app V.unop).op)
    infer_instance
  have := hu
  have := hc
  have : (SheafOfModules.overFunctor.{u} R U).IsEquivalence :=
    adj.toEquivalence.isEquivalence_functor
  infer_instance

private theorem bijective_of_equiv_square {X Y P Q : Type*}
    (a : X ≃ P) (b : Y ≃ Q) (f : X → Y) (g : P → Q)
    (comm : ∀ x, b (f x) = g (a x)) (hg : Function.Bijective g) :
    Function.Bijective f := by
  constructor
  · intro x y h
    apply a.injective
    apply hg.injective
    exact (comm x).symm.trans ((congrArg b h).trans (comm y))
  · intro y
    obtain ⟨z, hz⟩ := hg.surjective (b y)
    obtain ⟨x, rfl⟩ := a.surjective z
    exact ⟨x, b.injective ((comm x).trans hz)⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
-- Section evaluation and localization comparisons need extra elaboration heartbeats.
private theorem projective_hom_quasiIso {A : Type u} [CommRing A]
    (E : CochainComplex (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A))) ℤ)
    (d : ℤ) [E.IsStrictlyLE d] [∀ n : ℤ, Projective (E.X n)]
    {N N' : CochainComplex (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A))) ℤ}
    (s : N ⟶ N') [QuasiIso s] :
    QuasiIso (((homComplexFunctor (R := CochainComplex.onePointRingSheaf A)).obj
      (op E)).map s) := by
  classical
  let R := CochainComplex.onePointRingSheaf A
  let R₀ := (sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  apply quasiIso_of_sections
  intro U
  have := module_overFunctor_preservesZero R₀ U
  have := over_projective (A := A) U
  let res := (SheafOfModules.overFunctor.{u} R₀ U).mapHomologicalComplex (.up ℤ)
  have : CochainComplex.IsStrictlyLE (res.obj E) d := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (SheafOfModules.overFunctor.{u} R₀ U).map_isZero
      (E.isZero_of_isStrictlyLE d i hi)
  have : ∀ i : ℤ, Projective ((res.obj E).X i) := fun i ↦
    (SheafOfModules.overFunctor.{u} R₀ U).projective_obj_of_projective inferInstance
  have : CochainComplex.IsKProjective (res.obj E) := CochainComplex.isKProjective_of_projective _ d
  have : QuasiIso (res.map s) := localizedModule_restriction_quasiIso R₀ U
    inferInstance s
  let := HasDerivedCategory.standard (SheafOfModules.{u} (R₀.over U))
  let H := HomotopyCategory.quotient (SheafOfModules.{u} (R₀.over U)) (.up ℤ)
  refine ⟨fun n ↦ ?_⟩
  obtain ⟨a, b, hab⟩ := homComplex_sections_homotopy_naturality R U s (𝟙 E) n
  dsimp only [homComplex] at a b
  simp only [op_id, Functor.map_id, NatTrans.id_app, Category.id_comp] at hab
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  have hbij : Function.Bijective (fun g : H.obj (res.obj E) ⟶
      H.obj ((res.obj N)⟦n⟧) ↦
        g ≫ H.map ((shiftFunctor _ n).map (res.map s))) := by
    have : IsIso (DerivedCategory.Qh.map
        (H.map ((shiftFunctor _ n).map (res.map s)))) := by
      have hq : IsIso (DerivedCategory.Q.map
          ((shiftFunctor _ n).map (res.map s))) := by infer_instance
      exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso _)
        ((shiftFunctor _ n).map (res.map s))).2 hq
    have h₁ := CochainComplex.IsKProjective.Qh_map_bijective
      (res.obj E) (H.obj ((res.obj N)⟦n⟧))
    have h₂ := CochainComplex.IsKProjective.Qh_map_bijective
      (res.obj E) (H.obj ((res.obj N')⟦n⟧))
    have h₃ : Function.Bijective
        (fun g : DerivedCategory.Qh.obj (H.obj (res.obj E)) ⟶
          DerivedCategory.Qh.obj (H.obj ((res.obj N)⟦n⟧)) ↦
            g ≫ DerivedCategory.Qh.map
              (H.map ((shiftFunctor _ n).map (res.map s)))) := by
      refine (Function.bijective_iff_has_inverse).2 ⟨fun g ↦ g ≫ inv
        (DerivedCategory.Qh.map (H.map ((shiftFunctor _ n).map (res.map s)))), ?_, ?_⟩
      · intro g; simp
      · intro g; simp
    apply (Function.Bijective.of_comp_iff' h₂ _).mp
    have eq : (DerivedCategory.Qh.map ∘ fun g : H.obj (res.obj E) ⟶
        H.obj ((res.obj N)⟦n⟧) ↦
          g ≫ H.map ((shiftFunctor _ n).map (res.map s))) =
        (fun g ↦ g ≫ DerivedCategory.Qh.map
          (H.map ((shiftFunctor _ n).map (res.map s)))) ∘ DerivedCategory.Qh.map := by
      funext g
      exact DerivedCategory.Qh.map_comp _ _
    rw [eq]
    exact h₃.comp h₁
  exact bijective_of_equiv_square a b _ _ hab hbij

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- Section evaluation and localization comparisons need extra elaboration heartbeats.
/-- A bounded-above complex of projective modules resolving `F` computes
`R Hom_A(F[0], G[0])` by the ordinary Hom complex `Hom^•(E, G[0])`, and hence the
cohomology of that complex in every integer degree.
Source: Stacks Project, More on Algebra, Tag 0A5W, Lemma 15.75.2;
Derived Categories Tag 06XR (blueprint: lem-sc-derived-hom-projective-resolution).

Proof:
1. By `lem-sc-bounded-above-projective-kprojective` (`CochainComplex.isKProjective_of_projective`)
   `E` is K-projective, so `Hom^•(E, -)` sends the quasi-isomorphism `η_{G[0]} : G[0] → I(G[0])`
   of any functorial K-injective replacement to a quasi-isomorphism.
2. Since `I(G[0])` is K-injective and `e` is a quasi-isomorphism, precomposition with `e`,
   `Hom^•(F[0], I(G[0])) → Hom^•(E, I(G[0]))`, is a quasi-isomorphism.
3. By `def-pur-derived-internal-hom` (`derivedInternalHom_comparison`),
   `Q Hom^•(F[0], I(G[0]))` is `R Hom(F[0], G[0])`; composing the localized maps of
   steps 1 and 2 gives the representing isomorphism `c`.
4. Applying `DerivedCategory.homologyFunctor i` to `c` and
   `DerivedCategory.homologyFunctorFactors` gives the identification of cohomology in
   every degree `i : ℤ`. -/
theorem derivedHom_projectiveResolution
    {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A)))]
    (F G : SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A)))
    (E : CochainComplex (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A))) ℤ)
    (d : ℤ) [E.IsStrictlyLE d] [∀ n : ℤ, Projective (E.X n)]
    (e : E ⟶ (HomologicalComplex.single (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A)))
      (ComplexShape.up ℤ) 0).obj F)
    [QuasiIso e] :
    Nonempty (DerivedCategory.Q.obj (homComplex (R := CochainComplex.onePointRingSheaf A) E
        ((HomologicalComplex.single (SheafOfModules.{u}
          ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf A))) (ComplexShape.up ℤ) 0).obj G)) ≅
      (derivedInternalHom ⊥ (CochainComplex.onePointRingSheaf A)).obj
        (op (DerivedCategory.Q.obj ((HomologicalComplex.single (SheafOfModules.{u}
          ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf A))) (ComplexShape.up ℤ) 0).obj F)),
          DerivedCategory.Q.obj ((HomologicalComplex.single (SheafOfModules.{u}
            ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (CochainComplex.onePointRingSheaf A))) (ComplexShape.up ℤ) 0).obj G))) ∧
    (∀ (I : CochainComplex (SheafOfModules.{u}
        ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (CochainComplex.onePointRingSheaf A))) ℤ ⥤
        CochainComplex (SheafOfModules.{u}
          ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf A))) ℤ)
      (η : 𝟭 (CochainComplex (SheafOfModules.{u}
        ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (CochainComplex.onePointRingSheaf A))) ℤ) ⟶ I),
      (∀ N : CochainComplex (SheafOfModules.{u}
          ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf A))) ℤ,
        QuasiIso (η.app N) ∧ (I.obj N).IsKInjective) →
        IsIso (DerivedCategory.Q.map
          (((homComplexFunctor (R := CochainComplex.onePointRingSheaf A)).obj (op E)).map
            (η.app ((HomologicalComplex.single (SheafOfModules.{u}
              ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
                (CochainComplex.onePointRingSheaf A))) (ComplexShape.up ℤ) 0).obj G)))) ∧
        IsIso (DerivedCategory.Q.map
          (((homComplexFunctor (R := CochainComplex.onePointRingSheaf A)).map e.op).app
            (I.obj ((HomologicalComplex.single (SheafOfModules.{u}
              ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
                (CochainComplex.onePointRingSheaf A))) (ComplexShape.up ℤ) 0).obj G))))) ∧
    ∀ i : ℤ, Nonempty
      ((HomologicalComplex.homologyFunctor (SheafOfModules.{u}
          ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf A))) (ComplexShape.up ℤ) i).obj
        (homComplex (R := CochainComplex.onePointRingSheaf A) E
          ((HomologicalComplex.single (SheafOfModules.{u}
            ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (CochainComplex.onePointRingSheaf A))) (ComplexShape.up ℤ) 0).obj G)) ≅
      (DerivedCategory.homologyFunctor (SheafOfModules.{u}
          ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf A))) i).obj
        ((derivedInternalHom ⊥ (CochainComplex.onePointRingSheaf A)).obj
          (op (DerivedCategory.Q.obj ((HomologicalComplex.single (SheafOfModules.{u}
            ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (CochainComplex.onePointRingSheaf A))) (ComplexShape.up ℤ) 0).obj F)),
            DerivedCategory.Q.obj ((HomologicalComplex.single (SheafOfModules.{u}
              ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
                (CochainComplex.onePointRingSheaf A))) (ComplexShape.up ℤ) 0).obj G)))) := by
  let R := CochainComplex.onePointRingSheaf A
  let B := SheafOfModules.{u}
    ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  let F₀ := (HomologicalComplex.single B (.up ℤ) 0).obj F
  let G₀ := (HomologicalComplex.single B (.up ℤ) 0).obj G
  have hmaps (I : CochainComplex B ℤ ⥤ CochainComplex B ℤ)
      (η : 𝟭 _ ⟶ I) (hI : ∀ N, QuasiIso (η.app N) ∧ (I.obj N).IsKInjective) :
      IsIso (DerivedCategory.Q.map
        (((homComplexFunctor (R := R)).obj (op E)).map (η.app G₀))) ∧
      IsIso (DerivedCategory.Q.map
        (((homComplexFunctor (R := R)).map e.op).app (I.obj G₀))) := by
    have : QuasiIso (η.app G₀) := (hI G₀).1
    have : (I.obj G₀).IsKInjective := (hI G₀).2
    constructor
    · have := projective_hom_quasiIso E d (η.app G₀)
      infer_instance
    · have : QuasiIso (((homComplexFunctor (R := R)).map e.op).app (I.obj G₀)) := by
        simpa using quasiIso_homComplex_map (𝟙 (I.obj G₀)) e
      infer_instance
  have : IsGrothendieckAbelian.{u} B := SheafOfModules.isGrothendieckAbelian _
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} B
  let η := CochainComplex.toKInjectiveResolution.{u} B
  have hI (N) : QuasiIso (η.app N) ∧ (I.obj N).IsKInjective :=
    ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} B N).2,
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} B N⟩
  obtain ⟨hc₁, hc₂⟩ := hmaps I η hI
  obtain ⟨c₀⟩ := derivedInternalHom_comparison ⊥ R I η hI
  let c := asIso (DerivedCategory.Q.map
      (((homComplexFunctor (R := R)).obj (op E)).map (η.app G₀))) ≪≫
    (asIso (DerivedCategory.Q.map
      (((homComplexFunctor (R := R)).map e.op).app (I.obj G₀)))).symm ≪≫
    (c₀.app (op F₀, G₀)).symm
  refine ⟨⟨c⟩, hmaps, fun i ↦ ?_⟩
  exact ⟨((DerivedCategory.homologyFunctorFactors B i).app _).symm ≪≫
    (DerivedCategory.homologyFunctor B i).mapIso c⟩


end CategoryTheory
