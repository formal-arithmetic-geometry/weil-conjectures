/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import
  WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# Counits in an exact square of derived adjunctions

Source: Stacks Project, Derived Categories, Tags 09T5 and 070Y; exact-square extraction
of tower normalization, steps 6--8 (blueprint: lem-weil-pbc-exact-square-derived-counit).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uA uAp uB uBp vA vAp vB vBp wA wAp wB wBp

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A : Type uA} {Ap : Type uAp} {B : Type uB} {Bp : Type uBp}
  [Category.{vA} A] [Category.{vAp} Ap] [Category.{vB} B] [Category.{vBp} Bp]
  [Abelian A] [Abelian Ap] [Abelian B] [Abelian Bp]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wAp} Ap]
  [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wBp} Bp]

/-- The Hom formula specifying the derived adjunction on the fixed functors and fixed
right-derived unit, for every chain map. Source: Stacks Tag 09T5, with Tag 070Y
(blueprint: lem-weil-pbc-exact-square-derived-counit). -/
def Adjunction.HasExactDerivedHomFormula
    (F : B ⥤ A) (G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    (d : F.mapDerivedCategory ⊣ RG) : Prop :=
  ∀ (M : CochainComplex B ℤ) (I : CochainComplex A ℤ)
    (f : (F.mapHomologicalComplex (.up ℤ)).obj M ⟶ I),
    d.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
        (F.mapDerivedCategoryFactors.hom.app M ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv M I f) ≫ η.app I

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

-- Adjoining a contractible summand makes a resolution monomorphic without changing
-- its homotopy type. No degreewise injectivity or enough-injectives assumption is used.
omit [HasDerivedCategory A] in
private theorem strongResolutions
    (h : ∀ K : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (q : K ⟶ I), I.IsKInjective ∧ QuasiIso q) :
    Abelian.HasKInjectiveResolutions A := by
  constructor
  intro K
  obtain ⟨I, q, hI, hq⟩ := h K
  let T := CochainComplex.mappingCone (𝟙 K)
  let c : K ⟶ T := CochainComplex.mappingCone.inr (𝟙 K)
  let j : K ⟶ T ⊞ I := biprod.lift c q
  let p : T ⊞ I ⟶ I := biprod.snd
  let e : HomotopyEquiv (T ⊞ I) I :=
    { hom := p
      inv := biprod.inr
      homotopyHomInvId := by
        let h₀ : Homotopy (𝟙 T) 0 :=
          CochainComplex.mappingCone.liftHomotopy _ _ _
            (CochainComplex.mappingCone.snd _) 0 (by simp) (by simp)
        let h₁ := (h₀.compRight (biprod.inl : T ⟶ T ⊞ I)).compLeft
          (biprod.fst : T ⊞ I ⟶ T)
        let h₂ := Homotopy.add h₁ (Homotopy.refl
          ((biprod.snd : T ⊞ I ⟶ I) ≫ biprod.inr))
        exact (Homotopy.ofEq (by simp [p])).trans
          (h₂.symm.trans (Homotopy.ofEq (by simp)))
      homotopyInvHomId := Homotopy.ofEq (by simp [p]) }
  have hTI : (T ⊞ I).IsKInjective := e.symm.isKInjective
  have hp : QuasiIso p := e.quasiIso_hom
  have hjp : j ≫ p = q := by simp [j, p]
  have hj : QuasiIso j := by
    have : QuasiIso (j ≫ p) := by rw [hjp]; infer_instance
    exact quasiIso_of_comp_right j p
  have hmono : Mono j := by
    apply HomologicalComplex.mono_of_mono_f
    intro n
    apply mono_of_mono_fac (show j.f n ≫
      (biprod.fst : T ⊞ I ⟶ T).f n ≫
        (CochainComplex.mappingCone.snd (𝟙 K)).v n n (add_zero n) = 𝟙 _ by
      simp [j, c, T])
  exact ⟨T ⊞ I, hTI, j, hmono, hj⟩

omit [HasDerivedCategory A] in
private theorem kInjectiveDerives (G : A ⥤ B) [G.Additive] :
    (CochainComplex.KInjectives.localizerMorphism A).Derives
      (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
  intro X Y f hf
  have hX : X.obj.IsKInjective := X.property
  have hY : Y.obj.IsKInjective := Y.property
  have hq : QuasiIso f.hom := hf
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp hq
  have : QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map f.hom) := by
    rw [← he]
    exact (G.mapHomotopyEquiv e).quasiIso_hom
  change IsIso (DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map f.hom))
  infer_instance

-- K-injectives compute the fixed universal pair, so any postcomposition is again derived.
private theorem rightAbsolute
    (h : ∀ K : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (q : K ⟶ I), I.IsKInjective ∧ QuasiIso q)
    (G : A ⥤ B) [G.Additive]
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    (hRG : RG.IsRightDerivedFunctor η (HomologicalComplex.quasiIso A (.up ℤ)))
    {T : Type*} [Category T] (L : DerivedCategory B ⥤ T) :
    (RG ⋙ L).IsRightDerivedFunctor
      (Functor.whiskerRight η L ≫ (Functor.associator _ _ _).hom)
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
  let := strongResolutions h
  let := hRG
  exact (CochainComplex.KInjectives.localizerMorphism A)
    |>.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure η
      (fun I ↦ (kInjectiveDerives G).isIso_of_isRightDerivedFunctor η I) L

private theorem normalizedExists
    (h : ∀ K : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (q : K ⟶ I), I.IsKInjective ∧ QuasiIso q)
    (F : B ⥤ A) (G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    (hRG : RG.IsRightDerivedFunctor η (HomologicalComplex.quasiIso A (.up ℤ))) :
    ∃ d : F.mapDerivedCategory ⊣ RG,
      Adjunction.HasExactDerivedHomFormula F G adj RG η d := by
  let := hRG
  let := rightAbsolute h G RG η hRG F.mapDerivedCategory
  let φ := F.mapDerivedCategoryFactors
  have hL : F.mapDerivedCategory.IsLeftDerivedFunctor φ.hom
      (HomologicalComplex.quasiIso B (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ φ
  let := hL
  have hLR : (F.mapDerivedCategory ⋙ RG).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight φ.hom RG)
      (HomologicalComplex.quasiIso B (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight φ RG)
  let := hLR
  let ac := adj.mapHomologicalComplex (.up ℤ)
  let d := ac.derived (HomologicalComplex.quasiIso B (.up ℤ))
    (HomologicalComplex.quasiIso A (.up ℤ)) φ.hom η
  refine ⟨d, ?_⟩
  intro M I f
  change d.unit.app _ ≫ RG.map (φ.hom.app M ≫ DerivedCategory.Q.map f) = _
  rw [RG.map_comp, ← Category.assoc]
  have hu := ac.derivedη_fac_app (HomologicalComplex.quasiIso B (.up ℤ)) φ.hom η M
  change d.unit.app _ ≫ RG.map (φ.hom.app M) = _ at hu
  have hn := η.naturality f
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [hu, Category.assoc, ← hn, ← DerivedCategory.Q.map_comp_assoc]
  rfl

private theorem normalizedCounit
    (F : B ⥤ A) (G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    (d : F.mapDerivedCategory ⊣ RG)
    (hd : Adjunction.HasExactDerivedHomFormula F G adj RG η d)
    (I : CochainComplex A ℤ) :
    F.mapDerivedCategory.map (η.app I) ≫ d.counit.app (DerivedCategory.Q.obj I) =
      F.mapDerivedCategoryFactors.hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app I) := by
  have he := hd _ I ((adj.mapHomologicalComplex (.up ℤ)).counit.app I)
  have hid : (adj.mapHomologicalComplex (.up ℤ)).homEquiv _ I
      ((adj.mapHomologicalComplex (.up ℤ)).counit.app I) = 𝟙 _ :=
    (adj.mapHomologicalComplex (.up ℤ)).right_triangle_components I
  rw [hid,
    DerivedCategory.Q.map_id, Category.id_comp] at he
  have he' := congrArg (d.homEquiv _ _).symm he
  simpa only [Equiv.symm_apply_apply, Adjunction.homEquiv_symm_apply] using he'.symm

private theorem normalizedUnique
    (h : ∀ K : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (q : K ⟶ I), I.IsKInjective ∧ QuasiIso q)
    (F : B ⥤ A) (G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    (hRG : RG.IsRightDerivedFunctor η (HomologicalComplex.quasiIso A (.up ℤ)))
    (e d : F.mapDerivedCategory ⊣ RG)
    (he : Adjunction.HasExactDerivedHomFormula F G adj RG η e)
    (hd : Adjunction.HasExactDerivedHomFormula F G adj RG η d) : e = d := by
  let := rightAbsolute h G RG η hRG F.mapDerivedCategory
  apply Adjunction.ext_counit
  apply (RG ⋙ F.mapDerivedCategory).rightDerived_ext
    (Functor.whiskerRight η F.mapDerivedCategory ≫ (Functor.associator _ _ _).hom)
    (HomologicalComplex.quasiIso A (.up ℤ))
  ext I
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.comp_id]
  exact (normalizedCounit F G adj RG η e he I).trans
    (normalizedCounit F G adj RG η d hd I).symm

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem squareFactors
    (Fp : Bp ⥤ Ap) (F : B ⥤ A) (r : Ap ⥤ A) (s : Bp ⥤ B)
    [Fp.Additive] [F.Additive] [r.Additive] [s.Additive]
    [PreservesFiniteLimits Fp] [PreservesFiniteColimits Fp]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    (hF : Fp ⋙ r = s ⋙ F) (K : CochainComplex Bp ℤ) :
    (Functor.mapDerivedCategorySquareIso (eqToIso hF)).hom.app (DerivedCategory.Q.obj K) ≫
        F.mapDerivedCategory.map (s.mapDerivedCategoryFactors.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app ((s.mapHomologicalComplex (.up ℤ)).obj K) =
      r.mapDerivedCategory.map (Fp.mapDerivedCategoryFactors.hom.app K) ≫
        r.mapDerivedCategoryFactors.hom.app ((Fp.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (eqToIso hF) (.up ℤ)).hom.app K) := by
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso Fp r).hom.app
    (DerivedCategory.Q.obj K))).mp
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [← Category.assoc]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac,
    Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  simp only [Iso.hom_inv_id_app_assoc]
  rfl

/-- Exact-square compatibility of canonically normalized derived adjunction counits.
Source: Stacks Tags 09T5 (lemma-derived-adjoint-functors) and 070Y
(lemma-K-injective-defined); exact-square extraction of tower normalization steps 6--8
(blueprint: lem-weil-pbc-exact-square-derived-counit).

Proof plan:
1. Use lem-weil-pbc-termwise-adjunction-homotopy for the termwise adjunctions.
   Exactness gives the canonical factorizations and universal left-derived pairs by
   lem-weil-pbc-exact-functor-derived-factorization and
   lem-weil-pbc-exact-functor-derived-functor. Apply
   lem-sfb-resolving-derived-adjunction-normalization with the whole homotopy category
   as resolving class. Work in a common ambient universe for the chosen Hom sets.
   This constructs the two adjunctions on the independently fixed right-derived pairs,
   with the displayed Hom formulas for every chain map.
2. Substitute the ordinary counit for f in the Hom formula. Its ordinary transpose is
   the identity, so inverse derived transposition gives the two counit normalizations.
3. The fixed right-derived units are invertible on K-injectives by
   def-sfb-right-derived-functor. Cancelling their left-adjoint images determines the
   counits there. Every derived object is isomorphic to such a representative by the
   resolution hypotheses and def-weil-abstract-derived-category. Naturality determines
   the counits everywhere, and hence both adjunctions uniquely from their Hom formulas.
4. At QJ for J K-injective, precompose both proposed square arrows with
   D(F)(D(s)(eta'_J)). This is invertible. The first composite is the localization of
   r applied to the ordinary primed counit, hence of the unprimed counit by hε.
   For the second use hβ and the unprimed counit normalization; rJ is K-injective by hr.
   Cancel this common invertible precomposition.
5. Both square arrows are natural. Transport their equality from QJ to any derived
   object using an isomorphism to a K-injective representative and cancel its image
   under D(r). Only hβ on K-injectives enters this calculation. -/
theorem exactSquare_derived_counit
    (hA : ∀ K : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (q : K ⟶ I), I.IsKInjective ∧ QuasiIso q)
    (hAp : ∀ K : CochainComplex Ap ℤ,
      ∃ (J : CochainComplex Ap ℤ) (q : K ⟶ J), J.IsKInjective ∧ QuasiIso q)
    (Fp : Bp ⥤ Ap) (Gp : Ap ⥤ Bp) (F : B ⥤ A) (G : A ⥤ B)
    [Fp.Additive] [Gp.Additive] [F.Additive] [G.Additive]
    [PreservesFiniteLimits Fp] [PreservesFiniteColimits Fp]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (adjp : Fp ⊣ Gp) (adj : F ⊣ G)
    (r : Ap ⥤ A) (s : Bp ⥤ B) [r.Additive] [s.Additive]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    (hF : Fp ⋙ r = s ⋙ F) (hG : Gp ⋙ s = r ⋙ G)
    (hε : ∀ X : Ap, r.map (adjp.counit.app X) =
      (eqToIso hF).hom.app (Gp.obj X) ≫ F.map ((eqToIso hG).hom.app X) ≫
        adj.counit.app (r.obj X))
    (hr : ∀ J : CochainComplex Ap ℤ, J.IsKInjective →
      CochainComplex.IsKInjective ((r.mapHomologicalComplex (.up ℤ)).obj J))
    (RGp : DerivedCategory Ap ⥤ DerivedCategory Bp)
    (ηp : Gp.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RGp)
    (hRGp : RGp.IsRightDerivedFunctor ηp (HomologicalComplex.quasiIso Ap (.up ℤ)))
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    (hRG : RG.IsRightDerivedFunctor η (HomologicalComplex.quasiIso A (.up ℤ)))
    (β : RGp ⋙ s.mapDerivedCategory ≅ r.mapDerivedCategory ⋙ RG)
    (hβ : ∀ J : CochainComplex Ap ℤ, J.IsKInjective →
      s.mapDerivedCategory.map (ηp.app J) ≫ β.hom.app (DerivedCategory.Q.obj J) ≫
          RG.map (r.mapDerivedCategoryFactors.hom.app J) =
        s.mapDerivedCategoryFactors.hom.app
            ((Gp.mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (eqToIso hG) (.up ℤ)).hom.app J) ≫
          η.app ((r.mapHomologicalComplex (.up ℤ)).obj J)) :
    ∃ (dp : Fp.mapDerivedCategory ⊣ RGp) (d : F.mapDerivedCategory ⊣ RG),
      Adjunction.HasExactDerivedHomFormula Fp Gp adjp RGp ηp dp ∧
      Adjunction.HasExactDerivedHomFormula F G adj RG η d ∧
      (∀ ep : Fp.mapDerivedCategory ⊣ RGp,
        Adjunction.HasExactDerivedHomFormula Fp Gp adjp RGp ηp ep → ep = dp) ∧
      (∀ e : F.mapDerivedCategory ⊣ RG,
        Adjunction.HasExactDerivedHomFormula F G adj RG η e → e = d) ∧
      (∀ I : CochainComplex A ℤ, I.IsKInjective →
        F.mapDerivedCategory.map (η.app I) ≫ d.counit.app (DerivedCategory.Q.obj I) =
          F.mapDerivedCategoryFactors.hom.app
              ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
            DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app I)) ∧
      (∀ J : CochainComplex Ap ℤ, J.IsKInjective →
        Fp.mapDerivedCategory.map (ηp.app J) ≫ dp.counit.app (DerivedCategory.Q.obj J) =
          Fp.mapDerivedCategoryFactors.hom.app
              ((Gp.mapHomologicalComplex (.up ℤ)).obj J) ≫
            DerivedCategory.Q.map ((adjp.mapHomologicalComplex (.up ℤ)).counit.app J)) ∧
      (∀ N : DerivedCategory Ap,
        r.mapDerivedCategory.map (dp.counit.app N) =
          (Functor.mapDerivedCategorySquareIso (eqToIso hF)).hom.app (RGp.obj N) ≫
            F.mapDerivedCategory.map (β.hom.app N) ≫
            d.counit.app (r.mapDerivedCategory.obj N)) := by
  obtain ⟨dp, hdp⟩ := normalizedExists hAp Fp Gp adjp RGp ηp hRGp
  obtain ⟨d, hd⟩ := normalizedExists hA F G adj RG η hRG
  have hc (I : CochainComplex A ℤ) (_ : I.IsKInjective) :=
    normalizedCounit F G adj RG η d hd I
  have hcp := normalizedCounit Fp Gp adjp RGp ηp dp hdp
  refine ⟨dp, d, hdp, hd, ?_, ?_, fun I hI ↦ hc I hI, fun J _ ↦ hcp J, ?_⟩
  · intro ep hep
    exact normalizedUnique hAp Fp Gp adjp RGp ηp hRGp ep dp hep hdp
  · intro e he
    exact normalizedUnique hA F G adj RG η hRG e d he hd
  · let α := Functor.mapDerivedCategorySquareIso (eqToIso hF)
    let L : RGp ⋙ Fp.mapDerivedCategory ⋙ r.mapDerivedCategory ⟶ r.mapDerivedCategory :=
      Functor.whiskerRight dp.counit r.mapDerivedCategory
    let R : RGp ⋙ Fp.mapDerivedCategory ⋙ r.mapDerivedCategory ⟶ r.mapDerivedCategory :=
      Functor.whiskerLeft RGp α.hom ≫ Functor.whiskerRight β.hom F.mapDerivedCategory ≫
        Functor.whiskerLeft r.mapDerivedCategory d.counit
    have hJ (J : CochainComplex Ap ℤ) (hJ : J.IsKInjective) :
        L.app (DerivedCategory.Q.obj J) = R.app (DerivedCategory.Q.obj J) := by
      let := strongResolutions hAp
      let := hRGp
      have hi : IsIso (ηp.app J) :=
        (kInjectiveDerives Gp).isIso_of_isRightDerivedFunctor ηp
          (CochainComplex.KInjectives.mk J)
      apply (cancel_epi (r.mapDerivedCategory.map
        (Fp.mapDerivedCategory.map (ηp.app J)))).mp
      apply (cancel_mono (r.mapDerivedCategoryFactors.hom.app J)).mp
      change (r.mapDerivedCategory.map (Fp.mapDerivedCategory.map (ηp.app J)) ≫
        r.mapDerivedCategory.map (dp.counit.app (DerivedCategory.Q.obj J))) ≫ _ =
        (r.mapDerivedCategory.map (Fp.mapDerivedCategory.map (ηp.app J)) ≫
          α.hom.app (RGp.obj (DerivedCategory.Q.obj J)) ≫
          F.mapDerivedCategory.map (β.hom.app (DerivedCategory.Q.obj J)) ≫
          d.counit.app (r.mapDerivedCategory.obj (DerivedCategory.Q.obj J))) ≫ _
      rw [← Functor.map_comp, hcp J, Functor.map_comp, Category.assoc]
      erw [r.mapDerivedCategoryFactors.hom.naturality
        ((adjp.mapHomologicalComplex (.up ℤ)).counit.app J)]
      have hn := α.hom.naturality (ηp.app J)
      dsimp only [Functor.comp_map, Functor.comp_obj] at hn
      have hcounit := d.counit.naturality (r.mapDerivedCategoryFactors.hom.app J)
      dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hcounit
      simp only [Category.assoc]
      rw [reassoc_of% hn, ← hcounit]
      simp only [← Functor.map_comp_assoc]
      rw [hβ J hJ]
      simp only [Functor.map_comp, Category.assoc]
      rw [hc _ (hr J hJ)]
      erw [reassoc_of% (F.mapDerivedCategoryFactors.hom.naturality
        ((NatIso.mapHomologicalComplex (eqToIso hG) (.up ℤ)).hom.app J))]
      erw [reassoc_of% (squareFactors Fp F r s hF
        ((Gp.mapHomologicalComplex (.up ℤ)).obj J))]
      simp only [← DerivedCategory.Q.map_comp]
      congr 2
      apply DerivedCategory.Q.congr_map
      ext n
      exact hε (J.X n)
    intro N
    obtain ⟨J, q, hJi, hq⟩ := hAp (DerivedCategory.Q.objPreimage N)
    let := hq
    let e : N ≅ DerivedCategory.Q.obj J :=
      (DerivedCategory.Q.objObjPreimageIso N).symm ≪≫ asIso (DerivedCategory.Q.map q)
    have he := hJ J hJi
    change L.app N = R.app N
    apply (cancel_mono (r.mapDerivedCategory.map e.hom)).mp
    rw [← L.naturality, ← R.naturality, he]

end CategoryTheory
