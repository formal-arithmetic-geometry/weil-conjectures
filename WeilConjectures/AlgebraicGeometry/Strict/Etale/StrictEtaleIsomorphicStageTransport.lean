/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleCoefficientTransportInterfaces
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived

/-!
# Strict étale transport at isomorphic coefficient stages

Source: Zheng, Construction 4.1 and Proposition 2.29(2)
(blueprint: lem-pur-strict-etale-isomorphic-stage-projection).

This is the coefficient-system part of the projection theorem.  It isolates the
construction of the exact transport and its finite-level equivalences from the
compact-support projection assembly.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

private theorem systemHom_ext
    {T : Scheme.{u}} {O : Type (u + 1)} [CommRing O] {ell : O}
    {M N : strictEtaleCoefficientSystem T O ell} (f g : M ⟶ N)
    (h : f.app = g.app) : f = g := by
  cases f
  cases g
  cases h
  rfl

private def scalarRoundTrip {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    restrictScalars.{u + 1} c.hom ⋙ restrictScalars c.inv ≅ 𝟭 _ :=
  pushforwardComp (F := 𝟭 C) (G := 𝟭 C) c.inv c.hom ≪≫
    pushforwardCongr c.inv_hom_id ≪≫ pushforwardId S

private def scalarEquivalence {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R where
  functor := restrictScalars c.hom
  inverse := restrictScalars c.inv
  unitIso := (scalarRoundTrip c).symm
  counitIso := scalarRoundTrip c.symm
  functor_unitIso_comp M := by ext U x; rfl

private def restrictionSquare {C : Type*} [Category C]
    {J : GrothendieckTopology C} {A B D E : Sheaf J RingCat.{u + 1}}
    (f : A ⟶ B) (g : D ⟶ E) (p : D ⟶ A) (q : E ⟶ B) (h : p ≫ f = g ≫ q) :
    restrictScalars.{u + 1} f ⋙ restrictScalars p ≅
      restrictScalars q ⋙ restrictScalars g :=
  pushforwardComp (F := 𝟭 C) (G := 𝟭 C) p f ≪≫ pushforwardCongr h ≪≫
    (pushforwardComp (F := 𝟭 C) (G := 𝟭 C) g q).symm

section Construction
variable {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
  {phi : O →+* O'} {index : ℕ →o ℕ}
  (a : StrictEtaleCoefficientChange O O' ell mu phi index)
  (ha : ∀ n, Function.Bijective (a.ring n))
  {T : Scheme.{u}}
  (PA : StrictEtaleEvaluation T O ell) (PB : StrictEtaleEvaluation T O' mu)

private def stageIso (n : ℕ) :
    coefficientQuotientSheaf (J := T.smallEtaleTopology) O ell (index n) ≅
      coefficientQuotientSheaf (J := T.smallEtaleTopology) O' mu n :=
  (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).mapIso
    (RingEquiv.ofBijective (a.ring n) (ha n)).toCommRingCatIso

private theorem stageSquare {m n : ℕ} (h : n ≤ m) :
    coefficientQuotientMap (J := T.smallEtaleTopology) O ell (index.monotone h) ≫
        a.sheaf T n =
      a.sheaf T m ≫ coefficientQuotientMap (J := T.smallEtaleTopology) O' mu h := by
  change (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).map _ ≫
    (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).map _ =
    (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).map _ ≫
    (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change a.ring n (Ideal.Quotient.mk _ x) =
    Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)) (a.ring m (Ideal.Quotient.mk _ x))
  rw [a.generators, a.generators]
  rfl

private def ringStageIso (n : ℕ) :=
  (sheafCompose T.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
    (stageIso a ha (T := T) n)

private theorem ringStageIso_hom (n : ℕ) :
    (ringStageIso a ha (T := T) n).hom =
      (sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.sheaf T n) := rfl

private def stageExtension (n : ℕ) : strictEtaleLevel T O ell (index n) ⥤
    strictEtaleLevel T O' mu n :=
  (scalarEquivalence (ringStageIso a ha (T := T) n)).inverse

private instance stageExtension_additive (n : ℕ) :
    (stageExtension a ha (T := T) n).Additive :=
  inferInstanceAs (restrictScalars.{u + 1} (ringStageIso a ha (T := T) n).inv).Additive

private def stageTensorIso (n : ℕ) :
    stageExtension a ha (T := T) n ≅ siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n) :=
  Adjunction.leftAdjointUniq
    (scalarEquivalence (ringStageIso a ha (T := T) n)).symm.toAdjunction
    (siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf T n))

private theorem inverseStageSquare {m n : ℕ} (h : n ≤ m) :
    (ringStageIso a ha (T := T) m).inv ≫
        (sheafCompose T.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (coefficientQuotientMap (J := T.smallEtaleTopology) O ell (index.monotone h)) =
      (sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (coefficientQuotientMap (J := T.smallEtaleTopology) O' mu h) ≫
            (ringStageIso a ha (T := T) n).inv := by
  apply (cancel_epi (ringStageIso a ha (T := T) m).hom).1
  apply (cancel_mono (ringStageIso a ha (T := T) n).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.hom_inv_id_assoc]
  rw [ringStageIso_hom, ringStageIso_hom]
  simpa only [Functor.map_comp] using congrArg
    (sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (stageSquare a (T := T) h)

private def stageRestrictionSquare {m n : ℕ} (h : n ≤ m) :
    coefficientRestriction (J := T.smallEtaleTopology) O ell (index.monotone h) ⋙
        stageExtension a ha (T := T) m ≅
      stageExtension a ha (T := T) n ⋙
        coefficientRestriction (J := T.smallEtaleTopology) O' mu h :=
  restrictionSquare
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (coefficientQuotientMap (J := T.smallEtaleTopology) O ell (index.monotone h)))
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (coefficientQuotientMap (J := T.smallEtaleTopology) O' mu h))
    (ringStageIso a ha (T := T) m).inv (ringStageIso a ha (T := T) n).inv
    (inverseStageSquare a ha (T := T) h)

private def stageOrdinary :
    strictEtaleCoefficientSystem T O ell ⥤ strictEtaleCoefficientSystem T O' mu where
  obj M := {
    level := fun n ↦ (stageExtension a ha (T := T) n).obj (M.level (index n))
    transition := fun n ↦
      (stageExtension a ha (T := T) (n + 1)).map
        ((PA.strictTransition (index.monotone (Nat.le_succ n))).app M) ≫
          (stageRestrictionSquare a ha (T := T) (Nat.le_succ n)).hom.app
            (M.level (index n)) }
  map f := {
    app := fun n ↦ (stageExtension a ha (T := T) n).map (f.app (index n))
    comm := by
      intro n
      ext U x
      exact congrArg (fun g ↦ g.val.app U x)
        ((PA.strictTransition (index.monotone (Nat.le_succ n))).naturality f) }
  map_id M := by
    apply systemHom_ext
    funext n
    exact (stageExtension a ha (T := T) n).map_id _
  map_comp f g := by
    apply systemHom_ext
    funext n
    exact (stageExtension a ha (T := T) n).map_comp _ _

private instance stageOrdinary_additive : (stageOrdinary a ha PA).Additive where
  map_add {M N f g} := by
    apply systemHom_ext
    funext n
    calc
      (stageExtension a ha (T := T) n).map ((f + g).app (index n)) =
          (stageExtension a ha (T := T) n).map (f.app (index n) + g.app (index n)) :=
        congrArg (stageExtension a ha (T := T) n).map
          ((coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell)
            (index n)).map_add (f := f) (g := g))
      _ = (stageExtension a ha (T := T) n).map (f.app (index n)) +
          (stageExtension a ha (T := T) n).map (g.app (index n)) :=
        (stageExtension a ha (T := T) n).map_add
      _ = ((stageOrdinary a ha PA).map f + (stageOrdinary a ha PA).map g).app n :=
        ((coefficientEvaluation (J := T.smallEtaleTopology) (O := O') (ell := mu) n).map_add
          (f := (stageOrdinary a ha PA).map f) (g := (stageOrdinary a ha PA).map g)).symm

private def stageEvaluation (n : ℕ) :
    stageOrdinary a ha PA ⋙ coefficientEvaluation
        (J := T.smallEtaleTopology) (O := O') (ell := mu) n ≅
      coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) (index n) ⋙
        stageExtension a ha (T := T) n := Iso.refl _

private theorem evaluation_jointlyReflects :
    JointlyReflectIsomorphisms
      (coefficientEvaluation (J := T.smallEtaleTopology) (O := O') (ell := mu)) where
  isIso {M N} f hf := by
    have hi (n : ℕ) : IsIso (f.app n) := hf n
    let g : N ⟶ M := {
      app := fun n ↦ inv (f.app n)
      comm := by
        intro n
        apply (cancel_epi (f.app (n + 1))).1
        simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
        rw [f.comm, Category.assoc]
        simp only [← Functor.map_comp, IsIso.hom_inv_id]
        rw [(coefficientRestriction (J := T.smallEtaleTopology) O' mu
          (Nat.le_succ n)).map_id]
        exact (Category.comp_id _).symm }
    refine ⟨g, ?_, ?_⟩
    · apply systemHom_ext
      funext n
      exact IsIso.hom_inv_id (f.app n)
    · apply systemHom_ext
      funext n
      exact IsIso.inv_hom_id (f.app n)

private instance stageExtension_isEquivalence (n : ℕ) :
    (stageExtension a ha (T := T) n).IsEquivalence :=
  (scalarEquivalence (ringStageIso a ha (T := T) n)).isEquivalence_inverse

private theorem stageOrdinary_exact :
    PreservesFiniteLimits (stageOrdinary a ha PA) ∧
      PreservesFiniteColimits (stageOrdinary a ha PA) := by
  have hlA (n : ℕ) : PreservesFiniteLimits
      (coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) n) :=
    (coefficientEvaluation_exact (J := T.smallEtaleTopology) (O := O) (ell := ell) n).1
  have hcA (n : ℕ) : PreservesFiniteColimits
      (coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) n) :=
    (coefficientEvaluation_exact (J := T.smallEtaleTopology) (O := O) (ell := ell) n).2
  have hlB (n : ℕ) : PreservesFiniteLimits
      (coefficientEvaluation (J := T.smallEtaleTopology) (O := O') (ell := mu) n) :=
    (coefficientEvaluation_exact (J := T.smallEtaleTopology) (O := O') (ell := mu) n).1
  have hcB (n : ℕ) : PreservesFiniteColimits
      (coefficientEvaluation (J := T.smallEtaleTopology) (O := O') (ell := mu) n) :=
    (coefficientEvaluation_exact (J := T.smallEtaleTopology) (O := O') (ell := mu) n).2
  have hl (n : ℕ) : PreservesFiniteLimits
      (stageOrdinary a ha PA ⋙ coefficientEvaluation
        (J := T.smallEtaleTopology) (O := O') (ell := mu) n) := by
    change PreservesFiniteLimits
      (coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) (index n) ⋙
        stageExtension a ha (T := T) n)
    infer_instance
  have hc (n : ℕ) : PreservesFiniteColimits
      (stageOrdinary a ha PA ⋙ coefficientEvaluation
        (J := T.smallEtaleTopology) (O := O') (ell := mu) n) := by
    change PreservesFiniteColimits
      (coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) (index n) ⋙
        stageExtension a ha (T := T) n)
    infer_instance
  constructor
  · constructor
    intro I _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨(evaluation_jointlyReflects (T := T) (O' := O') (mu := mu)).jointlyReflectsLimit
      (fun n ↦ isLimitOfPreserves
        (stageOrdinary a ha PA ⋙ coefficientEvaluation
          (J := T.smallEtaleTopology) (O := O') (ell := mu) n) hc)⟩
  · constructor
    intro I _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨(evaluation_jointlyReflects (T := T) (O' := O') (mu := mu)).jointlyReflectsColimit
      (fun n ↦ isColimitOfPreserves
        (stageOrdinary a ha PA ⋙ coefficientEvaluation
          (J := T.smallEtaleTopology) (O := O') (ell := mu) n) hc)⟩

include ha in
private theorem stageTensor_isEquivalence (n : ℕ) :
    (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)).IsEquivalence :=
  Functor.isEquivalence_of_iso (stageTensorIso a ha (T := T) n)

include ha in
private theorem stageLevel (n : ℕ) :
    ∃ L : StrictEtaleLevelScalar a T n,
      (∀ K, IsIso (L.counit.app K)) ∧ L.derived.IsEquivalence := by
  let E := siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)
  have : E.IsEquivalence := stageTensor_isEquivalence a ha (T := T) n
  let R := restrictScalars.{u + 1}
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.sheaf T n))
  let c := ringStageIso a ha (T := T) n
  have : R.IsEquivalence := (scalarEquivalence c).isEquivalence_functor
  obtain ⟨_, L, ε, hu, hc, adj, ht⟩ :=
    CategoryTheory.Adjunction.exists_leftDerived_adjunction E R
      (siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf T n)) (fun _ ↦ True)
      (fun K ↦ ⟨K, 𝟙 K, trivial, inferInstance⟩)
      (fun f _ _ hf ↦ by
        let := hf
        infer_instance)
  exact ⟨{
    derived := L
    counit := ε
    isDerived := hu
    computes := fun K _ ↦ hc K trivial
    restriction := R.mapDerivedCategory
    restrictionFactors := R.mapDerivedCategoryFactors
    derivedAdj := adj
    transpose := ht }, fun K ↦ hc K trivial,
      adj.isEquivalence_left_of_isEquivalence_right⟩

private theorem stageTensorIso_unit (n : ℕ)
    (M : strictEtaleLevel T O ell (index n)) :
    siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf T n) M ≫
      (SheafOfModules.toSheaf _).map ((stageTensorIso a ha (T := T) n).inv.app M) =
        𝟙 _ := by
  have h := congrArg (SheafOfModules.toSheaf _).map
    (Adjunction.unit_leftAdjointUniq_hom_app
      (scalarEquivalence (ringStageIso a ha (T := T) n)).symm.toAdjunction
      (siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf T n)) M)
  change (SheafOfModules.toSheaf _).map
    ((stageTensorIso a ha (T := T) n).hom.app M) =
      siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf T n) M at h
  rw [← h, ← Functor.map_comp, Iso.hom_inv_id_app]
  rfl

end Construction

section DerivedSquare
universe a b c d av bv cv dv w
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{w} B]
  {C : Type c} [Category.{cv} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type d} [Category.{dv} D] [Abelian D] [HasDerivedCategory.{w} D]
  (F : A ⥤ B) (eA : A ⥤ C) (eB : B ⥤ D) (L : C ⥤ D)
  [F.Additive] [eA.Additive] [eB.Additive] [L.Additive]
  (FD : DerivedCategory A ⥤ DerivedCategory B)
  (EA : DerivedCategory A ⥤ DerivedCategory C)
  (EB : DerivedCategory B ⥤ DerivedCategory D)
  (LD : DerivedCategory C ⥤ DerivedCategory D)
  (φF : DerivedCategory.Q ⋙ FD ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φA : DerivedCategory.Q ⋙ EA ≅ eA.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φB : DerivedCategory.Q ⋙ EB ≅ eB.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φL : DerivedCategory.Q ⋙ LD ≅ L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (α : F ⋙ eB ≅ eA ⋙ L)

private theorem transportDerivedSquare :
    ∃ δ : FD ⋙ EB ≅ EA ⋙ LD, ∀ P,
      δ.hom.app (DerivedCategory.Q.obj P) ≫ LD.map (φA.hom.app P) ≫
        φL.hom.app ((eA.mapHomologicalComplex (.up ℤ)).obj P) =
      EB.map (φF.hom.app P) ≫ φB.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex α (.up ℤ)).hom.app P) := by
  let ψF : DerivedCategory.Q ⋙ (FD ⋙ EB) ≅
      F.mapHomologicalComplex (.up ℤ) ⋙
        eB.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight φF EB ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ φB
  let ψL : DerivedCategory.Q ⋙ (EA ⋙ LD) ≅
      eA.mapHomologicalComplex (.up ℤ) ⋙
        L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight φA LD ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ φL
  let γ := Functor.mapHomologicalComplexCompIso α (.up ℤ)
  let τ := ψF ≪≫ isoWhiskerRight γ DerivedCategory.Q ≪≫ ψL.symm
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) (DerivedCategory D)
  let δ := ff.preimageIso τ
  refine ⟨δ, ?_⟩
  intro P
  have hd : δ.hom.app (DerivedCategory.Q.obj P) = τ.hom.app P := by
    exact congr_app (ff.map_preimage τ.hom) P
  rw [hd]
  dsimp only [τ, ψF, ψL, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    isoWhiskerRight_inv, isoWhiskerLeft_inv, whiskerRight_app, whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.id_comp, Category.comp_id, Category.assoc,
    ← LD.map_comp_assoc, Iso.inv_hom_id_app]
  erw [LD.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
  rfl
end DerivedSquare

/-- Isomorphic quotient stages admit an exact strict coefficient transport.

Proof: define extension of scalars on each evaluated level using the bijective
ring map, and define the successor arrows by tensor interchange.  The generator
formula for the coefficient change gives the system relations.  Exactness and
the equivalence of each derived level follow from the inverse quotient map;
localization and the universal counits provide the recorded derived and
representative fields.  This is the coefficient-only part of the geometric
construction, before compact-support mates are assembled.
Source: Zheng, Construction 4.1 and Proposition 2.29(2)
(blueprint: lem-pur-strict-etale-isomorphic-stage-transport).
-/
theorem nonempty_strictEtaleCoefficientTransport_of_bijective
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    (_ha : ∀ n, Function.Bijective (a.ring n))
    {T : Scheme.{u}}
    (PA : StrictEtaleEvaluation T O ell) (PB : StrictEtaleEvaluation T O' mu) :
    ∃ U : StrictEtaleCoefficientTransport a T PA PB,
      ∀ n, (U.level n).derived.IsEquivalence := by
  classical
  let F := stageOrdinary a _ha PA
  have : PreservesFiniteLimits F := (stageOrdinary_exact a _ha PA).1
  have : PreservesFiniteColimits F := (stageOrdinary_exact a _ha PA).2
  choose L hL hE using stageLevel a _ha (T := T)
  have hI (n : ℕ) : IsIso (L n).counit := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hL n
  let α (n : ℕ) : F ⋙ coefficientEvaluation
      (J := T.smallEtaleTopology) (O := O') (ell := mu) n ≅
      coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) (index n) ⋙
        siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n) :=
    stageEvaluation a _ha PA n ≪≫
      isoWhiskerLeft _ (stageTensorIso a _ha (T := T) n)
  choose δ hδ using fun n ↦ transportDerivedSquare F
    (coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) (index n))
    (coefficientEvaluation (J := T.smallEtaleTopology) (O := O') (ell := mu) n)
    (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n))
    F.mapDerivedCategory (PA.evaluation (index n)) (PB.evaluation n) (L n).derived
    F.mapDerivedCategoryFactors (PA.evaluationFactors (index n)) (PB.evaluationFactors n)
    (asIso (L n).counit) (α n)
  let U : StrictEtaleCoefficientTransportData a T PA PB := {
    ordinary := F
    evaluation := α
    unit := fun n ↦ (Iso.refl _).hom
    derived := F.mapDerivedCategory
    factors := F.mapDerivedCategoryFactors
    level := L
    derivedEvaluation := δ }
  refine ⟨⟨U, ?_⟩, hE⟩
  refine ⟨⟨inferInstance, inferInstance⟩, ?_, ?_, ?_⟩
  · intro n M
    exact (stageTensorIso_unit a _ha (T := T) n (M.level (index n))).symm
  · intro n M
    ext V x
    rfl
  · intro n K
    exact hδ n K

end AlgebraicGeometry
