/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.Paper.CompletedConstantRealizationData
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import Mathlib.CategoryTheory.Limits.Final
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Derived quotient towers from K-flat invariance

Source: Stacks Tags 06XN, 06YT and 06YU.
(blueprint: lem-weil-pbc-completed-constant-derived-tensor-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v w u' v'
open CategoryTheory CategoryTheory.Limits Opposite

-- A full, essentially surjective functor is initial: every comma object maps
-- to a fixed lift of the target, giving a zigzag between any two objects.
private theorem initial_of_full_essSurj
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B) [F.Full] [F.EssSurj] :
    F.Initial := by
  classical
  constructor
  intro Y
  let e := F.objObjPreimageIso Y
  let Z : CostructuredArrow F Y := CostructuredArrow.mk e.hom
  have lift (X : CostructuredArrow F Y) : Nonempty (X ⟶ Z) := by
    refine ⟨CostructuredArrow.homMk (F.preimage (X.hom ≫ e.inv)) ?_⟩
    simp [Z, e]
  let : Nonempty (CostructuredArrow F Y) := ⟨Z⟩
  apply zigzag_isConnected
  intro X X'
  exact (Zigzag.of_hom (lift X).some).trans (Zigzag.of_inv (lift X').some)

-- The induced functor on structured arrows is also full and essentially
-- surjective, so restricting the defining limit cone preserves its limit.
private noncomputable def pointwise_precomp_full
    {A C D H : Type*} [Category A] [Category C] [Category D] [Category H]
    (P : A ⥤ C) [P.Full] [P.EssSurj] (Q : C ⥤ D) (F : C ⥤ H) (L : D ⥤ H)
    (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      ((Functor.associator P Q L).hom ≫ Functor.whiskerLeft P α)).IsPointwiseRightKanExtension := by
  intro Y
  let p := StructuredArrow.pre Y P Q
  let : p.Initial := initial_of_full_essSurj p
  apply Limits.IsLimit.ofIsoLimit ((Functor.Initial.isLimitWhiskerEquiv p _).symm (h Y))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, p]
  simp

-- Transport the defining limit cone through an equivalence of structured
-- arrow categories and the prescribed isomorphism of diagram functors.
private noncomputable def pointwise_change_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {Q Q' : C ⥤ D} {F F' : C ⥤ H} (L : D ⥤ H)
    (i : Q ≅ Q') (j : F ≅ F') (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      (Functor.whiskerRight i.inv L ≫ α ≫ j.hom)).IsPointwiseRightKanExtension := by
  intro Y
  let Φ : StructuredArrow Y Q' ≌ StructuredArrow Y Q := Comma.mapRightIso _ i.symm
  let k : Φ.functor ⋙ StructuredArrow.proj Y Q ⋙ F ≅
      StructuredArrow.proj Y Q' ⋙ F' :=
    NatIso.ofComponents (fun X ↦ j.app X.right) (by
      intro X X' f
      exact j.hom.naturality f.right)
  apply Limits.IsLimit.ofIsoLimit
    ((Limits.IsLimit.postcomposeHomEquiv k _).symm ((h Y).whiskerEquivalence Φ))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, Φ, k]
  simp [Category.assoc]
  rfl

private theorem resolving_class_left_derived
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (D : Type u') [Category.{v'} D]
    (F : HomotopyCategory A (.up ℤ) ⥤ D)
    (P : Set (HomotopyCategory A (.up ℤ)))
    (hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : HomotopyCategory A (.up ℤ)) (s : Y ⟶ X),
        Y ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s)
    (hinv : ∀ (X Y : HomotopyCategory A (.up ℤ)) (s : X ⟶ Y),
      X ∈ P → Y ∈ P → HomotopyCategory.quasiIso A (.up ℤ) s → IsIso (F.map s)) :
    F.HasPointwiseLeftDerivedFunctor (HomotopyCategory.quasiIso A (.up ℤ)) ∧
      ∃ (L : DerivedCategory A ⥤ D) (ε : DerivedCategory.Qh ⋙ L ⟶ F),
        L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)) ∧
        ∀ X, X ∈ P → IsIso (ε.app X) := by
  classical
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  let Q := DerivedCategory.Qh (C := A)
  obtain ⟨hleft, hright, htri, hsat, htwo, _, _, _, _⟩ :=
    HomotopyCategory.quasiIso_saturated_triangulated A
  let : W.HasRightCalculusOfFractions := hright
  let : W.HasTwoOutOfThreeProperty := htwo
  have hwitness := Functor.resolvingClass_essentialConstancy W F P hres hinv
  have hpw : F.HasPointwiseLeftDerivedFunctor W := by
    intro X
    obtain ⟨Y, u, hc, hr, _⟩ := hwitness X
    have hb := leftDerived_defined_pointwiseKan_bridge W Q F X Y hc u hr
    exact (F.hasPointwiseLeftDerivedFunctorAt_iff Q W X).2 hb.1
  let : F.HasPointwiseLeftDerivedFunctor W := hpw
  let LF := F.totalLeftDerived Q W
  let ε := F.totalLeftDerivedCounit Q W
  have hLF : LF.IsLeftDerivedFunctor ε W := inferInstance
  refine ⟨hpw, LF, ε, hLF, ?_⟩
  · intro X hX
    obtain ⟨Y, u, hc, hr, hu⟩ := hwitness X
    obtain ⟨_, π, ⟨hπ⟩, _, hidentity⟩ :=
      leftDerived_defined_pointwiseKan_bridge W Q F X Y hc u hr
    let hcanonical :=
      Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor LF ε W (Q.obj X)
    let e := hcanonical.conePointUniqueUpToIso hπ
    have hid : W (𝟙 X) := W.id_mem X
    have : IsIso (u.app (⟨Over.mk (𝟙 X), hid⟩ : W.Over ⊤ X)) := hu hid hX
    have : IsIso (π.app (StructuredArrow.mk (𝟙 (Q.obj X)))) := by
      rw [hidentity hid]
      infer_instance
    have he := hcanonical.conePointUniqueUpToIso_hom_comp hπ
      (StructuredArrow.mk (𝟙 (Q.obj X)))
    have he' : e.hom ≫ π.app (StructuredArrow.mk (𝟙 (Q.obj X))) = ε.app X := by
      simpa [Functor.RightExtension.coneAt] using he
    rw [← he']
    infer_instance

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

namespace SheafOfModules
open AlgebraicGeometry.Scheme
-- K-flatness kills the tensor of an acyclic mapping cone.
set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
private theorem tensor_right_quasiIso
    (X : AlgebraicGeometry.Scheme.{u})
    {R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1}}
    {E E' K : CochainComplex (completedConstantModules X R) ℤ} (α : E ⟶ E')
    (hα : QuasiIso α) (hK : K.IsKFlatIndependentCoefficients) :
    QuasiIso (((completedConstantTensor X R).map α).app K) := by
  let := monoidalCategory R
  let := SheafOfModules.cochainModulesPreadditive R
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (CochainComplex.mappingCone α) hc
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht i).of_iso
    (CochainComplex.mapBifunctorMappingCone₁Iso α K
      (MonoidalCategory.curriedTensor (completedConstantModules X R)))

-- The module braiding and signed total-complex flip give the other tensor order.
set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
private theorem tensor_left_quasiIso
    (X : AlgebraicGeometry.Scheme.{u})
    {R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1}}
    {K E E' : CochainComplex (completedConstantModules X R) ℤ} (α : E ⟶ E')
    (hα : QuasiIso α) (hK : K.IsKFlatIndependentCoefficients) :
    QuasiIso (((completedConstantTensor X R).obj K).map α) := by
  let := monoidalCategory R
  let := symmetricCategory R
  let := SheafOfModules.cochainModulesPreadditive R
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (CochainComplex.mappingCone α) hc
  let F := MonoidalCategory.curriedTensor (completedConstantModules X R)
  let e : (((F.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (CochainComplex.mappingCone α)).obj K) ≅
      (((F.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (CochainComplex.mappingCone α)).obj K) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents
        (fun q ↦ β_ ((CochainComplex.mappingCone α).X p) (K.X q)) (by
          intro q q' hqq'
          exact (BraidedCategory.braiding_naturality_right
            ((CochainComplex.mappingCone α).X p) (K.d q q')).symm)) (by
        intro p p' hpp'
        ext q : 1
        exact (BraidedCategory.braiding_naturality_left
          ((CochainComplex.mappingCone α).d p p') (K.X q)).symm)
  have ht' : (CochainComplex.mapBifunctor K (CochainComplex.mappingCone α) F).Acyclic := by
    intro i
    exact (ht i).of_iso (HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫
      HomologicalComplex.mapBifunctorFlipIso K (CochainComplex.mappingCone α) F (.up ℤ))
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht' i).of_iso (CochainComplex.mapBifunctorMappingCone₂Iso K α F)

set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
private theorem tensor_kflat_quasiIso
    (X : AlgebraicGeometry.Scheme.{u})
    {R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1}}
    {K L N : CochainComplex (completedConstantModules X R) ℤ}
    (f : K ⟶ L) (hK : K.IsKFlatIndependentCoefficients)
    (hL : L.IsKFlatIndependentCoefficients) (hf : QuasiIso f) :
    QuasiIso (((completedConstantTensor X R).map f).app N) := by
  let := monoidalCategory R
  obtain ⟨E, t, hE, _, ht, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) N
  let T := completedConstantTensor X R
  have : QuasiIso ((T.map f).app E) := tensor_right_quasiIso X f hf hE
  have : QuasiIso ((T.obj K).map t) := tensor_left_quasiIso X t ht hK
  have : QuasiIso ((T.obj L).map t) := tensor_left_quasiIso X t ht hL
  have hcomp : QuasiIso ((T.obj K).map t ≫ (T.map f).app N) := by
    rw [(T.map f).naturality t]
    infer_instance
  have := hcomp
  exact quasiIso_of_comp_left ((T.obj K).map t) ((T.map f).app N)

end SheafOfModules

namespace AlgebraicGeometry.Scheme

/-- Derive the whole quotient diagram using K-flat resolutions.
Source: Stacks Tags 06XN and 06YU
(blueprint: lem-weil-pbc-completed-constant-derived-tensor-tower).

Proof: tensor descends through the homotopy quotient. Independent-coefficient
K-flat resolutions supply a resolving class. Tensor invariance makes its
resolution diagrams essentially constant: resolve the other tensor factor and use
the mapping-cone criterion in both variables and two-of-three. The pointwise Kan construction gives
a left-derived functor, with invertible counit on the resolving class. Precomposition
by the full, essentially surjective homotopy quotient preserves the defining Kan
limits; transport along its comparison with Q gives the cochain universal counit.
The target is a diagram category and needs no triangulated structure. -/
theorem completed_constant_derived_tensor_tower (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (P : ℕᵒᵖ ⥤ completedConstantModules X R) :
    Nonempty (CompletedConstantDerivedTower X R P) := by
  classical
  let A := completedConstantModules X R
  let := HasDerivedCategory.standard A
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  let := SheafOfModules.symmetricCategory R
  have hpres {K L : CochainComplex A ℤ} (f : K ⟶ L)
      (hK : CochainComplex.IsKFlatIndependentCoefficients (R := R) K)
      (hL : CochainComplex.IsKFlatIndependentCoefficients (R := R) L)
      (hf : QuasiIso f) : IsIso ((completedConstantTensorTower X R P).map f) := by
    have (n : ℕᵒᵖ) : IsIso (((completedConstantTensorTower X R P).map f).app n) := by
      let N := (HomologicalComplex.single A (.up ℤ) 0).obj (P.obj n)
      have hq : QuasiIso (((completedConstantTensor X R).map f).app N) :=
        SheafOfModules.tensor_kflat_quasiIso X (N := N) f hK hL hf
      change IsIso ((completedConstantQ A).map
        (((completedConstantTensor X R).map f).app N))
      exact (DerivedCategory.isIso_Q_map_iff_quasiIso A _).2 hq
    exact NatIso.isIso_of_isIso_app _
  let B := (MonoidalCategory.curriedTensor A).bifunctorMapHomotopyCategory
    (.up ℤ) (.up ℤ) (.up ℤ)
  let q := HomotopyCategory.quotient A (.up ℤ)
  let Qh := DerivedCategory.Qh (C := A)
  let S := P ⋙ HomologicalComplex.single A (.up ℤ) 0 ⋙ q
  let F := ((S ⋙ B.flip) ⋙ (Functor.whiskeringRight _ _ _).obj Qh).flip
  let j : q ⋙ F ≅ completedConstantTensorTower X R P := Iso.refl _
  let Kflat : Set (HomotopyCategory A (.up ℤ)) := fun Y ↦
    ∃ K : CochainComplex A ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := R) K ∧ q.obj K = Y
  have hres : ∀ Y : HomotopyCategory A (.up ℤ),
      ∃ (Z : HomotopyCategory A (.up ℤ)) (s : Z ⟶ Y),
        Z ∈ Kflat ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro Y
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    obtain ⟨L, f, hL, _, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) K
    refine ⟨q.obj L, q.map f, ⟨L, hL, rfl⟩, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf
  have hinv : ∀ (Y Z : HomotopyCategory A (.up ℤ)) (s : Y ⟶ Z),
      Y ∈ Kflat → Z ∈ Kflat → HomotopyCategory.quasiIso A (.up ℤ) s →
        IsIso (F.map s) := by
    rintro Y Z s ⟨K, hK, rfl⟩ ⟨L, hL, rfl⟩ hs
    obtain ⟨f, rfl⟩ := q.map_surjective s
    have hf : QuasiIso f := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 hs
    exact hpres f hK hL hf
  obtain ⟨hpw, T, ε, huniv, hcomp⟩ := resolving_class_left_derived A _ F Kflat hres hinv
  let : F.HasPointwiseLeftDerivedFunctor (HomotopyCategory.quasiIso A (.up ℤ)) := hpw
  let : T.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)) := huniv
  let α := (Functor.associator q Qh T).hom ≫ Functor.whiskerLeft q ε
  have hα := pointwise_precomp_full q Qh F T ε
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor T ε
      (HomotopyCategory.quasiIso A (.up ℤ)))
  let i := DerivedCategory.quotientCompQhIso A
  let β : completedConstantQ A ⋙ T ⟶ completedConstantTensorTower X R P :=
    Functor.whiskerRight i.inv T ≫ α ≫ j.hom
  have hβ := pointwise_change_iso T i j α hα
  refine ⟨{ functor := T
            counit := β
            universal := ⟨hβ.isRightKanExtension⟩
            computes := ?_ }⟩
  intro K hK
  have := hcomp (q.obj K) ⟨K, hK, rfl⟩
  dsimp [β, α]
  infer_instance

end AlgebraicGeometry.Scheme
