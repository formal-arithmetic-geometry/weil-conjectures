/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.LocalizingExceptionalAdjoint
import WeilConjectures.AlgebraicGeometry.ShriekCoefficientIsomorphism
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctorsBasics.BrownHypothesesStructural
import WeilConjectures.AlgebraicGeometry.FiniteLocalizingExceptionalPreservation
import WeilConjectures.SixFunctors.IntegralExceptionalRestriction
import WeilConjectures.AlgebraicGeometry.RationalRestrictionGlue
import WeilConjectures.AlgebraicGeometry.LocalizingClosureCtfEqualsBc
import WeilConjectures.NumberTheory.Padics.BaseCoefficientCondensedIdentification
import all WeilConjectures.AlgebraicGeometry.AdmissibleBoundedConstructibleTriangulated
/-! Right-adjoint preservation subclaim for det-existence-restriction.
Source: det-existence-restriction proof, coefficient preservation paragraph
(blueprint: det-existence-restriction-right). -/
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private instance ctf_replete
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :
    (shriekCoefficientCtf (Λ := Λ) T).IsClosedUnderIsomorphisms := by
  let _ := (constantModelConstructibleFiniteTor_wellDefined Λ T).2.1
  let _ := (constantModelConstructibleFiniteTor_wellDefined Λ T).2.2.2.1
  exact inferInstanceAs ((constantModelBoundedConstructible Λ T ⊓
    _root_.DerivedCategory.finiteTorAmplitude _).IsClosedUnderIsomorphisms)

private theorem map_closure
    {C D : Type v} [Category.{w} C] [Category.{w} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    [PreservesColimitsOfSize.{v, v} F]
    (S : ObjectProperty C) (T : ObjectProperty D) (hST : S ≤ T.inverseImage F) :
    localizingClosure S ≤ (localizingClosure T).inverseImage F := by
  intro M hM P hP hTP
  let _ := hP.1
  let _ := hP.2.1
  have hPF : IsLocalizingSubcategory (P.inverseImage F) := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro I H hH hHP
    let _ := hH
    have hFH : HasColimit (H ⋙ F) :=
      ⟨F.mapCocone (colimit.cocone H), isColimitOfPreserves F (colimit.isColimit H)⟩
    exact P.prop_of_iso (preservesColimitIso F H).symm (hP.2.2 (H ⋙ F) hFH hHP)
  exact hM _ hPF (fun N hN ↦ hTP _ (hST N hN))

set_option maxHeartbeats 2000000 in
-- Scalar and full-subcategory equivalences require several dependent reductions.
private theorem preservation_of_coefficient_iso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
      ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
    (h' : ∀ K, localizingClosureProEtale Λ' X K → localizingClosureProEtale Λ' Y
      ((rightDerivedLowerShriekOfCompactification Λ' c.obj.obj).obj K))
    (G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory)
    (G' : (localizingClosureProEtale Λ' Y).FullSubcategory ⥤
      (localizingClosureProEtale Λ' X).FullSubcategory)
    (adj : localizingLowerShriek Λ c.obj.obj h ⊣ G)
    (adj' : localizingLowerShriek Λ' c.obj.obj h' ⊣ G')
    (hp : ∀ K : (localizingClosureProEtale Λ' Y).FullSubcategory,
      shriekCoefficientCtf (Λ := Λ') Y K.obj →
        shriekCoefficientCtf (Λ := Λ') X (G'.obj K).obj) :
    ∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
      shriekCoefficientCtf (Λ := Λ) Y K.obj →
        shriekCoefficientCtf (Λ := Λ) X (G.obj K).obj := by
  classical
  let q (T : Scheme.{u}) : condensedRingObj Λ T ≅ condensedRingObj Λ' T :=
    (upperStarFromPoint T).mapIso ((Mon.forget _).mapIso e)
  have (T : Scheme.{u}) : IsMonHom (q T).hom :=
    inferInstanceAs (IsMonHom ((upperStarFromPoint T).map e.hom.hom))
  have (T : Scheme.{u}) : IsMonHom (q T).inv :=
    inferInstanceAs (IsMonHom ((upperStarFromPoint T).map e.inv.hom))
  let H (T : Scheme.{u}) := CategoryTheory.Equivalence.mk
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (q T).inv)
    (Mod.comap (q T).hom)
    ((Mod.comapId _).symm ≪≫ Mod.comapCongr (q T).hom_inv_id.symm ≪≫
      Mod.comapComp (q T).hom (q T).inv)
    ((Mod.comapComp (q T).inv (q T).hom).symm ≪≫
      Mod.comapCongr (q T).inv_hom_id ≪≫ Mod.comapId _)
  have (T : Scheme.{u}) : (H T).functor.Additive :=
    inferInstanceAs ((Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (q T).inv).Additive)
  have (T : Scheme.{u}) : (H T).inverse.Additive :=
    inferInstanceAs ((Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (q T).hom).Additive)
  let d (T : Scheme.{u}) := (H T).mapDerivedCategory
  have hlocal (T : Scheme.{u}) : (localizingClosureProEtale Λ' T).inverseImage
      (d T).functor = localizingClosureProEtale Λ T := by
    let S := shriekCoefficientCtf (Λ := Λ) T
    let S' := shriekCoefficientCtf (Λ := Λ') T
    obtain ⟨_, htri, hiso, _, _, _⟩ := brownHypotheses_structural Λ T
    obtain ⟨_, htri', hiso', _, _, _⟩ := brownHypotheses_structural Λ' T
    let _ := htri
    let _ := hiso
    let _ := htri'
    let _ := hiso'
    have hf : localizingClosureProEtale Λ T ≤
        (localizingClosureProEtale Λ' T).inverseImage (d T).functor :=
      map_closure (H T).functor.mapDerivedCategory S S'
        (fun K hK ↦ constantModelCtf_coefficientIso e T ⟨K, hK⟩)
    have hb : localizingClosureProEtale Λ' T ≤
        (localizingClosureProEtale Λ T).inverseImage (d T).inverse :=
      map_closure (H T).inverse.mapDerivedCategory S' S
        (fun K hK ↦ constantModelCtf_coefficientIso e.symm T ⟨K, hK⟩)
    funext K
    apply propext
    exact ⟨fun hK ↦ (localizingClosureProEtale Λ T).prop_of_iso
      ((d T).unitIso.app K).symm (hb _ hK), hf K⟩
  obtain ⟨_, htriX, hisoX, _, _, _⟩ := brownHypotheses_structural Λ' X
  obtain ⟨_, htriY, hisoY, _, _, _⟩ := brownHypotheses_structural Λ' Y
  let _ := htriX
  let _ := htriY
  let _ := hisoX
  let _ := hisoY
  let EX := (d X).congrFullSubcategory (hlocal X)
  let EY := (d Y).congrFullSubcategory (hlocal Y)
  let F := localizingLowerShriek Λ c.obj.obj h
  let F' := localizingLowerShriek Λ' c.obj.obj h'
  let comp : F ⋙ EY.functor ≅ EX.functor ⋙ F' :=
    ((localizingClosureProEtale Λ' Y).fullyFaithfulι.whiskeringRight _).preimageIso
      (Functor.isoWhiskerLeft (localizingClosureProEtale Λ X).ι
        (shriekCoefficientCompactificationIso e c))
  let left : (EX.inverse ⋙ F) ⋙ EY.functor ≅ F' :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft EX.inverse comp ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight EX.counitIso F' ≪≫ F'.leftUnitor
  let conj := (EX.symm.toAdjunction.comp adj).comp EY.toAdjunction
  let r := (conj.ofNatIsoLeft left).rightAdjointUniq adj'
  intro K hK
  have hp' := hp (EY.functor.obj K) (constantModelCtf_coefficientIso e Y ⟨K.obj, hK⟩)
  have ht : shriekCoefficientCtf (Λ := Λ') X (EX.functor.obj (G.obj K)).obj := by
    let i := r.app (EY.functor.obj K)
    let j := EX.functor.mapIso (G.mapIso (EY.unitIso.app K).symm)
    exact (shriekCoefficientCtf (Λ := Λ') X).prop_of_iso
      ((localizingClosureProEtale Λ' X).ι.mapIso (i.symm ≪≫ j)) hp'
  have hback := constantModelCtf_coefficientIso e.symm X
    ⟨(EX.functor.obj (G.obj K)).obj, ht⟩
  exact (shriekCoefficientCtf (Λ := Λ) X).prop_of_iso
    ((d X).unitIso.app (G.obj K).obj).symm hback

set_option maxHeartbeats 2000000 in
-- Equality transport identifies Loc(Dctf) with the integral theorem's Loc(Dbc).
private theorem integral_preservation
    (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ell k)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification.BoundaryCompactification f)
    (LX : ObjectProperty (IntegralCompactSupport.Ambient
      (Profinite.padicIntegersRingObj ell E.val) X))
    (LY : ObjectProperty (IntegralCompactSupport.Ambient
      (Profinite.padicIntegersRingObj ell E.val) Y))
    (heX : LX = IntegralCompactSupport.localizing
      (Profinite.padicIntegersRingObj ell E.val) X)
    (heY : LY = IntegralCompactSupport.localizing
      (Profinite.padicIntegersRingObj ell E.val) Y)
    (h : ∀ K, LX K → LY ((rightDerivedLowerShriekOfCompactification
      (Profinite.padicIntegersRingObj ell E.val) c.obj.obj).obj K))
    (G : LY.FullSubcategory ⥤ LX.FullSubcategory)
    (adj : LY.lift (LX.ι ⋙ rightDerivedLowerShriekOfCompactification
      (Profinite.padicIntegersRingObj ell E.val) c.obj.obj)
      (fun K ↦ h K.obj K.property) ⊣ G) :
    ∀ K : LY.FullSubcategory,
      shriekCoefficientCtf (Λ := Profinite.padicIntegersRingObj ell E.val) Y K.obj →
        shriekCoefficientCtf (Λ := Profinite.padicIntegersRingObj ell E.val) X
          (G.obj K).obj := by
  subst LX
  subst LY
  obtain ⟨hy, _, hr, _⟩ := IntegralCompactSupport.integralExceptionalRestriction
    ell E k hcd f c h G adj
  intro K hK
  exact hr ⟨K.obj, hK⟩

set_option maxHeartbeats 2000000 in
-- All coefficient cases elaborate in the same dependent localizing categories.
/-- The Brown right adjoint preserves the constructible finite-Tor property for
all six admissible coefficient presentations.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-existence/
det-existence-restriction.proof.md, opening paragraph and coefficient bullets
(blueprint: det-existence-restriction-right).

Proof: restriction of scalars along a coefficient isomorphism and its inverse is
an exact equivalence, hence gives inverse derived equivalences. These preserve
finite constant models and finite Tor amplitude. Pulling back the defining
localizing intersection in both directions identifies the actual localizing
categories. The compactification comparison identifies the conjugated lower
shriek with the lower shriek for the model coefficient. Conjugating the supplied
adjunction and using uniqueness of right adjoints therefore transfers preservation.
For finite coefficients, lift the small carrier by ULift, keeping its exponent,
and apply finite-coefficient exceptional preservation. For integral coefficients,
Dctf=Dbc identifies both localizing categories with those of the integral theorem;
its preservation assertion applies. The rational gluing theorem already accepts
an arbitrary isomorphic coefficient presentation and gives preservation of Dbc;
Dctf=Dbc on the qcqs source gives preservation of finite Tor amplitude too.
Finally the bottom finite intermediate field identifies Z_l and Q_l with the
integral and rational model coefficients. The six clauses of admissibility
exhaust these cases, including the zero finite ring and empty schemes. -/
theorem det_existence_restriction_right
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (_hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ell k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (_hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    (c : Compactification.BoundaryCompactification f.left)
    (h : ∀ K, localizingClosureProEtale Λ X.left K → localizingClosureProEtale Λ Y.left
      ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
    (G : (localizingClosureProEtale Λ Y.left).FullSubcategory ⥤
      (localizingClosureProEtale Λ X.left).FullSubcategory)
    (_adj : localizingLowerShriek Λ c.obj.obj h ⊣ G) :
    ∀ K : (ObjectProperty.inverseImage
        (constantModelBoundedConstructible Λ Y.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
        (localizingClosureProEtale Λ Y.left).ι).FullSubcategory,
      (constantModelBoundedConstructible Λ X.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
        (G.obj K.obj).obj := by
  classical
  have : IsSeparated (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  have : QuasiCompact (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  let : IsSeparated f.left := IsSeparated.of_comp f.left Y.hom
  let : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  let : QuasiCompact f.left := QuasiCompact.of_comp f.left Y.hom
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  let : f.left.IsOver (Spec (.of k)) := ⟨f.w⟩
  let : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X.hom›
  let : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType Y.hom›
  let : QuasiCompact (X.left ↘ Spec (.of k)) := ‹QuasiCompact X.hom›
  let : QuasiCompact (Y.left ↘ Spec (.of k)) := ‹QuasiCompact Y.hom›
  let : IsSeparated (X.left ↘ Spec (.of k)) := ‹IsSeparated X.hom›
  let : IsSeparated (Y.left ↘ Spec (.of k)) := ‹IsSeparated Y.hom›
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  suffices hall : ∀ K : (localizingClosureProEtale Λ Y.left).FullSubcategory,
      shriekCoefficientCtf (Λ := Λ) Y.left K.obj →
        shriekCoefficientCtf (Λ := Λ) X.left (G.obj K).obj by
    intro K
    exact hall K.obj K.property
  have transfer
      (Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj Λ'] [IsCommMonObj Λ'] (e : Mon.mk Λ ≅ Mon.mk Λ')
      (hadm : IsLocalizingAdmissibleCoefficient ell Λ')
      (hp : ∀
        (h' : ∀ K, localizingClosureProEtale Λ' X.left K →
          localizingClosureProEtale Λ' Y.left
            ((rightDerivedLowerShriekOfCompactification Λ' c.obj.obj).obj K))
        (G' : (localizingClosureProEtale Λ' Y.left).FullSubcategory ⥤
          (localizingClosureProEtale Λ' X.left).FullSubcategory),
        (localizingLowerShriek Λ' c.obj.obj h' ⊣ G') →
          ∀ K : (localizingClosureProEtale Λ' Y.left).FullSubcategory,
            shriekCoefficientCtf (Λ := Λ') Y.left K.obj →
              shriekCoefficientCtf (Λ := Λ') X.left (G'.obj K).obj) :
      ∀ K : (localizingClosureProEtale Λ Y.left).FullSubcategory,
        shriekCoefficientCtf (Λ := Λ) Y.left K.obj →
          shriekCoefficientCtf (Λ := Λ) X.left (G.obj K).obj := by
    obtain ⟨h', hTX, hTY, hdata⟩ :=
      exists_localizingExceptionalAdjoint Λ' ell k _hcd f.left c hadm
    let := hTX
    let := hTY
    obtain ⟨_, _, _, _, G', _, _, _, adj', _⟩ := hdata
    exact preservation_of_coefficient_iso e c h h' G G' _adj adj' (hp h' G' adj')
  have intCase (E : PadicAlgCl.FiniteIntermediateField ell)
      (e : Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E.val)) :
      ∀ K : (localizingClosureProEtale Λ Y.left).FullSubcategory,
        shriekCoefficientCtf (Λ := Λ) Y.left K.obj →
          shriekCoefficientCtf (Λ := Λ) X.left (G.obj K).obj := by
    let O := Profinite.padicIntegersRingObj ell E.val
    apply transfer O e (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)))))
    intro h' G' adj'
    have he (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] :
        localizingClosureProEtale O T = IntegralCompactSupport.localizing O T :=
      (localizingClosure_ctf_equals_bc ell T O
        (Or.inr (Or.inr (Or.inl ⟨E, Or.inl ⟨Iso.refl _⟩⟩)))).1.2.2.2.1
    exact integral_preservation ell E k _hcd f.left c _ _
      (he X.left) (he Y.left) h' G' adj'
  have ratCase (E : PadicAlgCl.FiniteIntermediateField ell)
      (hc : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.val)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell))) :
      ∀ K : (localizingClosureProEtale Λ Y.left).FullSubcategory,
        shriekCoefficientCtf (Λ := Λ) Y.left K.obj →
          shriekCoefficientCtf (Λ := Λ) X.left (G.obj K).obj := by
    obtain ⟨_, _, _, _, hG, _⟩ := rationalRestrictionGlue.{u, u} Λ ell E.val hc k
      (ringChar k) (Fact.out : ringChar k ≠ ell) _hcd f.left c h G _adj
    have he : (constantModelBoundedConstructible Λ X.left ⊓
        _root_.DerivedCategory.finiteTorAmplitude _) =
          constantModelBoundedConstructible Λ X.left := by
      apply (localizingClosure_ctf_equals_bc ell X.left Λ ?_).1.2.2.1
      rcases hc with hE | hbar
      · exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr hE⟩))
      · exact Or.inr (Or.inr (Or.inr hbar))
    intro K hK
    rw [show shriekCoefficientCtf (Λ := Λ) X.left = _ from he]
    exact hG K hK.1
  let E₀ : PadicAlgCl.FiniteIntermediateField ell := ⟨⊥, inferInstance⟩
  obtain ⟨_, _, _, _, _, _, _, _, qIso, zIso, _⟩ :=
    Profinite.base_coefficient_condensed_identification.{u} ell
  rcases _hΛ with hA | hZ | hQ | hE | hO | hbar
  · obtain ⟨A, _, _, _, _, hfin, hn, ⟨e⟩⟩ := hA
    let := hfin
    obtain ⟨j⟩ := AdmissibleTriangulated.finiteCoefficientLiftIso.{u} A
    apply transfer (Profinite.continuousCoefficientRingObj (ULift.{u} A)) (e ≪≫ j)
    · exact Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
        hfin, hn, ⟨j.symm⟩⟩
    · intro h' G' adj' K hK
      have hAn : ∃ r : ℕ, ((ell ^ r : ℕ) : ULift.{u + 1} (ULift.{u} A)) = 0 := by
        obtain ⟨r, hr⟩ := hn
        refine ⟨r, ?_⟩
        change ULift.up (ULift.up (((ell ^ r : ℕ) : A))) =
          ULift.up (ULift.up (0 : A))
        apply congrArg ULift.up
        apply congrArg ULift.up
        simpa only [nsmul_eq_mul, mul_one] using hr (1 : A)
      obtain ⟨_, hG', _⟩ := localizingExceptionalAdjoint_preserves_finiteConstructible
        ell k (ULift.{u} A) hAn f.left c h' G' adj'
      exact hG' ⟨K, hK⟩
  · obtain ⟨e⟩ := hZ
    exact intCase E₀ (e ≪≫ zIso)
  · obtain ⟨e⟩ := hQ
    exact ratCase E₀ (Or.inl ⟨e ≪≫ qIso⟩)
  · obtain ⟨E, hE⟩ := hE
    exact ratCase E (Or.inl hE)
  · obtain ⟨E, ⟨e⟩⟩ := hO
    exact intCase E e
  · exact ratCase E₀ (Or.inr hbar)

end AlgebraicGeometry.ProEtale.CondensedRing
