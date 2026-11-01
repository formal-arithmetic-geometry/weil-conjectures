/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalTowerTracePresentations
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.AlgebraicGeometry.ProEtale.Replete

/-! # Local descent for completed coefficient lines

Source: Stacks Tags 099L, 099M and 091Q, and the diagonal trace proof,
paragraph (1).
(blueprint: lem-sfb-diagonal-completed-line-complete-aux).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

private noncomputable abbrev sequencePower
    (A : Type*) [Category* A] [HasCountableProducts A] : A ⥤ A where
  obj M := ∏ᶜ fun _ : ℕ ↦ M
  map f := Limits.Pi.map fun _ ↦ f
  map_id M := by ext n; simp
  map_comp f g := by ext n; simp

private noncomputable instance sequencePower_preservesLimits
    {A : Type*} [Category* A] [HasCountableProducts A]
    {D : Type*} [Category* D] : PreservesLimitsOfShape D (sequencePower A) := by
  let T := (Functor.const (Discrete ℕ) : A ⥤ (Discrete ℕ ⥤ A)) ⋙ lim
  let e : sequencePower A ≅ T :=
    NatIso.ofComponents (fun M ↦ Pi.isoLimit ((Functor.const (Discrete ℕ)).obj M)) (by
      intro M N f
      apply limit.hom_ext
      rintro ⟨n⟩
      simp [sequencePower, T])
  exact preservesLimitsOfShape_of_natIso e.symm

private noncomputable def sequenceDifference
    (A : Type*) [Category* A] [Preadditive A] [HasCountableProducts A]
    (l : ℕ) : sequencePower A ⟶ sequencePower A where
  app M := 𝟙 _ - l • Pi.lift (fun n : ℕ ↦ Pi.π (fun _ : ℕ ↦ M) (n + 1))
  naturality {M N} f := by
    apply Pi.hom_ext
    intro n
    simp [sequencePower, Preadditive.comp_sub, Preadditive.sub_comp]

private theorem sequenceDifference_projection
    {A : Type*} [Category* A] [Preadditive A] [HasCountableProducts A]
    (l : ℕ) (M : A) (n : ℕ) :
    (sequenceDifference A l).app M ≫ Pi.π (fun _ : ℕ ↦ M) n =
      Pi.π (fun _ : ℕ ↦ M) n - l • Pi.π (fun _ : ℕ ↦ M) (n + 1) := by
  dsimp only [sequenceDifference, sequencePower]
  rw [Preadditive.sub_comp, Category.id_comp, Preadditive.nsmul_comp, Pi.lift_π]

private theorem sequenceDifference_map
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    [HasCountableProducts A] [HasCountableProducts B] (F : A ⥤ B) [F.Additive]
    (l : ℕ) (M : A) :
    F.map ((sequenceDifference A l).app M) ≫ piComparison F (fun _ : ℕ ↦ M) =
      piComparison F (fun _ : ℕ ↦ M) ≫ (sequenceDifference B l).app (F.obj M) := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, piComparison_comp_π]
  rw [← F.map_comp, sequenceDifference_projection, F.map_sub, F.map_nsmul]
  simp [sequenceDifference, Preadditive.comp_sub]

private theorem sequenceDifference_map_isIso_iff
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    [HasCountableProducts A] [HasCountableProducts B] (F : A ⥤ B) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F] (l : ℕ) (M : A) :
    IsIso (F.map ((sequenceDifference A l).app M)) ↔
      IsIso ((sequenceDifference B l).app (F.obj M)) := by
  have h := sequenceDifference_map F l M
  constructor
  · intro hF
    have := hF
    apply (isIso_comp_left_iff (piComparison F (fun _ : ℕ ↦ M)) _).mp
    rw [← h]
    infer_instance
  · intro hM
    have := hM
    apply (isIso_comp_right_iff _ (piComparison F (fun _ : ℕ ↦ M))).mp
    rw [h]
    infer_instance

private theorem sequenceDifference_iso
    {A : Type*} [Category* A] [Preadditive A] [HasCountableProducts A]
    (l : ℕ) {M N : A} (e : M ≅ N)
    (hN : IsIso ((sequenceDifference A l).app N)) :
    IsIso ((sequenceDifference A l).app M) := by
  have := hN
  have h : (sequenceDifference A l).app M =
      (sequencePower A).map e.hom ≫ (sequenceDifference A l).app N ≫
        (sequencePower A).map e.inv := by
    rw [← Category.assoc, (sequenceDifference A l).naturality,
      Category.assoc, ← Functor.map_comp, e.hom_inv_id, (sequencePower A).map_id, Category.comp_id]
  rw [h]
  infer_instance

private theorem sequenceDifference_limit
    {A : Type*} [Category* A] [Preadditive A] [HasCountableProducts A]
    {D : Type*} [Category* D] (F : D ⥤ A) [HasLimit F]
    [PreservesLimit F (sequencePower A)] (l : ℕ)
    (hF : ∀ d, IsIso ((sequenceDifference A l).app (F.obj d))) :
    IsIso ((sequenceDifference A l).app (limit F)) := by
  let δ := sequenceDifference A l
  let P := sequencePower A
  let α := Functor.whiskerLeft F δ
  have (d : D) : IsIso (α.app d) := hF d
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let hc := isLimitOfPreserves P (limit.isLimit F)
  let e := IsLimit.conePointsIsoOfNatIso hc hc (asIso α)
  have he : δ.app (limit F) = e.hom := by
    apply hc.hom_ext
    intro d
    change δ.app (limit F) ≫ P.map (limit.π F d) = _
    rw [← δ.naturality]
    exact (IsLimit.conePointsIsoOfNatIso_hom_comp hc hc (asIso α) d).symm
  rw [he]
  infer_instance

private theorem sequenceDifference_nilpotent
    {A : Type*} [Category* A] [Preadditive A] [HasCountableProducts A]
    (l : ℕ) (M : A) (e : ℕ) (he : l ^ e • 𝟙 M = 0) :
    IsIso ((sequenceDifference A l).app M) := by
  let s : End (∏ᶜ fun _ : ℕ ↦ M) :=
    l • Pi.lift (fun n : ℕ ↦ Pi.π (fun _ : ℕ ↦ M) (n + 1))
  have hs (r j : ℕ) : (s ^ r) ≫ Pi.π (fun _ : ℕ ↦ M) j =
      l ^ r • Pi.π (fun _ : ℕ ↦ M) (j + r) := by
    induction r generalizing j with
    | zero => simp
    | succ r ih =>
      rw [pow_succ, End.mul_def, Category.assoc, ih]
      simp only [s, Preadditive.nsmul_comp, Preadditive.comp_nsmul, Pi.lift_π]
      rw [smul_smul, ← pow_succ]
      simp only [Nat.add_assoc]
  have hnil : IsNilpotent s := by
    refine ⟨e, Pi.hom_ext _ _ fun j ↦ ?_⟩
    rw [hs, ← Category.comp_id (Pi.π (fun _ : ℕ ↦ M) (j + e)),
      ← Preadditive.comp_nsmul, he, comp_zero, zero_comp]
  exact (isUnit_iff_isIso (1 - s)).mp hnil.isUnit_one_sub

private theorem sequenceDifference_orthogonal
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    [HasCountableProducts A] (F : A ⥤ B) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F] (l : ℕ) (M : A)
    (hM : IsIso ((sequenceDifference A l).app M)) (V : B)
    [IsIso (l • 𝟙 V)] : Subsingleton (V ⟶ F.obj M) := by
  let g (f : V ⟶ F.obj M) : ℕ → (V ⟶ F.obj M) :=
    Nat.rec f (fun _ a ↦ inv (l • 𝟙 V) ≫ a)
  have hg (f : V ⟶ F.obj M) (n : ℕ) : l • g f (n + 1) = g f n := by
    change l • (inv (l • 𝟙 V) ≫ g f n) = _
    calc
      l • (inv (l • 𝟙 V) ≫ g f n) =
          (l • 𝟙 V) ≫ inv (l • 𝟙 V) ≫ g f n := by
        simp only [Preadditive.nsmul_comp, Category.id_comp]
      _ = g f n := IsIso.hom_inv_id_assoc _ _
  let P := Fan.mk (F.obj (∏ᶜ fun _ : ℕ ↦ M))
    (fun n : ℕ ↦ F.map (Pi.π (fun _ : ℕ ↦ M) n))
  have hP : IsLimit P :=
    (isLimitMapConeFanMkEquiv F _ _) (isLimitOfPreserves F (productIsProduct _))
  have hz (f : V ⟶ F.obj M) : f = 0 := by
    let a := Fan.IsLimit.lift hP (g f)
    have ha_proj (n : ℕ) : a ≫ F.map (Pi.π (fun _ : ℕ ↦ M) n) = g f n :=
      Fan.IsLimit.fac hP (g f) n
    have ha : a ≫ F.map ((sequenceDifference A l).app M) = 0 := by
      apply Fan.IsLimit.hom_ext hP
      intro n
      change (a ≫ F.map ((sequenceDifference A l).app M)) ≫
        F.map (Pi.π (fun _ : ℕ ↦ M) n) =
          (0 : V ⟶ F.obj (∏ᶜ fun _ : ℕ ↦ M)) ≫ F.map (Pi.π (fun _ : ℕ ↦ M) n)
      rw [Category.assoc, ← F.map_comp, sequenceDifference_projection,
        F.map_sub, F.map_nsmul, Preadditive.comp_sub, Preadditive.comp_nsmul]
      simp only [ha_proj, hg, sub_self, zero_comp]
    have : IsIso (F.map ((sequenceDifference A l).app M)) := by
      have := hM
      infer_instance
    have ha0 : a = 0 := (cancel_mono (F.map ((sequenceDifference A l).app M))).mp
      (by simpa only [zero_comp] using ha)
    have hh := Fan.IsLimit.fac hP (g f) 0
    change a ≫ F.map (Pi.π _ 0) = f at hh
    rw [ha0, zero_comp] at hh
    exact hh.symm
  exact ⟨fun f h ↦ (hz f).trans (hz h).symm⟩

private theorem completedForget_preservesSheafification (S : Scheme.{u}) :
    (Scheme.ProEt.topology S).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) := by
  have : EssentiallySmall.{u + 1} S.ProEt := essentiallySmallSelf.{0} _
  constructor
  intro P Q f hf
  change (Scheme.ProEt.topology S).W
    (Functor.whiskerRight f (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}))
  have hi : Presheaf.IsLocallyInjective (Scheme.ProEt.topology S) f := hf.isLocallyInjective
  have hs : Presheaf.IsLocallySurjective (Scheme.ProEt.topology S) f := hf.isLocallySurjective
  apply ((Scheme.ProEt.topology S).W_iff_isLocallyBijective _).mpr
  constructor
  · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem (Scheme.ProEt.topology S) f x y h⟩
  · exact ⟨fun x ↦ Presheaf.imageSieve_mem (Scheme.ProEt.topology S) f x⟩

private theorem finiteCoefficient_difference (l : ℕ) [Fact l.Prime]
    (S : Scheme.{u}) (n : ℕ) :
    IsIso ((sequenceDifference (Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}) l).app
      ((sheafCompose (Scheme.ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (Scheme.purTwistFiniteRing S l n))) := by
  have := completedForget_preservesSheafification S
  let J := Scheme.ProEt.topology S
  let R := CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))
  let A := (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}).obj R
  let F := constantSheaf J AddCommGrpCat.{u + 1}
  have hz : l ^ (n + 1) • 𝟙 A = 0 := by
    ext x
    apply ULift.ext
    change l ^ (n + 1) • x.down = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hF : l ^ (n + 1) • 𝟙 (F.obj A) = 0 := by
    rw [← F.map_id, ← F.map_nsmul, hz, F.map_zero]
  let e := (constantCommuteCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).app R
  exact sequenceDifference_iso l e (sequenceDifference_nilpotent l (F.obj A) (n + 1) hF)

private noncomputable instance completedForget_preservesLimits (S : Scheme.{u})
    {D : Type} [SmallCategory D] :
    PreservesLimitsOfShape D
      (sheafCompose (Scheme.ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})) := by
  let J := Scheme.ProEt.topology S
  let H := forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}
  have : PreservesLimitsOfShape D
      (sheafCompose J H ⋙ sheafToPresheaf J AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfShape_of_natIso
      (Iso.refl (sheafToPresheaf J CommRingCat.{u + 1} ⋙
        (Functor.whiskeringRight _ _ _).obj H))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J _)

private theorem completedCoefficient_difference (l : ℕ) [Fact l.Prime] (S : Scheme.{u}) :
    IsIso ((sequenceDifference (Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}) l).app
      ((sheafCompose (Scheme.ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (Scheme.purTwistZlCompletion S l))) := by
  let H := sheafCompose (Scheme.ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})
  let T := Scheme.purTwistZlTower S l
  let e := preservesLimitIso H T
  apply sequenceDifference_iso l e
  apply sequenceDifference_limit (T ⋙ H) l
  intro n
  exact finiteCoefficient_difference l S n.unop

/--
The local-to-global part of completeness for a completed coefficient line.

Source: blueprint latest, `sk-prop-diagonal-tower-trace.proof.md`, paragraph (1),
and Stacks Tags 099L, 099M and 091Q.

Proof: on each member of the displayed pro-etale cover, identify the line with the
regular completed coefficient module. The quotient tower of that regular module is
surjective on the weakly contractible basis, hence its derived inverse limit agrees
with its ordinary limit. The principal-ideal orthogonal criterion gives vanishing
of maps from every complex on which `l` acts invertibly. Exact restriction to the
constant coefficient category and descent for a sheaf cover transport this vanishing
to the globally displayed line. The empty site is included vacuously.
(blueprint: lem-sfb-diagonal-completed-line-complete-aux).
-/
theorem diagonalCompletedLine_complete_of_cover (l : ℕ) [Fact l.Prime] (S : Scheme.{u})
    [IsNoetherian S] [DiagonalTraceLocalizations l S]
    (L : DiagonalCompleted l S)
    (hcover : ∀ U : S.ProEt, ∃ s : Sieve U, s ∈ (Scheme.ProEt.topology S) U ∧
      ∀ (V : S.ProEt) (f : V ⟶ U), s f →
        Nonempty (L.over V ≅
          (SheafOfModules.unit
            (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l))).over V)) :
    ∀ V : DerivedCategory (DiagonalMod l S), IsIso (l • 𝟙 V) →
      Subsingleton (V ⟶ (diagonalCompletedUnderlying l S).obj
        ((DerivedCategory.singleFunctor (DiagonalCompleted l S) 0).obj L)) := by
  let J := Scheme.ProEt.topology S
  let R := Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l)
  let B := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
    (Scheme.purTwistZlCompletion S l)
  let M := (diagonalCompletedRestriction l S).obj L
  have hB : IsIso ((sequenceDifference (Sheaf J AddCommGrpCat.{u + 1}) l).app B) :=
    completedCoefficient_difference l S
  have hM : IsIso ((sequenceDifference (DiagonalMod l S) l).app M) := by
    apply Sheaf.isIso_of_isIso_app_of_mem J
    intro U
    obtain ⟨s, hs, hlocal⟩ := hcover U
    refine ⟨s, hs, ?_⟩
    intro V f hf
    obtain ⟨e⟩ := hlocal V f hf
    let E : DiagonalMod l S ⥤ AddCommGrpCat.{u + 1} :=
      sheafToPresheaf J (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) ⋙
        (evaluation _ _).obj (op V) ⋙
          forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) AddCommGrpCat.{u + 1}
    let EB : Sheaf J AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
      sheafToPresheaf J AddCommGrpCat.{u + 1} ⋙ (evaluation _ _).obj (op V)
    have hBg : IsIso ((sequenceDifference AddCommGrpCat.{u + 1} l).app (EB.obj B)) :=
      (sequenceDifference_map_isIso_iff EB l B).mp (by have := hB; infer_instance)
    let T := SheafOfModules.evaluation.{u + 1} (R.over V) (op (Over.mk (𝟙 V))) ⋙
      forget₂ (ModuleCat.{u + 1} ((R.over V).obj.obj (op (Over.mk (𝟙 V)))))
        AddCommGrpCat.{u + 1}
    let e' : E.obj M ≅ EB.obj B := T.mapIso e
    have hMg : IsIso ((sequenceDifference AddCommGrpCat.{u + 1} l).app (E.obj M)) :=
      sequenceDifference_iso l e' hBg
    have hm : IsIso (E.map ((sequenceDifference (DiagonalMod l S) l).app M)) :=
      (sequenceDifference_map_isIso_iff E l M).mpr hMg
    have : IsIso
        ((forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) AddCommGrpCat.{u + 1}).map
          (((sequenceDifference (DiagonalMod l S) l).app M).hom.app (op V))) := hm
    exact isIso_of_reflects_iso _
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) AddCommGrpCat.{u + 1})
  have : PreservesLimitsOfShape (Discrete ℕ)
      ((CochainComplex.singleFunctors (DiagonalMod l S)).functor 0) :=
    inferInstanceAs (PreservesLimitsOfShape _
      (HomologicalComplex.single (DiagonalMod l S) (.up ℤ) 0))
  have : PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.singleFunctor (DiagonalMod l S) 0) :=
    preservesLimitsOfShape_of_natIso
      (DerivedCategory.singleFunctorIsoCompQ (DiagonalMod l S) 0).symm
  let e := ((diagonalCompletedRestriction l S).mapDerivedCategorySingleFunctor 0).app L
  intro V hV
  have := hV
  have h := sequenceDifference_orthogonal
    (DerivedCategory.singleFunctor (DiagonalMod l S) 0) l M hM V
  exact ⟨fun f g ↦ (cancel_mono e.hom).mp (h.elim (f ≫ e.hom) (g ≫ e.hom))⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace
