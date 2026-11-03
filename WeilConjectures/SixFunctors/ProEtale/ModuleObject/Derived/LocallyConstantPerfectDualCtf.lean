/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyConstantPerfectComplex
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
import WeilConjectures.AlgebraicGeometry.AdmissiblePointPerfectDualCohomology
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackFiniteConstantLocalModel
import WeilConjectures.AlgebraicGeometry.FiniteAffineProEtaleRefinement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.Algebra.Homology.RealizedBoundedDualPairing
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit

/-! # Duality for locally constant scalar-perfect complexes

Source: current blueprint, internal-Hom stability proof, Step 6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite
open scoped CategoryTheory.Obj ZeroObject
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

open CategoryTheory.MonoidalCategory

private theorem point_term_dualizable
    (M : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (hM : FiniteProjectiveCondensedModule (Mon.mk Λ) M) : IsDualizable M := by
  obtain ⟨n, i, p, hip⟩ := hM
  exact (show finProj _ M from ⟨n, ⟨⟨i, p, hip⟩⟩⟩).isDualizable

private theorem point_sheaf_colimits (U : Scheme.{u}) :
    PreservesColimitsOfSize.{0, 0} (upperStarFromPoint U) :=
  (pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1}
      (toSpecZ U))).leftAdjoint_preservesColimits

@[irreducible] private def point_module_monoidal (U : Scheme.{u}) :
    (upperStarFromPointMod Λ U).Monoidal := by
  have := point_sheaf_colimits U
  let : (upperStarFromPoint U).Braided :=
    { toMonoidal := { monoidal_upperStarFromPoint U with
        toLaxMonoidal := (laxBraided_upperStarFromPoint U).toLaxMonoidal },
      braided := (laxBraided_upperStarFromPoint U).braided }
  exact Functor.monoidal_mapMod (upperStarFromPoint U)

omit [IsCommMonObj Λ] in
private theorem point_module_colimits (U : Scheme.{u}) :
    PreservesColimitsOfSize.{0, 0} (upperStarFromPointMod Λ U) := by
  have := point_sheaf_colimits U
  constructor
  intro J _
  have : PreservesColimitsOfShape J (upperStarFromPointMod Λ U ⋙ Mod.forget _) :=
    inferInstanceAs (PreservesColimitsOfShape J (Mod.forget Λ ⋙ upperStarFromPoint U))
  have : ReflectsColimitsOfShape J
      (Mod.forget (condensedRingObj Λ U) :
        Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U) ⥤
          Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves _ (Mod.forget _)

private theorem locally_dualizable
    {X : Scheme.{u}}
    (P : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hP : IsLocallyConstantPerfectComplex Λ X P) : IsDualizable P := by
  classical
  obtain ⟨𝒰, h𝒰⟩ := hP
  apply (condensed_dualizable_iff_proetale_cover ⟨Λ⟩ X 𝒰 P).mpr
  intro i
  obtain ⟨F, ⟨a, b, hb⟩, hp, hG, ⟨e⟩⟩ := h𝒰 i
  let G := (upperStarFromPoint (𝒰.X i)).mapMod Λ
  let : G.PreservesZeroMorphisms := hG
  let : G.Monoidal := point_module_monoidal Λ (𝒰.X i)
  let K : CochainComplex _ ℤ := (G.mapHomologicalComplex (.up ℤ)).obj F
  have : K.IsStrictlyGE a := (K.isStrictlyGE_iff a).mpr
    (fun n hn ↦ G.map_isZero (hb n (.inl hn)))
  have : K.IsStrictlyLE b := (K.isStrictlyLE_iff b).mpr
    (fun n hn ↦ G.map_isZero (hb n (.inr hn)))
  exact IsDualizable.of_iso e.symm
    (DerivedCategory.isDualizable_Q_obj K a b
      (fun n ↦ (point_term_dualizable Λ (F.X n) (hp n)).map G))

private theorem point_realized_pairing
    (F : CochainComplex (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) ℤ)
    (a b : ℤ) [F.IsStrictlyGE a] [F.IsStrictlyLE b]
    [∀ n : ℤ, HasRightDual (F.X n)] (U : Scheme.{u}) :
    Nonempty (ExactPairing
      (DerivedCategory.Q.obj (((upperStarFromPointMod Λ U).mapHomologicalComplex
        (.up ℤ)).obj F))
      (DerivedCategory.Q.obj (((upperStarFromPointMod Λ U).mapHomologicalComplex
        (.up ℤ)).obj F.rightDual))) := by
  let G := upperStarFromPointMod Λ U
  let : G.Monoidal := point_module_monoidal Λ U
  have := point_module_colimits Λ U
  exact CochainComplex.realized_bounded_dual_pairing G F a b

private theorem isZero_sheaf_of_refined_cover
    {S : Scheme.{u}} {I : Type*} {J : Type*}
    (U : I → S.ProEt) (α : J → I) (V : ∀ j, (U (α j)).left.Opens)
    (hcover : Presieve.ofArrows (fun j ↦ (V j).toScheme)
      (fun j ↦ (V j).ι ≫ (U (α j)).hom) ∈ Scheme.proetalePrecoverage S)
    (M : Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
    (hM : ∀ j, IsZero ((ProEtale.upperStar Ab.{u + 1} (U (α j)).hom).obj M)) :
    IsZero M := by
  let z : M ⟶ 0 := 0
  have hz (j : J) : IsIso
      ((localizationRestriction Ab.{u + 1} (U (α j)).hom inferInstance).map z) := by
    have : (localizationRestriction Ab.{u + 1} (U (α j)).hom inferInstance).Additive :=
      ⟨fun {_ _} f g ↦ by ext T; rfl⟩
    have h := (hM j).of_iso
      ((upperStarIsoLocalizationRestriction Ab.{u + 1} (U (α j)).hom inferInstance).app M).symm
    exact h.isIso
      ((localizationRestriction Ab.{u + 1} (U (α j)).hom inferInstance).map_isZero
        (isZero_zero _)) _
  have : IsIso z := by
    apply Sheaf.isIso_of_isIso_app_of_mem _ z
    intro T
    refine ⟨_, Scheme.ProEt.ofArrows_baseChange_mem_topology T
      (fun j ↦ (V j).ι ≫ (U (α j)).hom) hcover, ?_⟩
    rintro W f ⟨-, a, -, ⟨j⟩, rfl⟩
    apply isIso_app_of_isIso_localizationRestriction Ab.{u + 1} z
      (U (α j)).hom (hz j) W
      (a.left ≫ pullback.snd T.hom ((V j).ι ≫ (U (α j)).hom) ≫ (V j).ι)
    rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc]
    exact MorphismProperty.Over.w a
  exact (isZero_zero _).of_iso (asIso z)

-- Empty coverings force every sheaf on an empty scheme to vanish.
private theorem isZero_sheaf_on_empty
    (S : Scheme.{u}) [IsEmpty S]
    (M : Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) : IsZero M := by
  apply Sheaf.isZero_of_isZero_obj
  intro U
  have : IsEmpty U.unop.left := ⟨fun x ↦ isEmptyElim (show S from U.unop.hom x)⟩
  exact (Scheme.ProEt.isTerminalSectionsOfIsEmpty M U.unop).isZero

private def forget_pullback_iso {X U : Scheme.{u}} (g : U ⟶ X) :
    upperStar Λ g ⋙ Mod.forget _ ≅ Mod.forget _ ⋙ ProEtale.upperStar Ab.{u + 1} g :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft ((ProEtale.upperStar Ab.{u + 1} g).mapMod _)
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ g))) (Mod.forget _)

private theorem point_models_constructible
    {X : Scheme.{u}} [CompactSpace X]
    (Q : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (F : 𝒰.I₀ → CochainComplex
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) ℤ)
    (hb : ∀ i : 𝒰.I₀, ∃ a b : ℤ, ∀ q : ℤ,
      q < a ∨ b < q → IsZero ((F i).X q))
    (hm : ∀ i : 𝒰.I₀, Nonempty
      (((upperStar Λ (𝒰.f i)).mapDerivedCategory).obj Q ≅
        DerivedCategory.Q.obj (((upperStarFromPointMod Λ (𝒰.X i)).mapHomologicalComplex
          (.up ℤ)).obj (F i))))
    (hfp : ∀ (i : 𝒰.I₀) (q : ℤ), Mod.IsFinitelyPresented Λ ((F i).homology q)) :
    constantModelBoundedConstructible Λ X Q := by
  classical
  have hcoh (i : 𝒰.I₀) (q : ℤ) : Nonempty
      ((upperStar Λ (𝒰.f i)).obj ((DerivedCategory.homologyFunctor _ q).obj Q) ≅
        (upperStarFromPointMod Λ (𝒰.X i)).obj ((F i).homology q)) := by
    obtain ⟨e⟩ := hm i
    exact ⟨((upperStar Λ (𝒰.f i)).mapDerivedCategoryHomologyFunctorIso q).app Q ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ q).app _ ≪≫
      ((upperStarFromPointMod Λ (𝒰.X i)).mapHomologicalComplexHomologyIso
        (.up ℤ) q).app (F i)⟩
  have hlocal (q : ℤ) : HasFiniteConstantLocalModel Λ X
      ((DerivedCategory.homologyFunctor _ q).obj Q) :=
    ⟨𝒰, fun i ↦ ⟨(F i).homology q, hfp i q, hcoh i q⟩⟩
  have hstrat (T : Scheme.{u})
      (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
      (hM : HasFiniteConstantLocalModel Λ T M) : IsFiniteConstantStratified Λ T M :=
    ⟨Scheme.Stratification.trivial T,
      fun _ ↦ pullback_finiteConstantLocalModel Λ (𝟙 T) M hM⟩
  have hcons (q : ℤ) : IsConstantModelConstructible Λ X
      ((DerivedCategory.homologyFunctor _ q).obj Q) := by
    unfold IsConstantModelConstructible
    split
    · exact hstrat _ _ (hlocal q)
    · intro U _
      exact hstrat _ _ (pullback_finiteConstantLocalModel Λ U.ι _ (hlocal q))
  obtain ⟨a, b, hz⟩ : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj Q) := by
    by_cases he : IsEmpty X
    · let := he
      refine ⟨0, 0, fun q _ ↦ ?_⟩
      apply (IsZero.iff_id_eq_zero _).2
      apply (Mod.forget _).map_injective
      exact (isZero_sheaf_on_empty X _).eq_of_src _ _
    · have : Nonempty X := not_isEmpty_iff.mp he
      have (i : 𝒰.I₀) : WeaklyEtale (𝒰.f i) := 𝒰.forgetQc.map_prop i
      let U : 𝒰.I₀ → X.ProEt := fun i ↦ Scheme.ProEt.mk (𝒰.f i)
      obtain ⟨n, hn, α, V, _, hcover⟩ :=
        Scheme.finite_affine_proetale_refinement X 𝒰.I₀ U 𝒰.mem₀
      have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      choose lo hi hF using hb
      obtain ⟨ja, _, hja⟩ := Finset.exists_min_image Finset.univ
        (fun j : Fin n ↦ lo (α j)) Finset.univ_nonempty
      obtain ⟨jb, _, hjb⟩ := Finset.exists_max_image Finset.univ
        (fun j : Fin n ↦ hi (α j)) Finset.univ_nonempty
      refine ⟨lo (α ja), hi (α jb), fun q hq ↦ ?_⟩
      apply (IsZero.iff_id_eq_zero _).2
      apply (Mod.forget _).map_injective
      have hs := isZero_sheaf_of_refined_cover U α V hcover
        (((DerivedCategory.homologyFunctor _ q).obj Q).X) (fun j ↦ ?_)
      · exact hs.eq_of_src _ _
      · obtain ⟨e⟩ := hcoh (α j) q
        have hq' : q < lo (α j) ∨ hi (α j) < q := hq.elim
          (fun h ↦ .inl (h.trans_le (hja j (Finset.mem_univ _))))
          (fun h ↦ .inr ((hjb j (Finset.mem_univ _)).trans_lt h))
        have hp := ((upperStarFromPointMod Λ (𝒰.X (α j))).map_isZero
          (((F (α j)).sc q).isZero_homology_of_isZero_X₂ (hF (α j) q hq'))).of_iso e
        exact ((Mod.forget _).map_isZero hp).of_iso
          ((forget_pullback_iso Λ (𝒰.f (α j))).app _).symm
  have : Q.IsGE a := (DerivedCategory.isGE_iff Q a).2
    (fun q hq ↦ hz q (.inl hq))
  have : Q.IsLE b := (DerivedCategory.isLE_iff Q b).2
    (fun q hq ↦ hz q (.inr hq))
  exact ⟨⟨⟨a, inferInstance⟩, ⟨b, inferInstance⟩⟩, hcons⟩

/-- A locally constant scalar-perfect complex has a bounded constructible dual,
and its derived internal Hom into any ambient object is tensor with that dual.
Source: internal-Hom stability proof, Step 6
(blueprint: lem-sfb-locally-constant-perfect-dual-ctf).

Proof: A finite-projective condensed module is a finite-free retract, hence dualizable.
Strong monoidal point inverse image preserves dualizable terms. A bounded complex
of such terms is dualizable in the derived category, and the pro-etale cover criterion
makes P globally dualizable. Closed braided duality gives the tensor--Hom formula
against every ambient N, including unbounded N.
On each chart construct the signed termwise dual of its point complex. Map its exact
pairing through point inverse image, the homotopy category and the K-flat derived
quotient. Scheme inverse image is strong monoidal, so uniqueness of right duals
identifies this local model with the restriction of the specified relative dual.
The point-perfect dual cohomology theorem gives finite scalar presentations for its
cohomology, including integral and finite-subextension algebraic-closure coefficients.
Exact pullback commutes with cohomology. These presentations therefore give finite
constant local models, hence constructibility by the trivial stratification and its
pullbacks to affine opens. A finite affine refinement selects finitely many bounded
local complexes. Take their common cohomological bounds and descend vanishing by the
refined-cover sheaf criterion. On the empty scheme every abelian sheaf is zero, so
bounds zero and zero suffice. Finite Tor amplitude is a separate assertion supplied
by the existing dual Tor-amplitude theorem. -/
theorem locallyConstantPerfect_dual_constructible
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (P : (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    (hP : IsLocallyConstantPerfectComplex Λ X P) :
    constantModelBoundedConstructible Λ X (relativeInternalHomDual (Mon.mk Λ) X P) ∧
    ∀ N : (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      Nonempty (((derivedHom Λ X).obj (op P)).obj N ≅
      ((derivedTensor Λ X).obj (relativeInternalHomDual (Mon.mk Λ) X P)).obj N)  := by
  classical
  have hd := locally_dualizable Λ P hP
  let : HasRightDual P := hd.some
  let := condensedDerivedBraiding (⟨Λ⟩ : Profinite.CondensedRing.{u}) X
  refine ⟨?_, ?_⟩
  · have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
      (X ↘ Spec (.of k))
    obtain ⟨𝒰, h𝒰⟩ := hP
    choose F hb hp hG he using h𝒰
    choose a b hab using hb
    let (i : 𝒰.I₀) : (F i).IsStrictlyGE (a i) :=
      ((F i).isStrictlyGE_iff (a i)).mpr (fun n hn ↦ hab i n (.inl hn))
    let (i : 𝒰.I₀) : (F i).IsStrictlyLE (b i) :=
      ((F i).isStrictlyLE_iff (b i)).mpr (fun n hn ↦ hab i n (.inr hn))
    let (i : 𝒰.I₀) (n : ℤ) : HasRightDual ((F i).X n) :=
      (point_term_dualizable Λ ((F i).X n) (hp i n)).some
    let D (i : 𝒰.I₀) := (F i).rightDual
    apply point_models_constructible Λ _ 𝒰 D
    · intro i
      refine ⟨-b i, -a i, fun n hn ↦ ?_⟩
      exact hn.elim (fun h ↦ (D i).isZero_of_isStrictlyGE (-b i) n h)
        (fun h ↦ (D i).isZero_of_isStrictlyLE (-a i) n h)
    · intro i
      let : ExactPairing P (relativeInternalHomDual (Mon.mk Λ) X P) :=
        exactPairingCongrRight (ihomUnitIsoRightDual P)
      obtain ⟨hmono⟩ :=
        (condensed_derivedPullback_exact_symmetricMonoidal ⟨Λ⟩ (𝒰.f i)).2
      let := hmono
      let G := (upperStar Λ (𝒰.f i)).mapDerivedCategory
      let epair := ExactPairing.map G P (relativeInternalHomDual (Mon.mk Λ) X P)
      let := epair
      obtain ⟨e⟩ := he i
      let leftPair := exactPairingCongrLeft
        (Y := G.obj (relativeInternalHomDual (Mon.mk Λ) X P)) e.symm
      obtain ⟨rightPair⟩ := point_realized_pairing Λ (F i) (a i) (b i) (𝒰.X i)
      exact ⟨rightDualIso leftPair rightPair⟩
    · intro i q
      exact admissiblePointPerfect_dual_cohomology Λ ℓ hΛ (F i) (hp i) q
  · intro N
    let := BraidedCategory.exactPairing_swap P Pᘁ
    let := MonoidalClosed.isIso_ihomUnitTensorToIhom Pᘁ P N
    exact ⟨(asIso (MonoidalClosed.ihomUnitTensorToIhom P N)).symm⟩

end AlgebraicGeometry.ProEtale.CondensedRing
