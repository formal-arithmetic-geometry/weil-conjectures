/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.Data.ZMod.Basic
import WeilConjectures.AlgebraicGeometry.FiniteLocalAbelianForget
import WeilConjectures.AlgebraicGeometry.FiniteLocalCyclicModuleForget
import WeilConjectures.AlgebraicGeometry.KilledSheafModuleLift
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison

/-!
# Constructibility of torsion abelian sheaves and of cyclic-coefficient module sheaves

## References

* Stacks Project, Tags 03RW (2), (3), 095E and 03RU
-/

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private instance cyclicForgetFull (n : ℕ) :
    (forget₂ (ModuleCat.{v + 1} (ULift.{v + 1} (ZMod n)))
      AddCommGrpCat.{v + 1}).Full where
  map_surjective {M N} f := by
    let φ : M →+ N := f.hom
    refine ⟨ModuleCat.ofHom { φ with map_smul' := ?_ }, rfl⟩
    intro r x
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective r.down
    have hr : r = (a : ULift.{v + 1} (ZMod n)) := ULift.ext ha.symm
    change φ (r • x) = r • φ x
    rw [hr, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    exact map_zsmul φ a x

private theorem finiteAbelianLocal_congr {Y : Scheme.{v}}
    {G H : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}} (e : G ≅ H) :
    (IsLocallyConstantSheaf G ∧
      ∀ (Ω : Type v) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
        Finite (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{v + 1})).obj G)) ↔
    (IsLocallyConstantSheaf H ∧
      ∀ (Ω : Type v) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
        Finite (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{v + 1})).obj H)) := by
  suffices h : ∀ {G H : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}},
      (G ≅ H) → (IsLocallyConstantSheaf G ∧
        ∀ (Ω : Type v) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
          Finite (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{v + 1})).obj G)) →
      (IsLocallyConstantSheaf H ∧
        ∀ (Ω : Type v) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
          Finite (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{v + 1})).obj H)) from
    ⟨h e, h e.symm⟩
  intro G H e hG
  have := hG.1
  refine ⟨IsLocallyConstantSheaf.of_iso e, ?_⟩
  intro Ω _ _ s
  have := hG.2 Ω s
  exact Finite.of_equiv _
    ((CategoryTheory.forget AddCommGrpCat.{v + 1}).mapIso
      (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{v + 1})).mapIso e)).toEquiv

private noncomputable def abelianSetPullbackIso {X Y : Scheme.{v}} (g : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    (etaleSetPullback g).obj
      ((sheafCompose X.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{v + 1})).obj F) ≅
    (sheafCompose Y.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{v + 1})).obj
      ((Etale.upperStar AddCommGrpCat.{v + 1} g).obj F) := by
  let B := MorphismProperty.Over.pullback @Etale ⊤ g
  let U := CategoryTheory.forget AddCommGrpCat.{v + 1}
  let (V : Y.Etaleᵒᵖ) : IsFiltered (CostructuredArrow B.op V) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence B V.unop)
  let : Limits.PreservesFilteredColimitsOfSize.{v, v + 1} U :=
    Limits.preservesFilteredColimitsOfSize_shrink.{v + 1, v + 1, v, v + 1} U
  let (V : Y.Etaleᵒᵖ) : U.PreservesPointwiseLeftKanExtensionAt F.obj B.op V := by
    infer_instance
  have : U.PreservesLeftKanExtension F.obj B.op := by infer_instance
  have : Y.smallEtaleTopology.PreservesSheafification U := by infer_instance
  let e := U.leftKanExtensionCompIsoOfPreserves F.obj B.op
  exact (presheafToSheaf Y.smallEtaleTopology (Type (v + 1))).mapIso e.symm ≪≫
    (sheafComposeNatIso Y.smallEtaleTopology U
      (sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{v + 1})
      (sheafificationAdjunction Y.smallEtaleTopology (Type (v + 1)))).app
        (B.op.leftKanExtension F.obj)

private noncomputable def moduleAbelianPullbackIso {X Y : Scheme.{v}}
    (n : ℕ) (g : Y ⟶ X)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{v + 1} (ULift.{v + 1} (ZMod n)))) :
    (Etale.upperStar AddCommGrpCat.{v + 1} g).obj
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{v + 1} (ULift.{v + 1} (ZMod n)))
          AddCommGrpCat.{v + 1})).obj M) ≅
    (sheafCompose Y.smallEtaleTopology
      (forget₂ (ModuleCat.{v + 1} (ULift.{v + 1} (ZMod n))) AddCommGrpCat.{v + 1})).obj
      ((Etale.upperStar (ModuleCat.{v + 1} (ULift.{v + 1} (ZMod n))) g).obj M) := by
  let B := MorphismProperty.Over.pullback @Etale ⊤ g
  let U := forget₂ (ModuleCat.{v + 1} (ULift.{v + 1} (ZMod n))) AddCommGrpCat.{v + 1}
  let (V : Y.Etaleᵒᵖ) : IsFiltered (CostructuredArrow B.op V) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence B V.unop)
  let : Limits.PreservesFilteredColimitsOfSize.{v, v + 1} U :=
    Limits.preservesFilteredColimitsOfSize_shrink.{v + 1, v + 1, v, v + 1} U
  let (V : Y.Etaleᵒᵖ) : U.PreservesPointwiseLeftKanExtensionAt M.obj B.op V := by
    infer_instance
  have : U.PreservesLeftKanExtension M.obj B.op := by infer_instance
  have : Y.smallEtaleTopology.PreservesSheafification U := by
    constructor
    intro P Q φ hφ
    change Y.smallEtaleTopology.W (Functor.whiskerRight φ U)
    rw [Y.smallEtaleTopology.W_iff_isLocallyBijective] at hφ ⊢
    have := hφ.1
    have := hφ.2
    exact ⟨⟨fun x y h ↦ Presheaf.equalizerSieve_mem Y.smallEtaleTopology φ x y h⟩,
      ⟨fun s ↦ Presheaf.imageSieve_mem Y.smallEtaleTopology φ s⟩⟩
  let e := U.leftKanExtensionCompIsoOfPreserves M.obj B.op
  exact (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}).mapIso e.symm ≪≫
    (sheafComposeNatIso Y.smallEtaleTopology U
      (sheafificationAdjunction Y.smallEtaleTopology
        (ModuleCat.{v + 1} (ULift.{v + 1} (ZMod n))))
      (sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{v + 1})).app
        (B.op.leftKanExtension M.obj)

private theorem finiteSetLocal_congr {Y : Scheme.{v}}
    {G H : Sheaf Y.smallEtaleTopology (Type (v + 1))} (e : G ≅ H) :
    IsLisseEtaleSheafOfSets G ↔
      IsLisseEtaleSheafOfSets H := by
  suffices h : ∀ {G H : Sheaf Y.smallEtaleTopology (Type (v + 1))}, (G ≅ H) →
      IsLisseEtaleSheafOfSets G →
      IsLisseEtaleSheafOfSets H from ⟨h e, h e.symm⟩
  intro G H e hG
  constructor
  · obtain ⟨𝒰, h𝒰⟩ := hG.1
    refine ⟨𝒰, fun i ↦ ?_⟩
    have := h𝒰 i
    exact Sheaf.isConstant_congr _
      ((Y.smallEtaleTopology.overPullback (Type (v + 1))
        (𝒰.etalePrecoverageToEtale i)).mapIso e)
  · refine Scheme.isFiniteSheaf_of_finite_algClosed_stalks _ fun Ω _ _ s ↦ ?_
    have : Finite ((pointSmallEtale s).sheafFiber.obj G) :=
      hG.finite_sheafFiber Ω s
    exact Finite.of_equiv _
      (((pointSmallEtale s).sheafFiber (A := Type (v + 1))).mapIso e).toEquiv

-- Comparing coefficient structures and stratifications requires substantial reduction.
/-- An abelian sheaf killed by a positive integer is torsion and has a unique cyclic-ring
module structure. Underlying-set constructibility of the curve coefficient pair agrees
with constructibility of the module sheaf, using the same partitions and immersions.
Uniqueness of the module structure is stated in the fiber of the forgetful functor: any
other module lift of `F` has exactly one module isomorphism compatible with the given
identifications with `F`. -/
theorem constructible_torsion_modules_agree
    {k : Type v} [Field k] [IsAlgClosed k] {C : Scheme.{v}}
    (f : C ⟶ Spec (.of k)) [IsCurve f]
    (n : ℕ) (hn : 0 < n) (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{v + 1})
    (hF : n • 𝟙 F = 0) :
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let R := ULift.{v + 1} (ZMod n)
    let U := sheafCompose C.smallEtaleTopology
      (forget₂ (ModuleCat.{v + 1} R) AddCommGrpCat.{v + 1})
    ∃ hT : C.IsTorsionAbelianSheaf F,
      let P : CurveCoefficientPair k := ⟨C, f, inferInstance, F,
        (Scheme.isTorsionAbelianSheaf_characterizations F).1.mp hT⟩
      ∃ (M : Sheaf C.smallEtaleTopology (ModuleCat.{v + 1} R)) (e : U.obj M ≅ F),
        (∀ (N : Sheaf C.smallEtaleTopology (ModuleCat.{v + 1} R)) (eN : U.obj N ≅ F),
          ∃! a : M ≅ N, U.mapIso a ≪≫ eN = e) ∧
        ((Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{v + 1})).obj P.F)) ↔
          IsConstructibleEtaleModuleSheaf M) ∧
        ∀ S : Stratification C,
          ((∀ i : Fin S.n,
              IsLisseEtaleSheafOfSets
                ((etaleSetPullback (S.immersion i)).obj
                  ((sheafCompose C.smallEtaleTopology
                    (CategoryTheory.forget AddCommGrpCat.{v + 1})).obj F))) ↔
            ∀ i : Fin S.n,
              let G := (Etale.upperStar AddCommGrpCat.{v + 1} (S.immersion i)).obj F
              IsLocallyConstantSheaf G ∧
                ∀ (Ω : Type v) [Field Ω] [IsAlgClosed Ω]
                    (s : Spec (.of Ω) ⟶ S.domain i),
                  Finite (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{v + 1})).obj G)) ∧
          ((∀ i : Fin S.n,
              let G := (Etale.upperStar AddCommGrpCat.{v + 1} (S.immersion i)).obj F
              IsLocallyConstantSheaf G ∧
                ∀ (Ω : Type v) [Field Ω] [IsAlgClosed Ω]
                    (s : Spec (.of Ω) ⟶ S.domain i),
                  Finite (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{v + 1})).obj G)) ↔
            ∀ i : Fin S.n,
              let G := (Etale.upperStar (ModuleCat.{v + 1} R) (S.immersion i)).obj M
              ∃ d : LocallyConstantDatum G, ∀ j : d.cover.I₀,
                ∃ A : ModuleCat.{v + 1} R, Finite A ∧
                  Nonempty ((G.over (d.cover.etalePrecoverageToEtale j)) ≅
                    (constantSheaf
                      ((S.domain i).smallEtaleTopology.over
                        (d.cover.etalePrecoverageToEtale j))
                      (ModuleCat.{v + 1} R)).obj A)) := by
  classical
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let R := ULift.{v + 1} (ZMod n)
  let U := sheafCompose C.smallEtaleTopology
    (forget₂ (ModuleCat.{v + 1} R) AddCommGrpCat.{v + 1})
  have hT : C.IsTorsionAbelianSheaf F := by
    apply (isTorsionAbelianSheaf_characterizations F).1.mpr
    apply Sheaf.IsTorsion.of_forall_isAddTorsion
    intro V x
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, ?_⟩
    have h := congrArg (fun a : F ⟶ F ↦ a.hom.app V x) hF
    change ((n • (𝟙 (F.obj.obj V))).hom) x = 0 at h
    simpa using h
  obtain ⟨M, ⟨e⟩⟩ := exists_module_sheaf_of_nsmul_id_eq_zero C n F hF
  have hlocal {Y : Scheme.{v}} (g : Y ⟶ C) :
      IsLisseEtaleSheafOfSets
        ((etaleSetPullback g).obj
          ((sheafCompose C.smallEtaleTopology
            (CategoryTheory.forget AddCommGrpCat.{v + 1})).obj F)) ↔
      ∃ d : LocallyConstantDatum
          ((Etale.upperStar (ModuleCat.{v + 1} R) g).obj M), ∀ j : d.cover.I₀,
        ∃ A : ModuleCat.{v + 1} R, Finite A ∧
          Nonempty ((((Etale.upperStar (ModuleCat.{v + 1} R) g).obj M).over
            (d.cover.etalePrecoverageToEtale j)) ≅
              (constantSheaf (Y.smallEtaleTopology.over
                (d.cover.etalePrecoverageToEtale j)) (ModuleCat.{v + 1} R)).obj A) :=
    ((finiteSetLocal_congr (abelianSetPullbackIso g F)).trans
      (finite_local_abelian_forget_iff _)).trans
      ((finiteAbelianLocal_congr
        ((Etale.upperStar AddCommGrpCat.{v + 1} g).mapIso e.symm ≪≫
          moduleAbelianPullbackIso n g M)).trans
        (finite_local_cyclic_module_forget_iff n _))
  refine ⟨hT, M, e, ?_, ?_, ?_⟩
  · intro N eN
    refine ⟨U.preimageIso (e ≪≫ eN.symm), ?_, ?_⟩
    · apply Iso.ext
      change U.map (U.preimage (e.hom ≫ eN.inv)) ≫ eN.hom = e.hom
      simp
    · intro a ha
      apply U.mapIso_injective
      apply Iso.ext
      have h := congrArg Iso.hom ha
      change U.map a.hom ≫ eN.hom = e.hom at h
      change U.map a.hom = U.map (U.preimage (e.hom ≫ eN.inv))
      rw [Functor.map_preimage]
      calc
        U.map a.hom = (U.map a.hom ≫ eN.hom) ≫ eN.inv := by simp
        _ = e.hom ≫ eN.inv := by rw [h]
  · constructor
    · rintro ⟨S, hS⟩
      let T : Stratification C :=
        { toStratification := S.toStratification
          domain := S.domain
          immersion := S.immersion
          isImmersion := S.isImmersion
          range_immersion := S.range_immersion }
      exact ⟨T, fun i ↦ (hlocal (S.immersion i)).mp (hS i)⟩
    · rintro ⟨S, hS⟩
      let T : Stratification C :=
        { toStratification := S.toStratification
          domain := S.domain
          immersion := S.immersion
          isImmersion := S.isImmersion
          range_immersion := S.range_immersion }
      exact ⟨T, fun i ↦ (hlocal (S.immersion i)).mpr (hS i)⟩
  · intro S
    constructor
    · apply forall_congr'
      intro i
      exact (finiteSetLocal_congr (abelianSetPullbackIso (S.immersion i) F)).trans
        (finite_local_abelian_forget_iff _)
    · apply forall_congr'
      intro i
      exact (finiteAbelianLocal_congr
        ((Etale.upperStar AddCommGrpCat.{v + 1} (S.immersion i)).mapIso e.symm ≪≫
          moduleAbelianPullbackIso n (S.immersion i) M)).trans
        (finite_local_cyclic_module_forget_iff n _)

end AlgebraicGeometry.Scheme
