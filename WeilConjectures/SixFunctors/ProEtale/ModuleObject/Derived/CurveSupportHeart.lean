/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CurveWeil.CurveSupportHeartDefs
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CurveSupportDescription
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CurveSupportTiltConstruction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.Triangulated.TStructure.ShortExact
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstructibleTruncations

/-! # Support and cosupport describe the perverse heart on a smooth curve

Source: latest blueprint, sec-deligne-laumon-a1/sk-lem-wft-curve-heart/
thm-a1-curve-perverse-heart.md and its proof
(thm-a1-curve-perverse-heart.proof.md), Steps 0--6.
The finite-or-algebraically-closed field scope follows Wei Yang #1441, item 36.
(blueprint: thm-a1-curve-perverse-heart).

This statement uses the registered condensed support classes, not a definition of the
perverse classes by the cohomological description that the theorem must establish.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open scoped CategoryTheory.Obj ZeroObject

private theorem sixTermOfAmplitude
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (Q : ObjectProperty (DerivedCategory A)) [Q.IsTriangulated]
    (t : TStructure Q.FullSubcategory) (P : ObjectProperty Q.FullSubcategory)
    (hP : P = t.heart)
    (hamp : ∀ K : P.FullSubcategory, ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor A i).obj K.obj.obj))
    (S : ShortComplex P.FullSubcategory) (hS : S.ShortExact) :
    ∃ d : S.X₃.obj.obj ⟶ S.X₁.obj.obj⟦(1 : ℤ)⟧,
      Pretriangulated.Triangle.mk S.f.hom.hom S.g.hom.hom d ∈ distTriang _ ∧
      let δ := DerivedCategory.HomologySequence.δ
        (Pretriangulated.Triangle.mk S.f.hom.hom S.g.hom.hom d) (-1) 0
      Mono ((DerivedCategory.homologyFunctor A (-1)).map S.f.hom.hom) ∧
      Epi ((DerivedCategory.homologyFunctor A 0).map S.g.hom.hom) ∧
      (ComposableArrows.mk₂ ((DerivedCategory.homologyFunctor A (-1)).map S.f.hom.hom)
        ((DerivedCategory.homologyFunctor A (-1)).map S.g.hom.hom)).Exact ∧
      (ComposableArrows.mk₂ ((DerivedCategory.homologyFunctor A (-1)).map S.g.hom.hom)
        δ).Exact ∧
      (ComposableArrows.mk₂ δ ((DerivedCategory.homologyFunctor A 0).map S.f.hom.hom)).Exact ∧
      (ComposableArrows.mk₂ ((DerivedCategory.homologyFunctor A 0).map S.f.hom.hom)
        ((DerivedCategory.homologyFunctor A 0).map S.g.hom.hom)).Exact := by
  subst P
  let := t.hasHeartFullSubcategory
  obtain ⟨d, hd⟩ := (t.shortExact_iff_exists_distTriang S).mp hS
  have hd' := Q.ι.map_distinguished _ hd
  let δ := Q.ι.map d ≫ (Q.ι.commShiftIso (1 : ℤ)).hom.app S.X₁.obj
  change Pretriangulated.Triangle.mk S.f.hom.hom S.g.hom.hom δ ∈ distTriang _ at hd'
  let T := Pretriangulated.Triangle.mk S.f.hom.hom S.g.hom.hom δ
  refine ⟨δ, hd', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hd' (-2) (-1)).mpr
    exact (hamp S.X₃ (-2) (by omega) (by omega)).eq_of_src _ _
  · apply (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hd' 0 1).mpr
    exact (hamp S.X₁ 1 (by omega) (by omega)).eq_of_tgt _ _
  · exact (DerivedCategory.HomologySequence.exact₂ T hd' (-1)).exact_toComposableArrows
  · exact (DerivedCategory.HomologySequence.exact₃ T hd' (-1) 0).exact_toComposableArrows
  · exact (DerivedCategory.HomologySequence.exact₁ T hd' (-1) 0).exact_toComposableArrows
  · exact (DerivedCategory.HomologySequence.exact₂ T hd' 0).exact_toComposableArrows

private theorem singleOfOneDegree
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (K : DerivedCategory A) (n : ℤ) [K.IsGE n] [K.IsLE n] :
    Nonempty (K ≅ (DerivedCategory.singleFunctor A n).obj
      ((DerivedCategory.homologyFunctor A n).obj K)) := by
  obtain ⟨M, ⟨e⟩⟩ := K.exists_iso_singleFunctor_obj_of_isGE_of_isLE n
  let h := (DerivedCategory.homologyFunctor A n).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso A n).app M
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor A n).mapIso h.symm⟩

private theorem standardTruncationEndpoints
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (K : DerivedCategory A)
    (hamp : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor A i).obj K)) :
    Nonempty ((DerivedCategory.TStructure.t.truncLE (-1)).obj K ≅
      ((DerivedCategory.singleFunctor A 0).obj
        ((DerivedCategory.homologyFunctor A (-1)).obj K))⟦(1 : ℤ)⟧) ∧
    Nonempty ((DerivedCategory.TStructure.t.truncGE 0).obj K ≅
      (DerivedCategory.singleFunctor A 0).obj
        ((DerivedCategory.homologyFunctor A 0).obj K)) := by
  have : K.IsGE (-1) := (DerivedCategory.isGE_iff K (-1)).mpr
    (fun i hi ↦ hamp i (by omega) (by omega))
  have : K.IsLE 0 := (DerivedCategory.isLE_iff K 0).mpr
    (fun i hi ↦ hamp i (by omega) (by omega))
  have : IsIso ((DerivedCategory.homologyFunctor A (-1)).map
      ((DerivedCategory.TStructure.t.truncLEι (-1)).app K)) :=
    DerivedCategory.isIso_homologyFunctor_map_truncLTι_app K 0 (-1) (by omega)
  have : IsIso ((DerivedCategory.homologyFunctor A 0).map
      ((DerivedCategory.TStructure.t.truncGEπ 0).app K)) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K 0 0 (by omega)
  obtain ⟨e₁⟩ := singleOfOneDegree
    ((DerivedCategory.TStructure.t.truncLE (-1)).obj K) (-1)
  obtain ⟨e₂⟩ := singleOfOneDegree ((DerivedCategory.TStructure.t.truncGE 0).obj K) 0
  constructor
  · exact ⟨e₁ ≪≫ (DerivedCategory.singleFunctor A (-1)).mapIso
      (asIso ((DerivedCategory.homologyFunctor A (-1)).map
        ((DerivedCategory.TStructure.t.truncLEι (-1)).app K))) ≪≫
      (((DerivedCategory.singleFunctors A).shiftIso 1 (-1) 0 (by omega)).app _).symm⟩
  · exact ⟨e₂ ≪≫ (DerivedCategory.singleFunctor A 0).mapIso
      (asIso ((DerivedCategory.homologyFunctor A 0).map
        ((DerivedCategory.TStructure.t.truncGEπ 0).app K))).symm⟩

private theorem truncationShortExact
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (Q : ObjectProperty (DerivedCategory A)) [Q.IsTriangulated]
    (t : TStructure Q.FullSubcategory) (P : ObjectProperty Q.FullSubcategory)
    (hP : P = t.heart) (L K R : P.FullSubcategory)
    (e₁ : L.obj.obj ≅ (DerivedCategory.TStructure.t.truncLE (-1)).obj K.obj.obj)
    (e₂ : R.obj.obj ≅ (DerivedCategory.TStructure.t.truncGE 0).obj K.obj.obj) :
    ∃ S : ShortComplex P.FullSubcategory,
      S.X₁ = L ∧ S.X₂ = K ∧ S.X₃ = R ∧ S.ShortExact ∧
      ∃ (f : L ⟶ K) (g : K ⟶ R), HEq S.f f ∧ HEq S.g g ∧
        f.hom.hom = e₁.hom ≫ (DerivedCategory.TStructure.t.truncLEι (-1)).app K.obj.obj ∧
        g.hom.hom = (DerivedCategory.TStructure.t.truncGEπ 0).app K.obj.obj ≫ e₂.inv := by
  subst P
  let := t.hasHeartFullSubcategory
  let T := (DerivedCategory.TStructure.t.triangleLTGE 0).obj K.obj.obj
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished 0 K.obj.obj
  let f : L ⟶ K := ObjectProperty.homMk (ObjectProperty.homMk
    (e₁.hom ≫ (DerivedCategory.TStructure.t.truncLEι (-1)).app K.obj.obj))
  let g : K ⟶ R := ObjectProperty.homMk (ObjectProperty.homMk
    ((DerivedCategory.TStructure.t.truncGEπ 0).app K.obj.obj ≫ e₂.inv))
  let d := e₂.hom ≫ T.mor₃ ≫ (shiftFunctor (DerivedCategory A) (1 : ℤ)).map e₁.inv
  have hd : Pretriangulated.Triangle.mk f.hom.hom g.hom.hom d ∈ distTriang _ := by
    refine Pretriangulated.isomorphic_distinguished _ hT _
      (Pretriangulated.Triangle.isoMk _ _ e₁ (Iso.refl _) e₂ ?_ ?_ ?_)
    · simp [f, TStructure.truncLEι]
    · simp [g]
    · simp [d, T]
  have hfg : f ≫ g = 0 := by
    apply (t.heart.ι ⋙ Q.ι).map_injective
    exact Pretriangulated.comp_distTriang_mor_zero₁₂ _ hd
  let S := ShortComplex.mk f g hfg
  refine ⟨S, rfl, rfl, rfl, ?_, f, g, HEq.rfl, HEq.rfl, rfl, rfl⟩
  apply (t.shortExact_iff_exists_distTriang S).mpr
  refine ⟨ObjectProperty.homMk (d ≫ (Q.ι.commShiftIso (1 : ℤ)).inv.app L.obj), ?_⟩
  change Q.ι.mapTriangle.obj _ ∈ distTriang _
  change Pretriangulated.Triangle.mk f.hom.hom g.hom.hom
    ((d ≫ (Q.ι.commShiftIso (1 : ℤ)).inv.app L.obj) ≫
      (Q.ι.commShiftIso (1 : ℤ)).hom.app L.obj) ∈ distTriang _
  simpa [Category.assoc] using hd

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem constantModelIsoClosed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (IsConstantModelConstructible Λ X) := by
  have hloc (Y : Scheme.{u})
      (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (e : M ≅ N) (h : HasFiniteConstantLocalModel Λ Y M) :
      HasFiniteConstantLocalModel Λ Y N := by
    obtain ⟨U, hU⟩ := h
    refine ⟨U, fun i ↦ ?_⟩
    obtain ⟨Q, hQ, ⟨eQ⟩⟩ := hU i
    exact ⟨Q, hQ, ⟨((upperStar Λ (U.f i)).mapIso e).symm ≪≫ eQ⟩⟩
  have hstrat (Y : Scheme.{u})
      (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (e : M ≅ N) (h : IsFiniteConstantStratified Λ Y M) :
      IsFiniteConstantStratified Λ Y N := by
    obtain ⟨S, hS⟩ := h
    exact ⟨S, fun a ↦ hloc _ _ _ ((upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩
  constructor
  intro M N e h
  unfold IsConstantModelConstructible at h ⊢
  split_ifs at h ⊢ with hX
  · exact hstrat _ _ _ e h
  · intro U hU
    exact hstrat _ _ _ ((upperStar Λ U.ι).mapIso e) (h U hU)

private theorem punctualOfIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    {M N : CondensedCurvePerverse.Modules Λ X} (e : M ≅ N)
    (hM : CondensedCurvePerverse.IsPunctual Λ X M) :
    CondensedCurvePerverse.IsPunctual Λ X N := by
  let := constantModelIsoClosed Λ X
  obtain ⟨hM, U, hf, hc, hz⟩ := hM
  exact ⟨ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X) e hM,
    U, hf, hc, (((upperStar Λ U.ι).mapIso e).isZero_iff).mp hz⟩

private theorem punctualOfIsZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : CondensedCurvePerverse.Modules Λ X) (hz : IsZero M) :
    CondensedCurvePerverse.IsPunctual Λ X M := by
  have hlocal (T : Scheme.{u})
      (N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
      (hN : IsZero N) : HasFiniteConstantLocalModel Λ T N := by
    refine ⟨.singleton (𝟙 T) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
    refine ⟨0, ?_, ⟨?_⟩⟩
    · exact ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩
    · exact ((upperStar Λ _).map_isZero hN).iso
        (((upperStarFromPoint _).mapMod Λ).map_isZero (isZero_zero _))
  have hstrat (T : Scheme.{u})
      (N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
      (hN : IsZero N) : IsFiniteConstantStratified Λ T N := by
    refine ⟨Scheme.Stratification.trivial T, fun a ↦ ?_⟩
    exact hlocal _ _ ((upperStar Λ _).map_isZero hN)
  refine ⟨?_, ⊤, by simp, by simp, (upperStar Λ _).map_isZero hz⟩
  classical
  unfold IsConstantModelConstructible
  split
  · exact hstrat X _ hz
  · exact fun U _ ↦ hstrat _ _ ((upperStar Λ U.ι).map_isZero hz)

private theorem noPunctualOfIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    {M N : CondensedCurvePerverse.Modules Λ X} (e : M ≅ N)
    (hN : CondensedCurvePerverse.HasNoPunctualSubsheaf Λ X N) :
    CondensedCurvePerverse.HasNoPunctualSubsheaf Λ X M := by
  intro G i hi hp
  have : Mono i := hi
  exact hN G (i ≫ e.hom) inferInstance hp

private theorem noPunctualOfIsZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : CondensedCurvePerverse.Modules Λ X) (hz : IsZero M) :
    CondensedCurvePerverse.HasNoPunctualSubsheaf Λ X M := by
  intro G i hi _
  have : Mono i := hi
  exact IsZero.of_mono i hz


variable (ell : ℕ) [Fact ell.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
  (hbase : Finite k ∨ IsAlgClosed k)
  (C : Over (Spec (.of k))) [Smooth C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]

local notation "Λ" => Profinite.padicAlgClRingObj ell
local notation "R" => condensedRingObj Λ C.left
local notation "B" => BoundedConstructible R
local notation "M" => Mod (Sheaf (Scheme.ProEt.topology C.left) Ab) R
local notation "H" => DerivedCategory.homologyFunctor M
local notation "Perv" => FiniteOrClosedPerverseHeart ell hbase C
local notation "Punctual" => CondensedCurvePerverse.IsPunctual Λ C.left
local notation "NoPunctual" => CondensedCurvePerverse.HasNoPunctualSubsheaf Λ C.left

private theorem standardEndpointsInHeart
    (hchar : ∀ K : B, Perv K ↔
      (∀ a : ℤ, a ≠ -1 → a ≠ 0 → IsZero ((H a).obj K.obj)) ∧
      Punctual ((H 0).obj K.obj) ∧ NoPunctual ((H (-1)).obj K.obj))
    (P : (Perv).FullSubcategory) :
    ∃ A D : (Perv).FullSubcategory,
      Nonempty (A.obj.obj ≅ (DerivedCategory.TStructure.t.truncLE (-1)).obj P.obj.obj) ∧
      Nonempty (D.obj.obj ≅ (DerivedCategory.TStructure.t.truncGE 0).obj P.obj.obj) := by
  obtain ⟨s, hs⟩ := (condensedConstructibleTruncations_exists ell C.left).2.1
  obtain ⟨eL⟩ := (hs.2.2.2.2.2 (-1)).1
  obtain ⟨eD⟩ := (hs.2.2.2.2.2 0).2
  let L : B := ⟨(DerivedCategory.TStructure.t.truncLE (-1)).obj P.obj.obj,
    (boundedConstructible R).prop_of_iso (eL.app P.obj)
      ((s.truncLE (-1)).obj P.obj).property⟩
  let D' : B := ⟨(DerivedCategory.TStructure.t.truncGE 0).obj P.obj.obj,
    (boundedConstructible R).prop_of_iso (eD.app P.obj)
      ((s.truncGE 0).obj P.obj).property⟩
  have hP := (hchar P.obj).mp P.property
  have hL (a : ℤ) (ha : a < 0) : Nonempty ((H a).obj L.obj ≅ (H a).obj P.obj.obj) := by
    have : IsIso ((H a).map
        ((DerivedCategory.TStructure.t.truncLEι (-1)).app P.obj.obj)) :=
      DerivedCategory.isIso_homologyFunctor_map_truncLTι_app P.obj.obj 0 a ha
    exact ⟨asIso ((H a).map
      ((DerivedCategory.TStructure.t.truncLEι (-1)).app P.obj.obj))⟩
  have hD (a : ℤ) (ha : 0 ≤ a) : Nonempty ((H a).obj P.obj.obj ≅ (H a).obj D'.obj) := by
    have := DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app P.obj.obj 0 a ha
    exact ⟨asIso ((H a).map
      ((DerivedCategory.TStructure.t.truncGEπ 0).app P.obj.obj))⟩
  have hLp : Perv L := by
    apply (hchar L).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro a ha₁ ha₀
      by_cases ha : a < 0
      · obtain ⟨e⟩ := hL a ha
        exact e.isZero_iff.mpr (hP.1 a ha₁ ha₀)
      · exact DerivedCategory.isZero_of_isLE L.obj (-1) a (by omega)
    · exact punctualOfIsZero Λ C.left _
        (DerivedCategory.isZero_of_isLE L.obj (-1) 0 (by omega))
    · obtain ⟨e⟩ := hL (-1) (by omega)
      exact noPunctualOfIso Λ C.left e hP.2.2
  have hDp : Perv D' := by
    apply (hchar D').mpr
    refine ⟨?_, ?_, ?_⟩
    · intro a ha₁ ha₀
      by_cases ha : 0 ≤ a
      · obtain ⟨e⟩ := hD a ha
        exact e.isZero_iff.mp (hP.1 a ha₁ ha₀)
      · exact DerivedCategory.isZero_of_isGE D'.obj 0 a (by omega)
    · obtain ⟨e⟩ := hD 0 (by omega)
      exact punctualOfIso Λ C.left e hP.2.1
    · exact noPunctualOfIsZero Λ C.left _
        (DerivedCategory.isZero_of_isGE D'.obj 0 (-1) (by omega))
  exact ⟨⟨L, hLp⟩, ⟨D', hDp⟩, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩

/-- The perverse t-structure on a smooth curve, all five clauses.
Source: latest blueprint thm-a1-curve-perverse-heart.md; proof Steps 0--6;
field-scope correction Wei Yang #1441 item 36 (blueprint: thm-a1-curve-perverse-heart).

Proof: Step 0 descends lisse sheaves to finite coefficient extensions and applies the
integral lattice reductions to exclude punctual subobjects. For constructible F,
ker(F → j_*j^*F) is its maximal punctual subsheaf and its quotient is punctual-free.
Step 1 rewrites support dimensions on a curve as vanishing in positive degrees and
punctuality in degree zero. Step 2 uses smooth purity, lisse tensor duality and standard
truncations to compute dual cohomology on a dense lisse open and its finite complement.
Its residue fields remain finite or algebraically closed by the stipulated field scope.
Step 3 uses evaluation-compatible closed-costalk duality, biduality, constructibility,
and the canonical counit/unit localization triangle. Its bottom cohomology identifies
the negative costalk with the punctual radical and proves the cosupport description.
Step 4 proves shifts, orthogonality through H^0, and truncation existence by taking the
fibre of tau≤0 K → (H^0 K/F_p)[0], then using the octahedron. Ordinary bounds [a,b]
give perverse bounds [a,b+1]. The general heart theorem gives abelianness and intersection
gives clause (3). Step 5 applies punctual-freeness to ordinary j_*N and to punctual
sheaves in degree zero. Step 6 uses the canonical ordinary truncation triangle with
perverse endpoints, then identifies heart short exact sequences with triangles and
takes their long exact ordinary cohomology sequence. -/
theorem curveSupportHeart (_hpure : C.left.IsPureDimension 1) :
    CurveSupportDescription ell hbase C ∧ CurveSupportHeart ell hbase C ∧
      CurveSupportBasicObjects ell hbase C ∧ CurveSupportTruncationExact ell hbase C ∧
      CurveSupportSixTermExact ell hbase C := by
  have hdesc := curveSupportDescription_on_curve ell hbase C _hpure
  obtain ⟨t, hle, hge, hb, hheart, hbasic⟩ :=
    curveSupportTiltConstruction ell hbase C _hpure hdesc
  have hab : Nonempty (Abelian (Perv).FullSubcategory) := by
    rw [hheart]
    let := t.hasHeartFullSubcategory
    exact ⟨t.abelianHeart t.heart.FullSubcategory⟩
  have hchar (K : B) : Perv K ↔
      (∀ a : ℤ, a ≠ -1 → a ≠ 0 → IsZero ((H a).obj K.obj)) ∧
      Punctual ((H 0).obj K.obj) ∧ NoPunctual ((H (-1)).obj K.obj) := by
    change (FiniteOrClosedPerverseLEZero ell hbase C K ∧
      FiniteOrClosedPerverseGEZero ell hbase C K) ↔ _
    rw [hdesc.1 K, hdesc.2 K]
    constructor
    · rintro ⟨⟨hup, hp⟩, hlo, hn⟩
      refine ⟨?_, hp, hn⟩
      intro a ha₁ ha₀
      by_cases ha : 0 < a
      · exact hup a ha
      · exact hlo a (by omega)
    · rintro ⟨hamp, hp, hn⟩
      exact ⟨⟨fun a ha ↦ hamp a (by omega) (by omega), hp⟩,
        fun a ha ↦ hamp a (by omega) (by omega), hn⟩
  refine ⟨hdesc, ⟨⟨t, hle, hge, hb⟩, hab, hchar⟩, hbasic, ?_, ?_⟩
  · intro P
    obtain ⟨A, D, ⟨e₁⟩, ⟨e₂⟩⟩ := standardEndpointsInHeart ell hbase C hchar P
    obtain ⟨S, h₁, h₂, h₃, hS, f, g, hf, hg, hfe, hge'⟩ :=
      truncationShortExact (boundedConstructible R) t Perv hheart A P D e₁ e₂
    obtain ⟨⟨ea⟩, ⟨ed⟩⟩ := standardTruncationEndpoints P.obj.obj
      ((hchar P.obj).mp P.property).1
    exact ⟨A, D, S, h₁, h₂, h₃, hS, e₁, e₂,
      ⟨e₁ ≪≫ ea⟩, ⟨e₂ ≪≫ ed⟩, f, g, hf, hg, hfe, hge'⟩
  · intro S hS
    exact sixTermOfAmplitude (boundedConstructible R) t Perv hheart
      (fun K ↦ ((hchar K.obj).mp K.property).1) S hS

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing.CurveWeil

variable (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
  [Fact (ringChar D.k).Prime] [Fact (ringChar D.k ≠ ell)]
  (C₀ : Over (Spec (.of D.k₀))) [Smooth C₀.hom] [QuasiCompact C₀.hom]
  [IsSeparated C₀.hom]

local notation "Λ" => Profinite.padicAlgClRingObj ell
local notation "C" => D.geometricFiber C₀
local notation "g" => Iso.hom (WeilConjectures.FiniteFieldDatum.geometricFrobenius D C₀)
local notation "WM" => WeilConjectures.condensedWeilModules Λ g
local notation "Wprop" => WeilConjectures.condensedWeilComplexProperty Λ g
local notation "W" => WeilConjectures.condensedWeilComplex Λ g
local notation "For" => WeilConjectures.condensedWeilForget Λ g
local notation "H" => DerivedCategory.homologyFunctor WM
local notation "forgetM" => WeilConjectures.condensedWeilModuleForget Λ g
set_option quotPrecheck false in
local notation "Punctual" => CondensedCurvePerverse.IsPunctual Λ (C).left
set_option quotPrecheck false in
local notation "NoPunctual" => CondensedCurvePerverse.HasNoPunctualSubsheaf Λ (C).left

local instance : LocallyOfFiniteType (C).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd C₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
local instance : QuasiCompact (C).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd C₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
local instance : IsSeparated (C).hom :=
  inferInstanceAs (IsSeparated (pullback.snd C₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

local notation "Perv" => heart D ell C₀

/-- All five clauses for Weil complexes, in the ordinary derived category of Weil modules.
Source: latest blueprint thm-a1-curve-perverse-heart.md, opening Weil convention
(blueprint: thm-a1-curve-perverse-heart).

Proof: perform Steps 0--6 of curveSupportHeart with the canonical Weil structures.
Geometric Frobenius pullback is exact and commutes with ordinary cohomology and
truncations. The largest punctual submodule is its canonical kernel, hence Frobenius
stable. The localization maps are the specified counit and unit and therefore commute
with the structures. The truncation, fibre and octahedral constructions take place in
actual derived Weil modules. Their geometric cohomology gives the same description,
which supplies boundedness and abelianness. The ordinary direct image has the canonical
Frobenius base-change mate of middleWeilImage. Finally the truncation and cohomology
sequences are sequences of Weil objects and retain their specified equivariant maps. -/
theorem curveSupportWeilHeart (_hpure : C₀.left.IsPureDimension 1) :
    Description D ell C₀ ∧ HeartAssertions D ell C₀ ∧ BasicObjects D ell C₀ ∧
      TruncationExact D ell C₀ ∧ SixTermExact D ell C₀ := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.CurveWeil
