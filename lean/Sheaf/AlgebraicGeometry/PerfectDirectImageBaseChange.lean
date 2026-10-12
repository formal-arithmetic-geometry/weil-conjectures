/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups F1 and H1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage
import Sheaf.AlgebraicGeometry.CanonicalModuleBaseChangeAffineLocality
import Sheaf.AlgebraicGeometry.AffineRelativelyFlatCanonicalModuleBaseChange
import Sheaf.Topology.SheafIsomorphismLocalOpenCover
import Mathlib.CategoryTheory.Localization.Equivalence
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Perfect direct image and arbitrary base change

Source: Stacks Project, Tags 0B91 and 0A1H (blueprint: lem-pc-rf-perfect-base-change).
-/

@[expose] public section

set_option autoImplicit false
universe uPF wPF
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

open CategoryTheory.Functor in
/-- Transport a chosen localization along an exact equivalence, keeping its morphism universe.
Source: Mathlib's `Functor.IsLocalization.of_equivalence_source`; the same construction
appears in `SchemeIsoDerivedLocalizations`. -/
private theorem hasDerivedCategory_of_equivalence {C D : Type (uPF + 1)}
    [Category.{uPF} C] [Category.{uPF} D] [Abelian C] [Abelian D]
    (e : C ≌ D) [HasDerivedCategory.{wPF} D] : Nonempty (HasDerivedCategory.{wPF} C) := by
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let eC := e.mapHomologicalComplex (ComplexShape.up ℤ)
  let L := eC.functor ⋙ (DerivedCategory.Q (C := D))
  have : L.IsLocalization (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) := by
    refine Functor.IsLocalization.of_equivalence_source
      (DerivedCategory.Q (C := D)) (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
      L (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) eC.symm ?_ ?_ ?_
    · intro K M f hf
      have : QuasiIso f := hf
      exact (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).le_isoClosure _
        (show QuasiIso (eC.inverse.map f) from
          (show QuasiIso ((e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
            from inferInstance))
    · intro K M f hf
      have : QuasiIso f := hf
      have : QuasiIso (eC.functor.map f) :=
        (show QuasiIso ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
          from inferInstance)
      exact inferInstanceAs (IsIso (DerivedCategory.Q.map (eC.functor.map f)))
    · exact (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight eC.counitIso _ ≪≫ Functor.leftUnitor _
  exact ⟨{ D := DerivedCategory D, L := L }⟩

/-- A zero module is the free module with no generators, hence finitely presented.
Source: Stacks Project, Tag 01B5; the finite locally free presentation in the source library. -/
private theorem isFinitePresentation_of_isZero (X : Scheme.{uPF})
    (N : SheafOfModules.{uPF} (moduleRings X.toRingedSpace)) (hN : IsZero N) :
    N.IsFinitePresentation := by
  let M := SheafOfModules.free (R := moduleRings X.toRingedSpace) PEmpty.{uPF + 1}
  have hz : IsZero M := (IsZero.iff_id_eq_zero M).mpr (by
    apply Sigma.hom_ext
    intro i
    exact i.elim)
  let q : M.LocalGeneratorsData :=
    (SheafOfModules.free.generatingSections
      (R := moduleRings X.toRingedSpace) PEmpty.{uPF + 1}).localGeneratorsData
  have hq : q.IsLocallyFreeData := inferInstance
  have hf : q.IsFiniteType := by
    constructor
    intro i
    constructor
    change Finite PEmpty.{uPF + 1}
    infer_instance
  have : M.IsFiniteLocallyFree := by
    constructor
    exact ⟨q, hq, hf⟩
  have : N.IsFiniteLocallyFree :=
    SheafOfModules.IsFiniteLocallyFree.of_iso.{uPF, uPF, uPF} (hz.iso hN)
  infer_instance

open MonoidalCategory in
/-- The structure sheaf in degree zero is strictly perfect of rank one.
Source: Stacks Project, Tags 08C4 and 08CM. -/
private theorem unit_isPerfect (X : Scheme.{uPF})
    [HasDerivedCategory.{wPF} (SheafOfModules.{uPF} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{wPF}
      (SheafOfModules.{uPF} ((moduleRings X.toRingedSpace).over U))] :
    Scheme.IsPerfect X (𝟙_ (schemeDerivedCategory X)) := by
  intro x
  let R := (moduleRings X.toRingedSpace).over (⊤ : X.Opens)
  let K := (CochainComplex.singleFunctor (SheafOfModules.{uPF} R) 0).obj
    (SheafOfModules.unit R)
  refine ⟨⊤, trivial, K, ⟨?_, ?_⟩, ?_⟩
  · refine ⟨0, 0, ?_⟩
    intro n hn
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  · intro n
    by_cases hn : n = 0
    · subst n
      let e : K.X 0 ≅ SheafOfModules.free (R := R) (ULift.{uPF} (Fin 1)) :=
        (eqToIso (HomologicalComplex.single_obj_X_self _ _ _)) ≪≫
          (coproductUniqueIso (fun _ : ULift.{uPF} (Fin 1) ↦ SheafOfModules.unit R)).symm
      exact ⟨1, e.hom, e.inv, e.hom_inv_id⟩
    · have hz : IsZero (K.X n) :=
        HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
      exact ⟨0, 0, 0, by simpa using hz.eq_of_src (0 : K.X n ⟶ K.X n) (𝟙 _)⟩
  · let F := SheafOfModules.overFunctor.{uPF} (moduleRings X.toRingedSpace) ⊤
    let eunit : 𝟙_ (schemeDerivedCategory X) ≅
        (DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (moduleRings X.toRingedSpace)) := Iso.refl _
    exact ⟨F.mapDerivedCategory.mapIso eunit ≪≫
      (F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctorIsoCompQ _ 0).app (SheafOfModules.unit R)⟩

/-- Detect derived isomorphisms on an open cover by exact restriction of homology sheaves.
Source: Stacks Project, Tag 04TN; the detection argument in
`RelativelyFlatCanonicalModuleBaseChange`. -/
private theorem isIso_of_open_restrictions
    [∀ Y : Scheme.{uPF},
      HasDerivedCategory.{wPF} (SheafOfModules.{uPF} (moduleRings Y.toRingedSpace))]
    (Y : Scheme.{uPF}) {K L : schemeDerivedCategory Y} (φ : K ⟶ L)
    (I : Type uPF) (U : I → Y.Opens)
    (hcover : ∀ y : Y, ∃ i : I, y ∈ U i)
    (hlocal : ∀ i : I,
      IsIso ((schemeOpenRestriction Y (U i)).mapDerivedCategory.map φ)) : IsIso φ := by
  apply (DerivedCategory.isIso_iff _ φ).mpr
  intro n
  have hU : ⨆ i, U i = ⊤ := by
    apply le_antisymm le_top
    intro y _
    obtain ⟨i, hi⟩ := hcover y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  apply (sheaf_module_isIso_iff_isIso_over_open_cover
    Y.toRingedSpace I U hU _ _
    ((DerivedCategory.homologyFunctor _ n).map φ)).mpr
  intro i
  have := hlocal i
  have hhom : IsIso
      ((schemeOpenRestriction Y (U i)).map
        ((DerivedCategory.homologyFunctor _ n).map φ)) :=
    (NatIso.isIso_map_iff
      ((schemeOpenRestriction Y (U i)).mapDerivedCategoryHomologyFunctorIso n) φ).mpr
      (by
        change IsIso ((DerivedCategory.homologyFunctor _ n).map
          ((schemeOpenRestriction Y (U i)).mapDerivedCategory.map φ))
        exact Functor.map_isIso _ _)
  let F := (Scheme.Modules.overEquiv (U i)).functor
  have : IsIso (F.map (((DerivedCategory.homologyFunctor _ n).map φ).over (U i))) :=
    hhom
  exact isIso_of_reflects_iso _ F

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- For a proper morphism of finite presentation and a finitely presented module flat
relative to its base, the derived direct image is perfect and the canonical map to the
base-changed module's derived direct image is invertible for every base change: every
map with the characterising property of the canonical one is an isomorphism.
The localization instances choose models of the derived categories and impose no
geometric conditions. Additivity of each module tensor pullback (a left adjoint) is
assumed only to state the left-derived structure of the derived pullback.
Source: Stacks Project, Tag 0B91, clause (2) (blueprint: lem-pc-rf-perfect-base-change).

Proof:
1. Transport the given scheme derived localizations to localized open sites using
   `Scheme.Modules.overEquiv`. Preserve exactly the supplied localization family on S.
   The derived tensor unit is the structure sheaf in degree zero, represented on the
   top open by a strictly perfect rank-one complex.
2. Regard G as a complex K concentrated in degree zero. Its remaining terms are zero,
   so they are finitely presented and relatively flat. Every term has closed support
   by `finite_type_module_support_closed`. The reduced induced closed immersion of
   that support, composed with the proper f, is proper. Apply
   `properSupport_perfect_directImage` to the tensor unit and K. The left unitor and
   the single-complex comparison identify its direct image with Rf_*(G[0]); transport
   the local strictly perfect witnesses along that isomorphism.
3. Unpack the canonical comparison witnessing `IsDerivedModuleBaseChangeMap`.
   Cover the new base by affine opens mapping into affine opens of S. Apply
   `canonicalModuleBaseChange_isIso_affine_of_isFlatOver` and
   `canonicalModuleBaseChange_isIso_on_affine_open_of_affine_cases` to obtain
   invertibility on every member of that cover. Exact restriction commutes with
   homology, and isomorphisms of module sheaves are detected on an open cover.
   Hence all homology maps, and therefore the original derived map, are invertible. -/
theorem perfect_derivedDirectImage_baseChange
    [∀ Y : Scheme.{uPF},
      HasDerivedCategory.{wPF} (SheafOfModules.{uPF} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{uPF}} (f : X ⟶ S)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [∀ U : S.Opens, HasDerivedCategory.{wPF}
      (SheafOfModules.{uPF} ((moduleRings S.toRingedSpace).over U))]
    [∀ {Y Z : Scheme.{uPF}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    (G : X.Modules) [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) G]
    (hG : G.IsFlatOver f) :
    Scheme.IsPerfect S ((schemeDerivedDirectImage f).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{uPF} (moduleRings X.toRingedSpace)) 0).obj G)) ∧
      ∀ {T : Scheme.{uPF}} (g : T ⟶ S) φ, IsDerivedModuleBaseChangeMap f g G φ → IsIso φ := by
  classical
  let : Zero (SheafOfModules.{uPF} (moduleRings X.toRingedSpace)) :=
    HasZeroObject.zero' (SheafOfModules.{uPF} (moduleRings X.toRingedSpace))
  let hS : ∀ U : S.Opens, HasDerivedCategory.{wPF}
      (SheafOfModules.{uPF} ((moduleRings S.toRingedSpace).over U)) := inferInstance
  have hopen (Y : Scheme.{uPF}) (U : Y.Opens) :
      Nonempty (HasDerivedCategory.{wPF}
        (SheafOfModules.{uPF} ((moduleRings Y.toRingedSpace).over U))) :=
    hasDerivedCategory_of_equivalence
      (show SheafOfModules.{uPF} ((moduleRings Y.toRingedSpace).over U) ≌
        SheafOfModules.{uPF} (moduleRings U.toScheme.toRingedSpace) from
          Scheme.Modules.overEquiv U)
  let hOpen : ∀ (Y : Scheme.{uPF}) (U : Y.Opens), HasDerivedCategory.{wPF}
      (SheafOfModules.{uPF} ((moduleRings Y.toRingedSpace).over U)) :=
    Function.update (fun Y U ↦ Classical.choice (hopen Y U)) S hS
  have hh : hOpen S = hS := Function.update_self _ _ _
  let : ∀ (Y : Scheme.{uPF}) (U : Y.Opens), HasDerivedCategory.{wPF}
      (SheafOfModules.{uPF} ((moduleRings Y.toRingedSpace).over U)) := hOpen
  let K := (HomologicalComplex.single
    (SheafOfModules.{uPF} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ) 0).obj G
  have hKb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n) := by
    refine ⟨0, 0, ?_⟩
    intro n hn
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have hKfp : ∀ n : ℤ, (K.X n).IsFinitePresentation := by
    intro n
    dsimp [K, HomologicalComplex.single]
    split_ifs
    · infer_instance
    · exact isFinitePresentation_of_isZero X _ (isZero_zero _)
  have hKflat : ∀ n : ℤ, Scheme.Modules.IsFlatOver (K.X n) f := by
    intro n
    dsimp [K, HomologicalComplex.single]
    split_ifs
    · exact hG
    · intro V U e
      let F := SheafOfModules.forget.{uPF} (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.evaluation _ (Opposite.op U.1)
      have hz := Functor.map_isZero F
        (isZero_zero (SheafOfModules.{uPF} (moduleRings X.toRingedSpace)))
      have : Subsingleton (F.obj
          (0 : SheafOfModules.{uPF} (moduleRings X.toRingedSpace))) :=
        ModuleCat.subsingleton_of_isZero hz
      let : Module Γ(S, V.1) (F.obj
          (0 : SheafOfModules.{uPF} (moduleRings X.toRingedSpace))) :=
        Module.compHom _ (f.appLE V.1 U.1 e).hom
      change Module.Flat Γ(S, V.1) (F.obj
        (0 : SheafOfModules.{uPF} (moduleRings X.toRingedSpace)))
      infer_instance
  have hKproper : ∀ n : ℤ, Scheme.Modules.HasSupportProperOver f (K.X n) := by
    intro n
    have hclosed := (Scheme.Modules.finite_type_module_support_closed X (K.X n)).2.2.2
    refine ⟨⟨_, hclosed⟩, rfl, ?_⟩
    change IsProper (_ ≫ f)
    infer_instance
  have hp := (properSupport_perfect_directImage f
    (MonoidalCategory.tensorUnit (schemeDerivedCategory X))
    (unit_isPerfect X) K hKb hKflat hKproper).1
  let e : MonoidalCategory.tensorObj
      (MonoidalCategory.tensorUnit (schemeDerivedCategory X)) (DerivedCategory.Q.obj K) ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{uPF} (moduleRings X.toRingedSpace)) 0).obj G :=
    (MonoidalCategory.leftUnitor _) ≪≫ ((DerivedCategory.singleFunctorIsoCompQ
      (SheafOfModules.{uPF} (moduleRings X.toRingedSpace)) 0).app G).symm
  have hperfect : @Scheme.IsPerfect S _ (hOpen S)
      ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{uPF} (moduleRings X.toRingedSpace)) 0).obj G)) := by
    intro x
    obtain ⟨U, hx, L, hL, ⟨c⟩⟩ := hp x
    exact ⟨U, hx, L, hL, ⟨(SheafOfModules.overFunctor.{uPF}
      (moduleRings S.toRingedSpace) U).mapDerivedCategory.mapIso
        ((schemeDerivedDirectImage f).mapIso e.symm) ≪≫ c⟩⟩
  rw [hh] at hperfect
  refine ⟨hperfect, ?_⟩
  intro T g φ hφ
  obtain ⟨c, hc, rfl⟩ := hφ
  let I := {p : S.affineOpens × T.affineOpens | p.2.1 ≤ g ⁻¹ᵁ p.1.1}
  let U : I → T.Opens := fun p ↦ p.1.2.1
  have hcover : ∀ y : T, ∃ i : I, y ∈ U i := by
    intro y
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, _⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (g.base y)) isOpen_univ
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open hyV (g ⁻¹ᵁ V).2
    exact ⟨⟨(⟨V, hV⟩, ⟨W, hW⟩), hWV⟩, hyW⟩
  apply isIso_of_open_restrictions T _ I U hcover
  intro p
  exact canonicalModuleBaseChange_isIso_on_affine_open_of_affine_cases
    (fun f _ _ g _ G _ hflat c hc ↦
      canonicalModuleBaseChange_isIso_affine_of_isFlatOver f g G hflat c hc)
    f g (pullback.fst f g) (pullback.snd f g) (IsPullback.of_hasPullback f g)
    G hG c hc p.1.1 p.1.2 p.2

end AlgebraicGeometry
