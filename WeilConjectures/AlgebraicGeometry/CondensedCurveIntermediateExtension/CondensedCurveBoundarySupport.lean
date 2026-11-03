/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import WeilConjectures.AlgebraicGeometry.CurveMiddleExtension
public import WeilConjectures.AlgebraicGeometry.CurvePerverseHeartStatement.CurvePerverseHeartStatement
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleInverseImageStalk
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.Topology.KrullDimension

/-! # Support of a sheaf killed by open restriction -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj
open WeilConjectures
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CurvePerverseHeartStatement
namespace AlgebraicGeometry.ProEtale.CondensedCurveIntermediateExtension

/-- A constructible sheaf killed by the dense open has finite closed support.
Source: rem-dl-a1-conventions, intermediate-extension argument, step 3.
Proof: geometric base change is a smooth pure one-dimensional curve and the open
remains dense. Its complement is a finite set of closed points. For a point in
the open, factor its chosen algebraic-closure geometric point through the open.
The canonical stalk comparison for restriction identifies its stalk with a stalk
of the zero restriction, hence it is zero. The nonzero-stalk locus is therefore
contained in the closed complement, and so is its closure. A subset of the finite
closed-point complement is finite and all of its points are closed. Retain the
constructibility witness of the input sheaf. This includes zero sheaves and the
empty complement, and uses no exactness of direct image.
(blueprint: lem-dl-a1-condensed-curve-boundary-support). -/
theorem boundary_support_punctual
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (c : Scheme.MiddleExtensionCurve D) [GeometricallyConnected c.C.hom]
    (B : Modules D ell (geomC D c))
    (hB : IsConstructibleModuleObject (condensedRingObj (coeff ell) (geomC D c)) B)
    (hZero : IsZero ((CondensedRing.upperStar (coeff ell) (geomJ D c)).obj B)) :
    Punctual ell (geomC D c) B := by
  classical
  let : ConnectedSpace c.C.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton c.C.hom
  have : IsLocallyNoetherian c.C.left := LocallyOfFiniteType.isLocallyNoetherian c.C.hom
  have : IsRegular c.C.left := IsRegular.of_smooth c.C.hom
  have : IrreducibleSpace c.C.left := IsRegular.irreducibleSpace c.C.left
  have hd₀ : topologicalKrullDim c.C.left = (1 : WithBot ℕ∞) := by
    have h := c.pureDimension Set.univ (by simp [irreducibleComponents_eq_singleton])
    rw [IsHomeomorph.topologicalKrullDim_eq _
      (Homeomorph.Set.univ c.C.left).isHomeomorph] at h
    exact h
  have : SmoothOfRelativeDimension 1 c.C.hom :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq c.C.hom 1).mpr hd₀
  let a := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  have : LocallyOfFiniteType (D.geometricFiber c.C).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd c.C.hom a))
  have : QuasiCompact (D.geometricFiber c.C).hom :=
    inferInstanceAs (QuasiCompact (pullback.snd c.C.hom a))
  have : IsSeparated (D.geometricFiber c.C).hom :=
    inferInstanceAs (IsSeparated (pullback.snd c.C.hom a))
  have : Smooth (D.geometricFiber c.C).hom :=
    inferInstanceAs (Smooth (pullback.snd c.C.hom a))
  have : SmoothOfRelativeDimension 1 (D.geometricFiber c.C).hom :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd c.C.hom a))
  have : ConnectedSpace (geomC D c) :=
    inferInstanceAs (ConnectedSpace (↑(pullback c.C.hom a) : Type u))
  have : IsLocallyNoetherian (geomC D c) :=
    LocallyOfFiniteType.isLocallyNoetherian (D.geometricFiber c.C).hom
  have : IsRegular (geomC D c) := IsRegular.of_smooth (D.geometricFiber c.C).hom
  have : IrreducibleSpace (geomC D c) := IsRegular.irreducibleSpace (geomC D c)
  have hd : (geomC D c).IsPureDimension 1 := by
    intro Z hZ
    have hZeq : Z = Set.univ := by
      simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
      exact hZ
    subst Z
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (Homeomorph.Set.univ (geomC D c)).isHomeomorph).trans
        (topologicalKrullDim_eq_of_smoothOfRelativeDimension (D.geometricFiber c.C).hom 1)
  have hj : IsOpenImmersion (geomJ D c) :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) a c.j inferInstance
  have hden : DenseRange (geomJ D c) := by
    change Dense (Set.range ((Over.pullback a).map c.j).left)
    change Dense (Set.range (pullback.map c.U.hom a c.C.hom a
      c.j.left (𝟙 _) (𝟙 _) (by simp) (by simp)))
    rw [Scheme.Pullback.range_map]
    simpa using c.dense.preimage (pullback.fst c.C.hom a).isOpenMap
  have hdle : topologicalKrullDim (geomC D c) ≤ 1 := by
    rw [topologicalKrullDim_eq_of_smoothOfRelativeDimension (D.geometricFiber c.C).hom 1]
    exact le_rfl
  have hne : (Set.range (geomJ D c)).Nonempty := by
    obtain ⟨x⟩ := hden.nonempty
    exact ⟨_, Set.mem_range_self x⟩
  have hfin := (geomJ D c).isOpenEmbedding.isOpen_range
    |>.finite_compl_of_topologicalKrullDim_le_one hdle hne
  have hclosed (x : geomC D c) (hx : x ∈ (Set.range (geomJ D c))ᶜ) :
      IsClosed ({x} : Set (geomC D c)) :=
    (geomJ D c).isOpenEmbedding.isOpen_range.isClosed_singleton_of_mem_compl hdle hne hx
  have hAb : IsZero ((ProEtale.upperStar Ab.{u + 1} (geomJ D c)).obj B.X) :=
    ((Mod.forget _).map_isZero hZero).of_iso
      ((profinitePointModuleForgetPullbackIso (coeff ell) (geomJ D c)).app B).symm
  have hs : condensedModuleSupport (condensedRingObj (coeff ell) (geomC D c)) B ⊆
      (Set.range (geomJ D c))ᶜ := by
    apply closure_minimal _ (geomJ D c).isOpenEmbedding.isOpen_range.isClosed_compl
    intro x hx hxopen
    apply hx
    let t := (geomC D c).algClosurePoint x
    have ht : Set.range t ⊆ Set.range (geomJ D c) := by
      rintro _ ⟨z, rfl⟩
      simpa only [t, Scheme.algClosurePoint_base] using hxopen
    let v := IsOpenImmersion.lift (geomJ D c) t ht
    have hv : v ≫ geomJ D c = t := IsOpenImmersion.lift_fac _ _ _
    obtain ⟨e, _⟩ := Scheme.proEtaleInverseImage_abelianStalk (geomJ D c) v
    let S := sheafToPresheaf (Scheme.ProEt.topology (geomU D c)) Ab.{u + 1} ⋙
      (Functor.whiskeringLeft (Scheme.ProEtaleGeometricNeighbourhood v)ᵒᵖ
        (geomU D c).ProEtᵒᵖ Ab.{u + 1}).obj
          (Scheme.proEtaleGeometricNeighbourhoodForget v).op ⋙ colim
    have hz : IsZero (S.obj ((ProEtale.upperStar Ab.{u + 1} (geomJ D c)).obj B.X)) :=
      S.map_isZero hAb
    have he : IsZero (Scheme.proEtaleGeometricStalk (v ≫ geomJ D c) B.X) :=
      hz.of_iso (e B.X).symm
    simpa only [hv] using he
  exact ⟨hB, hfin.subset hs, fun x hx ↦ hclosed x (hs hx)⟩

end AlgebraicGeometry.ProEtale.CondensedCurveIntermediateExtension
