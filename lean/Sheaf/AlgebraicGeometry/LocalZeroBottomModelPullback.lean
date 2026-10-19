/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback
import Sheaf.AlgebraicGeometry.LocalZeroBottomTruncation
import Sheaf.AlgebraicGeometry.ZeroBottomArrowPullbackLocal
import Sheaf.Topology.SheafIsomorphismLocalOpenCover
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-! # Bottom cohomology of local zero-differential models
Source: Stacks Project, Tag 0BDL, pullback clause; Tags 06YD and 06YJ.
(blueprint: lem-sc-local-zero-bottom-model-pullback). -/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
namespace AlgebraicGeometry.Scheme

-- Compute the derived pullback of a flat single complex by the K-flat counit.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem flat_single_pullback_iso
    {T T' : Scheme.{u}} (g : T' ⟶ T)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T'.toRingedSpace))]
    (M : SheafOfModules.{u} (moduleRings T.toRingedSpace)) (a : ℤ)
    (hM : SheafOfModules.IsFlat M) :
    Nonempty ((derivedPullback g).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).obj M) ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) a).obj
          ((Modules.tensorPullback g).obj M)) := by
  let A := SheafOfModules.{u} (moduleRings T.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings T'.toRingedSpace)
  let K := (CochainComplex.singleFunctor A a).obj M
  let := SheafOfModules.monoidalCategory T.sheaf
  obtain ⟨⟨hpreadd⟩, _⟩ := SheafOfModules.tensorClosed T.sheaf
  let := hpreadd
  have hbounded : ∃ b : ℤ, ∀ q : ℤ, b < q → IsZero (K.X q) := by
    refine ⟨a, fun q hq ↦ ?_⟩
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have hflat : ∀ q : ℤ, SheafOfModules.IsFlat (K.X q) := by
    intro q
    by_cases hq : q = a
    · subst q
      let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a M
      exact (exactFunctor _ _).prop_of_iso
        ((MonoidalCategory.curriedTensor A).flip.mapIso e.symm) hM
    · exact (ObjectProperty.flat_of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)).2
  obtain ⟨F, hF, _, hFadd, _, _, ⟨e, _⟩⟩ :=
    flatComplexDerivedPullback g K hbounded hflat
  let := hFadd
  refine ⟨(derivedPullback g).mapIso
    ((DerivedCategory.singleFunctorIsoCompQ A a).app M ≪≫
      ((DerivedCategory.quotientCompQhIso A).app K).symm) ≪≫ e.symm ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K) ≪≫
    (DerivedCategory.quotientCompQhIso B).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) a).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ B a).app (F.obj M)).symm ≪≫
    (DerivedCategory.singleFunctor B a).mapIso (eqToIso (hF M))⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A locally bounded finite-free model with zero bottom differential has bottom
cohomology compatible with every derived pullback.
Source: Stacks Project, Tag 0BDL, pullback comparison clause; Tags 06YD, 06YJ and 0D5S.
(blueprint: lem-sc-local-zero-bottom-model-pullback).

Proof:
1. On a neighbourhood U furnished by hmodel, the complex K is bounded above
   and finite free, hence K-flat. Both differentials adjacent to degree a vanish:
   the incoming one has zero source and the outgoing one is zero by hypothesis.
   Consequently H^a(K) is canonically K^a, with the identification given by the
   kernel of zero and cokernel of zero, not by a choice of basis.
2. Restrict g to the inverse image of U. The flat-complex counit represents Lg*D
   by the termwise tensor pullback of K. This complex also has zero terms below a
   and zero outgoing differential at a. Its H^a is canonically g*K^a. Exact open
   restriction identifies these computations with restrictions of the two global
   homology sheaves. Thus the bottom comparison is an isomorphism on this open.
3. Refine overlaps by affine opens W. Restrict both models to W and transport
   between modules on W and modules on its localized open site. They are strictly
   perfect. By 08CR represent their derived transition by a chain map alpha.
   Both bottom homologies are their a-th terms, so H^a(alpha) is alpha.f a.
   This is invertible because the derived transition is an isomorphism. After
   termwise pullback the bottom homology map is g*(alpha.f a), also invertible.
   Naturality of the flat-complex counit identifies this map with the derived
   transition after pullback. Thus the two local comparisons commute with the
   same transition on both sides and are equal as maps of the restricted sheaves.
   Affine opens cover the overlap, so equality holds on the entire overlap.
   Their inverses agree by uniqueness. Glue maps and inverses; both composites
   are identity since they are identity on each member of the inverse-image cover.
   Empty schemes are included; no separatedness is required.
   No perfection or universal-rank hypothesis is used in this homological step. -/
theorem localZeroBottomModel_pullback
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (T : Scheme.{u}) (D : schemeDerivedCategory T) (a : ℤ)
    (hmodel :
      ∀ t : T, ∃ U : T.Opens, t ∈ U ∧
      ∃ K : CochainComplex
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ,
        (∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (K.X i)) ∧
        (∀ i : ℤ, i < a → IsZero (K.X i)) ∧ K.d a (a + 1) = 0 ∧
        (∀ i : ℤ, ∃ n : ℕ, Nonempty (K.X i ≅ SheafOfModules.free
          (R := moduleRings U.toScheme.toRingedSpace) (ULift.{u} (Fin n)))) ∧
        Nonempty ((derivedPullback U.ι).obj D ≅ DerivedCategory.Q.obj K))
    (T' : Scheme.{u}) (g : T' ⟶ T) :
    Nonempty
      ((Modules.tensorPullback g).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).obj D) ≅
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) a).obj
            ((derivedPullback g).obj D)) := by
  classical
  obtain ⟨hM, f, hf⟩ := localZeroBottomModel_truncation T D a hmodel
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) a
  let φ := H.map ((derivedPullback g).map f)
  have hlocal : ∀ y : T', ∃ V : T'.Opens, y ∈ V ∧ IsIso (φ.over V) := by
    intro y
    obtain ⟨U, hyU, K, hb, hn, hz, hfree, ⟨e⟩⟩ := hmodel (g.base y)
    exact zeroBottomArrow_pullback_local T D a _ f hf U K hb hn hz hfree e
      T' g y hyU
  choose V hV hIso using hlocal
  have hcover : ⨆ y, V y = ⊤ := by
    ext y
    change y ∈ (⨆ y, V y : T'.Opens) ↔ y ∈ (⊤ : T'.Opens)
    constructor
    · intro _
      trivial
    · intro _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hV y⟩
  have : IsIso φ :=
    (sheaf_module_isIso_iff_isIso_over_open_cover.{u, u, u}
      T'.toRingedSpace T' V hcover _ _ φ).2 hIso
  obtain ⟨eS⟩ := flat_single_pullback_iso g _ a hM
  exact ⟨((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) a).app _).symm ≪≫
    (H.mapIso eS).symm ≪≫ asIso φ⟩

end AlgebraicGeometry.Scheme
