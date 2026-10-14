/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.PicardTermwiseSingleMapComposition
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Exact single pullback comparison along a scheme isomorphism -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The pinned single pullback comparison is invertible along an isomorphism.
Source: Stacks Project, Tag 08DW (exact restriction), and Tag 06YJ.
(blueprint: lem-pc-picard-single-map-iso-y3)

Proof: Tensor pullback along an isomorphism is an equivalence: its inverse
is tensor pullback along the inverse scheme map, and the composition and
identity comparisons give its unit and counit. It is therefore exact. Its
homotopy-category functor inverts quasi-isomorphisms. The exact derived
functor with its invertible comparison is a left derived functor. Uniqueness
of left derived functors identifies the pinned derived counit with that
invertible comparison. Evaluate on the single complex and compose with the
single-map isomorphism. These are precisely the factors of
picardTermwiseSingleMap; all are invertible. The argument includes zero
modules and empty schemes. -/
theorem picardTermwiseSingleMap_isIso_of_iso
    {X Y : Scheme.{u}} (s : X ≅ Y) (M : Y.Modules) :
    letI := fun Z : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))
    IsIso (Scheme.picardTermwiseSingleMap s.hom M) := by
  classical
  let := fun Z : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace))
  let T : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
    Scheme.Modules.tensorPullback s.hom
  obtain ⟨c₁⟩ := Scheme.Modules.nonempty_tensorPullbackComp s.inv s.hom
  obtain ⟨c₂⟩ := Scheme.Modules.nonempty_tensorPullbackComp s.hom s.inv
  obtain ⟨u₁⟩ := Scheme.Modules.nonempty_tensorPullbackId Y
  obtain ⟨u₂⟩ := Scheme.Modules.nonempty_tensorPullbackId X
  let b₁ := c₁.symm ≪≫
    eqToIso (congrArg Scheme.Modules.tensorPullback s.inv_hom_id) ≪≫ u₁
  let b₂ := c₂.symm ≪≫
    eqToIso (congrArg Scheme.Modules.tensorPullback s.hom_inv_id) ≪≫ u₂
  have : T.IsEquivalence :=
    (CategoryTheory.Equivalence.mk T
      (Scheme.Modules.tensorPullback s.inv) b₁.symm b₂).isEquivalence_functor
  have : T.Additive := (Classical.choose exists_derivedPullbackComposition) s.hom
  let ε := (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) s.hom
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)
  have : (derivedPullback s.hom).IsLeftDerivedFunctor ε W :=
    (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) s.hom
  have : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ T.mapDerivedCategoryFactorsh
  let z := (HomotopyCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M
  let e := Functor.leftDerivedUnique T.mapDerivedCategory (derivedPullback s.hom)
    ε T.mapDerivedCategoryFactorsh.hom W
  have he : e.inv.app (DerivedCategory.Qh.obj z) ≫ ε.app z =
      T.mapDerivedCategoryFactorsh.hom.app z := by
    simpa only [e, Functor.leftDerivedUnique, Functor.leftDerivedNatIso_inv,
      Iso.refl_inv, NatTrans.id_app, Category.comp_id] using
      Functor.leftDerivedNatTrans_app T.mapDerivedCategory (derivedPullback s.hom)
        T.mapDerivedCategoryFactorsh.hom ε W (𝟙 _) z
  have : IsIso (e.inv.app (DerivedCategory.Qh.obj z) ≫ ε.app z) := by
    rw [he]
    infer_instance
  have : IsIso (ε.app z) :=
    IsIso.of_isIso_comp_left (e.inv.app (DerivedCategory.Qh.obj z)) (ε.app z)
  unfold Scheme.picardTermwiseSingleMap Scheme.Modules.canonicalSinglePullbackMap
  infer_instance

end AlgebraicGeometry
