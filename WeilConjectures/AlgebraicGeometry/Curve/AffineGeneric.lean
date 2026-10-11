/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.SplitSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.Affine
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Second cohomology of a generic extension on an affine curve

Let `C` be a smooth affine connected curve over an algebraically closed field `k`, with generic
point `η : Spec k(C) ⟶ C`. We show `H²(C, η_* M) = 0` for every torsion étale sheaf `M` on
`Spec k(C)` (blueprint `lem-sc-affine-generic-second`).

For a sheaf `N` split by a finite Galois extension `L` of `k(C)` whose Galois group is an
`ℓ`-group, with finite `ℓ`-primary sections over `Spec L`, `N` is filtered by constant sheaves
`ℤ/ℓ` (`AlgebraicGeometry.Scheme.IsSplitBy.induction`). For a monomorphism `ℤ/ℓ ⟶ N` with
cokernel `Q`, the sequence `0 ⟶ η_* ℤ/ℓ ⟶ η_* N ⟶ η_* Q` is exact, and the cokernel of the last
map has zero generic restriction since `η^* η_* = id`, hence no cohomology in positive degrees.
So `H²(C, η_* N) = 0` follows from `H²(C, η_* ℤ/ℓ) = H²(C, ℤ/ℓ) = 0`.

## Main statements

- `AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_two_lowerStar_of_isSplitBy`:
  `H²(C, η_* N) = 0` for `N` split by an `ℓ`-group extension.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Etale

/-- The pullback of a constant étale sheaf is constant: both functors `B ↦ g^* B_X` and
`B ↦ B_Y` are left adjoint to the global sections functor. -/
noncomputable def Etale.upperStarConstantSheafIso {X Y : Scheme.{u}} (g : Y ⟶ X) :
    constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙ (g)^*[AddCommGrpCat.{u + 1}] ≅
      constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} := by
  let G := MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g
  let T : X.Etale := MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X)
  let T' : Y.Etale := MorphismProperty.Over.mk ⊤ (𝟙 Y) (MorphismProperty.id_mem _ Y)
  have hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ _
  have hT' : IsTerminal T' := MorphismProperty.Over.mkIdTerminal _ _
  let e : G.obj T ≅ T' :=
    MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 X) g)) (Category.comp_id _)
  let adj₁ := (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} hT).comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g)
  let adj₂ := constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1} hT'
  let i : (g)_*[AddCommGrpCat.{u + 1}] ⋙ (sheafSections X.smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj (op T) ≅
      (sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op T') :=
    NatIso.ofComponents (fun N ↦ N.obj.mapIso e.op.symm) fun φ ↦ (φ.hom.naturality _).symm
  exact (adj₁.ofNatIsoRight i).leftAdjointUniq adj₂

/-- A zero sheaf has no cohomology. -/
lemma _root_.CategoryTheory.Sheaf.H.subsingleton_of_isZero {C : Type*} [Category C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})] {G : Sheaf J AddCommGrpCat.{u + 1}}
    (hG : IsZero G) (n : ℕ) : Subsingleton (Sheaf.H G n) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  rw [← Sheaf.H.map_id_apply x, hG.eq_of_src (𝟙 G) 0, Sheaf.H.map_apply, Abelian.Ext.mk₀_zero,
    Abelian.Ext.comp_zero]

namespace IsConnectedCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [IsConnectedCurve f] [Smooth f] [IsAffine C] [IsIntegral C]

include f in
/-- `H²(C, η_* ℤ/ℓ) = 0` for the generic point `η` of a smooth affine connected curve: it is
`H²(C, ℤ/ℓ)` by generic replacement. -/
theorem subsingleton_sheafH_two_lowerStar_constantZMod (ℓ : ℕ) [Fact ℓ.Prime] :
    Subsingleton (Sheaf.H ((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj
      ((Spec C.functionField).constantZMod ℓ)) 2) := by
  have hb := IsCurve.bijective_H_map_unit_fromSpecFunctionField f (C.constantZMod ℓ) 0
  have := subsingleton_sheafH_two_constantZMod f ℓ
  have h : Subsingleton (Sheaf.H ((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj
      ((C.fromSpecFunctionField)^*[AddCommGrpCat.{u + 1}].obj (C.constantZMod ℓ))) 2) :=
    ⟨fun x y ↦ by
      obtain ⟨x, rfl⟩ := hb.2 x
      obtain ⟨y, rfl⟩ := hb.2 y
      exact congrArg _ (Subsingleton.elim (α := Sheaf.H (C.constantZMod ℓ) 2) x y)⟩
  let e := ((Sheaf.functorH _ 2).mapIso ((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].mapIso
    ((upperStarConstantSheafIso C.fromSpecFunctionField).app
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))))).addCommGroupIsoToAddEquiv
  exact ⟨fun x y ↦ e.symm.injective (@Subsingleton.elim _ h _ _)⟩

omit [Smooth f] in
include f in
/-- **Extensions on the generic point.** Let `ι : A ⟶ N` be a monomorphism of sheaves on the
generic point `η` of a smooth affine connected curve `C`. If `H²(C, η_* A) = 0` and
`H²(C, η_* coker ι) = 0`, then `H²(C, η_* N) = 0`. The pushforward `η_*` is only left exact, but
the cokernel of `η_* N ⟶ η_* coker ι` has zero generic restriction, since `η^* η_* = id`
(`AlgebraicGeometry.Scheme.isIso_counit_app_fromSpecFunctionField`), hence no cohomology in
positive degrees. -/
theorem subsingleton_sheafH_two_lowerStar_of_mono
    {A N : Sheaf (Spec C.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}} (ι : A ⟶ N)
    [Mono ι] (hA : Subsingleton (Sheaf.H ((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj
      A) 2))
    (hQ : Subsingleton (Sheaf.H ((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj
      (cokernel ι)) 2)) :
    Subsingleton (Sheaf.H ((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj N) 2) := by
  set η := C.fromSpecFunctionField
  set R := (η)_*[AddCommGrpCat.{u + 1}]
  set φ := R.map (cokernel.π ι)
  set adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} η
  -- the generic restriction of `coker φ` vanishes
  have hε (M) : IsIso (adj.counit.app M) := Scheme.isIso_counit_app_fromSpecFunctionField M
  have hepi : Epi ((η)^*[AddCommGrpCat.{u + 1}].map φ) := by
    have h := adj.counit.naturality (cokernel.π ι)
    have : (η)^*[AddCommGrpCat.{u + 1}].map φ =
        adj.counit.app N ≫ cokernel.π ι ≫ inv (adj.counit.app (cokernel ι)) := by
      rw [← Category.assoc]
      exact (IsIso.eq_comp_inv _).2 h
    rw [this]
    infer_instance
  have hz : IsZero ((η)^*[AddCommGrpCat.{u + 1}].obj (cokernel φ)) :=
    (isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso _ φ)
  have hG (V : C.Etale) (s : (cokernel φ).obj.obj (op V)) :
      C.genericVanishingSieve (cokernel φ) s ∈ C.smallEtaleTopology V := by
    refine Etale.mem_smallEtaleTopology_of_forall_isAffine _ fun W g hW ↦ ?_
    let x := (cokernel φ).obj.map g.op s
    have hP := Scheme.fromSpecFunctionField_eq_functionFieldCone_comp C
    have hτ (U : C.NonemptyAffineOpens) := Etale.unit_app_comp_unitComparison
      (C.functionFieldCone.π.app U) (C.affineOpensDiagramι.app U) η (hP U) (cokernel φ)
    have hx : (adj.unit.app (cokernel φ)).hom.app (op W) x = 0 := by
      rw [(R.map_isZero hz).eq_of_tgt (adj.unit.app (cokernel φ)) 0]
      rfl
    let U₀ : C.NonemptyAffineOpens := Classical.arbitrary _
    have h₀ : (Etale.unitComparison (C.functionFieldCone.π.app U₀) (C.affineOpensDiagramι.app U₀)
        η (hP U₀) (cokernel φ)).hom.app (op W)
          ((C.affineOpenUnit U₀ (cokernel φ)).hom.app (op W) x) = 0 := by
      rw [← hτ U₀] at hx
      exact hx
    have : CompactSpace W.left := inferInstance
    obtain ⟨U, f', hU⟩ := Etale.exists_unitComparison_app_eq_zero_of_isLimit C.affineOpensDiagram
      C.affineOpensDiagramι C.functionFieldCone η hP C.isLimitFunctionFieldCone (cokernel φ) W
      U₀ _ h₀
    refine ⟨U, ?_⟩
    rw [← C.affineOpenUnit_comp_transition f' (cokernel φ)]
    exact hU
  have hH₁ := IsCurve.subsingleton_H_of_genericVanishing f (cokernel φ) hG 0
  -- the two short exact sequences
  let S₂ := ShortComplex.mk (Abelian.image.ι φ) (cokernel.π φ) (by simp)
  have hS₂ : S₂.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
      inferInstance inferInstance
  have hI : Subsingleton (Sheaf.H (Abelian.image φ) 2) :=
    have : Subsingleton (Sheaf.H S₂.X₃ 1) := hH₁
    have : Subsingleton (Sheaf.H S₂.X₂ (1 + 1)) := hQ
    Sheaf.H.subsingleton_X₁_of_shortExact hS₂ 1
  have hker : IsLimit (KernelFork.ofι (R.map ι) (show R.map ι ≫ φ = 0 by
      rw [← R.map_comp, cokernel.condition, R.map_zero])) :=
    isLimitForkMapOfIsLimit' R _ (Abelian.monoIsKernelOfCokernel _
      (colimit.isColimit (parallelPair ι 0)))
  let S₁ := ShortComplex.mk (R.map ι) (Abelian.factorThruImage φ)
    (by rw [← cancel_mono (Abelian.image.ι φ), Category.assoc, Abelian.image.fac,
      ← R.map_comp, cokernel.condition, R.map_zero, zero_comp])
  have hS₁ : S₁.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
    refine ShortComplex.exact_of_f_is_kernel _ ?_
    refine KernelFork.IsLimit.ofι' _ _ fun {B} k hk ↦ ⟨hker.lift (KernelFork.ofι k ?_), ?_⟩
    · change k ≫ Abelian.factorThruImage φ = 0 at hk
      rw [← Abelian.image.fac φ, ← Category.assoc, hk, zero_comp]
    · exact hker.fac _ WalkingParallelPair.zero
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, rfl⟩ := (Sheaf.H.exact_map_map hS₁ 2 x).1 (Subsingleton.elim (h := hI) _ _)
  rw [Subsingleton.elim (h := hA) y 0, map_zero]

include f in
/-- **`H²` of a split `ℓ`-primary sheaf on the generic point.** Let `L` be a finite Galois
extension of the function field of a smooth affine connected curve `C` with Galois group an
`ℓ`-group, and `N` a sheaf on the generic point `η` split by `L`, with finite `ℓ`-primary sections
over `Spec L`. Then `H²(C, η_* N) = 0`: `N` is filtered by constant sheaves `ℤ/ℓ`
(`AlgebraicGeometry.Scheme.IsSplitBy.induction`). -/
theorem subsingleton_sheafH_two_lowerStar_of_isSplitBy (L : Type u) [Field L]
    [Algebra C.functionField L] [Algebra.Etale C.functionField L] [IsGalois C.functionField L]
    (ℓ : ℕ) [Fact ℓ.Prime] (hP : IsPGroup ℓ (L ≃ₐ[C.functionField] L))
    (N : Sheaf (Spec C.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hN : Scheme.IsSplitBy N L) [Finite (N.obj.obj (op (Scheme.etaleSpec C.functionField L)))]
    (hNℓ : ∀ x : N.obj.obj (op (Scheme.etaleSpec C.functionField L)), ∃ k : ℕ, ℓ ^ k • x = 0) :
    Subsingleton (Sheaf.H ((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj N) 2) :=
  Scheme.IsSplitBy.induction ℓ hP
    (fun N ↦ Subsingleton (Sheaf.H ((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj N) 2))
    (fun _ hN ↦ Sheaf.H.subsingleton_of_isZero (Functor.map_isZero _ hN) 2)
    (fun _ _ hz hzℓ hQ ↦
      have := Scheme.mono_constantZModHom ℓ hz hzℓ
      subsingleton_sheafH_two_lowerStar_of_mono f (Scheme.constantZModHom ℓ hz)
        (subsingleton_sheafH_two_lowerStar_constantZMod f ℓ) hQ) hN hNℓ

end IsConnectedCurve

end AlgebraicGeometry
