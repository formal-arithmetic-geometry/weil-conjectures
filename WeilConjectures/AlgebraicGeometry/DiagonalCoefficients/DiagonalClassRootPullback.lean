/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalClassPullbackFrame
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalRlimForgetUnit

/-! # The canonical ordinary root-tower pullback

Source: diagonal coefficient changes, paragraph (3). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
open DiagonalTrace
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor diagonalCompletedSource

variable {l : ℕ} [Fact l.Prime] {Y Y' : Scheme.{u}} {g : Y' ⟶ Y}
  [DiagonalTraceLocalizations l (diagonalSurface Y)]
  [DiagonalTraceLocalizations l (diagonalSurface Y')]
  {hY : IsUnit (l : Γ(Y, ⊤))} {hY' : IsUnit (l : Γ(Y', ⊤))}
  {D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y))}
  {D' : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y'))}
  {d : ClassLimitPresentation l Y hY D} {d' : ClassLimitPresentation l Y' hY' D'}
  {e : CompletedRealization l (diagonalSurface Y)}
  {e' : CompletedRealization l (diagonalSurface Y')}


/-- Canonical inverse image of the ordinary root tower.
Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ladic-summary/sec-late-coefficients/
sk-prop-diagonal-tower/sk-prop-diagonal-tower-coefficients.proof.md,
paragraph (3), Kummer sequences natural under pullback.
(blueprint: def-diagonal-class-root-pullback). -/
def diagonalClassOrdinaryRootPullback
    (_frame : DiagonalClassPullbackFrame l g d d' e e') :
    (diagonalClassTowerPull l (baseW g)).obj d.H ⟶ d'.H := by
  let FS := diagonalForget l (diagonalSurface Y)
  let F := diagonalForget l (diagonalSurface Y')
  let G := diagonalClassPull l (baseW g)
  let A := upperStar Ab.{u + 1} (baseW g)
  let adjA := upperStarLowerStarAdjunction Ab.{u + 1} (baseW g)
  let adjG := upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) (baseW g)
  let fp (M : DiagonalMod l (diagonalSurface Y)) :=
    (adjA.homEquiv (FS.obj M) (F.obj (G.obj M))).symm (FS.map (adjG.unit.app M))
  have hfp (M : DiagonalMod l (diagonalSurface Y)) : IsIso (fp M) :=
    diagonalRlimForgetUnit l (baseW g) M
  let e : d.H ⋙ FS ⋙ A ≅ (d.H ⋙ G) ⋙ F :=
    NatIso.ofComponents (fun n ↦ @asIso _ _ _ _ (fp (d.H.obj n)) (hfp _)) (by
      intro n m f
      change A.map (FS.map (d.H.map f)) ≫ fp (d.H.obj m) =
        fp (d.H.obj n) ≫ F.map (G.map (d.H.map f))
      apply (adjA.homEquiv _ _).injective
      rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
      simp only [fp, Equiv.apply_symm_apply]
      change FS.map (d.H.map f) ≫ FS.map (adjG.unit.app (d.H.obj m)) =
        FS.map (adjG.unit.app (d.H.obj n)) ≫ FS.map
          ((G ⋙ lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) (baseW g)).map
            (d.H.map f))
      rw [← FS.map_comp, ← FS.map_comp]
      exact congrArg FS.map (adjG.unit.naturality (d.H.map f)))
  let tau : (d.H ⋙ G) ⋙ F ⟶ d'.H ⋙ F :=
    e.inv ≫ Functor.whiskerRight d.roots.hom A ≫
      ((Scheme.proEtaleRootsOfUnityInverseImageIso (baseW g)).2.1 l
        (Fact.out : l.Prime)).choose ≫ d'.roots.inv
  have killed (n : ℕ) (U : (diagonalSurface Y').ProEtᵒᵖ)
      (x : (d'.H.obj (op n)).obj.obj U) : l ^ (n + 1) • x = 0 := by
    let v := (d'.roots.hom.app (op n)).hom.app U
    have hv : Function.Injective v :=
      (AddCommGrpCat.mono_iff_injective v).mp inferInstance
    apply hv
    simp only [map_nsmul, map_zero]
    exact Scheme.proEtaleRootsOfUnity_nsmul _ _ U _
  exact
    { app n := ObjectProperty.homMk
        { app U := by
            let f : ((G.obj (d.H.obj n)).obj.obj U) →+
                ((d'.H.obj n).obj.obj U) := ((tau.app n).hom.app U).hom
            exact ModuleCat.ofHom
              { toFun := f
                map_add' := f.map_add
                map_smul' z x := by
                  change f (z • x) = z • f x
                  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1
                    (z.down.appr_spec (n.unop + 1))
                  have hz : z - (z.down.appr (n.unop + 1) : ULift.{u + 1} ℤ_[l]) =
                      ULift.up a * (l : ULift.{u + 1} ℤ_[l]) ^ (n.unop + 1) := by
                    apply ULift.ext
                    exact ha.symm
                  have split (y : ((G.obj (d.H.obj n)).obj.obj U)) :
                      z • y = l ^ (n.unop + 1) • (ULift.up a • y) +
                        z.down.appr (n.unop + 1) • y := by
                    conv_lhs => rw [← sub_add_cancel z
                      (z.down.appr (n.unop + 1) : ULift.{u + 1} ℤ_[l]), hz]
                    rw [add_smul, mul_comm (ULift.up a), mul_smul]
                    simp only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
                  rw [split, map_add, map_nsmul, killed, zero_add, map_nsmul]
                  conv_rhs => rw [← sub_add_cancel z
                    (z.down.appr (n.unop + 1) : ULift.{u + 1} ℤ_[l]), hz]
                  rw [add_smul, mul_comm (ULift.up a), mul_smul]
                  simp only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, killed, zero_add] }
          naturality U V i := by
            apply (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l]))
              AddCommGrpCat.{u + 1}).map_injective
            exact (tau.app n).hom.naturality i }
      naturality n m i := by
        ext U x
        exact congrArg (fun f ↦ f.hom.app U x) (tau.naturality i) }

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
