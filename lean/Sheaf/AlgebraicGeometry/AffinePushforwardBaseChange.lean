/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
import Sheaf.AlgebraicGeometry.ModulePullbackTensor
import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Affine pushforward and arbitrary base change

Source: Stacks Project, Cohomology of Schemes, Lemma 02KG; the algebra and composition
clauses are the affine-local consequences specified by the DAG node
(blueprint: lem-weil-pbc-affine-pushforward-base-change).
-/

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Affine pushforward preserves quasi-coherence and its canonical base change map is invertible.
Source: Stacks Project, Lemma 02KG
(blueprint: lem-weil-pbc-affine-pushforward-base-change).
Proof: (1) affine morphisms are quasi-compact and quasi-separated, so pushforward preserves
quasi-coherence (01LC). (2) Restrict to affine opens on the two bases using the open-restriction
base change lemma; isomorphisms are detected on this basis. (3) Identify the resulting square
with spectra of R, R-prime, B and R-prime tensor B. (4) Replace F by the tilde of its sections
using the affine tilde-Gamma adjunction. The pushforward and pullback tilde comparisons identify
the base change map with r tensor m mapping to (r tensor 1) tensor m, by the adjunction unit.
Its inverse sends (r tensor b) tensor m to r tensor b*m. Thus it is an isomorphism. -/
theorem affinePushforward_baseChange {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [IsAffineHom f]
    (F : X.Modules) [F.IsQuasicoherent] :
    ((pushforward f).obj F).IsQuasicoherent ∧
      IsIso (moduleBaseChangeMap f f' g g' sq.w F) := by
  sorry

/-- On affine charts, the canonical map is the tensor associativity identification.
The two equivalences are pinned by their values on generators, using the canonical units.
Applying this assertion to restricted affine squares gives the formula on affine opens.
Source: Stacks Project, Lemma 02KG, affine computation (01I9)
(blueprint: lem-weil-pbc-affine-pushforward-base-change).
Proof: step (4) of the node: the tilde-Gamma counit identifies quasi-coherent modules with
tildes. Pushforward of tilde is restriction of scalars; pullback of tilde is extension of
scalars. Their unit formulas give the two displayed generator equations. Adjointness of beta
then gives beta(eta_g(m)) = eta_g-prime(m), so linearity gives the last equation. The inverse
of the resulting map sends (r tensor b) tensor m to r tensor b*m. -/
theorem affinePushforward_baseChange_affine_formula
    (R B R' : Type u) [CommRing R] [CommRing B] [CommRing R']
    [Algebra R B] [Algebra R R'] (M : ModuleCat.{u} B) :
    letI : Module R M := Module.compHom M (algebraMap R B)
    letI : Algebra B (R' ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
    ∃ (w : Spec.map (CommRingCat.ofHom (algebraMap B (R' ⊗[R] B))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R B)) =
        Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] B))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R R')))
      (a : ((moduleSpecΓFunctor (R := .of R')).obj
        ((tensorPullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).obj
          ((pushforward (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj
            (tilde (R := .of B) M)))) ≃ₗ[R'] R' ⊗[R] M)
      (b : ((moduleSpecΓFunctor (R := .of R')).obj
        ((pushforward (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] B))))).obj
          ((tensorPullback (Spec.map (CommRingCat.ofHom (algebraMap B (R' ⊗[R] B))))).obj
            (tilde (R := .of B) M)))) ≃ₗ[R'] (R' ⊗[R] B) ⊗[B] M),
      (∀ m : M, a.symm ((1 : R') ⊗ₜ[R] m) =
        (((Classical.choose (exists_tensorPullbackAdjunction
            (Spec.map (CommRingCat.ofHom (algebraMap R R'))))).unit.app
          ((pushforward (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj
            (tilde (R := .of B) M))).val.app (op ⊤)
            (tilde.toOpen (R := .of B) M ⊤ m) :
          (moduleSpecΓFunctor (R := .of R')).obj
            ((tensorPullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).obj
              ((pushforward (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj
                (tilde (R := .of B) M))))) ∧
      (∀ (z : B) (m : M), b.symm (((1 : R') ⊗ₜ[R] z) ⊗ₜ[B] m) =
        (((Classical.choose (exists_tensorPullbackAdjunction
            (Spec.map (CommRingCat.ofHom (algebraMap B (R' ⊗[R] B)))))).unit.app
          (tilde (R := .of B) M)).val.app (op ⊤)
            (tilde.toOpen (R := .of B) M ⊤ (z • m)) :
          (moduleSpecΓFunctor (R := .of R')).obj
            ((pushforward (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] B))))).obj
              ((tensorPullback (Spec.map (CommRingCat.ofHom (algebraMap B (R' ⊗[R] B))))).obj
                (tilde (R := .of B) M))))) ∧
      (∀ (r : R') (m : M),
        b ((moduleBaseChangeMap (Spec.map (CommRingCat.ofHom (algebraMap R B)))
            (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] B))))
            (Spec.map (CommRingCat.ofHom (algebraMap R R')))
            (Spec.map (CommRingCat.ofHom (algebraMap B (R' ⊗[R] B)))) w
            (tilde (R := .of B) M)).app ⊤ (a.symm (r ⊗ₜ[R] m))) =
          (r ⊗ₜ[R] (1 : B)) ⊗ₜ[B] m) := by
  sorry

/-- For the structure sheaf the base change isomorphism respects multiplication and unit.
Multiplications are specified on all tensor sections, so they are the canonical sheaf
multiplications, rather than unspecified algebra structures. The tensor comparison is the
one of module_pullback_tensor, and epsilon is the landed tensorPullbackObjUnitToUnit
(the adjoint of the structure ring map); gamma is beta for O_X followed by f'_* of epsilon.
Source: Lemma 02KG, affine formula for M = B; node clause (2)
(blueprint: lem-weil-pbc-affine-pushforward-base-change).
Proof: step (5) of the node: the structure sheaf is quasi-coherent. Clause (1) and the
structure-sheaf pullback isomorphism make gamma invertible. On affine charts its formula
is the identity of R-prime tensor B, hence respects products and 1. The same follows from
the adjoint ring-map description of module-base-change-map-algebra. These equalities glue.
The inverse of an invertible module map respecting multiplication and unit respects them too. -/
theorem affinePushforward_baseChange_algebra {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [IsAffineHom f] :
    ∃ (mu : (pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) ⊗
          (pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
        (pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
      (mu' : (pushforward f').obj (SheafOfModules.unit X'.ringCatSheaf) ⊗
          (pushforward f').obj (SheafOfModules.unit X'.ringCatSheaf) ⟶
        (pushforward f').obj (SheafOfModules.unit X'.ringCatSheaf)),
      (∀ (U : S.Opens) (a b : Γ(X, f ⁻¹ᵁ U)), mu.app U (tmulSection a b) = a * b) ∧
      (∀ (U : S'.Opens) (a b : Γ(X', f' ⁻¹ᵁ U)), mu'.app U (tmulSection a b) = a * b) ∧
      IsIso (moduleBaseChangeMap f f' g g' sq.w (SheafOfModules.unit X.ringCatSheaf) ≫
          (pushforward f').map (tensorPullbackObjUnitToUnit g')) ∧
      (tensorPullback g).map mu ≫
        (moduleBaseChangeMap f f' g g' sq.w (SheafOfModules.unit X.ringCatSheaf) ≫
          (pushforward f').map (tensorPullbackObjUnitToUnit g')) =
        (Classical.choose (module_pullback_tensor g)
            ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
            ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))).hom ≫
          ((moduleBaseChangeMap f f' g g' sq.w (SheafOfModules.unit X.ringCatSheaf) ≫
          (pushforward f').map (tensorPullbackObjUnitToUnit g')) ⊗ₘ
            (moduleBaseChangeMap f f' g g' sq.w (SheafOfModules.unit X.ringCatSheaf) ≫
          (pushforward f').map (tensorPullbackObjUnitToUnit g'))) ≫ mu' ∧
      (tensorPullback g).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
          (moduleBaseChangeMap f f' g g' sq.w (SheafOfModules.unit X.ringCatSheaf) ≫
          (pushforward f').map (tensorPullbackObjUnitToUnit g')) =
        tensorPullbackObjUnitToUnit g ≫
          SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom := by
  sorry

/-- Compatibility with a further base change under the canonical composition isomorphisms.
Source: Stacks Project, Cohomology, Remark 0ATM; node clause (3)
(blueprint: lem-weil-pbc-affine-pushforward-base-change).
Proof: step (6) of the node: cartesian-square pasting identifies the iterated fibre product
with the outer one. Take adjoints of the four-arrow composite. Naturality of units and the
unit compatibility of the conjugate composition isomorphisms reduce its adjoint to the
pushforward of the unit for h-prime followed by g-prime, the defining adjoint of the outer
base change map. This is exactly moduleBaseChangeMap_pasting. -/
theorem affinePushforward_baseChange_comp
    {X S X' S' X'' S'' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (f'' : X'' ⟶ S'')
    (g : S' ⟶ S) (g' : X' ⟶ X) (h : S'' ⟶ S') (h' : X'' ⟶ X')
    (sq₁ : IsPullback g' f' f g) (sq₂ : IsPullback h' f'' f' h)
    [IsAffineHom f] (F : X.Modules) [F.IsQuasicoherent] :
    moduleBaseChangeMap f f'' (h ≫ g) (h' ≫ g')
        ((Category.assoc h' g' f).trans
          ((congrArg (fun k ↦ h' ≫ k) sq₁.w).trans
            ((Category.assoc h' f' g).symm.trans
              ((congrArg (fun k ↦ k ≫ g) sq₂.w).trans (Category.assoc f'' h g))))) F =
      ((conjugateIsoEquiv
          ((Classical.choose (exists_tensorPullbackAdjunction g)).comp
            (Classical.choose (exists_tensorPullbackAdjunction h)))
          (Classical.choose (exists_tensorPullbackAdjunction (h ≫ g)))).symm
          (pushforwardComp h g)).hom.app ((pushforward f).obj F) ≫
        (tensorPullback h).map (moduleBaseChangeMap f f' g g' sq₁.w F) ≫
        moduleBaseChangeMap f' f'' h h' sq₂.w ((tensorPullback g').obj F) ≫
        (pushforward f'').map
          (((conjugateIsoEquiv
            ((Classical.choose (exists_tensorPullbackAdjunction g')).comp
              (Classical.choose (exists_tensorPullbackAdjunction h')))
            (Classical.choose (exists_tensorPullbackAdjunction (h' ≫ g')))).symm
            (pushforwardComp h' g')).inv.app F) := by
  sorry


end
end AlgebraicGeometry.Scheme.Modules
