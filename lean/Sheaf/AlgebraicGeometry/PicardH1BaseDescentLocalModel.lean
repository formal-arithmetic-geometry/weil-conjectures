/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
import Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel
import Sheaf.AlgebraicGeometry.PerfectAffineMapRepresentative
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import Sheaf.AlgebraicGeometry.FieldPullbackRankOneTrivial
import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Local scalar models and degree-one comparison for Picard descent

Source: Stacks Project, Tag 0BF2, the finite-free complexes and the representing chain maps.
(blueprint: lem-sc-picard-h1-base-descent-local-model)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

/-- Construct the local finite-free model and its degree-one comparison square, without
assuming injectivity on H¹ and without realizing degree-zero cycles as sections.
Source: Stacks Project, Tag 0BF2, through the displayed chain maps, using Tags 0B91,
0BCD and 08CR. (blueprint: lem-sc-picard-h1-base-descent-local-model)

Proof: Base change to W. An empty residue fibre contradicts the structure adjunction
unit isomorphism, so the flat source and targets are faithfully flat. At a point of
any residue fibre a local free presentation of the descended module pulls back to a
rank-one module over a nonzero residue field. Invariance of finite free rank makes its
rank one. The local finite-free presentations therefore trivialize the target descended
modules on neighbourhoods of w; intersect them and choose an affine neighbourhood.
The immersion identifies κ(w) with κ(s). For the source fibre, use
nonempty_iso_unit_of_invertible_field_pullback on the descended hLs module and the
nonempty fibre to obtain a trivialization, and transport it to κ(w).
Apply perfect direct-image base change and the minimal finite-free residue model
lemma. Negative terms vanish and degree zero has rank one. Choose the global-section
bases e0 and e1 of the source terms, and set d to the coordinates of d⁰(1).
The residue differentials vanish, since the ranks of all terms are the fibre Betti
numbers. Represent the derived arrows to the target models by chain maps. Their target
trivializing sections are cycles and span the rank-one degree-zero terms after shrinking:
the coefficient has nonzero residue and hence becomes invertible on a neighbourhood.
Thus the target degree-zero differentials vanish. Their joint degree-one map is b and
the chain equations give b d = 0. Minimality identifies the source residue degree-one
term with fibre H¹; the fibre trivialization identifies that with structure-sheaf H¹,
giving α. For each target compare the pullback of this fibre generator with its
chosen trivialization; multiply its H¹ identification by the resulting nonzero residue
scalar. This makes the coefficient pullback maps the structure-sheaf pullback maps.
Take the finite product of these identifications to give β. Affineness
identifies the residue field of the evaluation kernel with κ(w), and the immersion
identifies κ(w) with κ(s). Naturality of canonical derived base change identifies the
chain-map degree-one components with the displayed cohomology pullbacks, giving the
square. If m or q is zero the corresponding free term is zero; for n = 0 use the zero
joint target and its unique map. No injectivity is used in this construction. -/
theorem picard_h1_base_descent_local_model
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (hOi : ∀ i, ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd (fi i) g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (hLi : ∀ i, ∃ (N : W.Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
        ((Modules.tensorPullback (ui i)).obj L) ≅
        (Modules.tensorPullback (pullback.snd (fi i) k)).obj N))
    (hLs : ∃ (N : (Spec (S.residueField s)).Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
        (Modules.tensorPullback (pullback.snd f (S.fromSpecResidueField s))).obj N)) :
    ∃ (U : W.Opens) (hwU : w ∈ U), IsAffineOpen U ∧
      ∃ (m q : ℕ) (d : Fin m → Γ(W, U))
        (b : (Fin m → Γ(W, U)) →ₗ[Γ(W, U)] (Fin q → Γ(W, U)))
        (K : CochainComplex
          (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ),
        IsStrictlyPerfect W U K ∧ (∀ i : ℤ, i < 0 → IsZero (K.X i)) ∧
        ∃ (e0 : (K.X 0).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] Γ(W, U))
          (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U))),
          Nonempty ((SheafOfModules.overFunctor.{v}
            (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
              ((schemeDerivedDirectImage (pullback.snd f k)).obj
                ((DerivedCategory.singleFunctor
                  (SheafOfModules.{v}
                    (moduleRings (pullback f k).toRingedSpace)) 0).obj
                      ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
            DerivedCategory.Q.obj K) ∧
          (∀ a : Γ(W, U), e1 ((K.d 0 1).val.app (.op (Over.mk (𝟙 U))) (e0.symm a)) = a • d) ∧
          (∀ i, W.evaluation U w hwU (d i) = 0) ∧ b d = 0 ∧
          let p := RingHom.ker (W.evaluation U w hwU).hom
          letI : p.IsPrime := RingHom.ker_isPrime (W.evaluation U w hwU).hom
            ∃ (α : (p.ResidueField ⊗[Γ(W, U)] (Fin m → Γ(W, U))) ≃+
                Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
              (β : (p.ResidueField ⊗[Γ(W, U)] (Fin q → Γ(W, U))) →+
                (∀ i, Sheaf.H
                  (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1)),
              ∀ z, β ((b.baseChange p.ResidueField) z) = fun i ↦
                structureSheafCohomologyPullback
                  (((Over.pullback (S.fromSpecResidueField s)).map
                    (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                      (ui i) (hui i))).left) 1 (α z) := by sorry

end AlgebraicGeometry.Scheme
