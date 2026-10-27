/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.AlgebraicGeometry.CompleteLinearFlag
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import Sheaf.AlgebraicGeometry.FreeQuotientGrassmannProjective
import WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.AffineFreeMapZeroLocus
import WeilConjectures.AlgebraicGeometry.LocalClosedLocusGluing
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper

/-! # The projective complete flag scheme and its linear action

Source: Milne, Algebraic Groups (2017), Propositions 7.29--7.30, printed p.146
(blueprint: lem-sfb-complete-linear-flag-scheme).

Representability on algebras is expressed by bijections from the affine restriction
of the scheme's Yoneda functor, natural under the specified scalar-image operation.
The internal action includes the identity and associativity diagrams as structure fields.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry

/-- The complete flag functor is represented by a projective, proper, finite type
scheme with the natural GL action, and its k-points are the usual linear flags.

Source: Milne, Propositions 7.29--7.30, printed p.146
(blueprint: lem-sfb-complete-linear-flag-scheme).

Proof, following the eight steps of the node:
1. Use lem-sfb-free-quotient-grassmann-projective for quotient ranks n-i.
   Split the universal quotients locally. Their kernels are locally free of rank i
   by lem-weil-pbc-finite-projective-standard-free-cover and commute with arbitrary
   pullback, using def-pc-module-pullback and the affine tilde-gamma adjunction.
2. Form the finite product by def-pc-fibre-product and cut out the vanishing of
   K_i -> Q_(i+1). Use lem-sc-affine-free-map-zero-locus and
   lem-sc-local-closed-locus-gluing. For n=1 the condition is empty.
3. The Grassmannian classifications and the zero condition identify maps into the
   incidence scheme with flags. Kernels and quotient classes determine each other;
   this identification commutes with pullback by the splitting in step 1.
4. Apply lem-weil-pbc-affine-tilde-gamma-adjunction, -spec-tilde-free-module,
   -spec-module-tilde-sections and -tilde-pullback-base-change to identify affine
   flags with the embedded algebra submodules here. Tensor images give the stated
   scalar extension. Over k, the rank condition is precisely dimension i.
5. Embed the finite Grassmannian product into projective space inductively using
   lem-chow-segre, lem-weil-pbc-closed-immersion-base-change and -comp. Compose
   with the closed incidence immersion to obtain H-projectivity.
6. Apply lem-kun-projective-implies-proper. Proper implies finite type and
   quasi-compact, hence also projective in def-pc-projective-morphism's convention.
7. On GL times the incidence scheme, apply the universal invertible matrix to each
   universal subbundle. This is again a flag and hence classifies a scheme morphism.
   Its affine points have precisely the displayed submodule-image formula.
8. On GL times GL times the scheme, (gh)K_i = g(hK_i); the identity fixes every K_i.
   Uniqueness in the classification proves both scheme action diagrams, using the
   group laws of def-sc-general-linear-group, over nonreduced algebras as well.
-/
theorem exists_completeLinearFlagScheme (k : Type u) [Field k] (n : ℕ) (hn : 1 ≤ n) :
    ∃ (Fl : Over (Spec (.of k)))
      (e : ∀ A : CommAlgCat.{u} k,
        ((yoneda.obj Fl).obj (op ((algSpec (.of k)).obj (op A)))) ≃
          CompleteLinearFlag A n)
      (a : ModObj (GeneralLinearGroup (LinearGroupSchemes.Index.{u} n) k) Fl),
      IsProjective Fl.hom ∧ IsProper Fl.hom ∧
      (LocallyOfFiniteType Fl.hom ∧ QuasiCompact Fl.hom) ∧
      (∀ (A B : CommAlgCat.{u} k) (f : A ⟶ B)
        (x : (algSpec (.of k)).obj (op A) ⟶ Fl) (i : Fin (n + 1)),
        ((e B ((algSpec (.of k)).map f.op ≫ x)).step i).toSubmodule =
          completeFlagScalarImage f.hom.toRingHom ((e A x).step i).toSubmodule) ∧
      (∀ (A : CommAlgCat.{u} k)
        (g : (algSpec (.of k)).obj (op A) ⟶
          GeneralLinearGroup (LinearGroupSchemes.Index.{u} n) k)
        (x : (algSpec (.of k)).obj (op A) ⟶ Fl) (i : Fin (n + 1)),
        ((e A (CartesianMonoidalCategory.lift g x ≫ a.smul)).step i).toSubmodule =
          (((e A x).step i).toSubmodule).map
            (GeneralLinearGroup.homMulEquiv
              (LinearGroupSchemes.Index.{u} n) k A g).val.mulVecLin) ∧
      (∀ F : Fin (n + 1) → Submodule k (LinearGroupSchemes.Index.{u} n → k),
        (Monotone F ∧ F 0 = ⊥ ∧ F (Fin.last n) = ⊤ ∧
          ∀ i, Module.finrank k (F i) = i.val) ↔
        ∃! x : (algSpec (.of k)).obj (op (CommAlgCat.of k k)) ⟶ Fl,
          ∀ i, ((e (CommAlgCat.of k k) x).step i).toSubmodule = F i) := by
  sorry

end AlgebraicGeometry
