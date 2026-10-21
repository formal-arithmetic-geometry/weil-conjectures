/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Free

import Sheaf.Paper.ContinuousRingUniverseRealization
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.CategoryTheory.Preadditive.HomOrthogonal
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Analysis.Normed.Algebra.Ultra
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap

/-!
# Invariant rank of finite free continuous coefficient sheaves

Source: Hemo--Richarz--Scholbach, Example 3.1, p. 6; blueprint
`sec-six-functors-basics/sk-lem-stratified-lattice/sk-lem-stratified-lattice-rank.proof.md`,
first paragraph (blueprint: lem-sfb-continuous-coefficient-free-rank).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Limits MonObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private lemma continuousRegular_map_mul (X : Scheme.{u}) (T : Type u)
    [TopologicalSpace T] [Ring T] [IsTopologicalRing T]
    (f : Mod.regular ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousCoefficientRingSheaf X T)) ⟶
      Mod.regular ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousCoefficientRingSheaf X T)))
    (U : X.ProEtᵒᵖ) (a b : ULift.{u + 1} C(U.unop.left, T)) :
    f.hom.hom.app U (a * b) =
      a * (show ULift.{u + 1} C(U.unop.left, T) from f.hom.hom.app U b) := by
  let R := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousCoefficientRingSheaf X T)
  let F := sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  let : MonObj R.obj := (continuousCoefficientRingSheaf X T).obj.monObjCompForget₂
  let g : R ⟶ R := f.hom
  have hf : μ[R] ≫ g = R ◁ g ≫ μ[R] := Mod.act_hom f
  have hm : Functor.LaxMonoidal.μ F R R ≫ F.map μ[R] = μ[R.obj] :=
    Sheaf.μ_comp_map_mul R
  have h : μ[R.obj] ≫ g.hom = R.obj ◁ g.hom ≫ μ[R.obj] := by
    calc
      _ = (Functor.LaxMonoidal.μ F R R ≫ F.map μ[R]) ≫ F.map g := by
        rw [hm]
        rfl
      _ = Functor.LaxMonoidal.μ F R R ≫ F.map (R ◁ g ≫ μ[R]) := by
        rw [Category.assoc, ← F.map_comp, hf]
      _ = _ := by
        rw [F.map_comp, ← Category.assoc, ← Functor.LaxMonoidal.μ_natural_right,
          Category.assoc, hm]
        rfl
  have h' := congr_app h U
  exact congrArg (fun z ↦ z.hom (a ⊗ₜ[ℤ] b)) h'

private lemma continuousRegular_comm (X : Scheme.{u}) (T : Type u)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (f g : End (Mod.regular ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousCoefficientRingSheaf X T)))) : f * g = g * f := by
  apply Mod.hom_ext
  apply Sheaf.hom_ext
  ext U a
  have h (k : End (Mod.regular ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousCoefficientRingSheaf X T))))
      (b : ULift.{u + 1} C(U.unop.left, T)) :
      k.hom.hom.app U b = b * (show ULift.{u + 1} C(U.unop.left, T) from
        k.hom.hom.app U (ULift.up 1)) := by
    have hk := continuousRegular_map_mul X T k U b (ULift.up 1)
    have hb : b * ULift.up (1 : C(U.unop.left, T)) = b := _root_.mul_one b
    rw [hb] at hk
    exact hk
  change f.hom.hom.app U (g.hom.hom.app U a) =
    g.hom.hom.app U (f.hom.hom.app U a)
  rw [h f (g.hom.hom.app U a), h g (f.hom.hom.app U a), h g a, h f a]
  ac_rfl

/-- Finite free continuous coefficient sheaves on a nonempty scheme have invariant rank.
The normed algebra structure specifies the unique extension of the ℓ-adic norm to `E`.
The finite biproduct defining `Mod.finiteFree` includes the zero module in rank zero.

Source: Hemo--Richarz--Scholbach, Example 3.1, p. 6; blueprint stratified-lattice rank
proof, first paragraph (blueprint: lem-sfb-continuous-coefficient-free-rank).

Proof:
1. The unique extended absolute value is nonarchimedean
   (`lem-weil-l-adic-extension-absolute-value`). Ultrametric balls are clopen and separate
   distinct points, so `E` is totally disconnected. Apply
   `lem-sfb-continuous-ring-universe-realization` to identify the coefficient ring object
   with the ring sheaf `R(U) = C(|U|, E)`. Transport the given isomorphism and its inverse
   along this ring isomorphism, retaining both inverse identities.
2. For each finite biproduct use its inclusions `i_j` and projections `p_j`.
   They satisfy `p_j i_k = δ_jk` and `Σ i_j p_j = 1`, including the empty sum in rank zero
   (`sk-def-sfb-module-objects`, `def-weil-additive-category`).
3. A regular-module endomorphism `h` satisfies `h_W(a) = a h_W(1)` by its module-morphism
   equation. For the transported maps `f` and `g`, take entries
   `A_ij = (p_i f i_j)_W(1)` and `B_ji = (p_j g i_i)_W(1)` in `C(|W|, E)`.
   Insert the biproduct identity resolutions into `gf = 1` and `fg = 1`.
   Linearity on sections and commutativity give `BA = I_m` and `AB = I_n`.
4. Choose `w : W`. Evaluation at `w` preserves all ring operations, so the evaluated
   matrices define mutually inverse linear maps `E^m` and `E^n`. The same formulas use
   empty matrices and empty sums when either rank is zero.
5. The standard coordinate vectors are bases of these spaces, of dimensions `m` and `n`
   (`def-weil-vector-space-dimension`). Their images under the two inverse maps are
   independent. Apply `lem-weil-independent-family-card-le-dimension` in both directions
   to obtain `m ≤ n` and `n ≤ m`, and conclude by antisymmetry. -/
theorem continuous_coefficient_finiteFree_rank
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] (W : Scheme.{u}) [Nonempty W] (m n : ℕ)
    (_e : Mod.finiteFree (condensedRingObj (Profinite.continuousCoefficientRingObj E) W) m ≅
      Mod.finiteFree (condensedRingObj (Profinite.continuousCoefficientRingObj E) W) n) :
    m = n := by
  classical
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  let := Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} E
  let φ := ContinuousRingUniverse.comparison W E
  let : IsIso φ := ContinuousRingUniverse.comparison_isIso W E
  let : IsMonHom φ := ContinuousRingUniverse.comparison_isMonHom W E
  let R := (sheafCompose (Scheme.ProEt.topology W)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousCoefficientRingSheaf W E)
  let M := Mod.regular R
  -- Regular endomorphisms commute by their sectionwise multiplier formula.
  let : CommRing (End M) := { (inferInstance : Ring (End M)) with
    mul_comm := continuousRegular_comm W E }
  -- The constant unit section is nonzero on a nonempty scheme.
  have h10 : (1 : End M) ≠ 0 := by
    intro h
    have hh := congrArg (fun k : End M ↦
      (k.hom.hom.app (Opposite.op (Scheme.ProEt.mk (𝟙 W))) (ULift.up 1)).down
        (Classical.choice (inferInstance : Nonempty W))) h
    exact one_ne_zero (α := E) hh
  let : Nontrivial (End M) := nontrivial_of_ne 1 0 h10
  let e : Mod.finiteFree R m ≅ Mod.finiteFree R n :=
    (Mod.finiteFreeIsoComap (inv φ) m).symm ≪≫
      (Mod.comap (inv φ)).mapIso _e ≪≫ Mod.finiteFreeIsoComap (inv φ) n
  -- A singleton hom-orthogonal family gives invariant multiplicities, including zero.
  have ho : HomOrthogonal (fun _ : Unit ↦ M) := by
    intro i j hij
    exact (hij (Subsingleton.elim _ _)).elim
  obtain ⟨a, _ha⟩ := ho.equiv_of_iso (f := fun _ : Fin m ↦ ())
    (g := fun _ : Fin n ↦ ()) e
  simpa only [Fintype.card_fin] using Fintype.card_congr a

end AlgebraicGeometry.ProEtale
