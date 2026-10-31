/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologicalDimensionSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.AffineEtalePullbackDimension
import WeilConjectures.AlgebraicGeometry.Sites.FiniteTypeTorsionCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Sites.HigherDirectImageAffineEtaleBound
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive

/-!
# Open direct-image bound over a field of finite torsion cohomological dimension

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sf-localization/
prop-sf-localization-all-stages.proof.md, "(1') at the finite stage", general field bound.
(blueprint: lem-sf-etale-open-cd-field-bound)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- If `k` has torsion étale cohomological dimension at most `c`, an open immersion of
separated finite-type `k`-schemes with source dimension at most `d` has vanishing higher
direct images in degrees greater than `2 * d + c`, for every sheaf of modules over a
finite commutative ring killed by a positive integer invertible in `k`. No constructibility
condition is imposed. The dimension bound is normalized to zero for an empty source.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sf-localization/
prop-sf-localization-all-stages.proof.md, "(1') at the finite stage", general field bound.
(blueprint: lem-sf-etale-open-cd-field-bound)

Proof:
1. Put `N = 2 * d + c`. For each affine étale `W` over `X`, apply
   lem-sf-affine-etale-pullback-dimension to the `k`-morphism `j`. The pullback
   `V = W ×_X U` is finite type over `k` and has dimension at most `d`. Only the
   test object `W` is assumed affine; arbitrary étale neighborhoods need not be finite type.
2. If `V` is nonempty, write its dimension as `e ≤ d` and apply
   thm-sc-finite-type-torsion-cd. Its torsion cohomological dimension is at most
   `2 * e + c ≤ N`, in the sense of def-sc-etale-torsion-cd. If `V` is empty, the
   empty covering forces every abelian sheaf on its small étale site to be zero,
   and all derived global sections vanish. Thus the bound holds in that case too.
3. Let `n` be the positive integer killing `A`. Every local section `m` of the
   underlying abelian sheaf of `M` satisfies `n • m = (n : A) • m = 0`.
   It is therefore locally torsion. Apply lem-sfb-higher-direct-image-affine-etale-bound
   with the bound from step 2 to obtain vanishing of its abelian higher direct image.
   This uses the sheafification criterion, not an equality of higher-direct-image
   sections with the cohomology of a pullback.
4. Apply lem-sbc-higher-direct-image-forget-comparison to `A`, `j`, `q`, and `M`.
   Its underlying abelian higher direct image is zero by step 3. The faithful
   forgetful functor reflects the equation that the identity is zero, hence reflects
   zero objects. This proves the module-sheaf conclusion, including the zero ring
   and the empty source. -/
theorem isZero_higherDirectImage_openImmersion_of_field_cd
    (k : Type u) [Field k] (c d : ℕ)
    (hc : Scheme.HasTorsionEtaleCohomologicalDimensionLE (Spec (.of k)) c)
    {U X : Scheme.{u}} (aU : U ⟶ Spec (.of k)) (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aU] [QuasiCompact aU] [IsSeparated aU]
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (j : U ⟶ X) [IsOpenImmersion j] (hj : j ≫ aX = aU)
    (hd : topologicalKrullDim U ≤ (d : WithBot ℕ∞))
    (hEmpty : IsEmpty U → d = 0)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, 0 < n ∧ IsUnit (n : k) ∧ (n : A) = 0)
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (q : ℤ) (hq : (2 * d + c : ℕ) < q) :
    IsZero (higherDirectImage A j q M) := by
  classical
  have _ := hEmpty
  let ΦU := sheafCompose U.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
  let ΦX := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
  have hM : (ΦU.obj M).IsTorsion := by
    obtain ⟨n, hn, _, hnA⟩ := hA
    apply Sheaf.IsTorsion.of_forall_isAddTorsion
    intro W m
    apply isOfFinAddOrder_iff_nsmul_eq_zero.2
    refine ⟨n, hn, ?_⟩
    have hm : ∀ x : M.obj.obj W, n • x = 0 := by
      intro x
      rw [← Nat.cast_smul_eq_nsmul A, hnA, zero_smul]
    exact hm m
  have hbound : ∀ {W : Scheme.{u}} (w : W ⟶ X) [AlgebraicGeometry.Etale w]
      [IsAffine W], Scheme.HasTorsionEtaleCohomologicalDimensionLE
        (pullback w j) (2 * d + c) := by
    intro W w _ _
    obtain ⟨⟨hft, hqc⟩, _, hdim, _⟩ :=
      affine_etale_pullback_dimension aU aX j hj d hd w
    let V := pullback w j
    let : V.Over (Spec (.of k)) := ⟨pullback.snd w j ≫ aU⟩
    let : LocallyOfFiniteType (V ↘ Spec (.of k)) := hft
    let : QuasiCompact (V ↘ Spec (.of k)) := hqc
    have hVdim : topologicalKrullDim V ≤ (d : WithBot ℕ∞) := hdim.trans hd
    rcases isEmpty_or_nonempty V with hV | hV
    · let := hV
      intro F _ n _
      apply AddCommGrpCat.isZero_iff_subsingleton.mp
      change IsZero (((Sheaf.Γ V.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))
      exact (((Sheaf.Γ V.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).map_isZero
          ((DerivedCategory.singleFunctor _ 0).map_isZero
            (Scheme.Etale.isZero_sheaf_of_isEmpty F)))
    · let := hV
      have hbot : topologicalKrullDim V ≠ ⊥ := by
        apply Order.krullDim_ne_bot_iff.2
        obtain ⟨v⟩ := hV
        exact ⟨⟨closure {v}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
      obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.1 hbot
      have hed : e ≤ (d : ℕ∞) := WithBot.coe_le_coe.1 (he ▸ hVdim)
      obtain ⟨n, rfl, hnd⟩ := ENat.le_natCast_iff.1 hed
      have hcd := Scheme.hasTorsionEtaleCohomologicalDimensionLE_of_finiteType
        k c n hc V he.symm
      intro F hF r hr
      exact hcd F hF r (by omega)
  have hz := isZero_higherDirectImage_of_affineEtale_cd j (2 * d + c)
    hbound (ΦU.obj M) hM q (by exact_mod_cast hq)
  obtain ⟨e⟩ := nonempty_higherDirectImage_forget_iso A j q M
  have hz' : IsZero (ΦX.obj (higherDirectImage A j q M)) := hz.of_iso e
  apply (IsZero.iff_id_eq_zero _).2
  apply ΦX.map_injective
  exact hz'.eq_of_src _ _

end AlgebraicGeometry.Etale
