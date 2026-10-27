/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J9
-/
module

public import Sheaf.AlgebraicGeometry.PrescribedPointSystemData
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitKernel
import WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial
import WeilConjectures.AlgebraicGeometry.Cohomology.AcyclicResolution

/-!
# Eventual restriction onto a finite closed subscheme

Source: Stacks Project, Tag 0B5T (4), and the cohomology exact sequence.
(blueprint: lem-zl-projective-twist-restriction-surjective).
-/

@[expose] public section

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules MonoidalCategory

noncomputable section

attribute [local irreducible] tensorPullback

private theorem surjective_restriction_of_vanishing
    {Y Z : Scheme.{u}} (w : Z ⟶ Y) [IsClosedImmersion w]
    (P : Y.Modules) [P.IsInvertible]
    [Subsingleton ((w.ker.toModules ⊗ P).H 1)] :
    Function.Surjective (pullbackΓ w P) := by
  classical
  let μ : w.ker.toModules ⊗ P ⟶ P := w.ker.toModulesι ▷ P ≫ (λ_ P).hom
  have : Mono μ := inferInstance
  let adj := Classical.choice (nonempty_tensorPullbackAdjunction w)
  obtain ⟨hepi, hzero, ⟨hlim⟩⟩ := closedImmersion_unit_kernel w P
  let : Epi (adj.unit.app P) := hepi
  let S := ShortComplex.mk (image.ι μ) (adj.unit.app P) hzero
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel S hlim
      mono_f := inferInstance
      epi_g := hepi }
  have : Subsingleton ((image μ).H 1) :=
    subsingleton_H_of_iso (imageMonoIsoSource μ).symm 1
  have hs : Function.Surjective ((adj.unit.app P).app ⊤) :=
    surjective_app_g_of_subsingleton hS
  let e := (adj.leftAdjointUniq (pullbackPushforwardAdjunction w)).app P
  let q := (pushforward w).mapIso e
  have hq : Function.Surjective (q.hom.app ⊤) :=
    (ModuleCat.epi_iff_surjective
      ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).map q.hom)).mp inferInstance
  have hu := adj.unit_leftAdjointUniq_hom_app (pullbackPushforwardAdjunction w) P
  rw [pullbackΓ_def]
  change Function.Surjective (((pullbackPushforwardAdjunction w).unit.app P).app ⊤)
  rw [← hu]
  exact hq.comp hs

/-- High projective twists restrict surjectively to every closed subscheme with finite
support, including nonreduced first infinitesimal neighbourhoods.

Source: Stacks Project, coherent.tex, Tag 0B5T (4), applied to the ideal of the
closed subscheme; blueprint, finite-cover-curve proof, paragraph 2.
(blueprint: lem-zl-projective-twist-restriction-surjective).

Proof: A closed projective subscheme over a field is proper and Noetherian. The ideal
of `w` is coherent, as a quasi-coherent submodule of the structure sheaf. Tensor
`0 -> ker(w) -> O_Y -> w_* O_W -> 0` with the invertible twist. Tensoring is exact,
as is checked in a local frame. Serre vanishing makes H^1 of the ideal twist zero
in every sufficiently large degree. The long exact cohomology sequence then makes
restriction from global sections onto global sections of the restricted twist
surjective. The projection formula for the closed immersion identifies the quotient
with `w_* w^* O_Y(n)` and its global sections with those on `W`; the resulting arrow
is the canonical `pullbackΓ`. Tensor powers of the ample pullback of O(1) are
isomorphic to the projective twists. Transport the restriction maps by naturality.
In fact the same argument works without the finite-support hypothesis.
-/
theorem exists_eventual_projectiveTwist_restriction_surjective
    {k : Type u} [Field k] {N : ℕ} {Y Z : Scheme.{u}}
    (c : Y ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k))) [IsClosedImmersion c]
    (w : Z ⟶ Y) [IsClosedImmersion w] (hw : (Set.range w).Finite) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      Function.Surjective (pullbackΓ w (prescribedPointTwist c n)) := by
  classical
  have _ := hw
  let f := c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k))
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have := isQuasicoherent_toModules w.ker
  have := isFinitePresentation_toModules w.ker
  obtain ⟨m₀, hm₀⟩ := exists_subsingleton_H_tensor_twist (k := k) c w.ker.toModules
  refine ⟨m₀.toNat, ?_⟩
  intro n hn
  have hm : m₀ ≤ (n : ℤ) := (Int.self_le_toNat m₀).trans (by exact_mod_cast hn)
  have := hm₀ (n : ℤ) hm 1 Nat.one_pos
  let adj := Classical.choose (exists_tensorPullbackAdjunction c)
  let e := (adj.leftAdjointUniq (pullbackPushforwardAdjunction c)).app
    (ProjectiveSpace.twist _ _ (n : ℤ))
  have : Subsingleton ((w.ker.toModules ⊗ prescribedPointTwist c n).H 1) :=
    subsingleton_H_of_iso (whiskerLeftIso w.ker.toModules e.symm) 1
  have : (prescribedPointTwist c n).IsInvertible :=
    ((invertible_pullback_tensor c).1 (ProjectiveSpace.twist _ _ (n : ℤ))).2
  exact surjective_restriction_of_vanishing w (prescribedPointTwist c n)

end

end AlgebraicGeometry
