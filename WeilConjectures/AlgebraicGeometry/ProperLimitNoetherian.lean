/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.AlgebraicGeometry.EventuallyProper
import WeilConjectures.AlgebraicGeometry.ProperFinitePresentationClosedLimit
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.ProperLimitNoetherianCore

/-! # Proper morphisms as limits of proper finite-type models

## References

* [Stacks Project, Tag 0A0P](https://stacks.math.columbia.edu/tag/0A0P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A proper morphism over a quasi-compact and quasi-separated scheme is a limit of
proper morphisms over schemes of finite type over `ℤ`, with affine transitions
(Stacks, Tag 0A0P). -/
theorem exists_proper_limit_noetherian
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
      (Xs Ss : Λᵒᵖ ⥤ Scheme.{u}) (fs : Xs ⟶ Ss)
      (πX : (Functor.const Λᵒᵖ).obj X ⟶ Xs) (πS : (Functor.const Λᵒᵖ).obj S ⟶ Ss),
      Nonempty (IsLimit (Cone.mk X πX)) ∧ Nonempty (IsLimit (Cone.mk S πS)) ∧
      (∀ (i j : Λᵒᵖ) (a : i ⟶ j), IsAffineHom (Xs.map a) ∧ IsAffineHom (Ss.map a)) ∧
      (∀ i : Λᵒᵖ, IsProper (fs.app i)) ∧
      (∀ i : Λᵒᵖ, LocallyOfFiniteType (specULiftZIsTerminal.from (Ss.obj i)) ∧
        QuasiCompact (specULiftZIsTerminal.from (Ss.obj i))) ∧
      (∀ i : Λᵒᵖ, πX.app i ≫ fs.app i = f ≫ πS.app i) ∧
      (IsAffine S →
        (∀ i : Λᵒᵖ, IsAffine (Ss.obj i) ∧
          RingHom.FiniteType (algebraMap ℤ (Scheme.Γ.obj (Opposite.op (Ss.obj i))))) ∧
        Nonempty (IsColimit (Scheme.Γ.mapCocone (Cone.mk S πS).op))) := by
  by_cases hS : IsAffine S
  · obtain ⟨Λ, hpre, hne, hdir, Xs, Ss, fs, πX, πS, hlimX, hlimS,
      htrans, hproper, hfinite, hcomm, haff, hcol⟩ :=
      proper_limit_noetherian_affine_clause f hS
    exact ⟨Λ, hpre, hne, hdir, Xs, Ss, fs, πX, πS, hlimX, hlimS,
      htrans, hproper, hfinite, hcomm, fun _ => ⟨haff, hcol⟩⟩
  · obtain ⟨Λ, hpre, hne, hdir, Xs, Ss, fs, πX, πS, hlimX, hlimS,
      htrans, hproper, hfinite, hcomm⟩ := exists_proper_limit_noetherian_core f
    exact ⟨Λ, hpre, hne, hdir, Xs, Ss, fs, πX, πS, hlimX, hlimS,
      htrans, hproper, hfinite, hcomm, fun h => (hS h).elim⟩

end AlgebraicGeometry
