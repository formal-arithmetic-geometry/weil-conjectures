/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.LinearAlgebra.Dual.Defs
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.AffineDualRestrictionComparison
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Bidual

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Restriction of the actual affine double dual

Source: Stacks Project, Tags 0583 and 0EY6.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Taking the actual finite double dual preserves a finite locally free restriction.
Source: Stacks Project, Tag 0583 (localization of Hom) and Tag 0EY6 proof of (1).
(blueprint: new-affine-double-dual-restriction)

Proof: Noetherianity makes M and its first dual finitely presented. On each
basic affine open inside W, Hom therefore commutes with localization twice.
The resulting canonical comparison identifies the restriction of tilde(M**)
with the sheaf double dual of the restriction of tilde M. Transport the given
isomorphism to P through the two contravariant dual functors. Evaluation into
the double dual is an isomorphism for a finite locally free sheaf, as verified
on finite free trivializations. These canonical local comparisons agree on
overlaps, so they glue to the stated restriction isomorphism. There is no
boundary hypothesis and no depth assertion here. The empty open and rank-zero
locally free modules are included. -/
theorem affine_double_dual_restriction
    (A : CommRingCat.{u}) [IsNoetherianRing A] (W : (Spec A).Opens)
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (P : W.toScheme.Modules) [P.IsFiniteLocallyFree]
    (e : Modules.restrict (tilde M) W.ι ≅ P) :
    Nonempty (Modules.restrict
      (tilde (ModuleCat.of A (Module.Dual A (Module.Dual A M)))) W.ι ≅ P) := by
  let N := Modules.restrict (tilde M) W.ι
  let : N.IsFiniteLocallyFree := SheafOfModules.IsFiniteLocallyFree.of_iso.{u, u, u} e.symm
  obtain ⟨d₁⟩ := affine_dual_restriction_comparison A W M
  obtain ⟨d₂⟩ := affine_dual_restriction_comparison A W
    (ModuleCat.of A (Module.Dual A M))
  let d₃ := ((SheafOfModules.homFunctor W.toScheme.sheaf).flip.obj
    (SheafOfModules.unit W.toScheme.ringCatSheaf)).mapIso d₁.op
  have := SheafOfModules.isIso_bidual N
  exact ⟨d₂ ≪≫ d₃.symm ≪≫ (asIso (SheafOfModules.bidual N)).symm ≪≫ e⟩

end AlgebraicGeometry.Scheme
