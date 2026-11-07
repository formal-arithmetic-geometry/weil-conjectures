/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteQuotientEtaleOriginCore
import Submission.WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteQuotientEtaleOriginTransportMap

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Conditional constant-model transport for a finite quotient origin

Source: Stacks Project, Tag 09C6.
(blueprint: lem-weil-pbc-lisse-finite-quotient-etale-origin-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

/-- Transport a supplied constant model through a core finite quotient origin.

Proof: restrict the core comparison to an étale chart `Z`, compose it with the
supplied constant-model isomorphism, and pull the resulting square to `W`. The
comparison-pullback coherence and the canonical finite-coefficient comparison
identify the constant side with `constantAdicQuotientRealization`; pulling the
finite constant local models gives the relative finite lisse statement.

Source: Stacks Project, proetale.tex, Tag 09C6
(blueprint: lem-weil-pbc-lisse-finite-quotient-etale-origin-transport).
-/
theorem lisse_finite_quotient_etale_origin_transport
    {X Y : Scheme.{u}} {g : Y ⟶ X}
    {A : Type (u + 1)} [CommRing A] {d : AdicCoefficientDatum A} {n : ℕ}
    {K : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n)))}
    {V : Y.Etale}
    (C : LisseFiniteQuotientEtaleOriginCore X Y g d n K V)
    (Z : V.left.Etale)
    (E : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
    (hE : Nonempty ((AlgebraicGeometry.Etale.upperStar _ Z.hom).mapDerivedCategory.obj
        C.level ≅ (constantSheaf Z.left.smallEtaleTopology _).mapDerivedCategory.obj E))
    (W : Y.ProEt) (_w : W ⟶ (toProEt Y).obj (Etale.mk (Z.hom ≫ V.hom))) :
    Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj E ≅
      (adicTowerPullback (W.hom ≫ g)
        ((pbcAdicRings X d).obj (op n))).obj K) := by
  obtain ⟨f, hf, hg⟩ := lisse_finite_quotient_etale_origin_transport_map C Z E hE W _w
  letI : Mono f := hf
  letI : Epi f := hg
  haveI : IsIso f := by
    apply isIso_of_mono_of_epi
  exact ⟨asIso f⟩

end AlgebraicGeometry.Scheme
