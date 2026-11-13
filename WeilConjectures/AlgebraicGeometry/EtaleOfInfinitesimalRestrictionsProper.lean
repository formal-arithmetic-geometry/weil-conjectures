/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.AdicCompletion.Basic
import WeilConjectures.AlgebraicGeometry.EtaleOpenOfInfinitesimalRestrictions
import WeilConjectures.AlgebraicGeometry.ProperEtaleOpen

/-!
# Étaleness detected by infinitesimal restrictions with proper source

Source: Stacks Project, Fundamental Groups, Tag 0GS2, complete Noetherian
essential-surjectivity paragraph, the last two sentences before the conclusion.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry


/-- A finite type morphism to a locally Noetherian scheme is étale if all its
infinitesimal restrictions are étale and its source is proper over the complete base.
Source: Stacks Project, Tag 0GS2, complete Noetherian essential-surjectivity
paragraph, using More on Morphisms, Tag 0A43(2), and Algebra, Tag 05GI(4). -/
theorem etale_of_infinitesimal_restrictions_of_proper
    {A : Type u} [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    {X Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) (g : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsProper (g ≫ f)]
    (h_etale : ∀ n : ℕ, Etale (pullback.snd g (pullback.fst f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))))) :
    Etale g := by
  obtain ⟨W, hW, hEt⟩ :=
    etale_open_of_infinitesimal_restrictions I f g h_etale
  have htop : W = ⊤ := proper_closed_fiber_open_eq_top I f g W hW
  subst W
  let : Etale ((⊤ : X.Opens).ι ≫ g) := hEt
  have : Etale (X.topIso.inv ≫ ((⊤ : X.Opens).ι ≫ g)) := inferInstance
  simpa only [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp] using this

end AlgebraicGeometry
