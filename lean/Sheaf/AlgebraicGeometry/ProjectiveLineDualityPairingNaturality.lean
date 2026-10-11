/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Sheaf.AlgebraicGeometry.LocallyFreeExtCohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.DualityPairing
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine

/-!
# Naturality and connecting-square compatibility of projective-line duality

Source: Weil conjectures blueprint, `thm-sc-p1-duality`, proof, Step 2
(blueprint: lem-sc-p1-duality-pairing-naturality).
-/

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- The Yoneda pairing is linear in the global section.
Source: blueprint `thm-sc-p1-duality`, proof, Step 2
(blueprint: lem-sc-p1-duality-pairing-naturality).
Proof: identify H0(G) with Hom(O,G) via lem-sc-ext-locally-free in degree zero.
The canonical comparison is compatible with scalar multiplication: evaluation, tensor,
internal Hom and global sections all commute with multiplication by a base scalar.
Yoneda composition is additive and commutes with that scalar action, by representing
it as composition of derived-category morphisms (def-sc-ext-sheaf).
Apply the canonical comparison in degree one and the linear form t. -/
theorem extDualPairing_isLinear {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [HasExt.{u} X.Modules] {ω : X.Modules}
    (t : Module.Dual k (ω.H 1)) (G : X.Modules) (e : Ext G ω 1) :
    IsLinearMap k (fun s : G.H 0 ↦
      t (locallyFreeUnitExtAddEquivH ω 1
        (((locallyFreeUnitExtAddEquivH G 0).symm s).comp e (Nat.zero_add 1)))) := sorry

/-- The map beta sends e to the functional s ↦ t(e composed with s).
The canonical unit Ext comparison identifies H0 with Hom(O,-) and Ext1(O,omega) with H1.
Source: blueprint `thm-sc-p1-duality`, proof, Step 2
(blueprint: lem-sc-p1-duality-pairing-naturality). -/
def extDualPairing {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [HasExt.{u} X.Modules] {ω : X.Modules}
    (t : Module.Dual k (ω.H 1)) (G : X.Modules) (e : Ext G ω 1) :
    Module.Dual k (G.H 0) :=
  IsLinearMap.mk' _ (extDualPairing_isLinear t G e)

/-- Both projective-line duality pairings are contravariantly natural, and their
connecting square commutes with sign +1. The Ext boundary is pushout, written as
composition with the extension class, rather than the signed boundary in Ext.δ.
Source: blueprint `thm-sc-p1-duality`, proof, Step 2
(blueprint: lem-sc-p1-duality-pairing-naturality).
Proof: (1) The formulas are dualPairing and extDualPairing, using def-sc-ext-sheaf
and the canonical unit comparison of lem-sc-ext-locally-free.
(2) Functoriality of H1 gives alpha naturality (def-sc-sheaf-cohomology-functor).
(3) Ext pullback is precomposition (lem-sc-p1-ext-yoneda-functoriality); associativity
of Yoneda composition (lem-sc-p1-ext-yoneda-associativity) gives beta naturality.
(4) Write delta for the short exact sequence's extension class. The cohomology
boundary sends s to delta composed with s (lem-sc-p1-boundary-extension-composition).
The Ext boundary sends phi to phi[1] composed with delta, by pushout
(lem-sc-p1-ext-yoneda-associativity). Naturality of the unit comparison
(lem-sc-p1-ext-yoneda-functoriality) and associativity identify both evaluations
with t(phi[1] composed with delta composed with s), with no minus sign. -/
theorem p1_duality_pairing_naturality (k : Type u) [Field k] [IsAlgClosed k]
    [HasExt.{u} (ProjectiveLine (Spec (.of k))).Modules]
    (t : ((ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials).H 1 ≃ₗ[k] k) :
    (∀ (G' G : (ProjectiveLine (Spec (.of k))).Modules) (f : G' ⟶ G)
      (φ : G ⟶ (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials),
      dualPairing t.toLinearMap G' (f ≫ φ) =
        (dualPairing t.toLinearMap G φ).comp (H.mapLinearMap k f 1)) ∧
    (∀ (G' G : (ProjectiveLine (Spec (.of k))).Modules) (f : G' ⟶ G)
      (e : Ext G (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials 1),
      extDualPairing t.toLinearMap G' ((Abelian.Ext.mk₀ f).comp e (Nat.zero_add 1)) =
        (extDualPairing t.toLinearMap G e).comp (H.mapLinearMap k f 0)) ∧
    (∀ (S : ShortComplex (ProjectiveLine (Spec (.of k))).Modules) (hS : S.ShortExact)
      (φ : S.X₁ ⟶ (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials),
      extDualPairing t.toLinearMap S.X₃
          (hS.extClass.comp (Abelian.Ext.mk₀ φ) (Nat.add_zero 1)) =
        (dualPairing t.toLinearMap S.X₁ φ).comp (H.δLinearMap k hS 0)) := sorry

end

end AlgebraicGeometry.Scheme.Modules
