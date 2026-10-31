/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteAdjointCompositorTransposes

/-! # Normalized finite compact-support compositors

Source: smooth-purity composition comparisons, proof (1), compact-support construction.
(blueprint: lem-sp-finite-support-compositor-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- The proper/open normalized compositor for the specified restricted support functors.
Source: blueprint det-sp-composition-comparisons, proof (1), construction of alpha.
(blueprint: lem-sp-finite-support-compositor-existence).

Proof: Use the finite-ring constructible origin equivalence on the three Noetherian
schemes. Transport the etale proper/open compositor through that fully faithful
comparison and the compact-support site isomorphisms. Its endpoints are the given
support restrictions because the closure proofs change no objects or morphisms.
Finite compact-site coherence identifies the transported map on every bounded-below
etale witness with the displayed word. Naturality transports this equality along
an etale-origin isomorphism; full faithfulness gives a natural isomorphism on the
intrinsic constructible subcategories. The same calculation for the inverse gives
both inverse equations. The normalization also determines this compositor uniquely,
since every constructible object has an etale origin.
-/
theorem finiteSupportCompositor_exists
    (R : Type u) [CommRing R] [Finite R]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    {f : X ⟶ Y} {g : Y ⟶ Z} [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g) (ch : Compactification (f ≫ g))
    (hFf : ∀ M : spFiniteConstructibleTorCategory X R,
      spFiniteConstructibleTor Y R ((reductionCompactSupport R cf.i cf.g).obj M.obj))
    (hFg : ∀ M : spFiniteConstructibleTorCategory Y R,
      spFiniteConstructibleTor Z R ((reductionCompactSupport R cg.i cg.g).obj M.obj))
    (hFh : ∀ M : spFiniteConstructibleTorCategory X R,
      spFiniteConstructibleTor Z R ((reductionCompactSupport R ch.i ch.g).obj M.obj)) :
    ∃ alpha : finiteAdjointSupport R cf hFf ⋙ finiteAdjointSupport R cg hFg ≅
      finiteAdjointSupport R ch hFh,
    ∀ (E : DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} R))))
      (hE : spFiniteConstructibleTor X R ((reductionSite R X).obj E.obj)),
      (alpha.hom.app ⟨(reductionSite R X).obj E.obj, hE⟩).hom =
        (reductionCompactSupport R cg.i cg.g).map
            ((finiteAdjointSiteSupportIso R cf).hom.app E) ≫
          (finiteAdjointSiteSupportIso R cg).hom.app
            ((Etale.rightDerivedLowerShriekOfCompactificationPlus
              (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) cf).obj E) ≫
          (reductionSite R Z).map
            ((coherenceEtaleCompositor (ULift.{u + 1, u} R) cf cg ch).hom.app E).hom ≫
          (finiteAdjointSiteSupportIso R ch).inv.app E := by sorry

end AlgebraicGeometry.ProEtale
