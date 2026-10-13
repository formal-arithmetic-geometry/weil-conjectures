/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators

/-! # Tensor-power sections under open restriction

Source: Stacks Project, Modules, Tag 01CD; Properties, Tag 01PW, restriction to the
opens in its proof; Cohomology of Schemes, Tag 09MR, affine-open paragraph.
(blueprint: lem-sc-tensor-power-section-open-restriction).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Open restriction identifies tensor-power numerator groups, their transition maps,
and the equations expressing multiplication by a tensor power of a section.
No affineness, invertibility, quasi-coherence, or nonvanishing hypothesis is needed.

Source: Stacks Project, Modules, Tag 01CD (functorial tensor-pullback comparison),
Properties, Tag 01PW, proof (restriction to the affine opens), and Cohomology of
Schemes, Tag 09MR, affine-open paragraph.
(blueprint: lem-sc-tensor-power-section-open-restriction).

Proof: Identify restriction along U.ι with pullback using restrictFunctorIsoPullback.
Pullback is strong monoidal; transport its unit and tensor comparisons to restriction.
Induction on n, starting with the unit comparison, identifies the restriction of
L.tensorPow n with (L.restrict U.ι).tensorPow n. Tensor this comparison with F and
apply restrictAppIso on sections. At the top open, U.ι_image_top identifies its image
with U, giving N n in the indicated direction. The restricted global section sU is
obtained by ordinary restriction of s and the inverse restrictAppIso. The unit
comparison sends the morphism homOfGlobalSection L s to homOfGlobalSection _ sU.
Induction on n in tensorPowSection and coherence with unitors and associators show
that these comparisons identify mulTensorPowSection in every degree. This proves
the first displayed equality. For V, compose restrictAppIso for F with the presheaf
isomorphism induced by hW to get T. Naturality of restrictAppIso identifies the two
restriction maps from U and the top open. The tensor comparison carries
z tensor sU^n to T(z) tensor s^n. By rightUnitor_inv_comp_whiskerLeft_app the latter
is precisely the ambient coefficient map. Apply the injective numerator comparison
on V to the two sides of the restricted equation; naturality gives exactly the
ambient equation. Applying its inverse proves the reverse implication. Every
comparison is an isomorphism, so this argument includes n = 0, zero modules,
zero sections and the empty open without a choice of a generator. -/
theorem exists_tensorPowSection_open_restriction (X : Scheme.{u}) (L F : X.Modules)
    (s : Γ(L, ⊤)) (U : X.Opens) :
    let LU := L.restrict U.ι
    let FU := F.restrict U.ι
    let sU : Γ(LU, ⊤) :=
      (L.restrictAppIso U.ι ⊤).inv (L.presheaf.map (homOfLE le_top).op s)
    ∃ N : ∀ n : ℕ, Γ(F ⊗ L.tensorPow n, U) ≃+ Γ(FU ⊗ LU.tensorPow n, ⊤),
      (∀ (n b : ℕ) (t : Γ(F ⊗ L.tensorPow n, U)),
        N (n + b) ((mulTensorPowSection (homOfGlobalSection L s) F n b).app U t) =
          (mulTensorPowSection (homOfGlobalSection LU sU) FU n b).app ⊤ (N n t)) ∧
      ∀ (V : U.toScheme.Opens) (W : X.Opens) (hW : U.ι ''ᵁ V = W) (hWU : W ≤ U),
        ∃ T : Γ(FU, V) ≃+ Γ(F, W),
          ∀ (n : ℕ) (t : Γ(F ⊗ L.tensorPow n, U)) (z : Γ(FU, V)),
            tmulSection z (tensorPowSectionOne (homOfGlobalSection LU sU) n V) =
                (FU ⊗ LU.tensorPow n).presheaf.map (homOfLE le_top).op (N n t) ↔
              (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
                  F ⟶ (F ⊗ L.tensorPow n : X.Modules)).app W (T z) =
                (F ⊗ L.tensorPow n).presheaf.map (homOfLE hWU).op t := by sorry

end AlgebraicGeometry.Scheme.Modules
