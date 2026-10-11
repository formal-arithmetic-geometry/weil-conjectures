/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-!
# Tensor products of quasi-coherent modules on affine opens

Source: Stacks Project, Schemes, Lemma 01I8 and Section 01LA; Modules, Lemma 01CE
(blueprint: lem-weil-pbc-quasi-coherent-tensor-product-affine-sections).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- The tensor product of quasi-coherent modules is quasi-coherent, and its canonical
section map on every affine open is bijective. Source: Stacks Project, Schemes, Lemma 01I8(1)
and Section 01LA(1),(2),(8); Modules, Lemma 01CE(3)
(blueprint: lem-weil-pbc-quasi-coherent-tensor-product-affine-sections).

Proof:
1. Fix an affine open `U`, put `R = Γ(X, U)`, and use its canonical affine chart.
   Restriction preserves quasi-coherence. The affine tilde/global-sections equivalence
   identifies the restrictions of `F` and `G` with the tilde sheaves of their sections
   (`lem-weil-pbc-module-restriction-open-immersion-colimits`,
   `lem-weil-pbc-affine-tilde-gamma-adjunction`, `lem-weil-pbc-spec-module-tilde-sections`).
2. The sectionwise tensor presheaf restricts to the tensor presheaf on `U`. For the open
   immersion `j : U ⟶ X`, its tensor presheaf `P`, and any module sheaf `H` on `U`, identify
   Hom((Pᵟ)|U, H) with Hom(Pᵟ, j_*H), then Hom(P, j_*H), then Hom(P|U, H).
   Here `Pᵟ` denotes sheafification. The outer identifications use the restriction/direct-
   image adjunction (`lem-weil-pbc-module-restriction-open-immersion-colimits`); the middle
   uses sheafification (`def-weil-presheaf-modules-sheafification`). Direct image is a sheaf
   (`lem-weil-pbc-site-continuous-pushforward-sheaf`, `def-weil-pbc-direct-image`). Thus
   restriction commutes with sheafification and with the sheaf tensor product
   (`def-pur-sheaf-tensor-product`). Apply `lem-weil-pbc-affine-tilde-tensor` to identify this
   restriction with the tilde sheaf of `Γ(F, U) ⊗[R] Γ(G, U)`. Track pure tensors through
   the comparison: the original sheafification component sends `s ⊗ t` to
   `tmulSection s t` (`tensorSectionsMap_tmul`), so its map on sections is exactly
   `tensorSectionsMap F G U` and is bijective.
3. Every point has an affine open neighbourhood (`def-pc-scheme`). Step 2 identifies the
   tensor product there with a tilde module. The affine-local criterion (`pqf-def-coherent`)
   gives quasi-coherence; Step 2 already gives the second clause for every affine open.
-/
theorem quasiCoherent_tensor_product_affine_sections {X : Scheme.{u}} (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (tensorObj F G).IsQuasicoherent ∧
      ∀ (U : X.Opens), IsAffineOpen U → Function.Bijective (tensorSectionsMap F G U) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
