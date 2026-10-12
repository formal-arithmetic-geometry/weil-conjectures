/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-!
# Restriction and tensor products of modules

Source: Stacks Project, Modules, Lemma 01CD.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction along an open immersion commutes with the sheaf tensor product, compatibly
with the canonical pure tensor sections. Source: Stacks Project, Modules, Lemma 01CD,
label lemma-tensor-product-pullback
(blueprint: lem-weil-pbc-module-restriction-tensor-comparison).

Proof: write the tensor product as sheafification of the sectionwise tensor presheaf.
Restriction of that presheaf is the tensor presheaf of the restrictions: the structure-ring
isomorphism on each open identifies the balanced tensor products. Restriction commutes with
sheafification by the restriction/direct-image adjunction: for every module sheaf H on the
source, Hom((P^#)|Y,H) = Hom(P^#,j_*H) = Hom(P,j_*H) = Hom(P|Y,H). The middle equality is
the sheafification adjunction and j_*H is a sheaf. Uniqueness of the representing object gives
the comparison isomorphism. These adjunction identifications preserve the sheafification
unit. Its component sends s tensor t to tmulSection s t, which proves the displayed formula
on every open, after applying the canonical restriction section isomorphisms. -/
theorem exists_restriction_tensor_comparison {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (F G : X.Modules) :
    ∃ e : (F ⊗ G).restrict j ≅ F.restrict j ⊗ G.restrict j,
      ∀ (V : Y.Opens) (s : Γ(F.restrict j, V)) (t : Γ(G.restrict j, V)),
        ((F ⊗ G).restrictAppIso j V).hom (e.inv.app V (tmulSection s t)) =
          tmulSection ((F.restrictAppIso j V).hom s) ((G.restrictAppIso j V).hom t) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
