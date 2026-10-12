/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkMaps
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.Topology.PresheafModuleStalkFunctor

/-! # Short exact Mayer--Vietoris sequence for extension by zero

Source: Stacks Project, Cohomology, Tag 08BU, the short exact sequence in the proof
(blueprint: lem-sc-derived-open-mayer-vietoris-ses).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- For a two-open cover, extension by zero gives the short exact Mayer--Vietoris
sequence. The comparison maps `iU`, `iV` are specified by their composites with the
counits: both composites are the counit on the intersection. Since the counit of
extension by zero is monic, these equations uniquely specify the canonical maps.
The different adjunctions are chosen from `open_restriction_adjunction_exact`.

Source: Stacks Project, Cohomology, Tag 08BU, proof
(blueprint: lem-sc-derived-open-mayer-vietoris-ses).

Proof:
1. Use the canonical extension-by-zero maps of
   `lem-sc-module-extension-by-zero-stalk-maps`. Their composites with the counits
   are the overlap counit by transitivity. The first differential is `(iU, -iV)`
   and the second is the sum of the two counits, so their composite is zero.
2. By that same stalk-map lemma and `def-weil-pbc-module-stalk`, on the overlap
   the sequence is `0 → F_x → F_x ⊕ F_x → F_x → 0`, with diagonal difference and
   addition. On either open minus the other it is `0 → 0 → F_x → F_x → 0`, with
   identity differential. These module sequences are short exact. There are no
   points outside the union, by the covering hypothesis.
3. Apply `lem-weil-pbc-module-stalk-exact` to obtain sheaf exactness. Exactness at
   the two ends gives the mono and epi conditions of `def-weil-pbc-exact-sequence`,
   namely `ShortComplex.ShortExact`. -/
theorem open_extension_mayer_vietoris_shortExact
    (X : RingedSpace.{u}) (U V : Opens X) (hcover : U ⊔ V = ⊤)
    (F : SheafOfModules.{u} (moduleRings X)) :
    ∃ (iU : ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) (U ⊓ V) ⋙
          PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
            ((SheafOfModules.overFunctor.{u} (moduleRings X) (U ⊓ V)).obj F)) ⟶
        ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
          PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
            ((SheafOfModules.overFunctor.{u} (moduleRings X) U).obj F)))
      (iV : ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) (U ⊓ V) ⋙
          PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
            ((SheafOfModules.overFunctor.{u} (moduleRings X) (U ⊓ V)).obj F)) ⟶
        ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) V ⋙
          PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
            ((SheafOfModules.overFunctor.{u} (moduleRings X) V).obj F))),
      iU ≫ ((Classical.choice
          (open_restriction_adjunction_exact X U).2.2.2.2).counit.app F) =
        ((Classical.choice
          (open_restriction_adjunction_exact X (U ⊓ V)).2.2.2.2).counit.app F) ∧
      iV ≫ ((Classical.choice
          (open_restriction_adjunction_exact X V).2.2.2.2).counit.app F) =
        ((Classical.choice
          (open_restriction_adjunction_exact X (U ⊓ V)).2.2.2.2).counit.app F) ∧
      ∃ (hzero : biprod.lift iU (-iV) ≫
        biprod.desc ((Classical.choice
          (open_restriction_adjunction_exact X U).2.2.2.2).counit.app F)
          ((Classical.choice
          (open_restriction_adjunction_exact X V).2.2.2.2).counit.app F) = 0),
        (ShortComplex.mk (biprod.lift iU (-iV))
          (biprod.desc ((Classical.choice
          (open_restriction_adjunction_exact X U).2.2.2.2).counit.app F)
            ((Classical.choice
          (open_restriction_adjunction_exact X V).2.2.2.2).counit.app F)) hzero).ShortExact := by
  sorry

end AlgebraicGeometry
