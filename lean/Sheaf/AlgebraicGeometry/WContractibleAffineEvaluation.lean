/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.RingTheory.IndPrincipalZariski
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtale
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.Sites.WContractibleCoverSection

/-!
# Evaluation at a w-contractible affine pro-etale object

Source: Stacks Project, Tags 0981, 098F and 098H, with the small-site adaptation
in the DAG proof; Sites, Tags 090K and 090L
(blueprint: lem-weil-pbc-wcontractible-affine-weakly-contractible).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- Evaluation at `Spec A` sends every epimorphism of sheaves of sets on the full small
pro-etale site to a surjection, provided every faithfully flat weakly etale ring map
out of `A` has a ring retraction.

Source: Stacks Project, Tags 0981 and 098H, implication (1) to (2), adapted to the
small site over `X`; Sites, Tags 090K and 090L.
(blueprint: lem-weil-pbc-wcontractible-affine-weakly-contractible).

Proof plan:
1. By `lem-weil-pbc-site-sheaf-sets-epi-locally-surjective`, a section of `G` over
   `Spec A` lifts to `F` on some covering family `T_i → Spec A`.
2. Apply `lem-weil-pbc-wcontractible-cover-section` to this underlying scheme cover,
   obtaining a section `Spec A → ∐ T_i` of its structural morphism.
3. Pull back the disjoint clopen coproduct components along this section.
   Quasi-compactness of `Spec A` leaves finitely many disjoint clopens covering it.
   The inclusions are weakly etale (flat with flat diagonal); composition makes
   them objects of the same small site. They form a pro-etale cover, as seen on
   finite affine refinements over each affine test open. This uses the coproduct,
   prime-spectrum compactness, flatness and weakly-etale stability nodes in the DAG.
4. Restrict the local lifts to these clopens. Naturality identifies their images
   with the given section. They agree on empty intersections, since the empty
   covering forces a unique section of each sheaf there. Glue by the sheaf axiom;
   separatedness identifies its image with the original section. The same empty
   covering argument handles the zero ring. -/
theorem surjective_app_of_affine_ring_retractions
    (X : Scheme.{u}) (A : Type u) [CommRing A]
    (f : Spec (CommRingCat.of A) ⟶ X) [WeaklyEtale f]
    (hA : ∀ (B : Type u) [CommRing B] (φ : A →+* B),
      φ.FaithfullyFlat → φ.WeaklyEtale →
        ∃ r : B →+* A, r.comp φ = RingHom.id A)
    (F G : Sheaf (topology X) (Type (max (u + 1) v)))
    (α : F ⟶ G) [Epi α] :
    Function.Surjective (α.hom.app (op (ProEt.mk f))) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
