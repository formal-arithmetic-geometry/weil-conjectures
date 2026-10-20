/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.CategoryTheory.Sites.CoherentTopos
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Sheaf.CategoryTheory.Sites.CoherentToposRepair

/-!
# Coherence of an epimorphic quotient with quasi-compact kernel pair

Source: literature/stacks-project/sites.tex, Tags 0GMP, 00WN, 00W2
(blueprint: lem-trf-coherent-epimorphic-quotient).
-/

set_option autoImplicit false

@[expose] public section

universe w u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- An epimorphic quotient of a coherent object with quasi-compact kernel pair is coherent.
Source: literature/stacks-project/sites.tex, Tags 0GMP, 00WN, 00W2; ILO XI, Lemma 2.5,
printed p. 179 (blueprint: lem-trf-coherent-epimorphic-quotient).

Proof:
1. Present the topos on a small site using `def-trf-coherent-topos`. By
   `lem-weil-pbc-site-sheaf-sets-epi-locally-surjective`, epimorphisms are locally
   surjective. Sectionwise pullbacks (`lem-weil-pbc-site-sheaf-sets-limits-sectionwise`)
   then show that epimorphisms are stable under pullback. By the adjunction of
   `def-weil-pbc-sheafification`, a coproduct of sheaves is the sheafification of the
   presheaf coproduct. Its sections locally belong to a summand by
   `lem-weil-pbc-site-sheafification-sections-local`. Thus jointly epimorphic families
   are exactly locally lifting families, and are stable under pullback.
2. An epimorphic image of a quasi-compact object is quasi-compact: pull a jointly
   epimorphic family back to the domain, choose finitely many members, and cancel the
   epimorphism to show that the selected family covers the codomain. Finite coproducts
   of quasi-compact objects are quasi-compact: pull a covering family back to each
   summand and take the union of the finite selections. The empty coproduct is also
   quasi-compact since any two morphisms from the initial object agree.
3. Fix the small coherent generating family from `def-trf-coherent-topos`. Every
   quasi-compact object has a finite jointly epimorphic family of these generators:
   select finitely many members of its generating epimorphism. Moreover, for an
   epimorphism onto a quasi-compact object, compose a generating family of its domain
   with that epimorphism and select finitely many composites. These finitely many
   generator maps to the codomain retain their lifts to the domain. The family may
   be empty, and its index sets lie in the universe of `def-weil-size-convention`.
4. The quasi-compactness of P and step 2 imply that A is quasi-compact. For arbitrary
   quasi-compact B and C over A, step 3 supplies finite generator covers G_i of B and
   H_j of C. Successive pullbacks make the finite family G_i ×_A H_j cover B ×_A C.
   By step 2 it suffices to show each of these pullbacks is quasi-compact.
5. Fix G and H from step 4. The epimorphisms P ×_A G → G and P ×_A H → H admit finite
   generator covers K_a → G and L_b → H with lifts k_a : K_a → P and l_b : L_b → P,
   by step 3. Pullback stability makes K_a ×_A L_b → G ×_A H a finite covering family.
6. Put R = P ×_A P, with projections r_1 and r_2. The universal property gives
   K_a ×_A L_b ≅ (K_a ×_{k_a,P,r_1} R) ×_{r_2,P,l_b} L_b. Sectionwise, a pair (x,y)
   belongs to either side exactly when p(k_a(x)) = p(l_b(y)); its R-component must
   be (k_a(x),l_b(y)). This identification is natural by sectionwise limits. The
   objects K_a, R, L_b are quasi-compact, so the quasi-separatedness of P first makes
   K_a ×_P R quasi-compact and then makes its pullback with L_b over P quasi-compact.
   Step 2 transports quasi-compactness across the displayed isomorphism.
7. Step 2 now makes G ×_A H quasi-compact using the cover in step 5, and then makes
   B ×_A C quasi-compact using step 4. This is exactly quasi-separatedness of A in
   `def-trf-coherent-topos`. Together with step 4 it proves coherence of A. Step 2
   includes empty finite covers, so no nonemptiness hypothesis is needed.
-/
theorem coherent_of_epi_of_quasiCompact_kernelPair
    {E : Type u} [Category.{v} E] [HasCoproducts.{w} E] [HasFiniteLimits E]
    (hE : IsCoherentTopos.{w} E) {P A : E} (p : P ⟶ A) [Epi p]
    (hP : IsCoherentObject.{w} P)
    (hR : IsQuasiCompactObject.{w} (pullback p p)) :
    IsCoherentObject.{w} A := by
  sorry

end CategoryTheory
