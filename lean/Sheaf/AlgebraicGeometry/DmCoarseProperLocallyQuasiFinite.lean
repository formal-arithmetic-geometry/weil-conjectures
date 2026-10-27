module

public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.FiniteStackSchemeTests
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite

/-! # Proper and locally quasi-finite DM coarse morphisms

Source: Stacks Project, Tag 0DUT (Keel--Mori), with Tags 06U9, 06PU and 0CL5
(blueprint: lem-sfb-dm-coarse-proper-locally-quasifinite).

This is the finite-diagonal DM consequence of Keel--Mori. No tameness or linear
reductivity of stabilizers is assumed. Properness and local quasi-finiteness are
properties of the stack morphism; the coarse map need not be representable.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicGeometry

/-- The coarse morphism of a finite-type DM stack with finite diagonal is proper
and locally quasi-finite, with no restriction on stabilizer reductivity.
Source: Stacks, Tags 0DUT, 06U9, 06PU and 0CL5
(blueprint: lem-sfb-dm-coarse-proper-locally-quasifinite).

Proof:
1. The automorphism sheaf of x over T is the base change of the absolute diagonal
along (x,x). Thus the finite-diagonal hypothesis makes inertia finite on every
scheme test (def-sfb-stable-pointed-moduli-groupoids and
def-weil-finite-integral-morphism).
2. Apply lem-sfb-keel-mori-finite-inertia-quotient over Spec k. It supplies a
categorical quotient p to an algebraic space M, separated, quasi-compact, and a
universal homeomorphism, without a reductivity hypothesis.
3. Coarse initiality gives Q → M factoring p through q; categorical initiality
gives M → Q factoring q through p. Uniqueness makes both composites identities.
Transfer separatedness, quasi-compactness and universal homeomorphism to q.
4. Choose the finite-type atlas U of X. The composite U → Q → Spec k is locally
of finite type. lemma-nagata-finite-type-to-separated-target, clause (a), makes
U → Q locally of finite type, without separatedness of Q. Together with the
quasi-compactness from step 3 this gives finite type of q.
5. Every base change of q is a homeomorphism on points, hence closed. Together
with finite type and proper relative diagonal this is properness (Tag 0CL5).
6. Over a scheme with two objects of X having equal images in Q, Isom over Q
equals Isom over k because Q is discrete. The relative diagonal is therefore
finite on scheme tests. Apply pqf-lem-finite-qf and pqf-lem-qf-locqf-qc to get
the recorded local quasi-finiteness of that diagonal.
7. For every field K and Spec K → Q, the universal homeomorphism identifies the
point space of the fibre with the singleton |Spec K|. It is discrete. Combining
this with steps 4 and 6 is exactly Tag 06PU, including non-algebraically closed K.
For the empty stack initiality forces Q empty and the fibre tests are vacuous. -/
theorem dmCoarseProperLocallyQuasiFinite (k : Type u) [Field k]
    (X : BasedCategory.{v, w} (Over (Spec (.of k))))
    (hX : IsDeligneMumfordModuliStack X) (hft : HasFiniteTypeEtaleModuliAtlas X)
    (hdiag : HasFiniteModuliDiagonal X)
    (Q : Over (Spec (.of k))) (q : BasedFunctor X (discreteModuli (yoneda.obj Q)))
    (hq : IsCoarseModuliScheme X Q q) :
    IsProperModuliMap q ∧ IsLocallyQuasiFiniteModuliMap q := by
  sorry

end AlgebraicGeometry
