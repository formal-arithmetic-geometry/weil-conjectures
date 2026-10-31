/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.PostnikovAdditiveExactCoupleData
import WeilConjectures.CategoryTheory.PostnikovCanonicalExactCouple
import WeilConjectures.CategoryTheory.PostnikovPageFunctoriality
import WeilConjectures.CategoryTheory.PostnikovSpectralSequence
import WeilConjectures.CategoryTheory.PostnikovStablePages
import WeilConjectures.CategoryTheory.PostnikovNaturalAbutment
import WeilConjectures.CategoryTheory.PostnikovAbutmentTransport

/-! # Additive Postnikov exact couples

The construction combines the canonical tower, additive pages, stabilization and abutment.
-/

@[expose] public section

set_option autoImplicit false

universe u v w uB vB

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]

/-- The canonical Postnikov tower of every derived object gives an additive exact couple,
an E2 spectral sequence, additive stabilized entries, and the natural filtered half-plane
abutment, with all compatibilities preserved by additive natural abutment comparisons.
No boundedness, Grothendieck, injective-resolution or convergence hypothesis is imposed
on the initial tower.

Source: Stacks Project, Homology, Tags 011Q, 011R, 011S, 0AMJ and 012U; Derived Categories,
Tag 08J5 (blueprint: lem-per-postnikov-additive-exact-couple).

Proof:
1. Use the canonical truncation triangle of lem-weil-pbc-truncation-triangle. Its first
arrow commutes with the inclusions into L and its quotient induces identity on H^q.
Reuse postnikovAlpha, postnikovG and postnikovF, and the truncation-layer comparison
normalized by tower.layer_normalized; no second D/E functors or triangle arrows are defined.
Apply lem-sp-long-exact-of-triangle to T after shifts. At total degree p+q the three
exact positions are exactly the three fields of BigradedExactCouple; translating p by
ρ changes none of their degrees. This gives C and its three canonical-map squares.
2. Iterate by lem-sp-derived-couple-exact. The type-r couple has differential of degree
(r+2,-r-1), and its next E term is the cokernel of the incoming differential lifted into
the outgoing kernel. Assemble these complexes and homology isomorphisms into the Mathlib
spectral sequence starting at page two (def-sp-spectral-sequence).
3. The coherent single-functor shift comparisons identify H^q(L)[-q][p+q] with H^q(L)[p].
First use tower.layerIso to pass from the canonical truncation layer to the single-term
embedding. These comparisons are natural, and after T give initialPageIso and its normalization.
4. Apply truncation and cohomology functors to every u. Naturality of the three triangle
arrows gives a couple morphism. The standard truncation, cohomology, single-term and shift
functors are additive by lem-per-derived-standard-functors-additive, so its two components
are additive and preserve identities and composition.
5. Use lem-sp-derived-couple-functoriality inductively. Image restriction, restriction to
cycles, and descent to the page quotient determine the next maps uniquely. Cancel the
target image and kernel monomorphisms, and the source quotient epimorphism, to check sums,
zero, identities and composition. Package their components as the additive functors P.D
and P.E; image_square and homology_square retain their defining equations.
6. When entries stabilize, use a common sufficiently late page for any pair of objects
and any composition. The same kernel and quotient squares identify successive late pages;
uniqueness gives cutoff independence, functoriality and additivity of the stabilized map.
This proves S without assuming arbitrary intersections or unions exist in B.
7. On the full subcategory of objects satisfying postnikovHalfPlane, apply
thm-sp-half-plane-convergence and lem-sp-couple-morphism, allowing distinct lower bounds.
The canonical abutment is D^{0,n}; the alpha squares give cocone_square also at negative
indices, by inversion where the alpha maps are isomorphisms. The theorem gives convergence
and its canonical stable-page/graded identification, characterized by comparison_eq.
8. Restrict the abutment map to each image filtration step and descend to its quotient.
Cancel the target step inclusion and source quotient projection to prove additivity and
functor laws. The same uniqueness gives the natural comparison and its compatibility with
the stabilized page and the initial cycles modulo boundaries. This gives H.
9. For any additive natural comparison η, postcompose the filtration inclusions with η.
Naturality supplies their squares; their images form the transported filtration. Pass to
quotients to obtain e. Bilinearity of composition preserves addition; identities and
composition remain the functor laws of the same step and graded functors. Composing e
with H.comparison preserves the stable-page square. This is H.Transport.
-/
theorem exists_postnikov_additive_exact_couple
    (T : DerivedCategory A ⥤ B) [T.Additive] [T.IsHomological] :
    ∃ C : PostnikovCoupleData T, ∃ P : PostnikovPageData C,
      Nonempty (PostnikovSpectralData P) ∧ Nonempty (PostnikovStableData P) ∧
      ∃ H : PostnikovAbutmentData P, H.Transport := by
  obtain ⟨C⟩ := exists_postnikov_canonical_exact_couple T
  obtain ⟨P⟩ := exists_postnikov_page_data T C
  obtain ⟨H⟩ := exists_postnikov_abutment_data P
  exact ⟨C, P, exists_postnikov_spectral_data P, exists_postnikov_stable_data P,
    H, postnikov_abutment_transport H⟩

end DerivedCategory
