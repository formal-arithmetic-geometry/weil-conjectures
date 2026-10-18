/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.EssentiallySmall
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.Paper.LatticeSheafBasic
import Sheaf.Paper.CoefficientHeartCommonStratification
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
import Sheaf.Paper.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# Essential smallness of the constructible coefficient heart

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-coefficient-heart,
`sk-lem-coefficient-heart-small.md` and its proof
(blueprint: det-lem-coefficient-heart-small).

The coefficient is the actual condensed ring pulled back from the point. The full
constructible category uses finite constant scalar models. This reopened stage-2
record retains the same canonical statement and proof interface. The smallness universe is
`u + 1`, containing the bounded schemes, the pro-etale site, and coefficient sections;
the ambient category of sheaves can have object universe `u + 2`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The constructible heart for a finite subextension E of Qbar_l, or for Qbar_l itself,
has a set of isomorphism classes in the fixed larger universe.
Source: blueprint sk-lem-coefficient-heart-small and its proof, with the nine-step
DAG refinement (blueprint: det-lem-coefficient-heart-small).

Proof plan:
1. Use def-weil-pbc-internal-abelian-sheaf-module-equivalence, with the monoidal
sheafification of sk-def-sfb-sheaf-tensor, to work with sectionwise modules without
changing the pulled-back coefficient ring, sections, or restriction maps.
2. By def-weil-size-convention the bounded schemes and morphisms form a set in the
larger universe. Finite lists of locally closed immersions over X form a set; select
those with disjoint constructible images covering X (def-constructible-stratification).
3. The scalar ring of either condensed coefficient is the corresponding field, by
def-sfb-padic-subfield-condensed-ring and sk-def-sfb-qlbar-condensed. A finitely
presented scalar module has finitely many generators (def-sfb-finitely-presented-module).
Choose a basis by lem-weil-pbc-vector-space-free. The union of the finite supports of
these generators is finite and spans; independence shows that it is the whole basis.
Thus the scalar module is free of some finite rank, including rank zero.
4. Local Noetherianity gives quasi-separatedness
(lem-weil-pbc-locally-noetherian-quasi-separated). Together with quasi-compactness,
sk-def-sfb-constructible gives a finite adapted stratification. Sheafify coordinate
maps (def-weil-pbc-sheafification), then use lem-weil-pbc-lattice-free-scalar-extension
to identify each scalar model with a finite free coefficient sheaf. Refinement preserves
this by det-lem-coefficient-heart-common-stratification (2).
5. For a site object U over a stratum S, lem-weil-proetale-weakly-etale-localization (1)
identifies U_proet with the slice S_proet/U. In the indexing category for inverse image
(def-weil-proetale-inverse-image), (T,id) is initial, so the opposite colimit is M(T).
Slice coverings are unchanged, so this is already a sheaf. The same calculation applies
to the ring and its action. sk-prop-sfb-cartesian-coefficients therefore identifies a
trivialization with the original finite free section modules over every T over U.
6. On a fixed small site choose a trivializing cover, removing repeated objects. Its
indices form a subset of the site objects; the cover need not be finite. Record its
ranks and the mutually inverse transition matrices on overlaps, with the cocycle on
triple overlaps and identity only after restriction to the diagonal of a self-overlap.
These data form a set of codes. Different ranks and empty overlaps are allowed.
7. For a code c, define its model on V as the compatible families of sections in the
free modules on V times_S U_i, with componentwise restrictions and scalar action.
The coefficient sheaf axiom glues these families uniquely
(def-weil-pbc-sites-and-cohomology). The sheaf axiom on the pulled-back cover identifies
any sheaf producing c with this explicit model (def-weil-sheaf-of-modules-category).
8. Fix the finitely many stratum models L_a and put H = product_a a_* L_a.
The adjunction units (sk-def-sfb-module-pushforward-pullback) and the chosen restriction
isomorphisms give F to H. Its kernel restricts to zero on every stratum: exact pullback
(sk-prop-sfb-cartesian-coefficients) and the triangle identity show this. Detection on
strata (det-lem-coefficient-heart-common-stratification (3)) makes the kernel zero.
Thus F embeds in this fixed H.
9. Subsheaves of H are determined by subsets of its sections at each site object,
with inherited operations and restrictions (def-weil-sheaf-of-modules-category). They
form a subset of a product of power sets, hence a set in the larger universe. Take the
union over the set of stratifications and finite tuples of codes, retain constructible
models, and quotient by isomorphism. This gives the required set of representatives.
For empty X the stratum detection gives F = 0; empty strata and rank zero are allowed. -/
theorem coefficientHeart_essentiallySmall (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ)]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X] :
    EssentiallySmall.{u + 1}
      (ConstantModelConstructible
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ) X) := by
  sorry

end AlgebraicGeometry.ProEtale
