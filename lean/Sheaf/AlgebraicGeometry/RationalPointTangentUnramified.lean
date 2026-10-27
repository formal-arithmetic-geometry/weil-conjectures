module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
import Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality
import Mathlib.LinearAlgebra.Dual.Lemmas
import Sheaf.AlgebraicGeometry.RationalUnramifiedCotangentCriterion

/-! # Rational-point tangent criterion for unramifiedness

Source: Stacks Project, Varieties, Tag 0B2G; Schemes, Tag 01J9;
Morphisms, Tag 01TE (blueprint: lem-sfb-rational-point-tangent-unramified).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A rational section point is closed, its structural residue-field map is an
isomorphism with inverse induced by the section, and unramifiedness on a neighbourhood
is equivalent to vanishing of its relative tangent space. Vanishing is expressed by
`Subsingleton` on the recorded tangent vector space, so it means every vector is zero.
Source: Stacks Project, Varieties, Tag 0B2G; Schemes, Tag 01J9; Morphisms, Tag 01TE
(blueprint: lem-sfb-rational-point-tangent-unramified).

Proof for stage 3:
1. Write `w = x (IsLocalRing.closedPoint k)`. The structural map `r : k → κ(w)`
   and the section-induced map `c : κ(w) → k` satisfy `c ∘ r = id` by the section
   identity and lem-weil-pbc-scheme-stalk-map-composition, after passing to residues
   (def-weil-residue-field). The field map `c` is injective, so
   `c (r (c a)) = c a` implies `r (c a) = a`. Thus `r` and `c` are inverse.
2. Apply lem-trf-finite-residue-tower-local-geometry with `C = D = Z`, first arrow
   `p`, second arrow the identity and both points `w`. The first residue extension
   is the isomorphism of step 1 and the second is the identity; both have degree one.
   Both arrows are locally of finite type (def-weil-finite-type-morphism), so `w`
   is closed. This is precisely Stacks Tag 01TE(2) over the closed point of `Spec k`.
3. By lem-sc-rational-tangent-cotangent-duality, the differential of `p` at `w`
   is dual to `0 → m_w/m_w²`, since the target local ring is `k`. Its target tangent
   space is zero, so the differential is injective exactly when the source tangent
   space vanishes. By lem-sc-dual-map-injective-iff-surjective this is equivalent
   to cotangent surjectivity. Both points are closed, their residue fields are `k`,
   and `p` is locally of finite type. Hence lem-sc-rational-unramified-cotangent-criterion
   identifies cotangent surjectivity with unramifiedness on an open neighbourhood.
-/
theorem rationalPoint_tangent_unramified
    (k : Type u) [Field k] (Z : Scheme.{u}) (p : Z ⟶ Spec (.of k))
    [LocallyOfFiniteType p] (x : Spec (.of k) ⟶ Z) (hx : x ≫ p = 𝟙 _) :
    IsClosed ({x (IsLocalRing.closedPoint k)} : Set Z) ∧
      (∃ e : k ≃+* Z.residueField (x (IsLocalRing.closedPoint k)),
        e.toRingHom =
          (StructureSheaf.toStalk k (p (x (IsLocalRing.closedPoint k))) ≫
            p.stalkMap (x (IsLocalRing.closedPoint k)) ≫
            Z.residue (x (IsLocalRing.closedPoint k))).hom ∧
        e.symm.toRingHom = (Z.descResidueField (Scheme.stalkClosedPointTo x)).hom) ∧
      ((∃ U : Z.Opens, x (IsLocalRing.closedPoint k) ∈ U ∧ IsUnramified (U.ι ≫ p)) ↔
        Subsingleton (schemeTangentSpace k Z p (x (IsLocalRing.closedPoint k)))) := by
  sorry

end AlgebraicGeometry
