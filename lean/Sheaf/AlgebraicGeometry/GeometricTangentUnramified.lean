module

public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality
import Sheaf.AlgebraicGeometry.RationalUnramifiedCotangentCriterion
import Sheaf.AlgebraicGeometry.UnramifiedLocusBaseChange
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Unramified morphisms detected by geometric fibre tangent spaces

Source: Stacks Project, varieties.tex, Tags 0B2C and 0B2G, and morphisms.tex,
Tags 02G4, 02GF and 0475 (blueprint: lem-sfb-geometric-tangent-unramified).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A locally finite type morphism is unramified exactly when the tangent space at every
rational point of every geometric fibre vanishes; equivalently, every relative dual-number
lift of such a point is the constant lift. No flatness or Noetherian assumption is made.
Source: Stacks Project, varieties.tex, Tags 0B2C, 0B2E, 0B2F and 0B2G; morphisms.tex,
Tags 02G4, 02GF and 0475 (blueprint: lem-sfb-geometric-tangent-unramified).

Proof plan:
1. An Omega-point of an Omega-scheme has residue field Omega: the two field maps whose
composite is the identity are inverse isomorphisms. It is closed, since on every affine
neighbourhood the corresponding algebra map to Omega is surjective, with maximal kernel.
2. Apply `lem-sc-rational-tangent-cotangent-duality` to the structure morphism of a locally
finite type Omega-scheme at this point. Its tangent map has zero target and is dual to
its cotangent map from zero. By `lem-sc-dual-map-injective-iff-surjective`, its injectivity
is equivalent to cotangent surjectivity. By `lem-sc-rational-unramified-cotangent-criterion`,
this is equivalent to being unramified at the point. Thus tangent vanishing is equivalent
to unramifiedness there.
3. If f is unramified, its unramified locus is all of X. By
`lem-trf-unramified-locus-base-change`, the unramified locus in each geometric fibre is the
whole fibre. The fibre morphism is locally of finite type by `lem-weil-pbc-lft-base-change`.
Step 2 proves the asserted vanishing at each Omega-point.
4. Conversely, for any z in X take an algebraic closure Omega of its residue field
(`def-weil-algebraic-closure`). The induced map a : Spec Omega to X, composed with f,
is a geometric point of S. The pair (a, identity) gives an Omega-point of the pullback
lying over z. This geometric point is allowed even when Omega is transcendental over
the residue field of f(z).
5. By Step 2 the vanishing hypothesis makes the fibre unramified at this lifted point.
The base-change equality of `lem-trf-unramified-locus-base-change` puts z in the unramified
locus of f. As z was arbitrary, unramified source neighbourhoods cover X; the affine-local
definition in `def-weil-unramified-morphism` then makes f unramified globally.
6. At an Omega-point, the residue field is Omega by Step 1, so the recorded tangent vectors
are precisely the relative Omega dual-number lifts of that point. The zero vector is the
constant map: scalar zero precomposes with epsilon sent to zero, which factors through
Spec Omega and the given point. A vector space is zero exactly when all its elements are
zero. The two characterizations therefore agree. Empty fibres have no Omega-points, so
their conditions are vacuous; the empty source is also unramified. -/
theorem unramified_iff_geometricFiber_tangentSpace_zero
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] :
    (IsUnramified f ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
        (x : Spec (.of Ω) ⟶ pullback f s),
        x ≫ pullback.snd f s = 𝟙 (Spec (.of Ω)) →
          Subsingleton (schemeTangentSpace Ω (pullback f s) (pullback.snd f s)
            (x (IsLocalRing.closedPoint Ω)))) ∧
    (IsUnramified f ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
        (x : Spec (.of Ω) ⟶ pullback f s),
        x ≫ pullback.snd f s = 𝟙 (Spec (.of Ω)) →
          ∀ θ : Spec (.of (DualNumber Ω)) ⟶ pullback f s,
            θ ≫ pullback.snd f s =
                Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom Ω Ω)) →
            Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom) ≫ θ = x →
              θ = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom Ω Ω)) ≫ x) := by
  sorry

end AlgebraicGeometry
