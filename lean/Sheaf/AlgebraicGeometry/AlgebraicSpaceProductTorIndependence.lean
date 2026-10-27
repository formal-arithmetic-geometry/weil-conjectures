module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceTorIndependenceEtaleChart
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Monoidal.Tor
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest

/-! # Tor independence for an algebraic-space product square

Source: Stacks Project, More on Morphisms of Spaces, Tag 0CTQ,
lemma-case-of-tor-independence
(blueprint: lem-sfb-space-product-tor-independence).

We use the canonical identification `(X₀ ×_{B₀} B) ×_B (Y₀ ×_{B₀} B) =
(X₀ ×_{B₀} Y₀) ×_{B₀} B`, up to the unique projection-preserving isomorphism.
The two `IsPullback` witnesses allow arbitrary choices of the indicated products.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a commutative square with Y₀ → B₀ and Z₀ → X₀ flat on étale charts,
Z₀ and the arbitrary base change of X₀ ×_{B₀} Y₀ are geometrically Tor independent
over X₀ ×_{B₀} Y₀. The map from Z₀ is the canonical pullback lift.
Here P is P₀ ×_{B₀} B, canonically the product of the two base-changed factors over B.
Source: Stacks Project, More on Morphisms of Spaces, Tag 0CTQ
(blueprint: lem-sfb-space-product-tor-independence).

Proof: (1) Choose surjective étale scheme atlases W₀ → B₀, W → B ×_{B₀} W₀,
U₀ → X₀ ×_{B₀} W₀ and V₀ → Y₀ ×_{B₀} W₀. Put Q₀ = U₀ ×_{W₀} V₀
and choose T₀ → Z₀ ×_{P₀} Q₀ surjective étale. Fibre-product identities show that
Q₀ → P₀ and T₀ → Z₀ ×_{X₀} U₀ are surjective étale
[lem-trf-space-fibre-products-etale-covers, lem-trf-space-chartwise-etale-permanence].
(2) The arbitrary-chart criterion gives flatness of V₀ → W₀ and T₀ → U₀
[lem-sfb-space-local-properties-chart-test]. Base change makes Q₀ → U₀ flat
[lem-weil-pbc-flat-morphism-base-change]. No flatness of T₀ → Q₀ is used.
(3) Set A = U₀ ×_{W₀} W and Q = Q₀ ×_{W₀} W. The flat-family theorem over
U₀, applied to T₀ → Q₀ and A → U₀, gives ordinary local-ring Tor vanishing
for T₀ and Q over Q₀ [lem-sfb-flat-families-tor-independent].
(4) The projection-preserving product identities identify P with the product of the
base changes of X₀ and Y₀, and Q with an étale atlas of P ×_{P₀} Q₀.
The geometric Tor-independence chart criterion, applied to Q₀, T₀, Q, gives the
asserted vanishing of every positive Tor group at every compatible geometric pair
[lem-sfb-space-tor-independence-etale-chart-criterion]. -/
theorem product_torIndependent {S : Scheme.{u}}
    {Z₀ X₀ Y₀ B₀ B P₀ P : AlgebraicSpace S}
    (zX : Z₀ ⟶ X₀) (zY : Z₀ ⟶ Y₀) (f : X₀ ⟶ B₀) (g : Y₀ ⟶ B₀)
    (comm : zX ≫ f = zY ≫ g) (a : B ⟶ B₀)
    (r : P₀ ⟶ X₀) (s : P₀ ⟶ Y₀)
    (hP₀ : IsPullback r.hom s.hom f.hom g.hom)
    (p : P ⟶ P₀) (b : P ⟶ B)
    (hP : IsPullback p.hom b.hom (r ≫ f).hom a.hom)
    (hg : MapIsFlat g) (hzX : MapIsFlat zX) :
    IsGeometricallyTorIndependent
      (ObjectProperty.homMk
        (hP₀.lift zX.hom zY.hom (congrArg InducedCategory.Hom.hom comm))) p := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
