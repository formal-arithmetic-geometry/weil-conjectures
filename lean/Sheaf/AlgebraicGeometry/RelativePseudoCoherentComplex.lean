module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Sheaf.AlgebraicGeometry.MPseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage

/-! # Relative pseudo-coherence of complexes

Source: Stacks Project, More on Morphisms, Tag 09UI, clauses (1) and (2), with the
existential embedding condition of Tag 09VC
(blueprint: def-sfb-relative-pseudo-coherent-complex).

The affine coverings are expressed by affine neighbourhoods of every base point and
then every source point over that neighbourhood. The embeddings are over the base open.

## Main definitions

* `Scheme.IsMPseudoCoherentRelativeTo`: relative pseudo-coherence in an integer degree.
* `Scheme.IsPseudoCoherentRelativeTo`: relative pseudo-coherence in every integer degree.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A derived object is `m`-pseudo-coherent relative to a locally finite type morphism
if affine opens cover the base and, over each, affine opens cover its preimage, with
closed embeddings into finite affine space whose derived direct images of the restricted
object are `m`-pseudo-coherent. Neighbourhood quantifiers express these two open covers.
Source: Stacks Project, More on Morphisms, Tag 09UI (1), using the existential condition
in Tag 09VC (blueprint: def-sfb-relative-pseudo-coherent-complex). -/
def IsMPseudoCoherentRelativeTo
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (m : ℤ) (E : schemeDerivedCategory X) : Prop :=
  ∀ s : S, ∃ V : S.Opens, IsAffineOpen V ∧ s ∈ V ∧
    ∀ x : X, f x ∈ V → ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∃ hUV : U ≤ f ⁻¹ᵁ V, ∃ n : ℕ,
        ∃ i : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.toScheme,
          IsClosedImmersion i ∧
          i ≫ (AffineSpace (ULift.{u} (Fin n)) V.toScheme ↘ V.toScheme) =
            f.resLE V U hUV ∧
          IsMPseudoCoherent (AffineSpace (ULift.{u} (Fin n)) V.toScheme) m
            ((schemeDerivedDirectImage i).obj ((derivedPullback U.ι).obj E))

/-- A derived object is pseudo-coherent relative to the base if it is relatively
`m`-pseudo-coherent for every integer `m`. Each degree has its own existential affine
covers, dimensions and embeddings; no uniform choices are required.
Source: Stacks Project, More on Morphisms, Tag 09UI (2)
(blueprint: def-sfb-relative-pseudo-coherent-complex). -/
def IsPseudoCoherentRelativeTo
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (E : schemeDerivedCategory X) : Prop :=
  ∀ m : ℤ, IsMPseudoCoherentRelativeTo f m E

end AlgebraicGeometry.Scheme
