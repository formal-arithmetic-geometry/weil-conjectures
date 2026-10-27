module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Closed immersions among universally closed morphisms

Source: Stacks Project, etale.tex, Tags 04XV (equivalence of (1) and (5)) and 05VH.
(blueprint: lem-sfb-universally-closed-unramified-radicial-criterion)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A universally closed morphism is a closed immersion exactly when it is
unramified and universally injective.

Source: Stacks Project, etale.tex, Tag 04XV, (1) iff (5), and Tag 05VH.
(blueprint: lem-sfb-universally-closed-unramified-radicial-criterion)

Proof:
1. If g is a closed immersion, lem-pc-proper-monomorphism-closed gives properness
and the monomorphism property. By def-weil-proper-morphism and
def-weil-finite-type-morphism, g is locally of finite type. In the fibre product
P = X ×_Y X of def-pc-fibre-product, cancellation gives equality of the two
projections. The first projection and the diagonal are inverse: check their
composites using both projections and the fibre-product universal property.
Thus the diagonal is an isomorphism, hence an open immersion and surjective.
By def-weil-unramified-morphism and the diagonal-surjectivity equivalence of
def-weil-radicial-morphism, g is unramified and universally injective.
2. Conversely, unramifiedness gives local finite type and an open-immersion
diagonal by def-weil-unramified-morphism. Universal injectivity makes the
diagonal surjective by def-weil-radicial-morphism. By def-weil-open-immersion,
a surjective open immersion identifies its source with the entire target,
so the diagonal is an isomorphism.
3. For maps a,b : T → X with equal composites into Y, the induced map
(a,b) : T → P from def-pc-fibre-product factors through the invertible diagonal.
Composing with the projections gives a = b, so g is a monomorphism.
4. By lem-trf-scheme-monomorphism-separated, g is separated. Its assumed
universal closedness gives quasi-compactness by
lem-weil-pbc-universally-closed-quasi-compact. Together with local finite type,
this gives finite type by def-weil-finite-type-morphism, hence properness by
def-weil-proper-morphism. The reverse implication of
lem-pc-proper-monomorphism-closed now gives a closed immersion. -/
theorem IsClosedImmersion.iff_isUnramified_and_universallyInjective
    {X Y : Scheme.{u}} (g : X ⟶ Y) [UniversallyClosed g] :
    IsClosedImmersion g ↔ IsUnramified g ∧ UniversallyInjective g := by
  sorry

end AlgebraicGeometry
