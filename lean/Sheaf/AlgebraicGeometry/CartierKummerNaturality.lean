/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.CartierKummerData

/-! # Functoriality of the normalized Cartier realization

Source: blueprint main-20261015, lem-amb-cartier-kummer-map.proof.md,
final paragraph, and the expanded proof steps 7, 12 and 13.
(blueprint: lem-amb-cartier-kummer-naturality)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor ChangeOfRings
namespace AlgebraicGeometry.Etale
open Scheme
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Realization of the ordinary relative boundaries preserves arbitrary finite
coefficient reduction and every Cartier-preserving scheme pullback.

Source: blueprint main-20261015, lem-amb-cartier-kummer-map.proof.md, final paragraph;
expanded proof steps 7, 12 and 13 (blueprint: lem-amb-cartier-kummer-naturality).

Proof: First work at a common annihilating exponent for two coefficient levels.
The source supported constant and the finite root line are flat over the
initial residue ring, as seen on geometric stalks and a root-trivializing cover.
Their scalar extensions are the corresponding supported constant and root line
over each quotient coefficient. On K-flat resolutions tensor associativity
identifies successive extension with direct extension. The scalar units send
a constant b to its quotient image and a root tensor b tensor z to its quotient
tensor z. Relative-boundary naturality and uniqueness of its Ext representative
then give SupportedKummerScalar for the two etale classes. For the pro-etale
clause use the normalized GeoCartierScalarCompatibility supplied by
exists_geoCartierCycleClass at that exponent: it already asserts the scalar-unit
Hom bijections against every unbounded pro-etale test object. Ordinary boundary
uniqueness and the quotient-unit normalization identify its supported source
comparison with that in the realization. Conjugate its target unit by the two
finite Tate comparison isomorphisms and restricted-scalar inverse isomorphism.
Composition with these isomorphisms preserves those Hom bijections. On local
pure tensors the unit sends b tensor x to the quotient of b tensor x, because
the root-projection-normalized comparisons send each etale root tensor to the
same tensor of its compatible root lift. Tensor sheafification determines the
unit globally. Conjugating the GeoCartier scalar Ext square and substituting the
two realization equations gives the pro-etale reduction equation, including
the identity reduction. A common exponent exists by increasing an annihilator
of the larger quotient; mapping its zero equation gives one for the smaller.
For scheme pullback, pull back the Cartier local equations and their dual
frames. The assumed Cartier property gives precisely the new trivialized line
and hence the new relative boundary. The ordinary boundary pullback theorem
supplies its Ext square. Closed exchange is invertible, with identity stalk
on the divisor and zero stalk off it. Comparison with the pro-etale site
commutes with inverse image by its adjunction mate. The finite Tate descent
pullback square intertwines the normalized root comparisons. Conjugating the
ordinary Ext square by the supported and Tate comparisons proves the displayed
pro-etale square. Quotient units and all root projections retain their stated
normalizations. No flatness of either the coefficient or scheme map occurs. -/
theorem cartier_kummer_naturality
    (hkill : ∀ n : ℕ, ∃ r : ℕ,
      ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    (κ : CartierEtaleKummerFamily l E) (c : CartierKummerFamily l E)
    (hκ : CartierEtaleKummerNormalization l E κ)
    (hc : CartierKummerRealization l E κ c) :
    CartierEtaleKummerReduction l E κ ∧
      CartierKummerBaseChange l E c ∧ CartierKummerReduction l E c := by
  sorry

end AlgebraicGeometry.Etale
