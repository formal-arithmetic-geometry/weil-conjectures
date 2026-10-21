/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.CartierKummerData

/-! # Descent and exponent independence of normalized Cartier boundaries

Source: blueprint main-20261015, lem-amb-cartier-kummer-map.proof.md,
final paragraph, and the expanded DAG proof, steps 8--11 and 13.
(blueprint: lem-amb-cartier-kummer-descent)
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

/-- A normalized ordinary boundary family descends to a unique family in the
published pro-etale Tate lines, independently of the annihilating exponent.

Source: blueprint main-20261015, lem-amb-cartier-kummer-map.proof.md, final paragraph;
expanded proof steps 8--11 and 13 (blueprint: lem-amb-cartier-kummer-descent).

Proof: At each coefficient level choose an annihilating exponent. The canonical
closed direct-image mate is invertible by the exact site comparison and the
open-closed quotient presentation. Its composite with the ordinary quotient is
constant comparison followed by the pro-etale quotient. Transport the ordinary
Ext class by this source isomorphism and by the root-projection-normalized Tate
isomorphism supplied by finite_tate_site_descent. This defines an arrow at that
level. For two exponents compare both with their maximum. The map of Kummer
sequences has identity on the right-hand G_m and power l^(s-r) in the middle
and on roots. Boundary naturality identifies the two relative classes; exact
coefficient forgetting and support Hom preserve the equation. The normalized
scalar adjunction identifies successive extension with direct extension.
The root projections satisfy p_r=p_(s,r)p_s, so the Tate comparisons carry
this equation to equality of the two transported arrows. Thus one arrow realizes
every allowed exponent. For uniqueness the quotient unit is epic, so its
normalization fixes the source comparison. The Tate comparison is fixed on local
pure root tensors: refine a root-trivializing etale cover by pro-etale covers
where roots lift compatibly to the tower, and use the tensor sheafification
universal property. The realization equation, cancelled against the invertible
source comparison, now determines the arrow at every argument. Function
extensionality proves uniqueness of the simultaneous family. Empty schemes and
empty divisors satisfy the same quotient and tensor calculations. -/
theorem cartier_kummer_descent
    (hkill : ∀ n : ℕ, ∃ r : ℕ,
      ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    (κ : CartierEtaleKummerFamily l E)
    (hκ : CartierEtaleKummerNormalization l E κ) :
    ∃! c : CartierKummerFamily l E, CartierKummerRealization l E κ c := by
  sorry

end AlgebraicGeometry.Etale
