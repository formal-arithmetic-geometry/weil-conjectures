/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GlobalVerdierDualityData

/-! # Identity normalization of global-duality construction data

Source: global-duality proof, normalization of the exceptional adjunction of the
point identity, before the five-adjunction argument proves invertibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated.Opposite
open scoped CategoryTheory.Functor
namespace WeilConjectures.GlobalVerdierDuality
open ConstructibleExceptionalCoefficients VerdierExchange

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Normalize the construction data at the coefficient point. This statement supplies
closed structures, their actual projection, its naturality, and equations for shifts
and coefficients. It does not assert that the exchange map is invertible.

Source: latest blueprint, sec-six-functors/sk-thm-sf-global-duality,
sole proof paragraph (specialize exchange and identify the point dual); expanded
proof steps 2--5 of the imported node
(blueprint: lem-sf-global-identity-normalization).

Proof: choose a constructible exceptional System for the identity of s=Spec k using
lem-sf-constructible-exceptional-adjunction-coefficients and its proper identity
compactification. Apply the supplied Verdier exchange assertion with Sf=A and
Sfg=A transported along a followed by the identity. The normalized identity-open
and identity-direct-image maps identify the compact-support functor of s with the
identity at each finite coefficient level. Conjugate that left comparison under its
exceptional adjunction and the identity adjunction. The conjugate is the unique
right comparison characterized by the counit equation. On integral coefficients
make the comparison on the entire strict quotient tower before applying its total
limit; then restrict to complete finite-Tor objects. Localize this comparison for
finite coefficient fields and pass through the common finite-field Hom colimit for
the closed coefficient stage. Thus all identity comparisons use the published
operations and their coefficient maps.

Transport the two closed structures and the ordinary pull/star adjunction from the
exchange package. Replace its point dualizing target by the coefficient unit using
the preceding counit comparison, and replace its X target by A.G(unit) using the
composition comparison. With these choices the new dualizing isomorphism is the
identity. The new epsilon is the projection/evaluation transpose: apply the three
inverse Hom bijections to its transported naturality square, use the defining
counit equations for both conjugate comparisons, and cancel the inverse pairs.
This proves the recorded components, naturality and shift equation without using
invertibility. Projection naturality follows from naturality of the proper counit,
open tensor comparison and tensor symmetries in RingProjection. At integral stages
this is an equality on the whole quotient tower and survives completion; at field
stages it localizes and descends to the common-stage category.

The coefficient unit has Tor amplitude [0,0]. The finite-Tor inclusions therefore
contain the tensor units. Lift their ambient unit maps through the fully faithful
inclusions to obtain unitX and unitY. Tensor/evaluation normalization identifies
these maps with the ambient multiplication unitors, proving both displayed unitor
equations. The ring realizations and projection records are the old ones with the
target comparisons composed; evaluation normalizations follow by naturality in the
second Hom variable. Transport signed Hom shifts in the same way. Their comparison
maps do not depend on a proof of invertibility, so they give ringShifts for every
such proof.

Finally, conjugate each old scalar comparison by the identity and target
comparisons. Its q is the prescribed A comparison: after the faithful inclusion
both are the canonical compact-support scalar map; its b is then determined by
the unit/counit mate equations. The same calculation on the coefficient unit gives
the normalized unit equation. Transpose the scalar evaluation squares to obtain
ScalarConclusion; the signed comparison squares give ScalarShifts for any proof of
invertibility. Rationalization and rational scalar extension preserve these equal
maps, and common-stage descent uses a single common finite coefficient field for
each square. No constant-object duality or inverse to epsilon is used here.
-/
theorem identity_normalization (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    : letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
    VerdierExchange.Assertion l Ω D hl (X ↘ Spec (.of D.k)) →
    ∀ (A : System.{u, u} l Ω D hl (f := X ↘ Spec (.of D.k)))
      (c : Compactification (X ↘ Spec (.of D.k))),
      Nonempty (NormalizedData l Ω D hl (X ↘ Spec (.of D.k)) A c) := by
  sorry

end WeilConjectures.GlobalVerdierDuality
