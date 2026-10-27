/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B8
-/
module

public import Sheaf.SixFunctors.RamifiedScalarPreparation

/-! # Compatibility of the normalized ramified support comparison

The ordered proper/open scalar comparison is compared before taking a derived
limit. This is the support square, independently of exceptional limit realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RamifiedScalarSupportCompatibility
open FiniteScalarMate

variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (i : E →ₐ[ℚ_[l]] L)

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)


variable {l E L i D hl f c}


variable (l E L i D hl f c)

/-- The proper coefficient projection followed by open balancing gives the same
support arrow after the specified scalar and support conjugations.
Source: parent node step 6; current blueprint
`sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-compact-support.proof.md`,
isomorphism and composition paragraphs
(blueprint: lem-coef-ramified-scalar-support-compatibility).

Proof: expand the two support identifications into cofinal restriction, inverse
reduction counits and the prescribed support/scalar realizations. Naturality of
cofinal restriction moves the system comparison past the retained limit map.
Naturality of the system proper/open comparison moves the inverse exceptional
reduction comparison to the input; thus it suffices to compute the support square
on the actual reduction of an integral constructible object. On one flat-term
K-flat representative, scalar reassociation commutes with every quotient map.
The proper coefficient projection and open tensor balancing are the ordered
strict-tower maps defining the completed compact-support comparison. Their
composite therefore agrees before localization, on both Roos coordinates.
The scalar-model normalization identifies its limit with ordinary completed
scalar extension. The two completion comparisons are precisely the inverse at
the support output and the forward map at the input in integralAlphaComponent.
The support-unit normalizations cancel the remaining reduction and limit units
by the adjunction triangles. Localizing the chain equality and composing with
the fixed support realizations yields the displayed equation, naturally in M.
No equality of system arrows is deduced from their finite evaluations. -/
theorem supportComparison (e : ℕ)
    (he : PurCompactSupport.Ramification l E L i e) (hp : 1 ≤ e)
    (a : Context l E L i D hl f c)
    (P : RamifiedScalarPreparation.Preparation a e he hp)
    (M : sfIntegralConstructibleCategory l E Y) :
    (retainedLimit l L Y e).map ((a.alpha.app (a.r.G.obj (a.RY.obj M))).hom) ≫
        P.supportSource.hom.app M =
      P.supportTarget.hom.app M ≫ a.integralAlphaComponent (a.GR.obj M) := by sorry

end WeilConjectures.RamifiedScalarSupportCompatibility
