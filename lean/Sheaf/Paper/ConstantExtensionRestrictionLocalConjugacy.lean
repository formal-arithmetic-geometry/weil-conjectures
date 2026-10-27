/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Paper.ConstantExtensionWeilHeartData

/-! # Residue powers for distinguished-sheet restriction

Source: Deligne, Weil II, (1.1.8), p. 151, and the paragraph after (1.1.10), p. 152.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [hsep : IsSeparated X₀.hom]
  (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

include hsep in
/-- The local operator of sheet restriction of actual pullback is the residue power.
Source: Deligne, Weil II, (1.1.8), p. 151, and after (1.1.10), p. 152.
(blueprint: lem-zl-constant-extension-restriction-local-conjugacy).

Proof: apply the generic constructible Weil-pullback local-Frobenius theorem to
constantExtensionProjection, regarded over k₀. The induced residue algebra is exactly
the algebra in constantExtensionResidueDegree, so its exponent is the displayed f.
Use the sheet-return local-operator comparison to identify the operator of its return
under R with this pulled-back operator. The hypothesis on R fixes its carrier on
all arrows and its ordered return map, hence identifies it with the specified return
functor by the unique lift of its carrier comparison to Weil objects.
First take the residue embedding at the image induced by the chosen embedding at z;
then the geometric points are compatible and the generic pullback comparison applies.
For arbitrary embeddings and finite presentations, use sfLocalFrobenius_model_conjugacy
at each base-field datum. Represent the finite diagram at a common coefficient
field. Naturality of local Frobenius under Weil isomorphisms transports both operators
to the given presentations K and K'. Scalar compatibility of point transports and of
cohomology identifies their scalar extensions with the operators in LocalConjugacy.
Compose the two stalk isomorphisms, orienting the composite from the original stalk
to the restricted stalk; functoriality preserves the fth power. No eigenbasis is used.
The argument includes zero stalks, m=1, and the empty scheme. -/
theorem constantExtensionRestrictionLocalConjugacy
    (R : sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω ⥤
      sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω)
    (hR : ConstantExtensionSheetSpec D m hm X₀ l hl Ω R)
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω)
    (z : {z : (constantExtensionModel D m hm X₀).left //
      z ∈ closedPoints (constantExtensionModel D m hm X₀).left}) :
    ConstantExtensionLocalConjugacy D m hm X₀ l hl Ω X₀ F
      (R.obj ((zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀)).obj F))
      (constantExtensionClosedImage D m hm X₀ z) z
      (constantExtensionResidueDegree D m hm X₀ z.val) := by sorry

end WeilConjectures
