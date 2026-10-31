/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalOperations.RationalOperationsData
import WeilConjectures.SixFunctors.RationalOperations.RationalHomScalarEvaluationCore

/-! # Finite scalar compatibility of normalized rational Hom evaluation

Source: the finite-extension evaluation and rationalization argument of
lem-sf-rational-hom-identifications, steps 9--10
(blueprint: lem-sf-rational-hom-scalar-evaluation).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalOperations

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]

variable (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- The evaluation of two normalized full rational tensor-Hom adjunctions commutes
with the recorded finite scalar comparisons.
Source: lem-sf-rational-hom-identifications, steps 9--10 (the finite-extension
paragraphs retained from lem-coef-rational-operations); Stacks Tag 08J9
(blueprint: lem-sf-rational-hom-scalar-evaluation).

Proof: first take integral constructible K and M and write H = RHom(K,M). Uncurrying
of the ordinary internal-Hom scalar comparison is scalar-extended ordinary evaluation
preceded by the inverse ordinary tensor scalar comparison. This follows from the
comparison's definition as a closed transpose. Its local formula is
(h tensor s, k tensor t) maps to h(k) tensor st. The completed scalar comparison
conjugates this identity by the three canonical scalar-completion maps. The completed
tensor comparison does the same for tensor. Naturality of the normalized completion
unit identifies these conjugates with the inverse-completion/ordinary-evaluation
counits specified in the two Hom identifications. The quotient-map and zero-coordinate
normalization fixes these maps already on strict K-flat tensor representatives;
finite-free scalar extension commutes with that tower and its mapping fiber. Thus the
integral completed evaluation square commutes. Apply rational localization to that
square. The recorded rational tensor and Hom scalar comparisons are the localizations
of these integral comparisons, so their pure-map specifications give exactly the
stated square. Every rational object is an unchanged integral object, hence these
squares cover all K and M. Identity embeddings use multiplication by one; ramified
extensions use the same finite-free scalar map on cofinal powers, so no unramified
hypothesis or exception for torsion or zero objects is needed. -/
theorem rationalHom_scalar_evaluation
    (wE : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wL : IntegralFiniteExtension.DualizingDatum l X D hl L)
    (A : RationalVerdier.Datum D l hl X E wE)
    (B : RationalVerdier.Datum D l hl X L wL)
    (hE : HomIdentification l E X D hl wE A)
    (hL : HomIdentification l L X D hl wL B) :
    HomScalarCompatibility l E X D hl L ι wE wL A B hE hL := by
  apply scalarEvaluation_of_normalizedCounits D l hl X E L ι
    hE.permitted hL.permitted
    (fun K M ↦ (hE.adjunction K).counit.app M)
    (fun K M ↦ (hL.adjunction K).counit.app M)
  · intro K M
    exact homIdentification_counit_normalized D l hl X E wE A hE K M
  · intro K M
    exact homIdentification_counit_normalized D l hl X L wL B hL K M

end WeilConjectures.RationalOperations
