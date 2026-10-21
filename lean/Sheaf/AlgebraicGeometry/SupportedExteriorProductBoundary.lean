/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.SupportedLocalizationComparisons
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Connecting maps and supported exterior products

This is the connecting-map part of supported localization, stated independently of
completion to a triangle morphism. Both tensor shift comparisons are retained.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry.Etale

/-- Supported exterior products commute with the normalized connecting maps in either
variable. This asserts only the connecting square; it does not assert either of the
support-inclusion or open-restriction squares.

Source: Stacks Tags 09XP, 095L and 0F1E; the coefficient-cone argument in steps 3--10
of `lem-pur-supported-product-localization`, and Tag 08JC for exactness of derived Hom.
(blueprint: lem-pur-supported-exterior-product-boundary).

Proof: write S_Z for the closed direct image of the rank-one constant module on Z.
The normalized coefficient adjunction gives the ordinary A-linear equivalence
Hom(C_Z(A),F) to Gamma_Z(F), sending f to the value at 1 of its adjoint. Linearity
of Gamma_Z follows by canceling its monic inclusion into global sections; the
adjunction unit formula then proves linearity and naturality of this equivalence.
For the coefficient in degree zero, the fromSingleEquiv cochain comparison identifies
its Hom differential with postcomposition by the target differential. Thus, for a
bounded-below injective representative I, Hom(S_Z,I) is the kernel of restriction
I(T) to I(T minus Z): apply Hom(-,I) to the open-closed sequence of the constant sheaf,
and use the extension-by-zero adjunction. This identifies it, differentials included,
with the complex defining supported sections. Apply the open-closed sequence instead
to S_B. Its terms are j_!S_(B intersect U), S_B, and S_(B intersect C), as checked on
geometric stalks. Those stalks are A or zero, so the three terms are flat. Their
external tensors with S_D are the three corresponding product-support coefficients;
the comparison maps send a pair of constant sections to their tensor.

Apply the external derived-Hom evaluation cone pairing to this short exact coefficient
sequence and the fixed coefficient S_D. Its hypotheses hold by flatness and the three
boundedness assumptions. The supported-Hom identification sends the evaluation
counits to the normalized supported coefficient counits: precomposition with the
constant quotient determines both. The same normalization identifies its tensor
comparison with supportedCoefficientTensorDerived, by the complex comparison and
uniqueness of descent. The open coefficient term is identified by extension by zero;
the resulting product-open identification is supportedFirstLocalizationThirdIso.
Thus the cone pairing gives the displayed first connecting square for the specified
exterior products. The Hom short exact sequence is the support restriction sequence,
so its connecting map is the normalized boundary, not an arbitrary completion.
For the second square apply the same argument to the coefficient sequence on Y,
keeping S_B fixed on X; its open comparison is supportedSecondLocalizationThirdIso.
The cochain total differential gives the tensor shift map x tensor y to x tensor y
in the first square, and x tensor y to (-1)^degree(x) x tensor y in the second.
These are exactly the CommShift comparisons in the two mapTriangle expressions.
Empty supports give zero terms; full cut supports give zero open terms, so the same
construction and normalizations apply in both edge cases. -/
theorem supportedExteriorProduct_boundary (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hF : ∃ n : ℤ,
      (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj).IsGE n) :
    (∀ {B C D : Scheme.{u}} (b : B ⟶ X) (c : C ⟶ X) (d : D ⟶ Y)
      [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d],
      ((tensorRight ((supportedSectionsDerived A d).obj L.obj)).mapTriangle.obj
          (normalizedSupportTriangle A b c K.obj)).mor₃ ≫
        (supportedExteriorProduct A f g (supportIntersection b c) d K.obj L.obj ≫
          (derivedSupportCongruence A
            (supportedProductImmersion f g (supportIntersection b c) d)
            (supportIntersection (supportedProductImmersion f g b d)
              (supportedProductImmersion f g c (𝟙 Y)))
            (supportedFirstIntersection_complement f g b c d)).hom.app
              (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj))⟦(1 : ℤ)⟧' =
      (supportedExteriorProduct A (c.openComplement.ι ≫ f) g
          (supportOnOpen b c.openComplement) d
          ((upperStar (ModuleCat.{u + 1} A) c.openComplement.ι).mapDerivedCategory.obj K.obj)
          L.obj ≫ (supportedFirstLocalizationThirdIso A f g b c d K.obj L.obj).inv) ≫
        (normalizedSupportTriangle A (supportedProductImmersion f g b d)
          (supportedProductImmersion f g c (𝟙 Y))
          (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj)).mor₃) ∧
    (∀ {B C D : Scheme.{u}} (b : B ⟶ X) (c : C ⟶ Y) (d : D ⟶ Y)
      [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d],
      ((tensorLeft ((supportedSectionsDerived A b).obj K.obj)).mapTriangle.obj
          (normalizedSupportTriangle A d c L.obj)).mor₃ ≫
        (supportedExteriorProduct A f g b (supportIntersection d c) K.obj L.obj ≫
          (derivedSupportCongruence A
            (supportedProductImmersion f g b (supportIntersection d c))
            (supportIntersection (supportedProductImmersion f g b d)
              (supportedProductImmersion f g (𝟙 X) c))
            (supportedSecondIntersection_complement f g b c d)).hom.app
              (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj))⟦(1 : ℤ)⟧' =
      (supportedExteriorProduct A f (c.openComplement.ι ≫ g) b
          (supportOnOpen d c.openComplement) K.obj
          ((upperStar (ModuleCat.{u + 1} A) c.openComplement.ι).mapDerivedCategory.obj L.obj) ≫
        (supportedSecondLocalizationThirdIso A f g b c d K.obj L.obj).inv) ≫
        (normalizedSupportTriangle A (supportedProductImmersion f g b d)
          (supportedProductImmersion f g (𝟙 X) c)
          (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj)).mor₃) := by
  sorry

end AlgebraicGeometry.Etale
