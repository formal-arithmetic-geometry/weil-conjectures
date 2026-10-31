/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldExtensionReductionLimits
public import WeilConjectures.AlgebraicGeometry.FieldExtensionIntegralModels
public import WeilConjectures.AlgebraicGeometry.FieldExtensionIntegralCoordinates
public import WeilConjectures.AlgebraicGeometry.FieldExtensionSystemCoordinates
public import WeilConjectures.AlgebraicGeometry.FieldScalarReductionData
public import WeilConjectures.AlgebraicGeometry.FiniteFreeCompletedScalarComparison

/-! # Field extension reduction tensor maps

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.proof.md, paragraph (1), final sentences
(blueprint: lem-route-field-extension-reduction-tensor-map).

The statement records the two normalized natural isomorphisms for fixed integral and
system coordinates.  The proof uses finite-free completed scalar comparison, the
coordinate and system comparison data, and the normalized scalar reduction data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldExtensionTowers

/-- The normalized integral and reduction tensor maps for fixed coordinates.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-field-extension/sk-lem-sp-field-extension-towers.proof.md, paragraph (1),
final sentences (blueprint: lem-route-field-extension-reduction-tensor-map).

Proof.
1. Every object `K` of `Integral P E T` is derived complete for the completed
   `E`-coefficients, since `Integral P E T` is the full subcategory of derived-complete
   objects with constructible reductions in a common bounded interval. Hence the
   finite-free completed scalar comparison `χ_{F/E,K}` (`completedScalarComparison`),
   from the ordinary derived scalar extension to `integralScalarExtension`, is an
   isomorphism, natural in `K` (`finiteFreeCompletedScalarComparison`). Restriction of
   scalars along `RB` is a functor, so the restricted `χ_{F/E,K}` is a natural
   isomorphism on `Integral P E T` and may be inverted.
2. By definition of `IntegralCoordinates`, the given `A` carries the derived natural
   isomorphism `A.ordinaryDerived`, from the ordinary completed derived scalar extension
   followed by restriction along `RB` to restriction along `RA` followed by the derived
   scalar extension `(FieldScalar.integralScalar A.data.coefficients).model.T`; it is
   fixed on cochain representatives by the completed-scalar counit and the ordinary
   comparison `s ⊗ x ↦ s ⊗ x` (`A.ordinaryDerived_rep`). `A.data` carries normalized
   field-scalar data, whose reduction comparison is one of its fields. No new `A` is built.
3. By definition of `SystemCoordinates`, the given `B` carries the natural isomorphism
   `B.system` from the derived whole-system scalar extension of `A` to `towerScalar P D h T`,
   equal on every object to the unit of the section-preserving realization equivalence
   followed by the image of `B`'s derived system comparison. It is an isomorphism of
   functors into the derived category of whole strict systems, so it commutes with every
   quotient transition.
4. The reduction comparison `A.data.comparison.isoDerived` is a derived natural isomorphism
   from the derived scalar extension of `A`'s integral scalar model followed by `RB.red` to
   `RA.red` followed by `A`'s derived whole-system scalar extension. On a local generator
   its ordinary forward map is `(x ⊗ s) ⊗ b ↦ (x ⊗ 1) ⊗ (s̄ b)`, with inverse inserting one,
   and it is characterized by the counit equation on K-flat representatives.
5. Define `integral_K` as the inverse of the restricted `χ_{F/E,K}` of step 1 followed by
   `A.ordinaryDerived` at `K` (step 2). It has the source and target of
   `Reduction.integral` and is a natural isomorphism as a composite of natural
   isomorphisms; composing the restricted `χ_{F/E,K}` with `integral_K` cancels the inverse,
   which is the first conjunct. Define `reduction_K` as `RB.red.map integral_K`, followed
   by `isoDerived` (step 4) at the `RA`-restriction of `K`, followed by `B.system` (step 3)
   at its `RA`-reduction. The three factors are natural isomorphisms whose targets and
   sources match successively; `spCompletedReduction` is `RB.red` after restriction along
   `RB` (resp. `RA.red` after restriction along `RA`), so the composite has the type of
   `Reduction.reduction`. The second conjunct holds by definition.
-/
theorem field_extension_reduction_tensor_map
    (P : PurityFiniteSetting.{u}) (D : FieldShriekSystem.Models P)
    (E F : FieldShriekSystem.Index P) (h : E ≤ F) (T : Scheme.{u})
    (RA : SpReductionTower P.coefficients.l E.val T ((D.coordinates E).abelian T))
    (RB : SpReductionTower P.coefficients.l F.val T ((D.coordinates F).abelian T))
    (A : IntegralCoordinates P D E F h T RA RB)
    (B : SystemCoordinates P D E F h T RA RB A) :
    ∃ (integral :
        (sfIntegralConstructible P.coefficients.l E.val T).ι ⋙
            integralScalarExtension P.coefficients.l E.val F.val
              (IntermediateField.inclusion h) T ⋙
            (SheafOfModules.restrictScalars
              ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
                RB.coefficient.hom)).mapDerivedCategory ≅
          (sfIntegralConstructible P.coefficients.l E.val T).ι ⋙
            (SheafOfModules.restrictScalars
              ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
                RA.coefficient.hom)).mapDerivedCategory ⋙
            (FieldScalar.integralScalar A.data.coefficients).model.T)
      (reduction :
        (sfIntegralConstructible P.coefficients.l E.val T).ι ⋙
            integralScalarExtension P.coefficients.l E.val F.val
              (IntermediateField.inclusion h) T ⋙
            spCompletedReduction P.coefficients.l F.val T
              ((D.coordinates F).abelian T) RB ≅
          (sfIntegralConstructible P.coefficients.l E.val T).ι ⋙
            spCompletedReduction P.coefficients.l E.val T
              ((D.coordinates E).abelian T) RA ⋙
            towerScalar P D h T),
      (∀ K : Integral P E T,
        (restriction P D F T RB).mapDerivedCategory.map
              ((completedScalarComparison P.coefficients.l E.val F.val
                (IntermediateField.inclusion h) T).app K.obj) ≫ integral.hom.app K =
            A.ordinaryDerived.hom.app K.obj) ∧
      ∀ K : Integral P E T,
        reduction.hom.app K =
          RB.red.map (integral.hom.app K) ≫
            A.data.comparison.isoDerived.hom.app
              ((restriction P D E T RA).mapDerivedCategory.obj K.obj) ≫
            B.system.hom.app
              (RA.red.obj ((restriction P D E T RA).mapDerivedCategory.obj K.obj)) := by
  sorry

end AlgebraicGeometry.ProEtale.FieldExtensionTowers
