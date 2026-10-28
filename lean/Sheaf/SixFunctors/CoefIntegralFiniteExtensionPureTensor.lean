module

public import Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore

/-! Pure-tensor coefficient and associator component of integral extension coherence.
Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, final paragraph.
(blueprint: lem-sf-integral-finite-extension-composition-pure-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

/-- Pure tensor unit and associator equations for fixed integral comparisons.
Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, final paragraph.
Proof: on pure coefficient tensors scalar multiplication is the identity unitor,
and iterated scalar extension is balanced multiplication; the normalized completion
maps cancel at intermediate vertices. The two parenthesizations therefore agree.
-/
theorem comparison_composition_pure_tensor
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (wE : DualizingDatum l X D hl E) (wL : DualizingDatum l X D hl L)
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X)) :
    ∀ (F : Type u) [Field F] [Algebra (Padic l) F]
      [FiniteDimensional (Padic l) F]
      (j : L →ₐ[Padic l] F) (wF : DualizingDatum l X D hl F)
      (c : IntegralHom.TensorPresentation.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l F X)),
      (∀ (K : sfIntegralConstructibleCategory l E X),
        (comp l E E (AlgHom.id (Padic l) E) X L ι K.obj K.property.1).hom =
          (integralScalarExtensionOfUniverses l E L ι X).map
            (unit l E X K.obj K.property.1).hom) ∧
      (∀ (K : sfIntegralConstructibleCategory l E X),
        (comp l E L ι X L (AlgHom.id (Padic l) L) K.obj K.property.1).hom =
          (unit l L X
            ((integralScalarExtensionOfUniverses l E L ι X).obj K.obj)
            (extension_complete l E L ι X K.obj K.property.1)).hom) ∧
      (∀ (G : Type u) [Field G] [Algebra (Padic l) G]
        [FiniteDimensional (Padic l) G]
        (k : F →ₐ[Padic l] G) (K : sfIntegralConstructibleCategory l E X),
        (integralScalarExtensionOfUniverses l F G k X).map
            (comp l E L ι X F j K.obj K.property.1).hom ≫
          (comp l E F (j.comp ι) X G k K.obj K.property.1).hom =
          (comp l L F j X G k
            ((integralScalarExtensionOfUniverses l E L ι X).obj K.obj)
            (extension_complete l E L ι X K.obj K.property.1)).hom ≫
          (comp l E L ι X G (k.comp j) K.obj K.property.1).hom) := by
  sorry

end WeilConjectures.IntegralFiniteExtension
