module

public import Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore

/-! Evaluation-transpose component of integral extension coherence.
Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, final paragraph.
(blueprint: lem-sf-integral-finite-extension-composition-transpose).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

/-- Composition equations for u, v and beta, obtained by transposing evaluations.
Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, final paragraph.
Proof: transpose the two successive evaluation maps under the same scalar
associator. Evaluation naturality identifies both transposes; postcomposition
with internal Hom into the u equation gives the beta equation. Coherent finite
counits and normalized limits preserve these equalities.
-/
theorem comparison_composition_transpose
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
      (completedIntegralCommRingSheafUnrestricted l L X))
    (_hevalE : ∀ (K K' M : IntegralVerdier.Ambient l E X) (f : K' ⟶ K),
      a.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l E X)).map
            (Prod.mkHom f.op (𝟙 M)))) ≫ (a.adjunction K').counit.app M =
        a.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (a.adjunction K).counit.app M)
    (_hevalL : ∀ (K K' M : IntegralVerdier.Ambient l L X) (f : K' ⟶ K),
      b.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l L X)).map
            (Prod.mkHom f.op (𝟙 M)))) ≫ (b.adjunction K').counit.app M =
        b.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (b.adjunction K).counit.app M) :
    ∀ (F : Type u) [Field F] [Algebra (Padic l) F]
      [FiniteDimensional (Padic l) F]
      (j : L →ₐ[Padic l] F) (wF : DualizingDatum l X D hl F)
      (c : IntegralHom.TensorPresentation.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l F X)),
      (∀ (K K' M : IntegralVerdier.Ambient l F X) (f : K' ⟶ K),
        c.tensor.map (Prod.mkHom (𝟙 K')
            ((IntegralHom.hom.{u, u} X
              (completedIntegralCommRingSheafUnrestricted l F X)).map
              (Prod.mkHom f.op (𝟙 M)))) ≫ (c.adjunction K').counit.app M =
          c.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (c.adjunction K).counit.app M) →
      (integralScalarExtensionOfUniverses l L F j X).map
          (u l E L ι X D hl wE wL) ≫ u l L F j X D hl wL wF =
        (comp l E L ι X F j wE.omega.obj wE.omega.property.1).hom ≫
          u l E F (j.comp ι) X D hl wE wF ∧
      (∀ (K M : sfIntegralConstructibleCategory l E X),
        (integralScalarExtensionOfUniverses l L F j X).map
            (v l E L ι X a b K.obj M.obj K.property.1 M.property.1) ≫
          v l L F j X b c
            ((integralScalarExtensionOfUniverses l E L ι X).obj K.obj)
            ((integralScalarExtensionOfUniverses l E L ι X).obj M.obj)
            (extension_complete l E L ι X K.obj K.property.1)
            (extension_complete l E L ι X M.obj M.property.1) ≫
          (IntegralHom.hom.{u, u}
            X (completedIntegralCommRingSheafUnrestricted l F X)).map
            (Prod.mkHom
              (comp l E L ι X F j K.obj K.property.1).inv.op
              (comp l E L ι X F j M.obj M.property.1).hom) =
        (comp l E L ι X F j
          ((IntegralHom.hom.{u, u}
            X (completedIntegralCommRingSheafUnrestricted l E X)).obj
            (op K.obj, M.obj))
          (scalarInternalHom_complete l E X K.obj M.obj M.property.1)).hom ≫
          v l E F (j.comp ι) X a c K.obj M.obj K.property.1 M.property.1) ∧
      (∀ (K : sfIntegralConstructibleCategory l E X),
        (integralScalarExtensionOfUniverses l L F j X).map
            (beta l E L ι X D hl wE wL a b K.obj K.property.1) ≫
          beta l L F j X D hl wL wF b c
            ((integralScalarExtensionOfUniverses l E L ι X).obj K.obj)
            (extension_complete l E L ι X K.obj K.property.1) ≫
          (IntegralVerdier.dual l F X wF.omega.obj).map
            (comp l E L ι X F j K.obj K.property.1).inv.op =
        (comp l E L ι X F j
          ((IntegralVerdier.dual l E X wE.omega.obj).obj (op K.obj))
          (scalarInternalHom_complete l E X K.obj wE.omega.obj
            wE.omega.property.1)).hom ≫
          beta l E F (j.comp ι) X D hl wE wF a c K.obj K.property.1) := by
  sorry

end WeilConjectures.IntegralFiniteExtension
