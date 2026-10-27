module

public import Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore

/-! Split compatibility squares for integral finite-extension reduction pairing. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.derivedInternalHomOfUniverses
  CategoryTheory.homComplexFunctor
  WeilConjectures.IntegralHom.totalTensor WeilConjectures.IntegralHom.homModelMap
  WeilConjectures.IntegralHom.projection WeilConjectures.IntegralHom.evaluate

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

variable (wE : DualizingDatum l X D hl E) (wL : DualizingDatum l X D hl L)


/-- Signed biduality square under scalar extension.
Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, paragraphs 5-7
(blueprint: lem-sf-integral-finite-extension-reduction-pairing).

Proof: The signed double-dual square follows by transposing the scalar-extended
evaluation on simultaneous normalized representatives. The tensorator commutes with the
signed swap by degree-zero scalar balancing, and the assumed naturality equations identify
both transposes. -/
theorem CoefIntegralFiniteExtensionDeltaSquare
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (sE : IntegralVerdier.SignedSymmetry X _ a)
    (sL : IntegralVerdier.SignedSymmetry X _ b)
    (mE : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
    (mL : ∀ n : ℕ, IntegralHom.ReductionPresentation l L X D hl b n)
    (hnatE : ∀ (K M K' M' : IntegralVerdier.Ambient l E X)
      (f : K ⟶ K') (g : M ⟶ M'),
      a.tensor.map (Prod.mkHom f g) ≫ (sE.swap K' M').hom =
        (sE.swap K M).hom ≫ a.tensor.map (Prod.mkHom g f))
    (hnatL : ∀ (K M K' M' : IntegralVerdier.Ambient l L X)
      (f : K ⟶ K') (g : M ⟶ M'),
      b.tensor.map (Prod.mkHom f g) ≫ (sL.swap K' M').hom =
        (sL.swap K M).hom ≫ b.tensor.map (Prod.mkHom g f))
    (hevalE : ∀ (K K' M : IntegralVerdier.Ambient l E X) (f : K' ⟶ K),
      a.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l E X)).map
            (Prod.mkHom f.op (𝟙 M)))) ≫ (a.adjunction K').counit.app M =
        a.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (a.adjunction K).counit.app M)
    (hevalL : ∀ (K K' M : IntegralVerdier.Ambient l L X) (f : K' ⟶ K),
      b.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l L X)).map
            (Prod.mkHom f.op (𝟙 M)))) ≫ (b.adjunction K').counit.app M =
        b.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (b.adjunction K).counit.app M)
    (hfinE : ∀ (n : ℕ) (K K' W : DerivedCategory (scalarReductionTarget l E X n))
      (f : K' ⟶ K),
      (mE n).target.tensor.map (Prod.mkHom (𝟙 K')
        ((IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).map
          (Prod.mkHom f.op (𝟙 W)))) ≫ ((mE n).target.adjunction K').counit.app W =
      (mE n).target.tensor.map (Prod.mkHom f (𝟙 _)) ≫
        ((mE n).target.adjunction K).counit.app W)
    (hfinL : ∀ (n : ℕ) (K K' W : DerivedCategory (scalarReductionTarget l L X n))
      (f : K' ⟶ K),
      (mL n).target.tensor.map (Prod.mkHom (𝟙 K')
        ((IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l L X n)).map
          (Prod.mkHom f.op (𝟙 W)))) ≫ ((mL n).target.adjunction K').counit.app W =
      (mL n).target.tensor.map (Prod.mkHom f (𝟙 _)) ≫
        ((mL n).target.adjunction K).counit.app W) :
    let T := integralScalarExtensionOfUniverses l E L ι X
    let HE := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l E X)
    let DE := IntegralVerdier.dual l E X wE.omega.obj
    let DL := IntegralVerdier.dual l L X wL.omega.obj
    (∀ K : sfIntegralConstructibleCategory l E X,
      IntegralVerdier.delta X b sL wL.omega.obj (T.obj K.obj) ≫
          DL.map (beta l E L ι X D hl wE wL a b K.obj K.property.1).op =
        T.map (IntegralVerdier.delta X a sE wE.omega.obj K.obj) ≫
          beta l E L ι X D hl wE wL a b (DE.obj (op K.obj))
            (scalarInternalHom_complete l E X K.obj wE.omega.obj wE.omega.property.1)) := by
  sorry

end WeilConjectures.IntegralFiniteExtension
