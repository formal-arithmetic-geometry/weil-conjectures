module

public import Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore
import Sheaf.SixFunctors.IntegralVerdierSignedCalculus
import Sheaf.SixFunctors.CoefIntegralFiniteExtensionReductionPairing
import Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibility
import Sheaf.SixFunctors.CoefIntegralFiniteExtensionCocycles
import Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic

/-! # Integral duality under finite coefficient extension

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, order 2494
(blueprint: lem-coef-integral-finite-extension).

The defining comparisons are publicly re-exported from the models module.
-/

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

private theorem evaluation_transport
    {C : Type*} [Category C] (T : C × C ⥤ C) (H : Cᵒᵖ × C ⥤ C)
    (adj : ∀ K : C, (Functor.curry.obj T).obj K ⊣ (Functor.curry.obj H).obj (op K))
    (hn : ∀ (K K' M : C) (f : K' ⟶ K),
      T.map (Prod.mkHom (𝟙 K') (H.map (Prod.mkHom f.op (𝟙 M)))) ≫
          (adj K').counit.app M =
        T.map (Prod.mkHom f (𝟙 _)) ≫ (adj K).counit.app M)
    (K K' M M' : C) (f : K' ⟶ K) (g : M ⟶ M') :
    T.map (Prod.mkHom (𝟙 K') (H.map (Prod.mkHom f.op g))) ≫
        (adj K').counit.app M' =
      T.map (Prod.mkHom f (𝟙 (H.obj (op K, M)))) ≫
        (adj K).counit.app M ≫ g := by
  have hh : H.map (Prod.mkHom f.op g) =
      H.map (Prod.mkHom (𝟙 (op K)) g) ≫ H.map (Prod.mkHom f.op (𝟙 M')) := by
    rw [← H.map_comp]
    simp only [prod_comp, Category.id_comp, Category.comp_id]
  rw [hh]
  have ht : T.map (Prod.mkHom (𝟙 K')
      (H.map (Prod.mkHom (𝟙 (op K)) g) ≫ H.map (Prod.mkHom f.op (𝟙 M')))) =
      T.map (Prod.mkHom (𝟙 K') (H.map (Prod.mkHom (𝟙 (op K)) g))) ≫
        T.map (Prod.mkHom (𝟙 K') (H.map (Prod.mkHom f.op (𝟙 M')))) := by
    rw [← T.map_comp]
    simp only [prod_comp, Category.id_comp]
  rw [ht, Category.assoc, hn]
  have ht' : T.map (Prod.mkHom (𝟙 K') (H.map (Prod.mkHom (𝟙 (op K)) g))) ≫
      T.map (Prod.mkHom f (𝟙 _)) =
      T.map (Prod.mkHom f (𝟙 _)) ≫
        T.map (Prod.mkHom (𝟙 K) (H.map (Prod.mkHom (𝟙 (op K)) g))) := by
    simp only [← T.map_comp, prod_comp, Category.id_comp, Category.comp_id]
  erw [← Category.assoc, ht', Category.assoc]
  congr 1
  exact (adj K).counit.naturality g

private theorem v_evaluation
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (hn : ∀ (K K' M : IntegralVerdier.Ambient l L X) (f : K' ⟶ K),
      b.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l L X)).map
            (Prod.mkHom f.op (𝟙 M)))) ≫ (b.adjunction K').counit.app M =
        b.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (b.adjunction K).counit.app M)
    (K M : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) (hM : IsSfDerivedComplete l E X M) :
    b.tensor.map (Prod.mkHom (𝟙 _) (v l E L ι X a b K M hK hM)) ≫
        (b.adjunction _).counit.app _ =
      extendedEvaluation l E L ι X a b K M hK hM := by
  let T := integralScalarExtensionOfUniverses l E L ι X
  let F := pbcDerivedExtend (completedCoefficientMap l E L ι X)
  let H := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l L X)
  let cK := completion l E L ι X K hK
  let cM := completion l E L ι X M hM
  let cH := completion l E L ι X _ (scalarInternalHom_complete l E X K M hM)
  change b.tensor.map (Prod.mkHom (𝟙 _)
      (cH.inv ≫ homMap X (completedCoefficientMap l E L ι X) a b K M ≫
        H.map (Prod.mkHom cK.inv.op cM.hom))) ≫ _ = _
  have ht : b.tensor.map (Prod.mkHom (𝟙 (T.obj K))
      (cH.inv ≫ homMap X (completedCoefficientMap l E L ι X) a b K M ≫
        H.map (Prod.mkHom cK.inv.op cM.hom))) =
      b.tensor.map (Prod.mkHom (𝟙 (T.obj K)) cH.inv) ≫
        b.tensor.map (Prod.mkHom (𝟙 (T.obj K))
          (homMap X (completedCoefficientMap l E L ι X) a b K M)) ≫
        b.tensor.map (Prod.mkHom (𝟙 (T.obj K))
          (H.map (Prod.mkHom cK.inv.op cM.hom))) := by
    simp only [← Functor.map_comp, prod_comp, Category.id_comp]
  rw [ht, Category.assoc, Category.assoc,
    evaluation_transport b.tensor H b.adjunction hn _ _ _ _ cK.inv cM.hom]
  have ht' : b.tensor.map (Prod.mkHom (𝟙 (T.obj K)) cH.inv) ≫
      b.tensor.map (Prod.mkHom (𝟙 (T.obj K))
        (homMap X (completedCoefficientMap l E L ι X) a b K M)) ≫
      b.tensor.map (Prod.mkHom cK.inv (𝟙 _)) =
      b.tensor.map (Prod.mkHom cK.inv cH.inv) ≫
        b.tensor.map (Prod.mkHom (𝟙 (F.obj K))
          (homMap X (completedCoefficientMap l E L ι X) a b K M)) := by
    simp only [← Functor.map_comp, prod_comp, Category.id_comp, Category.comp_id]
    erw [Category.comp_id]
  have he := congrArg (fun f ↦ f ≫
    (b.adjunction (F.obj K)).counit.app (F.obj M) ≫ cM.hom) ht'
  simp only [Category.assoc] at he
  erw [he]
  have htrans : b.tensor.map (Prod.mkHom (𝟙 (F.obj K))
      (homMap X (completedCoefficientMap l E L ι X) a b K M)) ≫
      (b.adjunction (F.obj K)).counit.app (F.obj M) =
      (PurCompactSupport.scalarTensor (completedCoefficientMap l E L ι X)
        (tensorModel X a) (tensorModel X b)).inv.app
          (K, (IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l E X)).obj (op K, M)) ≫
        F.map ((a.adjunction K).counit.app M) := by
    exact ((b.adjunction (F.obj K)).homEquiv _ _).symm_apply_apply _
  have htrans' := congrArg
    (fun f ↦ b.tensor.map (Prod.mkHom cK.inv cH.inv) ≫ f ≫ cM.hom) htrans
  simpa only [Category.assoc, extendedEvaluation, cK, cH, cM, F] using htrans'

end WeilConjectures.IntegralFiniteExtension

namespace WeilConjectures
open IntegralFiniteExtension

/-- The canonical integral coefficient comparisons and all their normalization equations.
Source: current blueprint sec-smooth-purity/sk-lem-sp-tower, order 2494
(blueprint: lem-coef-integral-finite-extension).
Proof:
1. Finite freeness identifies strict completed extension with ordinary derived tensor
on complete inputs. Ordinary tensor and the Roos completion are triangulated. The
normalized finite quotient calculations preserve the uniform constructible bounds.
2. Construct the finite maps by transposing the compact-support counit comparisons.
Their identity and quotient composition equations give a coherent map on the full
S-tower, including levels between the ramification-multiple exponents. Take its
total limit and use the normalized counits. This gives the map u defined above,
not an arbitrary isomorphism; all its finite reductions are isomorphisms.
3. Finite freeness computes the evaluation transpose on a K-injective representative
as the finite-basis Hom identity. Completion gives precisely v. It is invertible
for constructible inputs. Composing with RHom(TK,u) gives beta and its invertibility.
4. Transpose the scalar-extended evaluation equation under the tensor-Hom adjunction.
The signed symmetry defines the actual delta; its transpose is evaluation, so the
same equation gives the displayed double-dual square. The coefficient tensor
associators identify these transposes after each finite reduction. Together with
the finite counit squares for u this gives all three quotient equations.
5. On local pure tensors, identity extension is multiplication and iterated extension
sends c tensor (b tensor x) to c*j(b) tensor x. These formulas give all three unit
and composition equations. Three successive extensions multiply coefficients in
the same order, proving the associator pentagon. The normalized completion maps
cancel in the intermediate positions. Localization and coherent total limit
preserve these equations. This includes identity fields, zero objects and empty X.
The further presentation c is assumed natural in the first tensor variable, as
the chosen a and b are; otherwise its adjunction is free off K-flat complexes. -/
theorem coef_integral_finite_extension
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (wE : DualizingDatum l X D hl E) (wL : DualizingDatum l X D hl L) :
    ∃ (a : IntegralHom.TensorPresentation.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X))
      (b : IntegralHom.TensorPresentation.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l L X))
      (sE : IntegralVerdier.SignedSymmetry X _ a)
      (sL : IntegralVerdier.SignedSymmetry X _ b)
      (mE : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
      (mL : ∀ n : ℕ, IntegralHom.ReductionPresentation l L X D hl b n),
      Conclusion l E L ι X D hl wE wL a b sE sL mE mL ∧
      IdentityConclusion l E X D hl wE a ∧ IdentityConclusion l L X D hl wL b ∧
      (∀ (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
        (j : L →ₐ[Padic l] F) (wF : DualizingDatum l X D hl F)
        (c : IntegralHom.TensorPresentation.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l F X)),
        (∀ (K K' M : IntegralVerdier.Ambient l F X) (f : K' ⟶ K),
          c.tensor.map (Prod.mkHom (𝟙 K')
              ((IntegralHom.hom.{u, u} X
                (completedIntegralCommRingSheafUnrestricted l F X)).map
                (Prod.mkHom f.op (𝟙 M)))) ≫ (c.adjunction K').counit.app M =
            c.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (c.adjunction K).counit.app M) →
        CompositionConclusion l E L ι X D hl wE wL a b F j wF c) := by
  obtain ⟨a, sE, mE, _, hnatE, hevalE, _, hfinE⟩ := IntegralVerdier.signedCalculus D l hl E X
  obtain ⟨b, sL, mL, _, hnatL, hn, _, hfinL⟩ := IntegralVerdier.signedCalculus D l hl L X
  obtain ⟨hdelta, hvred, hbred⟩ :=
    reductionPairing l E L ι X D hl wE wL a b sE sL mE mL hnatE hnatL hevalE hn hfinE hfinL
  obtain ⟨htri, hu, hv⟩ := comparison_invertibility l E L ι X D hl wE wL a b
  refine ⟨a, b, sE, sL, mE, mL, ?_,
    comparison_cocycles l E L ι X D hl wE wL a b hevalE hn⟩
  refine ⟨htri, ?_, hu, hv, ?_, ?_, ?_, hdelta, ?_, hvred, hbred⟩
  · intro K
    exact sfIntegralScalarExtension_constructible D.p l hl E L ι X K.obj K.property
  · intro K
    have := hu
    have := hv K wE.omega
    unfold beta
    have : IsIso (Prod.mkHom
        (𝟙 (op ((integralScalarExtensionOfUniverses l E L ι X).obj K.obj)))
        (u l E L ι X D hl wE wL)) :=
      (isIso_prod_iff _ _).mpr ⟨inferInstance, hu⟩
    infer_instance
  · intro K M
    exact v_evaluation l E L ι X a b hn K.obj M.obj K.property.1 M.property.1
  · intro K
    unfold beta
    let H := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l L X)
    let T := integralScalarExtensionOfUniverses l E L ι X
    have ht : b.tensor.map (Prod.mkHom (𝟙 (T.obj K.obj))
        (v l E L ι X a b K.obj wE.omega.obj K.property.1 wE.omega.property.1 ≫
          H.map (Prod.mkHom (𝟙 _) (u l E L ι X D hl wE wL)))) =
        b.tensor.map (Prod.mkHom (𝟙 _)
          (v l E L ι X a b K.obj wE.omega.obj K.property.1 wE.omega.property.1)) ≫
        b.tensor.map (Prod.mkHom (𝟙 _)
          (H.map (Prod.mkHom (𝟙 _) (u l E L ι X D hl wE wL)))) := by
      rw [← b.tensor.map_comp]
      simp only [prod_comp, Category.id_comp]
    rw [ht, Category.assoc]
    have he := (b.adjunction (T.obj K.obj)).counit.naturality
      (u l E L ι X D hl wE wL)
    change b.tensor.map (Prod.mkHom (𝟙 _)
        (v l E L ι X a b K.obj wE.omega.obj K.property.1 wE.omega.property.1)) ≫
      (b.tensor.map (Prod.mkHom (𝟙 _) (H.map (Prod.mkHom (𝟙 _)
        (u l E L ι X D hl wE wL)))) ≫ _) = _
    simp only [Functor.comp_map, Functor.curry_obj_obj_map, Functor.id_map] at he
    erw [he, ← Category.assoc,
      v_evaluation l E L ι X a b hn K.obj wE.omega.obj K.property.1 wE.omega.property.1]
  · exact u_reduction l E L ι X D hl wE wL

end WeilConjectures
