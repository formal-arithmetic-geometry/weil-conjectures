/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.BifunctorHomBidual
public import WeilConjectures.CategoryTheory.Monoidal.Mod.BidualTriangle
public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
public import WeilConjectures.WeilSheaf.SixFunctors.WeilGeometricHomConstructibility
public import WeilConjectures.PoincareDuality.Verdier
public import WeilConjectures.CategoryTheory.DerivedCategory.BifunctorHomBidual
public import WeilConjectures.CategoryTheory.Adjunction.ParametrizedTransport
import WeilConjectures.PoincareDuality.Biduality.ConstructibleDualFullyFaithful
import WeilConjectures.CategoryTheory.RingedForgetTwoInjective.RingedForgetTwoInjectiveHom
import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryClosedTensorModels
import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilRowHomComparison
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgettingMonoidal
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison

/-!
# The double-dual morphism of `ℓ`-adic sheaves

The biduality morphisms `M ⟶ 𝓗om(𝓗om(M, N), N)` of sheaves of `ℚ̄_ℓ,X`-modules
(`CategoryTheory.Mod.bidual`) are natural in `M` and dinatural in `N`; they form an evaluation
(`CochainComplex.BifunctorEvaluation`) for the internal hom
`AlgebraicGeometry.ProEtaleWeilSheaf.ordinaryIhomBifunctor`
(`AlgebraicGeometry.ProEtaleWeilSheaf.ordinaryBifunctorEvaluation`), hence define the double-dual
morphism `M ⟶ Hom(Hom(M, I), I)` of hom complexes of `ℓ`-adic sheaves
(`CochainComplex.bifunctorHomBidual`).
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Opposite MonoidalCategory Functor

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})

/-- The biduality morphisms `M ⟶ 𝓗om(𝓗om(M, N), N)` of `ℓ`-adic sheaves, as an evaluation for
the internal hom bifunctor. -/
noncomputable def ordinaryBifunctorEvaluation :
    CochainComplex.BifunctorEvaluation (ordinaryIhomBifunctor l Y) where
  ev M N := Mod.bidual M N
  naturality f N := Mod.bidual_naturality f N
  dinaturality M _ _ g := Mod.bidual_comp_ihom_map M g

lemma ordinaryBifunctorEvaluation_triangle :
    (ordinaryBifunctorEvaluation l Y).Triangle :=
  fun M N ↦ Mod.bidual_comp_ihomMap_bidual M N

/-- An adjunction `- ⊗ P ⊣ H(P, -)` for every `P`, natural in `P` in the sense of the
evaluations, is an adjunction with a parameter
`(MonoidalCategory.curriedTensor D).flip ⊣₂ curry H`. -/
noncomputable def parametrizedAdjunctionOfTensorRight {D : Type*} [Category* D]
    [MonoidalCategory D] (H : Dᵒᵖ × D ⥤ D)
    (adj : ∀ P : D, MonoidalCategory.tensorRight P ⊣ Prod.sectR (op P) D ⋙ H)
    (nat : ∀ (P P' Q : D) (f : P' ⟶ P),
      (MonoidalCategory.tensorRight P').map (H.map (Prod.mkHom f.op (𝟙 Q))) ≫
          (adj P').counit.app Q =
        (MonoidalCategory.tensorLeft (H.obj (op P, Q))).map f ≫ (adj P).counit.app Q) :
    (curriedTensor D).flip ⊣₂ Functor.curry.obj H :=
  let adj' : ∀ P : D, (curriedTensor D).flip.obj P ⊣ (Functor.curry.obj H).obj (op P) :=
    fun P ↦ adj P
  .mk' adj' (fun {P P'} f {X Q} g ↦ by
    apply ((adj' P).homEquiv X Q).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    have hg : g = ((curriedTensor D).flip.obj P').map ((adj' P').homEquiv X Q g) ≫
        (adj' P').counit.app Q := by
      have h0 := (((adj' P').homEquiv X Q).symm_apply_apply g).symm
      rwa [Adjunction.homEquiv_counit] at h0
    have h := nat P' P Q f
    conv_lhs => rw [hg]
    dsimp at h ⊢
    rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
    erw [h]
    rw [← MonoidalCategory.whisker_exchange_assoc])

/-- The derived hom into a K-injective complex sends quasi-isomorphisms in the first variable to
quasi-isomorphisms, when it has product-total representatives. -/
lemma precompQuasiIso_of_representatives
    {H : (DerivedCategory (ProEtale.AdicSheaf l Y))ᵒᵖ × DerivedCategory (ProEtale.AdicSheaf l Y) ⥤
      DerivedCategory (ProEtale.AdicSheaf l Y)}
    (R : NativeHomRepresentatives (ordinaryIhomBifunctor l Y) H)
    (I : CochainComplex (ProEtale.AdicSheaf l Y) ℤ) [hI : I.IsKInjective] :
    DerivedCategory.PrecompQuasiIso (ordinaryIhomBifunctor l Y) I := by
  intro K L a _
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  have h := R.naturality K L I I hI hI a (𝟙 I)
  rw [CochainComplex.bifunctorHomMapRight_id, Category.comp_id, ← Iso.inv_comp_eq] at h
  rw [← h, DerivedCategory.Q.map_id]
  have : IsIso (Prod.mkHom (DerivedCategory.Q.map a).op (𝟙 (DerivedCategory.Q.obj I)) :
      (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ⟶
        (op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj I)) :=
    ⟨Prod.mkHom (inv (DerivedCategory.Q.map a)).op (𝟙 _), by
      ext <;> simp, by ext <;> simp⟩
  infer_instance

variable {l}

/-- The comparison `D(ℓ-adic sheaves on Z) ⥤ D(condensed ℚ̲̄_ℓ-modules on Z)` of the two models of
`ℓ`-adic complexes: forget the `ℚ̄_ℓ`-linear structure and restrict scalars along the
identification of the coefficient rings. -/
noncomputable abbrev ordinaryToCondensed (Z : Scheme.{u}) :
    DerivedCategory (ProEtale.AdicSheaf l Z) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) Z)) :=
  (ProEtale.AdicSheaf.forgetAb l Z ⋙
    Mod.comap (ProEtale.nativeModuleCoefficientIso l Z).hom).mapDerivedCategory

end AlgebraicGeometry.ProEtaleWeilSheaf

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

variable (X) in
/-- The geometric fibre `X̄` of `X`, as a scheme over the algebraic closure `k̄` of `k₀`. -/
noncomputable abbrev geometricFiberOver : Over (Spec (.of (AlgebraicClosure k₀))) :=
  Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure

instance : Fact (ringChar (AlgebraicClosure k₀)).Prime :=
  ⟨Algebra.ringChar_eq k₀ (AlgebraicClosure k₀) ▸ CharP.char_is_prime k₀ (ringChar k₀)⟩

instance : Fact (ringChar (AlgebraicClosure k₀) ≠ l) :=
  ⟨Algebra.ringChar_eq k₀ (AlgebraicClosure k₀) ▸ Fact.out⟩

instance : LocallyOfFiniteType (geometricFiberOver (k₀ := k₀) X).hom :=
  inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd _ _))

instance : QuasiCompact (geometricFiberOver (k₀ := k₀) X).hom :=
  inferInstanceAs (QuasiCompact (Limits.pullback.snd _ _))

instance : IsSeparated (geometricFiberOver (k₀ := k₀) X).hom :=
  inferInstanceAs (IsSeparated (Limits.pullback.snd _ _))

end AlgebraicGeometry.WeilComplex

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open WeilComplex MonoidalCategory

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

set_option maxHeartbeats 1600000 in
-- Matching the naturality of `mapDerivedCategoryTensorComparison` with `derivedTensor` unfolds the
-- derived tensor products of both models.
/-- **Verdier biduality for `ℓ`-adic complexes on the geometric fibre, at the level of hom
complexes** (blueprint: `det-pd-biduality-coefficients`, case (iv)). Let `I` be a K-injective
complex of `ℓ`-adic sheaves on the geometric fibre `X̄` representing the dualizing complex
`ω_X̄ = Ra^! ℚ̄_ℓ` (`ProEtale.CondensedRing.dualizingComplex`), and `M` a complex of `ℓ`-adic
sheaves which is bounded with constructible cohomology. Then the double-dual morphism
`M ⟶ Hom(Hom(M, I), I)` of hom complexes is a quasi-isomorphism.

The proof reads the constructible biduality of the condensed model,
`ProEtale.CondensedRing.isIso_verdierBiduality`, in the model of `ℓ`-adic sheaves. The
double-dual morphism satisfies the triangle identity, so it is an isomorphism as soon as the
duality `D = RHom(-, I)` is fully faithful (`CategoryTheory.isIso_app_of_bijective_map`). Full
faithfulness is invariant under the coefficient equivalence, which intertwines the two derived
internal homs naturally in the first variable (`ParametrizedAdjunction.transportIso`), and holds in
the condensed model (`ProEtale.CondensedRing.bijective_derivedHom_map_dualizingComplex`). -/
theorem quasiIso_bifunctorHomBidual_ordinary
    {M I : CochainComplex (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ}
    [I.IsKInjective]
    (eI : Nonempty ((ordinaryToCondensed _).obj (DerivedCategory.Q.obj I) ≅
      (ObjectProperty.ι _).obj (ProEtale.CondensedRing.dualizingComplex l (geometricFiberOver X))))
    (hM : ProEtale.constantModelBoundedConstructible (Profinite.padicAlgClRingObj l) _
      ((ordinaryToCondensed _).obj (DerivedCategory.Q.obj M))) :
    QuasiIso (CochainComplex.bifunctorHomBidual
      (ordinaryBifunctorEvaluation l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) M I) := by
  classical
  let Z := geometricFiberOver (k₀ := k₀) X
  let Y := (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let Λ := Profinite.padicAlgClRingObj.{u} l
  -- the hom models and the closed structure of `ℓ`-adic complexes
  obtain ⟨m⟩ := native_two_injective_hom_model (k₀ := k₀) (l := l) (X := X)
  obtain ⟨Mh, -, -, -, -, -⟩ := native_row_hom_comparison k₀ l X m
  obtain ⟨⟨mon, adjS, natS⟩, -, hmon, -⟩ :=
    native_ordinary_closed_tensor_models l Y Mh.ordinaryHom Mh.ordinaryRepresentatives
  subst hmon
  let R := Mh.ordinaryRepresentatives
  have hI := precompQuasiIso_of_representatives l Y R I
  let Ev := ordinaryBifunctorEvaluation l Y
  let G := DerivedCategory.bifunctorRHomOfComplex (ordinaryIhomBifunctor l Y) I
  -- `RHom(-, I)` is the internal hom of the closed structure into `Q I`
  let e0 : DerivedCategory.Q.op ⋙ G ≅
      DerivedCategory.Q.op ⋙ Prod.sectL _ (DerivedCategory.Q.obj I) ⋙ Mh.ordinaryHom :=
    NatIso.ofComponents (fun K ↦ DerivedCategory.bifunctorRHomOfComplexQObjIso _ hI K.unop ≪≫
      (R.model K.unop I inferInstance).symm) (fun {K L} a ↦ by
        have h1 := DerivedCategory.bifunctorRHomOfComplexQObjIso_hom_naturality hI a.unop
        have h2 := R.naturality L.unop K.unop I I inferInstance inferInstance a.unop (𝟙 I)
        rw [CochainComplex.bifunctorHomMapRight_id, Category.comp_id,
          DerivedCategory.Q.map_id] at h2
        dsimp
        rw [reassoc_of% h1]
        rw [Category.assoc]
        refine (cancel_epi (DerivedCategory.bifunctorRHomOfComplexQObjIso _ hI K.unop).hom).2 ?_
        rw [Iso.comp_inv_eq, Category.assoc]
        erw [h2]
        rw [Iso.inv_hom_id_assoc])
  let ψ : G ≅ Prod.sectL _ (DerivedCategory.Q.obj I) ⋙ Mh.ordinaryHom :=
    Localization.liftNatIso DerivedCategory.Q.op
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)).op _ _ _ _ e0
  -- the coefficient equivalence and its tensor comparison
  let U := ProEtale.AdicSheaf.forgetAb l Y
  let V := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (ProEtale.nativeModuleCoefficientIso l Y).hom
  obtain ⟨cU⟩ := ProEtale.nativeScalarForgetting_monoidal l Y
  let : U.Monoidal := cU
  have : U.IsEquivalence := ProEtale.nativeScalarForgetting_isEquivalence l Y
  have : V.IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso
      (ProEtale.nativeModuleCoefficientIso l Y).hom).isEquivalence_functor
  let E0 := U ⋙ V
  let : E0.Monoidal := inferInstanceAs (U ⋙ V).Monoidal
  have : E0.IsEquivalence := inferInstance
  have : E0.PreservesFlat := Functor.preservesFlat_of_isEquivalence E0
  let E := E0.mapDerivedCategory.asEquivalence
  let : BraidedCategory (DerivedCategory (ProEtale.AdicSheaf l Y)) :=
    (DerivedCategory.nonempty_braidedCategory _).some
  let τ : (MonoidalCategory.curriedTensor _).flip ⋙
      (whiskeringRight _ _ _).obj E0.mapDerivedCategory ≅
      E0.mapDerivedCategory ⋙ ProEtale.CondensedRing.derivedTensor Λ Y ⋙
        (whiskeringLeft _ _ _).obj E0.mapDerivedCategory :=
    NatIso.ofComponents (fun P ↦ NatIso.ofComponents (fun Xc ↦
        E0.mapDerivedCategory.mapIso (β_ Xc P) ≪≫
          asIso ((E0.mapDerivedCategoryTensorComparison.app P).app Xc))
      (fun {X₁ X₂} g ↦ by
        dsimp
        rw [← E0.mapDerivedCategory.map_comp_assoc, BraidedCategory.braiding_naturality_left,
          E0.mapDerivedCategory.map_comp_assoc]
        rw [Category.assoc]
        refine (cancel_epi (E0.mapDerivedCategory.map (β_ X₁ P).hom)).2 ?_
        exact (E0.mapDerivedCategoryTensorComparison.app P).naturality g))
      (fun {P P'} f ↦ by
        ext Xc
        dsimp
        rw [← E0.mapDerivedCategory.map_comp_assoc, BraidedCategory.braiding_naturality_right,
          E0.mapDerivedCategory.map_comp_assoc]
        rw [Category.assoc]
        refine (cancel_epi (E0.mapDerivedCategory.map (β_ Xc P).hom)).2 ?_
        exact NatTrans.congr_app (E0.mapDerivedCategoryTensorComparison.naturality f) Xc)
  let c := ParametrizedAdjunction.transportIso
    (parametrizedAdjunctionOfTensorRight Mh.ordinaryHom adjS natS)
    (ProEtale.CondensedRing.derivedTensorHomAdjunction₂ Λ Y) E τ
  obtain ⟨eI⟩ := eI
  let H' := ProEtale.CondensedRing.derivedHom Λ Y
  let ω := (ObjectProperty.ι _).obj (ProEtale.CondensedRing.dualizingComplex l Z)
  -- the derived duals of the two models agree, naturally
  let e : ∀ A, E.functor.obj (G.obj (op A)) ≅ (H'.obj (op (E.functor.obj A))).obj ω := fun A ↦
    E.functor.mapIso (ψ.app (op A)) ≪≫ (c.app (op A)).app (DerivedCategory.Q.obj I) ≪≫
      (H'.obj (op (E.functor.obj A))).mapIso eI
  have he : ∀ {T A : DerivedCategory (ProEtale.AdicSheaf l Y)} (f : T ⟶ A),
      E.functor.map (G.map f.op) ≫ (e T).hom =
        (e A).hom ≫ (H'.map (E.functor.map f).op).app ω := by
    intro T A f
    have h1 := ψ.hom.naturality f.op
    have h2 := NatTrans.congr_app (c.hom.naturality f.op) (DerivedCategory.Q.obj I)
    dsimp [e] at h1 h2 ⊢
    rw [← E.functor.map_comp_assoc, h1, E.functor.map_comp_assoc]
    erw [reassoc_of% h2]
    simp only [Category.assoc]
    congr 2
    exact ((H'.map (E.functor.map f).op).naturality eI.hom).symm
  -- bounded constructibility
  have : IsNoetherian Y :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian Z.hom
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace Z.hom }
  have hpred := (ProEtale.adicConstructibilityPredicateComparison l Y Λ .algebraicClosure).2
  let bc := ProEtale.boundedConstructible (ProEtale.condensedRingObj Λ Y)
  have hbc : ∀ A, bc (E.functor.obj A) → bc (E.functor.obj (G.obj (op A))) := fun A hA ↦
    bc.prop_of_iso (e A).symm
      ((ProEtale.CondensedRing.isMonoidalClosed_boundedConstructible l Z).prop_ihom _ _ hA
        (ProEtale.CondensedRing.dualizingComplex l Z).property)
  -- full faithfulness of the dual
  have hbij : ∀ T A : DerivedCategory (ProEtale.AdicSheaf l Y), bc (E.functor.obj T) →
      bc (E.functor.obj A) → Function.Bijective (fun f : T ⟶ A ↦ G.map f.op) := by
    intro T A hT hA
    have key := ProEtale.CondensedRing.bijective_derivedHom_map_dualizingComplex l (X := Z)
      ⟨_, hT⟩ ⟨_, hA⟩
    have hκ : Function.Bijective (fun h : G.obj (op A) ⟶ G.obj (op T) ↦
        (e A).inv ≫ E.functor.map h ≫ (e T).hom) :=
      (Iso.homCongr (e A) (e T)).bijective.comp (E.fullyFaithfulFunctor.map_bijective _ _)
    rw [← hκ.of_comp_iff']
    convert key.comp (E.fullyFaithfulFunctor.map_bijective T A) using 1
    funext f
    simp only [Function.comp_apply]
    rw [he f, Iso.inv_hom_id_assoc]
    rfl
  have hQM : bc (E.functor.obj (DerivedCategory.Q.obj M)) := (congrFun hpred _).mpr hM
  rw [← DerivedCategory.isIso_bifunctorRHomBidual_app_Q_obj_iff Ev hI M]
  exact isIso_app_of_bijective_map G _
    (DerivedCategory.bifunctorRHomBidual_triangle Ev hI (ordinaryBifunctorEvaluation_triangle l Y))
    _ (hbij _ _ hQM hQM) (hbij _ _ (hbc _ (hbc _ hQM)) hQM)

end AlgebraicGeometry.ProEtaleWeilSheaf
