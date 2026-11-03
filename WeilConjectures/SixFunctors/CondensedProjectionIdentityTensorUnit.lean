/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FinitePartialPullbackTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FinitePartialPullbackTensor
import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteProjectionFixedCoordinates
import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackTensorComposition
import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FinitePullbackCompositionFixedCoordinates
import WeilConjectures.SixFunctors.ProEtale.RingSheaf.UpperStarSquare
public import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
public import WeilConjectures.SixFunctors.FinitePartialTensorIdentityComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleTensorPreservation

/-! # Tensor compatibility of normalized identity inverse image

Source: latest blueprint, part-appendices/sec-nagata-compactification/
sec-compactifications-and-refinements/sk-def-nagata-sketch-data/sk-prop-sf-pf-coherence/
prop-sf-pf-coherence.proof.md, first paragraph, identity sentence
(blueprint: lem-sf-projection-identity-tensor-unit).

The finite clause uses the published partial tensor comparison. The other three clauses
use ordinary condensed modules and the native derived tensorator and compositor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

private theorem normalized_identity_naturality
    {A : Type*} [Category* A] (U : A ⥤ A) (e : U ≅ 𝟭 A) (M : A) :
    U.map (e.hom.app M) = e.hom.app (U.obj M) := by
  apply (cancel_mono (e.hom.app M)).1
  exact e.hom.naturality (e.hom.app M)

private theorem tensor_identity_of_composition
    {A B : Type*} [Category* A] [Category* B]
    (T : A × B ⥤ A) (U : A ⥤ A) (V : B ⥤ B)
    (μ : T ⋙ U ≅ U.prod V ⋙ T)
    (c : ∀ M, U.obj M ≅ U.obj (U.obj M))
    (d : ∀ L, V.obj L ≅ V.obj (V.obj L))
    (hc : ∀ M L, μ.hom.app (M, L) ≫
        T.map (Prod.mkHom ((c M).hom) ((d L).hom)) =
      (c (T.obj (M, L))).hom ≫ U.map (μ.hom.app (M, L)) ≫
        μ.hom.app (U.obj M, V.obj L))
    (e : U ≅ 𝟭 A) (f : V ≅ 𝟭 B)
    (he : ∀ M, (c M).hom ≫ e.hom.app (U.obj M) = 𝟙 (U.obj M))
    (hf : ∀ L, (d L).hom ≫ f.hom.app (V.obj L) = 𝟙 (V.obj L))
    (M : A) (L : B) :
    μ.hom.app (M, L) ≫ T.map (Prod.mkHom (e.hom.app M) (f.hom.app L)) =
      e.hom.app (T.obj (M, L)) := by
  let ν := μ.hom.app (M, L) ≫ T.map (Prod.mkHom (e.hom.app M) (f.hom.app L))
  have hn := μ.hom.naturality (Prod.mkHom (e.hom.app M) (f.hom.app L))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [normalized_identity_naturality U e M, normalized_identity_naturality V f L] at hn
  have h := congrArg (fun k ↦ k ≫
    T.map (Prod.mkHom (e.hom.app (U.obj M)) (f.hom.app (V.obj L)))) (hc M L)
  have h' : μ.hom.app (M, L) =
      (c (T.obj (M, L))).hom ≫ U.map ν ≫ μ.hom.app (M, L) := by
    have h'' : μ.hom.app (M, L) ≫ T.map (𝟙 (U.obj M, V.obj L)) =
        (c (T.obj (M, L))).hom ≫ U.map ν ≫ μ.hom.app (M, L) := by
      simpa only [ν, Category.assoc, ← T.map_comp, prod_comp, he, hf,
        ← prod_id, ← hn, U.map_comp, Functor.id_obj] using h
    rw [T.map_id (U.obj M, V.obj L)] at h''
    exact (Category.comp_id (μ.hom.app (M, L))).symm.trans h''
  have hν : U.map ν = e.hom.app (U.obj (T.obj (M, L))) := by
    apply (cancel_epi ((c (T.obj (M, L))).hom)).1
    rw [he]
    exact ((cancel_mono (μ.hom.app (M, L))).1 (by
      simpa only [Category.id_comp, Category.assoc] using h')).symm
  have hnν := e.hom.naturality ν
  dsimp only [Functor.id_map] at hnν
  rw [hν] at hnν
  exact ((cancel_epi (e.hom.app (U.obj (T.obj (M, L))))).1 hnν).symm

private theorem fullSubcategory_eqToHom
    {A : Type*} [Category* A] {P : ObjectProperty A}
    {K L : P.FullSubcategory} (h : K = L) :
    (eqToHom h).hom = eqToHom (congrArg ObjectProperty.FullSubcategory.obj h) := by
  cases h
  rfl

private theorem hom_normalization
    {A : Type*} [Category* A] {K K' K'' : A} (t : K = K')
    (c : K ⟶ K'') (e : K'' ⟶ K') (h : c ≫ e = eqToHom t) :
    (eqToHom t.symm ≫ c) ≫ e = 𝟙 K' := by
  rw [Category.assoc, h]
  simp

private theorem compositor_normalization
    {A : Type*} [Category* A] {F : A ⥤ A} (e : F ≅ 𝟭 A)
    {K : A} (K' : A) (h : K = F.obj K')
    (c : K ≅ F.obj (F.obj K'))
    (hc : c.hom ≫ e.hom.app (F.obj K') = eqToHom h) :
    (eqToIso h.symm ≪≫ c).hom ≫ e.hom.app (F.obj K') = 𝟙 (F.obj K') := by
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, hc, eqToHom_trans,
    eqToHom_refl]

/-- The finite coefficient clause, with arbitrary first input and finite-Tor second input.
Source: latest blueprint prop-sf-pf-coherence.proof.md, first paragraph, identity sentence
(blueprint: lem-sf-projection-identity-tensor-unit).
Proof: apply lem-sf-finite-partial-tensor-identity-composition to the explicit comparison.
Lift e through the full finite-Tor inclusion; faithfulness gives its naturality and its
normalization. Naturality at e_M gives U(e_M) = e_(UM). Postcompose the composition square
by tensor(e_(UM),e_(VL)). The two normalizations and naturality of the tensorator reduce
it to mu = c U(nu) mu, where nu = mu tensor(e_M,e_L). Cancel mu and c to get
U(nu) = e_(U(T(M,L))) = U(e_(T(M,L))). Naturality of e at nu and cancellation of its
invertible component give nu = e_(T(M,L)). This includes zero objects, the empty scheme
and n = 1, and imposes no Tor condition on M. -/
theorem finiteProjectionIdentity_tensorUnit
    (S : SixFunctorFiniteOperations D C E n hn)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (e : S.finite.pull (𝟙 X) ≅ 𝟭 (sixFunctorFiniteCategory D C E n hn X))
    (he : ∀ M : sixFunctorFiniteCategory D C E n hn X,
      (S.finite.pullComposition (𝟙 X) (𝟙 X)).hom.app M ≫
          e.hom.app ((S.finite.pull (𝟙 X)).obj M) =
        eqToHom (congrArg (fun f ↦ (S.finite.pull f).obj M)
          (Category.id_comp (𝟙 X))))
    (M : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn X.obj.left) :
    (CompactSupportFiniteProjection.pullbackTensorComparison S (𝟙 X) M L).hom ≫
        ((CompactSupportFiniteProjection.partialTensor S X).map (e.hom.app M)).app
          ((CompactSupportFiniteProjection.torPull S (𝟙 X)).obj L) ≫
        ((CompactSupportFiniteProjection.partialTensor S X).obj M).map
          (ObjectProperty.isoMk (finiteTorConstructible C.l E n hn X.obj.left)
            (X := (CompactSupportFiniteProjection.torPull S (𝟙 X)).obj L) (Y := L)
            ((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι.mapIso
              (e.app ⟨L.obj, L.property.1⟩))).hom =
      e.hom.app (((CompactSupportFiniteProjection.partialTensor S X).obj M).obj L) := by
  let U := S.finite.pull (𝟙 X)
  let V := CompactSupportFiniteProjection.torPull S (𝟙 X)
  let T := Functor.uncurry.obj (CompactSupportFiniteProjection.partialTensor S X)
  let c := fun K ↦
    eqToIso (congrArg (fun f ↦ (S.finite.pull f).obj K)
      (Category.id_comp (𝟙 X)).symm) ≪≫
      (S.finite.pullComposition (𝟙 X) (𝟙 X)).app K
  let d := fun K ↦
    eqToIso (congrArg (fun f ↦ (CompactSupportFiniteProjection.torPull S f).obj K)
      (Category.id_comp (𝟙 X)).symm) ≪≫
      CompactSupportFiniteProjection.torPullComposition S (𝟙 X) (𝟙 X) K
  obtain ⟨μ, hμ, hc⟩ := finitePartialTensor_identityComposition S X
  let f : V ≅ 𝟭 (finiteTorConstructibleCategory C.l E n hn X.obj.left) :=
    NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
      ((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι.mapIso
        (e.app ⟨K.obj, K.property.1⟩))) (by
      intro K K' a
      apply ObjectProperty.hom_ext
      let b : (⟨K.obj, K.property.1⟩ : sixFunctorFiniteCategory D C E n hn X) ⟶
          ⟨K'.obj, K'.property.1⟩ := ObjectProperty.homMk a.hom
      exact congrArg (fun k ↦ k.hom) (e.hom.naturality b))
  have hec : ∀ K, (c K).hom ≫ e.hom.app (U.obj K) = 𝟙 (U.obj K) := by
    intro K
    exact compositor_normalization e K _ _ (he K)
  have hfd : ∀ K, (d K).hom ≫ f.hom.app (V.obj K) = 𝟙 (V.obj K) := by
    intro K
    apply ObjectProperty.hom_ext
    have h := congrArg (fun k ↦ k.hom) (hec ⟨K.obj, K.property.1⟩)
    simpa only [d, c, f, U, V, Iso.trans_hom, Iso.app_hom, eqToIso.hom,
      ObjectProperty.isoMk_hom,
      Functor.mapIso_hom, NatIso.ofComponents_hom_app, ObjectProperty.homMk_hom,
      ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
      CompactSupportFiniteProjection.torPullComposition, fullSubcategory_eqToHom,
      ObjectProperty.ι_map, CompactSupportFiniteProjection.torPull,
      ObjectProperty.lift, ObjectProperty.ιOfLE, Functor.comp_obj,
      ObjectProperty.ι, inducedFunctor_obj, inducedFunctor_map, Functor.id_obj] using h
  have h := tensor_identity_of_composition T U V μ c d hc e f hec hfd M L
  rw [show μ.hom.app (M, L) =
    (CompactSupportFiniteProjection.pullbackTensorComparison S (𝟙 X) M L).hom from
      congrArg Iso.hom (hμ M L)] at h
  exact h

end WeilConjectures

namespace AlgebraicGeometry.ProEtale.CondensedRing

open MonoidalCategory

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Native identity inverse image restricted to the recorded bounded constructible category.
Source: latest blueprint prop-sf-pf-coherence.proof.md, identity sentence, and the
restriction convention of det-def-sf-operations
(blueprint: lem-sf-projection-identity-tensor-unit).
The canonical native identity comparison proves preservation; the functor itself is the
full-subcategory lift of native pullback, with its actual object and morphism maps. -/
def constructibleIdentityPullback (X : Scheme.{u}) :
    ConstantModelBoundedConstructible Λ X ⥤ ConstantModelBoundedConstructible Λ X :=
  (constantModelBoundedConstructible Λ X).lift
    ((constantModelBoundedConstructible Λ X).ι ⋙ L((𝟙 X)^*⟦Λ⟧))
    (fun K ↦ (constantModelConstructibleFiniteTor_wellDefined Λ X).2.1.of_iso
      ((leftDerivedUpperStarId Λ X).app K.obj).symm K.property)

/-- The native condensed identity tensor equation, written through the faithful inclusion.
Source: latest blueprint prop-sf-pf-coherence.proof.md, first paragraph, identity sentence
(blueprint: lem-sf-projection-identity-tensor-unit).
The existential ranges only over proofs that the actual relative tensor is constructible;
it supplies the object property needed to evaluate e at that tensor, not a choice of tensor
or comparison. The normalization uses the raw native compositor and equality transport.
The conclusion uses the native tensorator and the two actual components of e. -/
def ConstructibleIdentityTensorEquation (X : Scheme.{u}) : Prop :=
  ∃ hT : ∀ M L : ConstantModelBoundedConstructible Λ X,
      constantModelBoundedConstructible Λ X (M.obj ⊗ L.obj),
    ∀ e : constructibleIdentityPullback Λ X ≅ 𝟭 (ConstantModelBoundedConstructible Λ X),
      (∀ M : ConstantModelBoundedConstructible Λ X,
        (leftDerivedUpperStarComp Λ (𝟙 X) (𝟙 X)).hom.app M.obj ≫
            (e.hom.app ((constructibleIdentityPullback Λ X).obj M)).hom =
          eqToHom (congrArg (fun f ↦ L((f)^*⟦Λ⟧).obj M.obj)
            (Category.id_comp (𝟙 X)))) →
      ∀ M L : ConstantModelBoundedConstructible Λ X,
        ((leftDerivedUpperStarTensorIso Λ (𝟙 X)).hom.app M.obj).app L.obj ≫
            ((e.hom.app M).hom ⊗ₘ (e.hom.app L).hom) =
          (e.hom.app ⟨M.obj ⊗ L.obj, hT M L⟩).hom

private theorem constructible_identity_tensor_equation (X : Scheme.{u})
    (hT : ∀ M L : ConstantModelBoundedConstructible Λ X,
      constantModelBoundedConstructible Λ X (M.obj ⊗ L.obj)) :
    ConstructibleIdentityTensorEquation Λ X := by
  refine ⟨hT, fun e he M L ↦ ?_⟩
  let P := constantModelBoundedConstructible Λ X
  let U := constructibleIdentityPullback Λ X
  let T : P.FullSubcategory × P.FullSubcategory ⥤ P.FullSubcategory :=
    P.lift (P.ι.prod P.ι ⋙ tensor _)
      (fun ML ↦ hT ML.1 ML.2)
  let μ : T ⋙ U ≅ U.prod U ⋙ T := NatIso.ofComponents
    (fun ML ↦ ObjectProperty.isoMk P
      (((leftDerivedUpperStarTensorIso Λ (𝟙 X)).app ML.1.obj).app ML.2.obj))
    (by
      rintro ⟨K, N⟩ ⟨K', N'⟩ ⟨a, b⟩
      apply ObjectProperty.hom_ext
      exact (leftDerivedUpperStarTensor_naturality Λ (𝟙 X) a.hom b.hom).symm)
  let c : ∀ K, U.obj K ≅ U.obj (U.obj K) := fun K ↦ ObjectProperty.isoMk P
    (eqToIso (congrArg (fun f ↦ L((f)^*⟦Λ⟧).obj K.obj)
      (Category.id_comp (𝟙 X)).symm) ≪≫
      (leftDerivedUpperStarComp Λ (𝟙 X) (𝟙 X)).app K.obj)
  have hc : ∀ K N, μ.hom.app (K, N) ≫
      T.map (Prod.mkHom (c K).hom (c N).hom) =
      (c (T.obj (K, N))).hom ≫ U.map (μ.hom.app (K, N)) ≫
        μ.hom.app (U.obj K, U.obj N) := by
    intro K N
    apply ObjectProperty.hom_ext
    simpa only [μ, c, T, U, P, constructibleIdentityPullback,
      NatIso.ofComponents_hom_app, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.homMk_hom, ObjectProperty.isoMk_hom, Iso.trans_hom, eqToIso.hom,
      Iso.app_hom, Functor.comp_map, Functor.prod_map, ObjectProperty.ι_map,
      ObjectProperty.lift, Functor.comp_obj, Functor.prod_obj, ObjectProperty.ι_obj,
      tensor_obj, tensor_map, leftDerivedUpperStarTensorIso, asIso_hom] using
      (leftDerivedUpperStarTensor_comp_of_eq Λ (𝟙 X) (𝟙 X)
        (Category.id_comp (𝟙 X)).symm K.obj N.obj)
  have hec : ∀ K, (c K).hom ≫ e.hom.app (U.obj K) = 𝟙 (U.obj K) := by
    intro K
    apply ObjectProperty.hom_ext
    simp only [c, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.FullSubcategory.id_hom, ObjectProperty.isoMk_hom,
      ObjectProperty.homMk_hom, Iso.trans_hom, eqToIso.hom, Iso.app_hom]
    exact WeilConjectures.hom_normalization
      (congrArg (fun f ↦ L((f)^*⟦Λ⟧).obj K.obj) (Category.id_comp (𝟙 X)))
      ((leftDerivedUpperStarComp Λ (𝟙 X) (𝟙 X)).hom.app K.obj)
      (e.hom.app (U.obj K)).hom (he K)
  exact congrArg (fun k ↦ k.hom)
    (WeilConjectures.tensor_identity_of_composition T U U μ c c hc e e hec hec M L)

end AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures

open AlgebraicGeometry.ProEtale.CondensedRing

/-- The three higher coefficient clauses in the ordinary condensed categories.
Source: latest blueprint prop-sf-pf-coherence.proof.md, first paragraph, identity sentence
(blueprint: lem-sf-projection-identity-tensor-unit).
Proof: the relative derived tensor restricts to bounded constructible objects at each of
these coefficients. Derive the twice-identity composition square directly from the native
monoidality equation of lem-fix-condensed-pullback-coherence.
Put c = t inverse followed by the compositor. Naturality of e at its own components gives
U(e_M) = e_(UM). For nu = mu tensor(e_M,e_L), postcompose that composition square by
tensor(e_(UM),e_(UL)); the normalizations and naturality give mu = c U(nu) mu. Cancel mu
and compare with c e_(U(T(M,L))) = 1. Thus U(nu) = U(e_(T(M,L))). Naturality of e at nu
and cancellation give the required equation. Faithfulness of the constructible inclusion
identifies this ambient equation with the equation in the constructible category. The
argument includes zero objects and the empty scheme. All comparisons are the native ones.
-/
theorem condensedProjectionIdentity_tensorUnit
    {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)
    (E : PadicAlgCl.FiniteIntermediateField C.l)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom] :
    ConstructibleIdentityTensorEquation (Profinite.padicIntegersRingObj C.l E) X.obj.left ∧
    ConstructibleIdentityTensorEquation (Profinite.continuousMapRingObj E) X.obj.left ∧
    ConstructibleIdentityTensorEquation (Profinite.padicAlgClRingObj C.l) X.obj.left := by
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  have hcard : Fintype.card D.k₀ = D.p ^ D.a := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hcard
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let : Fact (ringChar D.k ≠ C.l) := ⟨by
    rw [ringChar.eq D.k D.p]
    exact C.different.symm⟩
  let : LocallyOfFiniteType X.obj.hom := X.property.1
  let : QuasiCompact X.obj.hom := X.property.2
  let : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  let : IsLocallyNoetherian X.obj.left := LocallyOfFiniteType.isLocallyNoetherian X.obj.hom
  have hO := (adicConstructibilityPredicateComparison C.l X.obj.left
    (Profinite.padicIntegersRingObj C.l E) (.integral E)).2
  have hE := (adicConstructibilityPredicateComparison C.l X.obj.left
    (Profinite.continuousMapRingObj E) (.continuous E)).2
  have hQ := (adicConstructibilityPredicateComparison C.l X.obj.left
    (Profinite.padicAlgClRingObj C.l) .algebraicClosure).2
  refine ⟨constructible_identity_tensor_equation _ _ ?_,
    constructible_identity_tensor_equation _ _ ?_,
    constructible_identity_tensor_equation _ _ ?_⟩
  · intro M L
    have h := PadicIntegersRingObj.boundedConstructible_tensor_closure (X := X.obj) C.l E
      M.obj L.obj (by rw [hO]; exact M.property) (by rw [hO]; exact L.property)
    rw [hO] at h
    exact h
  · intro M L
    have h := ContinuousMapRingObj.boundedConstructible_tensor_closure (X := X.obj) C.l E
      M.obj L.obj (by rw [hE]; exact M.property) (by rw [hE]; exact L.property)
    rw [hE] at h
    exact h
  · intro M L
    have h := boundedConstructible_tensor_closure (X := X.obj) C.l
      M.obj L.obj (by rw [hQ]; exact M.property) (by rw [hQ]; exact L.property)
    rw [hQ] at h
    exact h

end WeilConjectures
