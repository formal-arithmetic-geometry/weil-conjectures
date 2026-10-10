/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.TateTwistCohomology

/-!
# The Fourier–Deligne transform commutes with Tate twists

The Tate twist `K ↦ K(m) = R𝓗om(ℚ̄_ℓ(m)^∨, K)` of Weil complexes is the constant twist by
`χ_ℓ(σ)^m`: the Tate sheaf `ℚ̄_ℓ(m)` is the constant twist `ℚ̄_ℓ ⊗ 𝓑_{χ_ℓ(σ)^m}`
(`AlgebraicGeometry.WeilSheaf.tateTwistSheafIso`), so its dual is the constant twist by the
inverse unit, and `𝓗om(ℚ̄_ℓ ⊗ 𝓑_b, -) ≅ 𝓗om(ℚ̄_ℓ, -) ⊗ 𝓑_{b⁻¹} ≅ - ⊗ 𝓑_{b⁻¹}`. Constant twists
only rescale the Weil structures, so every `ℚ̄_ℓ`-linear construction commutes with them: the
pullback, the internal hom out of a fixed sheaf, the direct image with compact support and the
shift. Hence so does the Fourier–Deligne transform
`FT_ψ(K) = Rpr₂!(pr₁^* K ⊗ μ^* ℒ_ψ)[1]`, and it commutes with Tate twists.

## Main statements

- `AlgebraicGeometry.nonempty_iso_fourierTransform_tateTwist` (`prop-base-linear`, clause (2)):
  `FT_ψ(K(m)) ≅ FT_ψ(K)(m)`, naturally in the Weil complex `K`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

namespace ProEtaleWeilSheaf

section Ihom

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

variable (k₀ l X) in
/-- Constant twists by equal units are isomorphic functors. -/
noncomputable def constantTwistFunctorCongrIso {b c : (PadicAlgCl l)ˣ} (h : b = c) :
    constantTwist k₀ l X b ≅ constantTwist k₀ l X c :=
  eqToIso (by rw [h])

variable [Fact (ringChar k₀ ≠ l)]

/-- An isomorphism `A ≅ A'` of pro-étale Weil sheaves induces `𝓗om(A', -) ≅ 𝓗om(A, -)`. -/
noncomputable def ihomFunctorMapIsoLeft {A A' : ProEtaleWeilSheaf k₀ l X} (φ : A ≅ A') :
    ihomFunctor k₀ l X A' ≅ ihomFunctor k₀ l X A :=
  NatIso.ofComponents (ihomMapIsoLeft φ) fun f ↦ by
    apply IsoAlgebra.hom_ext
    exact (Mod.ihomMapIso ((IsoAlgebra.forget _).mapIso φ)).hom.naturality f.hom.f

variable (k₀ l X) in
/-- `𝓗om(ℚ̄_ℓ, -)` is the identity of pro-étale Weil sheaves. -/
noncomputable def ihomFunctorAdicConstantIso :
    ihomFunctor k₀ l X (adicConstant k₀ l X) ≅ 𝟭 _ :=
  NatIso.ofComponents ihomAdicConstantIso fun f ↦ by
    apply IsoAlgebra.hom_ext
    exact Mod.ihomRegularIso.hom.naturality f.hom.f

/-- `𝓗om(A ⊗ 𝓑_b, -) ≅ 𝓗om(A, -) ⊗ 𝓑_{b⁻¹}`, the identity on underlying sheaves. -/
noncomputable def ihomFunctorConstantTwistLeftIso (A : ProEtaleWeilSheaf k₀ l X)
    (b : (PadicAlgCl l)ˣ) :
    ihomFunctor k₀ l X ((constantTwist k₀ l X b).obj A) ≅
      ihomFunctor k₀ l X A ⋙ constantTwist k₀ l X b⁻¹ :=
  NatIso.ofComponents (fun B ↦ ihomConstantTwistLeftIso A B b) fun _ ↦ by
    apply IsoAlgebra.hom_ext
    simp [ihomConstantTwistLeftIso]
    rfl

/-- `𝓗om(A, - ⊗ 𝓑_c) ≅ 𝓗om(A, -) ⊗ 𝓑_c`, the identity on underlying sheaves. -/
noncomputable def constantTwistCompIhomFunctorIso (A : ProEtaleWeilSheaf k₀ l X)
    (c : (PadicAlgCl l)ˣ) :
    constantTwist k₀ l X c ⋙ ihomFunctor k₀ l X A ≅
      ihomFunctor k₀ l X A ⋙ constantTwist k₀ l X c :=
  NatIso.ofComponents (fun B ↦ ihomConstantTwistRightIso A B c) fun _ ↦ by
    apply IsoAlgebra.hom_ext
    simp [ihomConstantTwistRightIso]
    rfl

/-- `𝓗om(ℚ̄_ℓ(m)^∨, -)` is the constant twist by `χ_ℓ(σ)^m`. -/
noncomputable def ihomFunctorTateTwistIso (m : ℤ) :
    ihomFunctor k₀ l X ((WeilSheaf.tateTwistSheaf k₀ l X m).dual
        (WeilSheaf.isLisse_tateTwistSheaf k₀ l X m)).obj ≅
      constantTwist k₀ l X (WeilSheaf.cyclotomicUnit k₀ l ^ m) :=
  ihomFunctorMapIsoLeft (WeilSheaf.dualObjIsoOfIso _ _
      (WeilSheaf.tateTwistSheafObjIso k₀ l X m)).symm ≪≫
    ihomFunctorConstantTwistLeftIso _ _ ≪≫
    Functor.isoWhiskerRight (ihomFunctorAdicConstantIso k₀ l X) _ ≪≫ Functor.leftUnitor _ ≪≫
    constantTwistFunctorCongrIso k₀ l X (inv_inv _)

/-- The derived internal hom `R𝓗om(ℚ̄_ℓ(m)^∨, -)` is the constant twist by `χ_ℓ(σ)^m`. -/
noncomputable def rightDerivedFunctorIhomFunctorTateTwistIso (m : ℤ) :
    (ihomFunctor k₀ l X ((WeilSheaf.tateTwistSheaf k₀ l X m).dual
        (WeilSheaf.isLisse_tateTwistSheaf k₀ l X m)).obj).rightDerivedFunctor ≅
      (constantTwist k₀ l X (WeilSheaf.cyclotomicUnit k₀ l ^ m)).mapDerivedCategory :=
  Functor.rightDerivedFunctorNatIso (ihomFunctorTateTwistIso m) ≪≫
    Functor.rightDerivedFunctorIsoMapDerivedCategory _

/-- The derived internal hom out of a pro-étale Weil sheaf commutes with constant twists. -/
noncomputable def mapDerivedCategoryConstantTwistCompRightDerivedIhomIso
    (A : ProEtaleWeilSheaf k₀ l X) (c : (PadicAlgCl l)ˣ) :
    (constantTwist k₀ l X c).mapDerivedCategory ⋙ (ihomFunctor k₀ l X A).rightDerivedFunctor ≅
      (ihomFunctor k₀ l X A).rightDerivedFunctor ⋙ (constantTwist k₀ l X c).mapDerivedCategory :=
  IsoAlgebra.mapDerivedCategoryTwistCompRightDerivedFunctorIso _ _ _
    (constantTwistCompIhomFunctorIso A c)

end Ihom

section UpperStar

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
  (b : (PadicAlgCl l)ˣ)

variable (k₀ l) in
/-- The pullback of pro-étale Weil sheaves commutes with constant twists. -/
noncomputable def constantTwistCompUpperStarIso :
    constantTwist k₀ l Y b ⋙ upperStar k₀ l φ ≅ upperStar k₀ l φ ⋙ constantTwist k₀ l X b :=
  constantTwistCompMapOfNatIsoIso k₀ l b (AdicSheaf.adicUpperStar_map_smul _)
    (adicUpperStarGeometricFiberMapCompFrobeniusIso l φ (comp_over φ _))

variable (k₀ l) in
/-- The derived pullback of pro-étale Weil sheaves commutes with constant twists. -/
noncomputable def mapDerivedCategoryConstantTwistCompUpperStarIso :
    (constantTwist k₀ l Y b).mapDerivedCategory ⋙ (upperStar k₀ l φ).mapDerivedCategory ≅
      (upperStar k₀ l φ).mapDerivedCategory ⋙ (constantTwist k₀ l X b).mapDerivedCategory :=
  IsoAlgebra.mapDerivedCategoryTwistCompMapDerivedCategoryIso _ _ _
    (constantTwistCompUpperStarIso k₀ l φ b)

end UpperStar

end ProEtaleWeilSheaf

section Fourier

variable [Fact (ringChar k₀ ≠ l)]

/-- If `τ₁ ⋙ F ≅ F ⋙ τ₂` and `τ₂ ⋙ G ≅ G ⋙ τ₃`, then `τ₁ ⋙ F ⋙ G ≅ (F ⋙ G) ⋙ τ₃`. -/
private noncomputable def compCommIso {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂]
    [Category C₃] {τ₁ : C₁ ⥤ C₁} {τ₂ : C₂ ⥤ C₂} {τ₃ : C₃ ⥤ C₃} {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₃}
    (e₁ : τ₁ ⋙ F ≅ F ⋙ τ₂) (e₂ : τ₂ ⋙ G ≅ G ⋙ τ₃) : τ₁ ⋙ F ⋙ G ≅ (F ⋙ G) ⋙ τ₃ :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e₁ G ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F e₂ ≪≫ (Functor.associator _ _ _).symm

/-- The Fourier–Deligne transform on the derived categories of pro-étale Weil sheaves,
`K ↦ Rpr₂!(pr₁^* K ⊗ μ^* ℒ_ψ)[1]`, of which `AlgebraicGeometry.fourierTransform` is the
restriction to Weil complexes. -/
private noncomputable abbrev fourierTransformDerived (ψ : AddChar k₀ (PadicAlgCl l)) :
    _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l (affineLine k₀)) ⥤
      _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l (affineLine k₀)) :=
  (ProEtaleWeilSheaf.upperStar k₀ l (affinePlane.fst k₀)).mapDerivedCategory ⋙
    (ProEtaleWeilSheaf.ihomFunctor k₀ l _
      ((fourierKernel ψ).dual (isLisse_fourierKernel ψ)).obj).rightDerivedFunctor ⋙
    ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l (affinePlane.snd k₀)
      (HasCompactification.compactification _
        (hf := hasCompactification_of_over (k₀ := k₀) _)) ⋙
    shiftFunctor _ (1 : ℤ)

/-- The Fourier–Deligne transform of Weil complexes followed by the inclusion into the derived
category is the inclusion followed by `fourierTransformDerived`. -/
private noncomputable def fourierTransformCompιIso (ψ : AddChar k₀ (PadicAlgCl l)) :
    fourierTransform ψ ⋙ (WeilComplex.objectProperty k₀ l (affineLine k₀)).ι ≅
      (WeilComplex.objectProperty k₀ l (affineLine k₀)).ι ⋙ fourierTransformDerived ψ :=
  Functor.isoWhiskerLeft (WeilComplex.upperStar (affinePlane.fst k₀) ⋙
      WeilComplex.tensorLisse (fourierKernel ψ) (isLisse_fourierKernel ψ) ⋙
      WeilComplex.derivedLowerShriek k₀ l (affinePlane.snd k₀))
    ((WeilComplex.objectProperty k₀ l (affineLine k₀)).ι.commShiftIso (1 : ℤ))

/-- The Fourier–Deligne transform on derived categories commutes with constant twists. -/
private noncomputable def constantTwistCompFourierTransformDerivedIso
    (ψ : AddChar k₀ (PadicAlgCl l)) (b : (PadicAlgCl l)ˣ) :
    (ProEtaleWeilSheaf.constantTwist k₀ l (affineLine k₀) b).mapDerivedCategory ⋙
        fourierTransformDerived ψ ≅
      fourierTransformDerived ψ ⋙
        (ProEtaleWeilSheaf.constantTwist k₀ l (affineLine k₀) b).mapDerivedCategory :=
  compCommIso (ProEtaleWeilSheaf.mapDerivedCategoryConstantTwistCompUpperStarIso k₀ l _ b)
    (compCommIso (ProEtaleWeilSheaf.mapDerivedCategoryConstantTwistCompRightDerivedIhomIso _ b)
      (compCommIso
        (ProEtaleWeilSheaf.mapDerivedCategoryConstantTwistCompRightDerivedLowerShriekIso k₀ l
          (affinePlane.snd k₀) b _)
        (((ProEtaleWeilSheaf.constantTwist k₀ l (affineLine k₀) b).mapDerivedCategory.commShiftIso
          (1 : ℤ)).symm)))

-- TODO(unify): sk-prop-base-linear
/-- The Fourier–Deligne transform of Weil complexes on the affine line commutes with the Tate
twist: `FT_ψ(K(m)) ≅ FT_ψ(K)(m)` as Weil complexes, naturally in `K`. This is the Weil
structure part of the second clause of the base linearity proposition; the underlying
statement on étale complexes is `AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_tateTwist`.

The Tate twist is the constant twist by `χ_ℓ(σ)^m`
(`AlgebraicGeometry.ProEtaleWeilSheaf.rightDerivedFunctorIhomFunctorTateTwistIso`), and each
constituent of the Fourier–Deligne transform commutes with constant twists.
(blueprint: `prop-base-linear`, clause (2)) -/
theorem nonempty_iso_fourierTransform_tateTwist (ψ : AddChar k₀ (PadicAlgCl l)) (m : ℤ) :
    Nonempty (WeilComplex.tateTwist k₀ l (affineLine k₀) m ⋙ fourierTransform ψ ≅
      fourierTransform ψ ⋙ WeilComplex.tateTwist k₀ l (affineLine k₀) m) := by
  let P := WeilComplex.objectProperty k₀ l (affineLine k₀)
  let e := ProEtaleWeilSheaf.rightDerivedFunctorIhomFunctorTateTwistIso
    (k₀ := k₀) (l := l) (X := affineLine k₀) m
  refine ⟨((P.fullyFaithfulι.whiskeringRight _).preimageIso ?_)⟩
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (WeilComplex.tateTwist k₀ l (affineLine k₀) m)
      (fourierTransformCompιIso ψ) ≪≫
    (Functor.associator P.ι _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft P.ι e) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft P.ι (constantTwistCompFourierTransformDerivedIso ψ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (fourierTransformCompιIso ψ).symm _ ≪≫
    Functor.isoWhiskerLeft _ e.symm ≪≫
    (Functor.associator (fourierTransform ψ) P.ι _).symm

end Fourier

end AlgebraicGeometry
