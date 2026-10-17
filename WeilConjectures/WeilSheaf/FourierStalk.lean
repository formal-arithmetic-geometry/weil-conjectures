/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.ArtinSchreierDual
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.DirectImageRestriction
public import WeilConjectures.WeilSheaf.DirectImageStalk
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.WeilSheaf.FourierInversion.UpperStar
public import WeilConjectures.WeilSheaf.FourierTateTwist
public import WeilConjectures.WeilSheaf.HomologyShift
public import WeilConjectures.WeilSheaf.LisseLocus
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
public import WeilConjectures.WeilSheaf.Stalk
public import WeilConjectures.WeilSheaf.StalkFrobenius
public import WeilConjectures.WeilSheaf.TraceFunctionOps

/-!
# Stalks of the Fourier–Deligne transform at rational points

At a `k₀`-rational point `a` of the dual line, the stalk of the Fourier–Deligne transform of a
Weil complex `K` is the compactly supported cohomology of `K ⊗ ℒ_{ψ(a x)}`, shifted by one, with
its Frobenius: this is the stalk formula of the transform, a consequence of compact support base
change along `a : Spec k₀ ⟶ 𝔸¹`. Tensoring with a lisse Weil sheaf isomorphic to the
constant sheaf does nothing; this applies at the origin, where the kernel `ℒ_{ψ(0 · x)}` is
constant.

The stalk of a Weil sheaf on `Spec k₀` at its point is its global sections: the geometric point
is an isomorphism `Spec k̄ ≅ Spec k₀ ×_{k₀} k̄`. The stalk of `𝓗ʳ FT_ψ(K)` at `a` is therefore
`Hʳ(Spec k̄, a^* FT_ψ(K))`, and compact support base change for the cartesian square formed by
the fibre `x ↦ (x, a)` of `pr₂ : 𝔸² ⟶ 𝔸¹` identifies `a^* Rpr₂!` with `RΓ_c` of the fibre.

## Main declarations

- `AlgebraicGeometry.affineLine.rationalPoint`: the closed point `x = a` of `𝔸¹_{k₀}`.
- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_globalSections_of_spec`: the stalk of a Weil
  sheaf on `Spec k₀` is its global sections, with the Frobenius.
- `AlgebraicGeometry.affinePlane.isPullback_sndFiberIncl`: the line `x ↦ (x, a)` is the fibre of
  `pr₂` over `a`.
- `AlgebraicGeometry.nonempty_equiv_stalk_homologySheaf_fourierTransform_rationalPoint`: the
  stalk formula at rational points (blueprint `lem-fd-stalk-formula`).
- `AlgebraicGeometry.WeilComplex.tensorLisseObjIsoOfIso`: tensoring with a Weil sheaf isomorphic
  to `ℚ̄_ℓ` is the identity.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

variable (k₀) in
/-- The `k₀`-rational point `x = a` of the affine line, as a closed point. -/
noncomputable def affineLine.rationalPoint (a : k₀) : (affineLine k₀).finitePoints :=
  ⟨(AffineSpace.homOfVector (𝟙 (Spec (CommRingCat.of k₀)))
      fun _ ↦ (Scheme.ΓSpecIso (.of k₀)).inv.hom a).base (IsLocalRing.closedPoint k₀),
    Scheme.Hom.mem_finitePoints_of_comp_eq_id (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) _
      (AffineSpace.homOfVector_over _ _) _⟩

namespace WeilComplex

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The derived internal hom `R𝓗om(F^∨, -)` out of the dual of a Weil sheaf `F ≅ ℚ̄_ℓ` is the
identity: `F^∨ ≅ 𝓗om(ℚ̄_ℓ, ℚ̄_ℓ) ≅ ℚ̄_ℓ`, the functor `𝓗om(ℚ̄_ℓ, -)` is the identity, and so is
its derived functor. -/
noncomputable def rightDerivedFunctorIhomFunctorDualIsoOfIso (F : WeilSheaf k₀ l X)
    (hF : F.IsLisse) (e : F ≅ WeilSheaf.adicConstant k₀ l X) :
    (ProEtaleWeilSheaf.ihomFunctor k₀ l X (F.dual hF).obj).rightDerivedFunctor ≅
      𝟭 (_root_.DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :=
  have eD : (F.dual hF).obj ≅ ProEtaleWeilSheaf.adicConstant k₀ l X :=
    (ProEtaleWeilSheaf.ihomMapIsoLeft ((ObjectProperty.ι _).mapIso e).symm _) ≪≫
      ProEtaleWeilSheaf.ihomAdicConstantIso _
  Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.ihomFunctorMapIsoLeft eD.symm ≪≫
      ProEtaleWeilSheaf.ihomFunctorAdicConstantIso k₀ l X) ≪≫
    Functor.rightDerivedFunctorIsoMapDerivedCategory _ ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Tensoring with a lisse Weil sheaf `F ≅ ℚ̄_ℓ` does not change a Weil complex. -/
noncomputable def tensorLisseObjIsoOfIso (F : WeilSheaf k₀ l X) (hF : F.IsLisse)
    (e : F ≅ WeilSheaf.adicConstant k₀ l X) (K : WeilComplex k₀ l X) :
    (tensorLisse F hF).obj K ≅ K :=
  ObjectProperty.isoMk _ ((rightDerivedFunctorIhomFunctorDualIsoOfIso F hF e).app K.obj)

end WeilComplex


namespace WeilSheaf

open scoped ProEtale

/-- An isomorphism of Frobenius modules given by a bijective linear map intertwining the two
Frobenius automorphisms. -/
noncomputable def _root_.FrobeniusModule.Equiv.ofBijective {K : Type*} [Field K]
    {M N : FrobeniusModule K} (f : M.carrier →ₗ[K] N.carrier) (hf : Function.Bijective f)
    (h : ∀ x, f (M.frobenius x) = N.frobenius (f x)) : M.Equiv N where
  toLinearEquiv := LinearEquiv.ofBijective f hf
  map_frobenius x := (LinearEquiv.ofBijective_apply _ _).trans
    ((h x).trans (congrArg N.frobenius (LinearEquiv.ofBijective_apply _ _).symm))

section GlobalSectionsToStalk

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l X)
  (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 1).hom =
    (specGeometricFrobenius k₀ ^ 1).hom ≫ s)

/-- The restriction `Γ(X̄, F) ⟶ F_s` of global sections to the stalk at a geometric point `s`
with `s ≫ Fr = σ ≫ s`, as a linear map of the underlying spaces of the Frobenius modules. -/
noncomputable def globalSectionsToStalkAt :
    F.globalSections.carrier →ₗ[PadicAlgCl l] (F.stalkAt s 1 hs).carrier :=
  ((WeilCoefficients.toModuleCat l).map (F.globalSectionsToStalkObj s)).hom

theorem globalSectionsToStalkAt_apply (y : F.globalSections.carrier) :
    globalSectionsToStalkAt F s hs y =
      ((WeilCoefficients.toModuleCat l).map (F.globalSectionsToStalkObj s)).hom y :=
  rfl

/-- The restriction of global sections to the stalk intertwines the Frobenius automorphisms. -/
theorem globalSectionsToStalkAt_frobenius (a : F.globalSections.carrier) :
    globalSectionsToStalkAt F s hs (F.globalSections.frobenius a) =
      (F.stalkAt s 1 hs).frobenius (globalSectionsToStalkAt F s hs a) :=
  (globalSectionsToStalkAt_apply F s hs _).trans
    ((F.globalSectionsToStalkObj_frobenius s hs a).trans
      (congrArg (F.stalkAt s 1 hs).frobenius (globalSectionsToStalkAt_apply F s hs a).symm))

theorem bijective_globalSectionsToStalkAt [IsIso (F.globalSectionsToStalkObj s)] :
    Function.Bijective (globalSectionsToStalkAt F s hs) := by
  rw [show ⇑(globalSectionsToStalkAt F s hs) = fun y ↦
      ((WeilCoefficients.toModuleCat l).map (F.globalSectionsToStalkObj s)).hom y from
    funext (globalSectionsToStalkAt_apply F s hs)]
  exact ConcreteCategory.bijective_of_isIso
    ((WeilCoefficients.toModuleCat l).map (F.globalSectionsToStalkObj s))

/-- If the restriction `Γ(X̄, F) ⟶ F_s` of global sections to the stalk at a geometric point `s`
with `s ≫ Fr = σ ≫ s` is an isomorphism, it is an isomorphism of Frobenius modules. -/
noncomputable def globalSectionsEquivStalkAt [IsIso (F.globalSectionsToStalkObj s)] :
    F.globalSections.Equiv (F.stalkAt s 1 hs) :=
  FrobeniusModule.Equiv.ofBijective _ (bijective_globalSectionsToStalkAt F s hs)
    (globalSectionsToStalkAt_frobenius F s hs)

end GlobalSectionsToStalk

/-- **The stalk of a Weil sheaf on `Spec k₀` is its global sections.** The geometric fibre of
`Spec k₀` over itself is `Spec k̄`, so the geometric point `s` at the (unique) point `x` is an
isomorphism; the restriction `Γ(Spec k̄, G) ⟶ Γ(Spec k̄, s^* G) = G_s` of global sections to the
stalk is then an isomorphism, and it intertwines the two Frobenius automorphisms. -/
theorem nonempty_equiv_stalk_globalSections_of_spec
    (G : WeilSheaf k₀ l (Spec (CommRingCat.of k₀))) (x : (Spec (CommRingCat.of k₀)).finitePoints) :
    Nonempty ((G.stalk x).Equiv G.globalSections) := by
  set f := Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)
  set s := f.geometricFiberPointOfFinitePoint x with hs_def
  -- `s` is an isomorphism: it is a section of the isomorphism `X̄ = Spec k₀ ×_{k₀} k̄ ⟶ Spec k̄`
  have hs₁ : s ≫ f.geometricFiberToAlgebraicClosure = 𝟙 _ := by
    simp only [hs_def, Scheme.Hom.geometricFiberPointOfFinitePoint,
      Scheme.Hom.geometricFiberPoint, Scheme.Hom.geometricFiberToAlgebraicClosure,
      pullback.lift_snd]
  have : IsIso f.geometricFiberToAlgebraicClosure := by
    unfold Scheme.Hom.geometricFiberToAlgebraicClosure
    infer_instance
  have : IsIso s := by
    rw [IsIso.eq_inv_of_inv_hom_id hs₁]
    infer_instance
  -- hence the unit of `s^* ⊣ s_*` is an isomorphism, and so is the restriction to the stalk
  have : ((s)_*[WeilCoefficients.{u} l]).IsEquivalence :=
    (ProEtale.lowerStarEquivalence _ (asIso s)).isEquivalence_functor
  have := (ProEtale.upperStarLowerStarAdjunction (WeilCoefficients.{u} l)
    s).isEquivalence_left_of_isEquivalence_right
  have : IsIso (G.globalSectionsToStalkObj s) := by
    unfold globalSectionsToStalkObj
    infer_instance
  -- the point `x` has degree one
  have hdeg : f.degreeOver x.1 = 1 := by
    simpa using Scheme.Hom.degreeOver_eq_one_of_comp_eq_id f (𝟙 _) (by simp [f]) x.1
  have hx := f.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow x
  have hs : s ≫ (f.geometricGaloisFrobenius ^ 1).hom =
      (specGeometricFrobenius k₀ ^ 1).hom ≫ s := by
    rw [← hdeg]
    exact hx
  obtain ⟨E⟩ := nonempty_equiv_stalkAt_of_eq G s hdeg hx hs
  exact ⟨E.trans (FrobeniusModule.Equiv.symm
    (globalSectionsEquivStalkAt G s hs))⟩

end WeilSheaf

/-- The `k₀`-rational point `a : Spec k₀ ⟶ 𝔸¹`, a section of the structure morphism. -/
noncomputable abbrev affineLine.rationalSection (a : k₀) :
    Spec (CommRingCat.of k₀) ⟶ affineLine k₀ :=
  AffineSpace.homOfVector (𝟙 (Spec (CommRingCat.of k₀)))
    fun _ ↦ (Scheme.ΓSpecIso (.of k₀)).inv.hom a

instance (a : k₀) : (affineLine.rationalSection a).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨AffineSpace.homOfVector_over _ _⟩

/-- The fibre `x ↦ (x, a)` of the second projection `pr₂ : 𝔸² ⟶ 𝔸¹` over `a ∈ k₀`. -/
noncomputable def affinePlane.sndFiberIncl (a : k₀) : affineLine k₀ ⟶ affinePlane k₀ :=
  pullback.lift (𝟙 _) ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)) ≫ affineLine.rationalSection a)
    (by simp)

omit [Finite k₀] in
@[reassoc (attr := simp)]
lemma affinePlane.sndFiberIncl_fst (a : k₀) :
    affinePlane.sndFiberIncl a ≫ affinePlane.fst k₀ = 𝟙 _ :=
  pullback.lift_fst _ _ _

omit [Finite k₀] in
@[reassoc (attr := simp)]
lemma affinePlane.sndFiberIncl_snd (a : k₀) :
    affinePlane.sndFiberIncl a ≫ affinePlane.snd k₀ =
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) ≫ affineLine.rationalSection a :=
  pullback.lift_snd _ _ _

instance (a : k₀) : (affinePlane.sndFiberIncl a).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨by
    change _ ≫ pullback.fst _ _ ≫ _ = _
    rw [affinePlane.sndFiberIncl, pullback.lift_fst_assoc, Category.id_comp]⟩

omit [Finite k₀] in
/-- The line `x ↦ (x, a)` is the fibre of the second projection over `a`. -/
lemma affinePlane.isPullback_sndFiberIncl (a : k₀) :
    IsPullback (affinePlane.sndFiberIncl a) (affineLine k₀ ↘ Spec (CommRingCat.of k₀))
      (affinePlane.snd k₀) (affineLine.rationalSection a) := by
  refine IsPullback.of_right ?_ (affinePlane.sndFiberIncl_snd a)
    (IsPullback.of_hasPullback (affineLine k₀ ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
  have h₁ : affinePlane.sndFiberIncl a ≫ pullback.fst _ _ = 𝟙 _ := affinePlane.sndFiberIncl_fst a
  have h₂ : affineLine.rationalSection a ≫ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) = 𝟙 _ :=
    AffineSpace.homOfVector_over _ _
  rw [h₁, h₂]
  exact IsPullback.id_horiz _

omit [Finite k₀] in
/-- Along the line `x ↦ (x, a)` the multiplication `μ` restricts to `x ↦ a x`. -/
lemma affinePlane.sndFiberIncl_mul (a : k₀) :
    affinePlane.sndFiberIncl a ≫ affinePlane.mul k₀ = affineLine.smul k₀ a := by
  refine AffineSpace.hom_ext ?_ fun _ ↦ ?_
  · rw [Category.assoc, affinePlane.mul, AffineSpace.homOfVector_over, affineLine.smul,
      AffineSpace.smul_over]
    exact comp_over (affinePlane.sndFiberIncl a) _
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, affinePlane.mul,
      AffineSpace.homOfVector_appTop_coord, map_mul, ← CommRingCat.comp_apply,
      ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
      affinePlane.sndFiberIncl_fst, affinePlane.sndFiberIncl_snd, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, AffineSpace.homOfVector_appTop_coord, affineLine.smul,
      AffineSpace.smul_appTop_coord, mul_comm]
    rfl

/-- The Fourier kernel is the pullback of `ℒ_ψ` along the multiplication. -/
lemma fourierKernel_eq (ψ : AddChar k₀ (PadicAlgCl l)) :
    fourierKernel ψ = (WeilSheaf.upperStar (affinePlane.mul k₀)).obj (artinSchreier ψ 1) :=
  rfl

omit [Finite k₀] in
/-- Multiplication by `a` followed by multiplication by `1` is multiplication by `a`. -/
lemma affineLine.smul_comp_smul_one (a : k₀) :
    affineLine.smul k₀ a ≫ affineLine.smul k₀ 1 = affineLine.smul k₀ a := by
  refine AffineSpace.hom_ext ?_ fun _ ↦ ?_
  · simp [affineLine.smul]
  · simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, affineLine.smul,
      AffineSpace.smul_appTop_coord, map_one, one_mul]

/-- Along the line `x ↦ (x, a)`, the Fourier kernel `μ^* ℒ_ψ` restricts to `ℒ_{ψ(a x)}`. -/
theorem nonempty_iso_upperStar_sndFiberIncl_fourierKernel (ψ : AddChar k₀ (PadicAlgCl l))
    (a : k₀) :
    Nonempty ((WeilSheaf.upperStar (affinePlane.sndFiberIncl a)).obj (fourierKernel ψ) ≅
      artinSchreier ψ a) := by
  obtain ⟨I, hI⟩ : ∃ I : WeilSheaf k₀ l (affineLine k₀), ∀ b : k₀,
      Nonempty (artinSchreier ψ b ≅ (WeilSheaf.upperStar (affineLine.smul k₀ b)).obj I) :=
    ⟨_, fun _ ↦ ⟨Iso.refl _⟩⟩
  rw [fourierKernel_eq]
  exact ⟨(WeilSheaf.nonempty_iso_upperStar_comp (affinePlane.sndFiberIncl a) (affinePlane.mul k₀)
      (artinSchreier ψ 1)).some.symm ≪≫
    (WeilSheaf.nonempty_iso_upperStar_of_eq (affinePlane.sndFiberIncl_mul a)
      (artinSchreier ψ 1)).some ≪≫
    (WeilSheaf.upperStar (affineLine.smul k₀ a)).mapIso (hI 1).some ≪≫
    (WeilSheaf.nonempty_iso_upperStar_comp (affineLine.smul k₀ a) (affineLine.smul k₀ 1)
      I).some.symm ≪≫
    (WeilSheaf.nonempty_iso_upperStar_of_eq (affineLine.smul_comp_smul_one a) I).some ≪≫
    (hI a).some.symm⟩

/-- Along the line `x ↦ (x, a)`, the integrand `pr₁^* K ⊗ μ^* ℒ_ψ` of the Fourier transform
restricts to `K ⊗ ℒ_{ψ(a x)}`. -/
theorem nonempty_iso_upperStar_sndFiberIncl_fourierIntegrand (ψ : AddChar k₀ (PadicAlgCl l))
    (K : WeilComplex k₀ l (affineLine k₀)) (a : k₀) :
    Nonempty ((WeilComplex.upperStar (affinePlane.sndFiberIncl a)).obj
      ((WeilComplex.tensorLisse (fourierKernel ψ) (isLisse_fourierKernel ψ)).obj
        ((WeilComplex.upperStar (affinePlane.fst k₀)).obj K)) ≅
      (WeilComplex.tensorLisse (artinSchreier ψ a) (isLisse_artinSchreier ψ a)).obj K) := by
  obtain ⟨t₁⟩ := WeilComplex.nonempty_iso_tensorLisse_comp_upperStar
    (affinePlane.sndFiberIncl a) (fourierKernel ψ) (isLisse_fourierKernel ψ)
  obtain ⟨u₁⟩ := WeilComplex.nonempty_iso_upperStar_comp (k₀ := k₀) (l := l)
    (affinePlane.sndFiberIncl a) (affinePlane.fst k₀)
  have key : ∀ (φ : affineLine k₀ ⟶ affineLine k₀) (_ : φ.IsOver (Spec (CommRingCat.of k₀))),
      φ = 𝟙 _ → Nonempty (WeilComplex.upperStar (k₀ := k₀) (l := l) φ ≅ 𝟭 _) := by
    rintro φ _ rfl
    exact WeilComplex.nonempty_iso_upperStar_id
  obtain ⟨u₀⟩ := key _ inferInstance (affinePlane.sndFiberIncl_fst a)
  obtain ⟨t₂⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso
    (nonempty_iso_upperStar_sndFiberIncl_fourierKernel ψ a).some
    ((isLisse_fourierKernel ψ).upperStar (affinePlane.sndFiberIncl a)) (isLisse_artinSchreier ψ a)
  exact ⟨t₁.app _ ≪≫ (WeilComplex.tensorLisse _ _).mapIso ((u₁.app K).symm ≪≫ u₀.app K) ≪≫
    t₂.app K⟩

/-- **Stalks of the Fourier transform are fibre integrals**, at the `k₀`-rational points of the
dual line: for a Weil complex `K` on `𝔸¹` and `a ∈ k₀`, the stalk of `𝓗ʳ FT_ψ(K)` at the point
`a` is `H_c^{r+1}(𝔸¹ ⊗ k̄, K ⊗ ℒ_{ψ(a x)})`, with its Frobenius. The fibre of the second
projection over `a` is the line `x ↦ (x, a)`, along which the kernel `μ^* ℒ_ψ` restricts to
`ℒ_{ψ(a x)}`, and compact support base change along `a : Spec k₀ ⟶ 𝔸¹` identifies the stalk of
`Rpr₂!` with the compactly supported cohomology of the fibre, compatibly with the Weil
structures; the shift `[1]` of the transform moves `r` to `r + 1`.
(blueprint: `lem-fd-stalk-formula`) -/
theorem nonempty_equiv_stalk_homologySheaf_fourierTransform_rationalPoint
    (ψ : AddChar k₀ (PadicAlgCl l)) (K : WeilComplex k₀ l (affineLine k₀)) (a : k₀) (r : ℤ) :
    Nonempty ((((WeilComplex.homologySheaf r).obj ((fourierTransform ψ).obj K)).stalk
      (affineLine.rationalPoint k₀ a)).Equiv
        (((WeilComplex.tensorLisse (artinSchreier ψ a) (isLisse_artinSchreier ψ a)).obj
          K).compactlySupportedCohomology (r + 1))) := by
  let σ := affineLine.rationalSection a
  have hσ : σ ≫ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) = 𝟙 _ :=
    AffineSpace.homOfVector_over _ _
  have hpt := Scheme.Hom.mem_finitePoints_of_comp_eq_id
    (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)) (𝟙 _) (by simp)
    (IsLocalRing.closedPoint k₀)
  have hdeg := Scheme.Hom.degreeOver_eq_one_of_comp_eq_id
    (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)) (𝟙 _) (by simp)
    (IsLocalRing.closedPoint k₀)
  simp only [Scheme.Hom.id_base, TopCat.hom_id, ContinuousMap.id_apply] at hpt hdeg
  let pt : (Spec (CommRingCat.of k₀)).finitePoints := ⟨IsLocalRing.closedPoint k₀, hpt⟩
  -- the stalk at `a` is the stalk of the pullback along `a : Spec k₀ ⟶ 𝔸¹`
  obtain ⟨E₁⟩ := WeilSheaf.nonempty_equiv_stalk_upperStar σ
    ((WeilComplex.homologySheaf r).obj ((fourierTransform ψ).obj K)) pt
    (affineLine.rationalPoint k₀ a) rfl (by
      rw [hdeg]
      exact (Scheme.Hom.degreeOver_eq_one_of_comp_eq_id _ σ hσ _).symm)
  -- a Weil sheaf on `Spec k₀` is its global sections
  obtain ⟨E₂⟩ := WeilSheaf.nonempty_equiv_stalk_globalSections_of_spec
    ((WeilSheaf.upperStar σ).obj
      ((WeilComplex.homologySheaf r).obj ((fourierTransform ψ).obj K))) pt
  -- compact support base change along `a`, and the restriction of the integrand to the fibre
  obtain ⟨bc⟩ := WeilComplex.nonempty_upperStar_derivedLowerShriek_iso (k₀ := k₀) (l := l)
    (affinePlane.isPullback_sndFiberIncl a)
  obtain ⟨eN⟩ := nonempty_iso_upperStar_sndFiberIncl_fourierIntegrand ψ K a
  let M := (WeilComplex.tensorLisse (fourierKernel ψ) (isLisse_fourierKernel ψ)).obj
    ((WeilComplex.upperStar (affinePlane.fst k₀)).obj K)
  let L := (WeilComplex.derivedLowerShriek k₀ l (affinePlane.snd k₀)).obj M
  let T := (WeilComplex.tensorLisse (artinSchreier ψ a) (isLisse_artinSchreier ψ a)).obj K
  let eF : (WeilComplex.upperStar σ).obj ((fourierTransform ψ).obj K) ≅
      ((WeilComplex.derivedLowerShriek k₀ l (affineLine k₀ ↘ Spec (CommRingCat.of k₀))).obj
        T)⟦(1 : ℤ)⟧ :=
    ((WeilComplex.upperStar σ).commShiftIso (1 : ℤ)).app L ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso (bc.app M ≪≫
      (WeilComplex.derivedLowerShriek k₀ l (affineLine k₀ ↘ Spec (CommRingCat.of k₀))).mapIso eN)
  let Ψ := (WeilComplex.homologySheafUpperStarIso σ r _).symm ≪≫
    (WeilComplex.homologySheaf r).mapIso eF ≪≫
    WeilComplex.homologySheafShiftIso _ 1 r (r + 1) (by omega)
  exact ⟨E₁.symm.trans (E₂.trans (WeilSheaf.globalSectionsEquivOfIso Ψ))⟩

end AlgebraicGeometry
