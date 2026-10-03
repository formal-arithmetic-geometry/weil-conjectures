/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.Mathlib.RingTheory.Etale.FiberDegree

/-!
# The degree of the fibre of an affine morphism at a point

For an affine morphism `g : U ⟶ X` and a point `x : X`, the scheme-theoretic fibre `g.fiber x`
is an affine scheme over `Spec κ(x)`, and we define `g.fiberDegree x` as the `κ(x)`-dimension
of its ring of global sections.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.ΓAlgebra`: for `h : Z ⟶ Spec R`, the ring of global sections
  of `Z` as an `R`-algebra.
- `AlgebraicGeometry.Scheme.Hom.finrankΓ`: the `R`-dimension of that algebra. For a finite
  group scheme over a field this is its order.
- `AlgebraicGeometry.Scheme.Hom.fiberDegree`: the degree of the fibre of an affine morphism
  at a point.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.finrankΓ_eq_of_iso`: `finrankΓ` is invariant under an
  isomorphism of schemes over an isomorphism of affine bases.
- `AlgebraicGeometry.Scheme.Hom.fiberDegree_of_isPullback`: the fibre degree is invariant under
  base change.
- `AlgebraicGeometry.Scheme.Hom.fiberDegree_of_isIso`: an isomorphism has fibre degree `1`.
- `AlgebraicGeometry.Scheme.Hom.isEmpty_of_forall_fiberDegree_eq_zero`: an étale morphism all of
  whose fibre degrees vanish has empty source.
- `AlgebraicGeometry.Scheme.Hom.fiberDegree_of_isCompl`: the fibre degree is additive in
  complementary open (and closed) subschemes of the source.
- `AlgebraicGeometry.Scheme.Hom.fiberDegree_SpecMap`: comparison with the ring-theoretic
  `Ideal.fiberDegree`.
- `AlgebraicGeometry.Scheme.Hom.fiberDegree_morphismRestrict`: compatibility with restriction
  to an open of the target.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

section ΓAlgebra

variable {Z : Scheme.{u}} {R : CommRingCat.{u}}

/-- For `h : Z ⟶ Spec R`, the ring of global sections of `Z` as an `R`-algebra. -/
@[instance_reducible]
noncomputable def Scheme.Hom.ΓAlgebra (h : Z ⟶ Spec R) : Algebra R Γ(Z, ⊤) :=
  ((Scheme.ΓSpecIso R).inv ≫ h.appTop).hom.toAlgebra

lemma Scheme.Hom.algebraMap_ΓAlgebra (h : Z ⟶ Spec R) :
    letI := h.ΓAlgebra
    algebraMap R Γ(Z, ⊤) = ((Scheme.ΓSpecIso R).inv ≫ h.appTop).hom :=
  rfl

/-- The `R`-dimension of the ring of global sections of a scheme over `Spec R`.

For a finite group scheme `G` over a field `K` this is its *order* `|G| = dim_K Γ(G, 𝒪_G)`. -/
noncomputable def Scheme.Hom.finrankΓ (h : Z ⟶ Spec R) : ℕ :=
  letI := h.ΓAlgebra
  Module.finrank R Γ(Z, ⊤)

/-- An isomorphism of schemes over an isomorphism of affine bases induces an isomorphism of
rings of global sections compatible with the algebra structures. -/
lemma Scheme.Hom.finrankΓ_eq_of_iso {Z Z' : Scheme.{u}} {R R' : CommRingCat.{u}}
    (h : Z ⟶ Spec R) (h' : Z' ⟶ Spec R') (e : Z ≅ Z') (i : R ≅ R')
    (he : e.hom ≫ h' ≫ Spec.map i.hom = h) :
    h.finrankΓ = h'.finrankΓ := by
  let _ := h.ΓAlgebra
  let _ := h'.ΓAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv i.commRingCatIsoToRingEquiv
    (asIso e.inv.appTop).commRingCatIsoToRingEquiv ?_
  have he' : e.inv ≫ h = h' ≫ Spec.map i.hom := by
    rw [← he, Iso.inv_hom_id_assoc]
  change ((ΓSpecIso R').inv ≫ h'.appTop).hom.comp i.hom.hom =
    e.inv.appTop.hom.comp ((ΓSpecIso R).inv ≫ h.appTop).hom
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Category.assoc, ← Scheme.Hom.comp_appTop, he',
    Scheme.Hom.comp_appTop, ← ΓSpecIso_inv_naturality_assoc]

lemma Scheme.Hom.appLE_top_top {Y X : Scheme.{u}} (f : Y ⟶ X) (h : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ h = f.appTop :=
  f.appLE_eq_app

section BaseChange

variable {Y X : Scheme.{u}} {K L : CommRingCat.{u}} (ψ : K ⟶ L)
  {q : Y ⟶ X} {iY : Y ⟶ Spec L} {iX : X ⟶ Spec K} (H : IsPullback q iY iX (Spec.map ψ))
  [IsAffine X]

include H in
/-- For a pullback square of affine schemes over `Spec K ← Spec L`, the ring of global
sections of the top-left corner is the base change of that of the top-right corner. -/
lemma Scheme.Hom.nonempty_algEquiv_tensorProduct_Γ_of_isPullback :
    letI := iX.ΓAlgebra
    letI := iY.ΓAlgebra
    letI := ψ.hom.toAlgebra
    Nonempty (L ⊗[K] Γ(X, ⊤) ≃ₐ[L] Γ(Y, ⊤)) := by
  let _ := iX.ΓAlgebra
  let _ := iY.ΓAlgebra
  let _ := ψ.hom.toAlgebra
  have hUST : (⊤ : (Spec L).Opens) ≤ (Spec.map ψ) ⁻¹ᵁ ⊤ := le_top
  have hUSX : (⊤ : X.Opens) ≤ iX ⁻¹ᵁ ⊤ := le_top
  have hUY : (⊤ : Y.Opens) = q ⁻¹ᵁ ⊤ ⊓ iY ⁻¹ᵁ ⊤ := by simp
  have hiso := isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY
    (isAffineOpen_top _) (isAffineOpen_top _) (isAffineOpen_top _)
  have P := (isIso_pushoutSection_iff H hUST hUSX hUY).mp hiso
  simp only [Scheme.Hom.appLE_top_top] at P
  -- Precompose with the identifications `Γ(Spec K, ⊤) ≅ K` and `Γ(Spec L, ⊤) ≅ L`.
  have P' : IsPushout (CommRingCat.ofHom (algebraMap K Γ(X, ⊤)))
      (CommRingCat.ofHom (algebraMap K L))
      q.appTop (CommRingCat.ofHom (algebraMap L Γ(Y, ⊤))) := by
    refine P.of_iso (Scheme.ΓSpecIso K) (Iso.refl _) (Scheme.ΓSpecIso L) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [Scheme.Hom.algebraMap_ΓAlgebra]
    · simp only [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
      exact Scheme.ΓSpecIso_naturality ψ
    · simp
    · simp [Scheme.Hom.algebraMap_ΓAlgebra]
  have T := CommRingCat.isPushout_tensorProduct K L Γ(X, ⊤)
  let e : CommRingCat.of (L ⊗[K] Γ(X, ⊤)) ≅ Γ(Y, ⊤) := T.isoPushout ≪≫ P'.flip.isoPushout.symm
  have he : CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e.hom =
      CommRingCat.ofHom (algebraMap L Γ(Y, ⊤)) := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, ← Category.assoc, IsPushout.inl_isoPushout_hom]
    rw [Iso.comp_inv_eq, IsPushout.inl_isoPushout_hom]
  refine ⟨AlgEquiv.ofRingEquiv (f := e.commRingCatIsoToRingEquiv) fun l ↦ ?_⟩
  change e.hom (algebraMap L (L ⊗[K] Γ(X, ⊤)) l) = algebraMap L Γ(Y, ⊤) l
  exact congr($(he).hom l)

end BaseChange

end ΓAlgebra

section FiberDegree

variable {U X : Scheme.{u}} (g : U ⟶ X) [IsAffineHom g] (x : X)

/-- The ring of global sections of the fibre `g.fiber x` as a `κ(x)`-algebra. -/
noncomputable instance Scheme.Hom.fiberAlgebra : Algebra (X.residueField x) Γ(g.fiber x, ⊤) :=
  (g.fiberToSpecResidueField x).ΓAlgebra

omit [IsAffineHom g] in
lemma Scheme.Hom.algebraMap_fiber :
    algebraMap (X.residueField x) Γ(g.fiber x, ⊤) =
      ((Scheme.ΓSpecIso _).inv ≫ (g.fiberToSpecResidueField x).appTop).hom :=
  rfl

/-- The degree of the fibre of the affine morphism `g` at `x`: the dimension over `κ(x)` of the
ring of global sections of the (affine) scheme-theoretic fibre. -/
noncomputable def Scheme.Hom.fiberDegree : ℕ :=
  Module.finrank (X.residueField x) Γ(g.fiber x, ⊤)

/-- The fibre degree is invariant under base change. -/
lemma Scheme.Hom.fiberDegree_of_isPullback {U' X' : Scheme.{u}} {g' : U' ⟶ X'} [IsAffineHom g']
    {π' : U' ⟶ U} {π : X' ⟶ X} (h : IsPullback π' g' g π) (x' : X') :
    g'.fiberDegree x' = g.fiberDegree (π x') := by
  let _ := (π.residueFieldMap x').hom.toAlgebra
  obtain ⟨e⟩ := Scheme.Hom.nonempty_algEquiv_tensorProduct_Γ_of_isPullback
    (π.residueFieldMap x') (isPullback_fiberToSpecResidueField_of_isPullback h x')
  have e' : (X'.residueField x') ⊗[X.residueField (π x')] Γ(g.fiber (π x'), ⊤)
      ≃ₐ[X'.residueField x'] Γ(g'.fiber x', ⊤) := e
  change Module.finrank _ _ = Module.finrank _ _
  rw [← e'.toLinearEquiv.finrank_eq]
  exact Module.finrank_baseChange

instance (V : X.Opens) : IsAffineHom (g ∣_ V) :=
  IsZariskiLocalAtTarget.restrict (P := @IsAffineHom) ‹_› V

/-- The fibre degree is compatible with restriction to an open of the target. -/
lemma Scheme.Hom.fiberDegree_morphismRestrict (V : X.Opens) (x : V) :
    (g ∣_ V).fiberDegree x = g.fiberDegree x :=
  g.fiberDegree_of_isPullback (isPullback_morphismRestrict g V).flip x

section Etale

/-- The fibre of an étale morphism is a finite algebra over the residue field. -/
lemma Scheme.Hom.etale_Γ_fiber [Etale g] : Algebra.Etale (X.residueField x) Γ(g.fiber x, ⊤) := by
  have : Etale (g.fiberToSpecResidueField x) := MorphismProperty.pullback_snd _ _ inferInstance
  have h := HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := g.fiberToSpecResidueField x)
    |>.mp this
  change RingHom.Etale (algebraMap (X.residueField x) Γ(g.fiber x, ⊤))
  rw [Scheme.Hom.algebraMap_fiber, CommRingCat.hom_comp,
    RingHom.Etale.respectsIso.cancel_left_isIso]
  exact h

instance Scheme.Hom.finite_Γ_fiber [Etale g] :
    Module.Finite (X.residueField x) Γ(g.fiber x, ⊤) := by
  have := g.etale_Γ_fiber x
  exact Algebra.FormallyUnramified.finite_of_free _ _

omit [IsAffineHom g] in
/-- An isomorphism has fibre degree one. -/
lemma Scheme.Hom.fiberDegree_of_isIso [IsIso g] : g.fiberDegree x = 1 := by
  have : IsIso (g.fiberToSpecResidueField x) :=
    inferInstanceAs (IsIso (pullback.snd g (X.fromSpecResidueField x)))
  have h := Scheme.Hom.finrankΓ_eq_of_iso (g.fiberToSpecResidueField x) (𝟙 _)
    (asIso (g.fiberToSpecResidueField x)) (Iso.refl _) (by simp)
  refine h.trans ?_
  let _ := Scheme.Hom.ΓAlgebra (𝟙 (Spec (X.residueField x)))
  rw [Scheme.Hom.finrankΓ, Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _)
    (Scheme.ΓSpecIso (X.residueField x)).commRingCatIsoToRingEquiv (S₁ := X.residueField x) ?_,
    Module.finrank_self]
  refine RingHom.ext fun y ↦ ?_
  change y = (Scheme.ΓSpecIso (X.residueField x)).hom
    (((Scheme.ΓSpecIso (X.residueField x)).inv ≫
      Scheme.Hom.appTop (𝟙 (Spec (X.residueField x)))) y)
  simp

omit [IsAffineHom g] in
/-- If `U` is empty, all fibre degrees vanish. -/
lemma Scheme.Hom.fiberDegree_of_isEmpty [IsEmpty U] : g.fiberDegree x = 0 := by
  have : IsEmpty (g.fiber x) := Function.isEmpty (g.fiberι x)
  exact Module.finrank_zero_of_subsingleton

/-- An étale morphism all of whose fibre degrees vanish has empty source. -/
lemma Scheme.Hom.isEmpty_of_forall_fiberDegree_eq_zero [Etale g]
    (h : ∀ x, g.fiberDegree x = 0) : IsEmpty U := by
  refine ⟨fun u ↦ ?_⟩
  have hsub : Subsingleton Γ(g.fiber (g u), ⊤) := Module.finrank_zero_iff.mp (h (g u))
  have : IsEmpty (Spec Γ(g.fiber (g u), ⊤)) :=
    inferInstanceAs (IsEmpty (PrimeSpectrum Γ(g.fiber (g u), ⊤)))
  exact this.false ((g.fiber (g u)).isoSpec.hom (g.asFiber u))

end Etale

section IsCompl

/-- For complementary opens `O₁ O₂` of a scheme `Z`, restriction identifies `Γ(Z, ⊤)` with
`Γ(Z, O₁) × Γ(Z, O₂)`. -/
lemma Scheme.bijective_restrict_prod_of_isCompl (Z : Scheme.{u}) {O₁ O₂ : Z.Opens}
    (h : IsCompl O₁ O₂) :
    Function.Bijective (RingHom.prod (Z.presheaf.map (homOfLE (le_top : O₁ ≤ ⊤)).op).hom
      (Z.presheaf.map (homOfLE (le_top : O₂ ≤ ⊤)).op).hom) := by
  have hinf : O₁ ⊓ O₂ = ⊥ := h.inf_eq_bot
  have hsup : O₁ ⊔ O₂ = ⊤ := h.sup_eq_top
  let c := Z.sheaf.isProductOfDisjoint O₁ O₂ hinf
  let e := c.conePointUniqueUpToIso (CommRingCat.prodFanIsLimit Γ(Z, O₁) Γ(Z, O₂))
  have he : e.hom = CommRingCat.ofHom (RingHom.prod
      (Z.presheaf.map (homOfLE (le_sup_left : O₁ ≤ O₁ ⊔ O₂)).op).hom
      (Z.presheaf.map (homOfLE (le_sup_right : O₂ ≤ O₁ ⊔ O₂)).op).hom) := rfl
  have hbij : Function.Bijective (RingHom.prod
      (Z.presheaf.map (homOfLE (le_sup_left : O₁ ≤ O₁ ⊔ O₂)).op).hom
      (Z.presheaf.map (homOfLE (le_sup_right : O₂ ≤ O₁ ⊔ O₂)).op).hom) := by
    have := ConcreteCategory.bijective_of_isIso e.hom
    rw [he] at this
    exact this
  have hbij' : Function.Bijective (fun s : Γ(Z, ⊤) ↦
      ((Z.presheaf.map (eqToHom hsup).op).hom s : Γ(Z, O₁ ⊔ O₂))) :=
    ConcreteCategory.bijective_of_isIso (Z.presheaf.map (eqToHom hsup).op)
  have key := hbij.comp hbij'
  have e₁ : Z.presheaf.map (homOfLE (le_top : O₁ ≤ ⊤)).op =
      Z.presheaf.map (eqToHom hsup).op ≫ Z.presheaf.map (homOfLE le_sup_left).op := by
    rw [← Functor.map_comp, ← op_comp]
    congr 1
  have e₂ : Z.presheaf.map (homOfLE (le_top : O₂ ≤ ⊤)).op =
      Z.presheaf.map (eqToHom hsup).op ≫ Z.presheaf.map (homOfLE le_sup_right).op := by
    rw [← Functor.map_comp, ← op_comp]
    congr 1
  convert key using 1
  ext s
  · exact congr($(e₁) s)
  · exact congr($(e₂) s)

variable {V₁ V₂ : U.Opens} (h : IsCompl V₁ V₂)

include h in
/-- Each of two complementary opens is closed. -/
lemma isClosedImmersion_ι_of_isCompl_left : IsClosedImmersion V₁.ι := by
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  rw [Scheme.Opens.range_ι]
  have h1 : ∀ x, x ∈ V₁ → x ∉ V₂ := fun x hx hx' ↦ by
    have : x ∈ V₁ ⊓ V₂ := ⟨hx, hx'⟩
    rw [h.inf_eq_bot] at this
    exact this
  have h2 : ∀ x, x ∉ V₂ → x ∈ V₁ := fun x hx ↦ by
    have : x ∈ V₁ ⊔ V₂ := by rw [h.sup_eq_top]; trivial
    exact (TopologicalSpace.Opens.mem_sup.mp this).resolve_right hx
  have : (V₁ : Set U) = (V₂ : Set U)ᶜ := Set.ext fun x ↦ ⟨h1 x, h2 x⟩
  rw [this]
  exact isClosed_compl_iff.mpr V₂.isOpen

include h in
/-- Each of two complementary opens is closed. -/
lemma isClosedImmersion_ι_of_isCompl_right : IsClosedImmersion V₂.ι :=
  isClosedImmersion_ι_of_isCompl_left h.symm

/-- The fibre of the restriction of `g` to an open `V ⊆ U` is the corresponding open of the
fibre of `g`, compatibly with the structure maps to `Spec κ(x)`. -/
noncomputable def Scheme.Hom.fiberRestrictIso (V : U.Opens) :
    (V.ι ≫ g).fiber x ≅ ((g.fiberι x) ⁻¹ᵁ V).toScheme :=
  (pullbackRightPullbackFstIso g (X.fromSpecResidueField x) V.ι).symm ≪≫
    pullbackSymmetry _ _ ≪≫ pullbackRestrictIsoRestrict (g.fiberι x) V

omit [IsAffineHom g] in
lemma Scheme.Hom.fiberRestrictIso_hom_ι_fiberToSpecResidueField (V : U.Opens) :
    (g.fiberRestrictIso x V).hom ≫ ((g.fiberι x) ⁻¹ᵁ V).ι ≫ g.fiberToSpecResidueField x =
      (V.ι ≫ g).fiberToSpecResidueField x := by
  simp only [Scheme.Hom.fiberRestrictIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackRestrictIsoRestrict_hom_ι_assoc]
  change _ ≫ (pullbackSymmetry V.ι (pullback.fst g (X.fromSpecResidueField x))).hom ≫
    pullback.fst (pullback.fst g (X.fromSpecResidueField x)) V.ι ≫
      pullback.snd g (X.fromSpecResidueField x) = pullback.snd (V.ι ≫ g) (X.fromSpecResidueField x)
  rw [pullbackSymmetry_hom_comp_fst_assoc]
  exact pullbackRightPullbackFstIso_inv_snd_snd g (X.fromSpecResidueField x) V.ι

omit [IsAffineHom g] in
/-- The fibre degree of the restriction of `g` to an open `V` is the dimension of the sections
of the fibre of `g` over the corresponding open. -/
lemma Scheme.Hom.fiberDegree_comp_ι (V : U.Opens) [IsAffineHom (V.ι ≫ g)] :
    letI := (((g.fiberι x) ⁻¹ᵁ V).ι ≫ g.fiberToSpecResidueField x).ΓAlgebra
    (V.ι ≫ g).fiberDegree x = Module.finrank (X.residueField x) Γ(((g.fiberι x) ⁻¹ᵁ V), ⊤) :=
  Scheme.Hom.finrankΓ_eq_of_iso _ _ (g.fiberRestrictIso x V) (Iso.refl _) (by
    simpa using g.fiberRestrictIso_hom_ι_fiberToSpecResidueField x V)

include h in
/-- **Additivity of the fibre degree** in complementary open (and closed) subschemes of the
source. -/
lemma Scheme.Hom.fiberDegree_of_isCompl [Module.Finite (X.residueField x) Γ(g.fiber x, ⊤)] :
    haveI := isClosedImmersion_ι_of_isCompl_left h
    haveI := isClosedImmersion_ι_of_isCompl_right h
    g.fiberDegree x = (V₁.ι ≫ g).fiberDegree x + (V₂.ι ≫ g).fiberDegree x := by
  have := isClosedImmersion_ι_of_isCompl_left h
  have := isClosedImmersion_ι_of_isCompl_right h
  rw [g.fiberDegree_comp_ι x V₁, g.fiberDegree_comp_ι x V₂]
  let Z := g.fiber x
  let ι := g.fiberι x
  let hZ := g.fiberToSpecResidueField x
  let O₁ : Z.Opens := ι ⁻¹ᵁ V₁
  let O₂ : Z.Opens := ι ⁻¹ᵁ V₂
  let _ := (O₁.ι ≫ hZ).ΓAlgebra
  let _ := (O₂.ι ≫ hZ).ΓAlgebra
  have hO : IsCompl O₁ O₂ := by
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff]
      change ι ⁻¹ᵁ V₁ ⊓ ι ⁻¹ᵁ V₂ = ⊥
      rw [← Scheme.Hom.preimage_inf, h.inf_eq_bot]
      rfl
    · rw [codisjoint_iff]
      change ι ⁻¹ᵁ V₁ ⊔ ι ⁻¹ᵁ V₂ = ⊤
      rw [← Scheme.Hom.preimage_sup, h.sup_eq_top]
      rfl
  -- The restriction maps as `κ(x)`-algebra homomorphisms.
  let r₁ : Γ(Z, ⊤) →ₐ[X.residueField x] Γ(O₁, ⊤) :=
    { O₁.ι.appTop.hom with commutes' := fun _ ↦ rfl }
  let r₂ : Γ(Z, ⊤) →ₐ[X.residueField x] Γ(O₂, ⊤) :=
    { O₂.ι.appTop.hom with commutes' := fun _ ↦ rfl }
  have hbij : Function.Bijective (r₁.prod r₂) := by
    have := Z.bijective_restrict_prod_of_isCompl (O₁ := O₁.ι ''ᵁ ⊤) (O₂ := O₂.ι ''ᵁ ⊤) (by
      simpa only [Scheme.Opens.ι_image_top] using hO)
    exact this
  let e : Γ(Z, ⊤) ≃ₐ[X.residueField x] Γ(O₁, ⊤) × Γ(O₂, ⊤) := AlgEquiv.ofBijective _ hbij
  have h₁ : Module.Finite (X.residueField x) Γ(O₁, ⊤) :=
    Module.Finite.of_surjective (LinearMap.fst _ _ _ ∘ₗ e.toLinearEquiv.toLinearMap)
      (Prod.fst_surjective.comp e.surjective)
  have h₂ : Module.Finite (X.residueField x) Γ(O₂, ⊤) :=
    Module.Finite.of_surjective (LinearMap.snd _ _ _ ∘ₗ e.toLinearEquiv.toLinearMap)
      (Prod.snd_surjective.comp e.surjective)
  change Module.finrank _ _ = _
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_prod]

end IsCompl

section Spec

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (x : PrimeSpectrum R)

/-- The scheme-theoretic fibre degree of `Spec S ⟶ Spec R` at a prime `p` is the ring-theoretic
fibre degree `Ideal.fiberDegree p S`. -/
lemma Scheme.Hom.fiberDegree_SpecMap :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberDegree x = x.asIdeal.fiberDegree S := by
  let a := Spec.fiberToSpecResidueFieldIso R S x
  let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let i : (Spec (.of R)).residueField x ≅ .of x.asIdeal.ResidueField :=
    Scheme.Spec.residueFieldIso (.of R) x
  have ha : a.hom.right = Spec.map i.inv := rfl
  have he : (Arrow.leftFunc.mapIso a).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap x.asIdeal.ResidueField (x.asIdeal.Fiber S))) ≫
        Spec.map i.hom = g.fiberToSpecResidueField x := by
    have hw := a.hom.w
    simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, ha] at hw
    change a.hom.left ≫ _ = _
    rw [← Category.assoc, hw, Category.assoc, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id,
      Category.comp_id]
  have h1 := Scheme.Hom.finrankΓ_eq_of_iso (g.fiberToSpecResidueField x)
    (Spec.map (CommRingCat.ofHom (algebraMap x.asIdeal.ResidueField (x.asIdeal.Fiber S))))
    (Arrow.leftFunc.mapIso a) i he
  refine h1.trans ?_
  let _ := (Spec.map (CommRingCat.ofHom
    (algebraMap x.asIdeal.ResidueField (x.asIdeal.Fiber S)))).ΓAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _)
    (Scheme.ΓSpecIso (.of (x.asIdeal.Fiber S))).commRingCatIsoToRingEquiv ?_
  refine RingHom.ext fun y ↦ ?_
  change algebraMap x.asIdeal.ResidueField (x.asIdeal.Fiber S) y =
    (Scheme.ΓSpecIso (.of (x.asIdeal.Fiber S))).hom
      (((Scheme.ΓSpecIso (.of x.asIdeal.ResidueField)).inv ≫
        (Spec.map (CommRingCat.ofHom
          (algebraMap x.asIdeal.ResidueField (x.asIdeal.Fiber S)))).appTop) y)
  rw [← CommRingCat.comp_apply, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]
  rfl

/-- For a standard étale algebra the scheme-theoretic fibre degrees are bounded. -/
lemma Scheme.Hom.exists_forall_fiberDegree_SpecMap_le [Algebra.IsStandardEtale R S] :
    ∃ n : ℕ, ∀ x : PrimeSpectrum R,
      (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberDegree x ≤ n := by
  obtain ⟨n, hn⟩ := Algebra.IsStandardEtale.exists_forall_fiberDegree_le R S
  exact ⟨n, fun x ↦ by rw [Scheme.Hom.fiberDegree_SpecMap]; exact hn x.asIdeal⟩

end Spec

end FiberDegree

end AlgebraicGeometry
