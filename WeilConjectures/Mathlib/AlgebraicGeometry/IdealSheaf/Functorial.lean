/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Kernels, dominant morphisms and factorizations through closed subschemes

We record the interaction of kernel ideal sheaves with scheme-theoretically dominant
morphisms and the resulting factorization criterion used by the valuative arguments of
the Nagata compactification proof:

- `AlgebraicGeometry.Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant`:
  precomposition with a scheme-theoretically dominant morphism preserves kernels;
- the inclusion of the generic point `Spec K ⟶ Spec A` of the spectrum of a domain
  with fraction field `K` is scheme-theoretically dominant;
- `AlgebraicGeometry.IsClosedImmersion.exists_lift_of_isFractionRing`: a morphism
  `Spec A ⟶ Y` from the spectrum of a domain factors through a closed subscheme
  `Z ⟶ Y` as soon as its restriction to the generic point does (blueprint:
  `lemma:nagata-valuation-factor-closed`).

We also record the affine-local description of the inverse image ideal sheaf along an
*arbitrary* morphism. For a morphism `Spec S ⟶ X` factoring through an affine open `U`
as `Spec.map φ ≫ fromSpec`, the ideal of sections of `I.comap _` on `⊤` is the
extension of `I(U)` along the section map
(`AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_specMap_fromSpec`); comparing two
affine opens `W ≤ f ⁻¹ᵁ V` gives
`AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_eq_map_appLE_of_le`, which extends
Mathlib's open-immersion statement `ideal_comap_eq_map_appLE`, and from it
multiplicativity `AlgebraicGeometry.Scheme.IdealSheafData.comap_mul` and its power
version `comap_pow`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X' X : Scheme.{u}}

/-- Precomposition with a scheme-theoretically dominant morphism does not change the
kernel ideal sheaf. -/
lemma Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant {T : Scheme.{u}} (d : T ⟶ X')
    (γ : X' ⟶ X) [IsSchemeTheoreticallyDominant d] : (d ≫ γ).ker = γ.ker := by
  rw [Scheme.Hom.ker_comp, d.ker_eq_bot, Scheme.IdealSheafData.map_bot]

section FractionRing

variable (A K : Type u) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K]

/-- The inclusion of the generic point of the spectrum of a domain is
scheme-theoretically dominant. -/
instance : IsSchemeTheoreticallyDominant
    (Spec.map (CommRingCat.ofHom (algebraMap A K))) := by
  have : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A K))) := by
    constructor
    change DenseRange (PrimeSpectrum.comap (algebraMap A K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective A K)]
    exact bot_le
  exact .of_isDominant _

variable {A K} {Y Z : Scheme.{u}}

/-- **Factorization through a closed subscheme over the spectrum of a domain**
(blueprint: `lemma:nagata-valuation-factor-closed`): let `A` be a domain with fraction
field `K`, let `ι : Z ⟶ Y` be a closed immersion and `γ : Spec A ⟶ Y` a morphism whose
restriction to the generic point `Spec K` factors through `Z`. Then `γ` factors
through `Z`. -/
theorem IsClosedImmersion.exists_lift_of_isFractionRing (ι : Z ⟶ Y) [IsClosedImmersion ι]
    (γ : Spec (CommRingCat.of A) ⟶ Y) (η : Spec (CommRingCat.of K) ⟶ Z)
    (hcomm : η ≫ ι = Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ γ) :
    ∃ l : Spec (CommRingCat.of A) ⟶ Z, l ≫ ι = γ := by
  have hker : ι.ker ≤ γ.ker := by
    refine le_trans ?_ (le_of_eq
      ((Spec.map
        (CommRingCat.ofHom (algebraMap A K))).ker_comp_of_isSchemeTheoreticallyDominant γ))
    rw [← hcomm]
    exact Scheme.Hom.le_ker_comp η ι
  exact ⟨IsClosedImmersion.lift ι γ hker, IsClosedImmersion.lift_fac ι γ hker⟩

end FractionRing

/-! ### The inverse image ideal sheaf on an affine probe -/

/-- The section map of `Spec.map φ ≫ fromSpec` from the affine open to the total
sections is `φ` composed with the global-sections isomorphism of the spectrum. -/
lemma appLE_specMap_comp_fromSpec (U : X.affineOpens) {S : CommRingCat.{u}}
    (φ : Γ(X, U.1) ⟶ S) (h : (⊤ : (Spec S).Opens) ≤ (Spec.map φ ≫ U.2.fromSpec) ⁻¹ᵁ U.1) :
    (Spec.map φ ≫ U.2.fromSpec).appLE U.1 ⊤ h = φ ≫ (Scheme.ΓSpecIso S).inv := by
  have e₁ : (⊤ : (Spec Γ(X, U.1)).Opens) ≤ U.2.fromSpec ⁻¹ᵁ U.1 :=
    U.2.fromSpec_preimage_self.ge
  have e₂ : (⊤ : (Spec S).Opens) ≤ Spec.map φ ⁻¹ᵁ ⊤ := le_rfl
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) U.2.fromSpec U.1 ⊤ ⊤ e₁ e₂]
  have h1 : U.2.fromSpec.appLE U.1 ⊤ e₁ = (Scheme.ΓSpecIso Γ(X, U.1)).inv := by
    rw [Scheme.Hom.appLE, U.2.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    rw [show (eqToHom U.2.fromSpec_preimage_self).op ≫ (homOfLE e₁).op = 𝟙 _ from
      Subsingleton.elim _ _]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  have h2 : (Spec.map φ).appLE ⊤ ⊤ e₂ =
      (Scheme.ΓSpecIso Γ(X, U.1)).hom ≫ φ ≫ (Scheme.ΓSpecIso S).inv := by
    have hTop : (Spec.map φ).appLE ⊤ ⊤ e₂ = (Spec.map φ).appTop :=
      Scheme.Hom.appLE_eq_app (Spec.map φ)
    rw [hTop, Scheme.ΓSpecIso_inv_naturality, ← Category.assoc, Iso.hom_inv_id,
      Category.id_comp]
  rw [h1, h2, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The ideal of sections on `⊤` of `ofIdealTop`. -/
lemma ideal_top_ofIdealTop {Y : Scheme.{u}} [IsAffine Y] (K : Ideal Γ(Y, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop K).ideal ⟨⊤, isAffineOpen_top _⟩ = K := by
  have h1 : Y.presheaf.map ((homOfLE le_top).op :
      Opposite.op (⊤ : Y.Opens) ⟶ Opposite.op (((⟨⊤, isAffineOpen_top Y⟩ :
        Y.affineOpens) : Y.Opens))) = 𝟙 _ := Y.presheaf.map_id _
  rw [Scheme.IdealSheafData.ofIdealTop_ideal, h1, CommRingCat.hom_id, Ideal.map_id]

/-- The kernel ideal sheaf of `Spec` of a quotient map, on global sections. -/
lemma ideal_top_ker_specMap_quotient {S : CommRingCat.{u}} (L : Ideal S) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk L))).ker.ideal
      ⟨⊤, isAffineOpen_top _⟩ = L.map (Scheme.ΓSpecIso S).inv.hom := by
  rw [Scheme.ker_of_isAffine, ideal_top_ofIdealTop]
  have happ : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk L))).appTop =
      (Scheme.ΓSpecIso S).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk L) ≫
        (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.ΓSpecIso_inv_naturality, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [happ]
  have hdec : (((Scheme.ΓSpecIso S).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk L) ≫
      (Scheme.ΓSpecIso _).inv)).hom =
      ((Scheme.ΓSpecIso (.of (S ⧸ L))).symm.commRingCatIsoToRingEquiv.toRingHom).comp
        ((Ideal.Quotient.mk L).comp (Scheme.ΓSpecIso S).hom.hom) := rfl
  rw [hdec, RingHom.ker_equiv_comp, ← RingHom.comap_ker, Ideal.mk_ker]
  exact (Ideal.map_symm (Scheme.ΓSpecIso S).commRingCatIsoToRingEquiv).symm

/-- **The inverse image ideal sheaf on an affine probe**: for an affine open
`U ⊆ X` and a morphism `Spec S ⟶ X` of the form `Spec.map φ ≫ fromSpec`, the ideal of
sections of `I.comap _` on `⊤` is the extension of `I(U)` along the section map.
(Blueprint: part of `thm:nagata-blowup-principalizes-center`, the affine description of
the inverse image ideal sheaf.) -/
theorem Scheme.IdealSheafData.ideal_comap_specMap_fromSpec (I : X.IdealSheafData)
    (U : X.affineOpens) {S : CommRingCat.{u}} (φ : Γ(X, U.1) ⟶ S)
    (h : (⊤ : (Spec S).Opens) ≤ (Spec.map φ ≫ U.2.fromSpec) ⁻¹ᵁ U.1) :
    (I.comap (Spec.map φ ≫ U.2.fromSpec)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (I.ideal U).map ((Spec.map φ ≫ U.2.fromSpec).appLE U.1 ⊤ h).hom := by
  -- the explicit pullback of the subscheme along the probe
  have s1 := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_quotient φ (I.ideal U))
  have H := (s1.paste_horiz (I.isPullback_subschemeCover_map U)).flip
  -- the first projection is the quotient `Spec` map, up to the pullback isomorphism
  have hfst : pullback.fst (Spec.map φ ≫ U.2.fromSpec) I.subschemeι =
      H.isoPullback.inv ≫ Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk ((I.ideal U).map φ.hom))) :=
    ((Iso.inv_comp_eq _).mpr H.isoPullback_hom_fst.symm).symm
  have hker : I.comap (Spec.map φ ≫ U.2.fromSpec) =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((I.ideal U).map φ.hom)))).ker := by
    change (pullback.fst (Spec.map φ ≫ U.2.fromSpec) I.subschemeι).ker = _
    rw [hfst, Scheme.Hom.ker_comp_of_isIso]
  refine (congrArg (fun J ↦ Scheme.IdealSheafData.ideal J ⟨⊤, isAffineOpen_top _⟩)
    hker).trans ?_
  refine (ideal_top_ker_specMap_quotient _).trans ?_
  -- identify the two descriptions of the extended ideal
  refine Eq.symm ?_
  refine (congrArg (fun t ↦ (I.ideal U).map (CommRingCat.Hom.hom t))
    (appLE_specMap_comp_fromSpec U φ h)).trans ?_
  refine (congrArg ((I.ideal U).map ·) (CommRingCat.hom_comp _ _)).trans ?_
  exact (Ideal.map_map _ _).symm


/-- The affine probe `Spec.map φ ≫ fromSpec` attached to an affine open `V` lies
over `V`. -/
lemma specMap_comp_fromSpec_preimage_le (V : X.affineOpens) {S : CommRingCat.{u}}
    (φ : Γ(X, V.1) ⟶ S) :
    (⊤ : (Spec S).Opens) ≤ (Spec.map φ ≫ V.2.fromSpec) ⁻¹ᵁ V.1 := by
  rw [Scheme.Hom.comp_preimage, V.2.fromSpec_preimage_self]
  exact le_rfl

/-- Pushforward of ideals along the inverse of an isomorphism of commutative rings is
injective. -/
lemma _root_.CommRingCat.ideal_map_inv_injective {R S : CommRingCat.{u}} (e : R ≅ S) :
    Function.Injective (fun J : Ideal S ↦ J.map e.inv.hom) := by
  intro J₁ J₂ hJ
  have h := congrArg (Ideal.map e.hom.hom) hJ
  simp only [Ideal.map_map, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id,
    Ideal.map_id] at h
  exact h

section ComapAffineLocality

/-! ### The affine-local description of the inverse image ideal sheaf

For an arbitrary morphism `f : Y ⟶ X` and affine opens `W ≤ f ⁻¹ᵁ V`, the pullback
ideal `(I.comap f)(W)` is the extension of `I(V)` along the section map
`f.appLE V W`. This extends Mathlib's `Scheme.IdealSheafData.ideal_comap_eq_map_appLE`
(the open immersion case) to arbitrary morphisms, and yields multiplicativity of
`comap`. -/

variable {Y : Scheme.{u}}

/-- **The affine-local description of the inverse image ideal sheaf** along an
arbitrary morphism: on an affine open `W` mapping into an affine open `V`, the
pullback of `I` is the extension of `I(V)` along the induced map on sections. -/
theorem Scheme.IdealSheafData.ideal_comap_eq_map_appLE_of_le (f : Y ⟶ X)
    (I : X.IdealSheafData) (V : X.affineOpens) (W : Y.affineOpens)
    (h : W.1 ≤ f ⁻¹ᵁ V.1) :
    (I.comap f).ideal W = (I.ideal V).map (f.appLE V.1 W.1 h).hom := by
  have h1 : ((I.comap f).comap W.2.fromSpec).ideal ⟨⊤, isAffineOpen_top _⟩ =
      ((I.comap f).ideal W).map (Scheme.ΓSpecIso Γ(Y, W.1)).inv.hom := by
    have e1 := (I.comap f).ideal_comap_specMap_fromSpec W (𝟙 Γ(Y, W.1))
      (specMap_comp_fromSpec_preimage_le W _)
    rw [appLE_specMap_comp_fromSpec W (𝟙 _) (specMap_comp_fromSpec_preimage_le W _),
      Category.id_comp, Spec.map_id, Category.id_comp] at e1
    exact e1
  have h3 : (I.comap f).comap W.2.fromSpec =
      I.comap (Spec.map (f.appLE V.1 W.1 h) ≫ V.2.fromSpec) := by
    rw [← Scheme.IdealSheafData.comap_comp,
      IsAffineOpen.SpecMap_appLE_fromSpec f V.2 W.2 h]
  have h4 : (I.comap (Spec.map (f.appLE V.1 W.1 h) ≫ V.2.fromSpec)).ideal
      ⟨⊤, isAffineOpen_top _⟩ =
      (I.ideal V).map ((f.appLE V.1 W.1 h) ≫ (Scheme.ΓSpecIso Γ(Y, W.1)).inv).hom := by
    rw [I.ideal_comap_specMap_fromSpec V _ (specMap_comp_fromSpec_preimage_le V _),
      appLE_specMap_comp_fromSpec V _ (specMap_comp_fromSpec_preimage_le V _)]
  apply CommRingCat.ideal_map_inv_injective (Scheme.ΓSpecIso Γ(Y, W.1))
  calc ((I.comap f).ideal W).map (Scheme.ΓSpecIso Γ(Y, W.1)).inv.hom
      = ((I.comap f).comap W.2.fromSpec).ideal ⟨⊤, isAffineOpen_top _⟩ := h1.symm
    _ = (I.ideal V).map ((f.appLE V.1 W.1 h) ≫ (Scheme.ΓSpecIso Γ(Y, W.1)).inv).hom := by
        rwa [h3]
    _ = ((I.ideal V).map (f.appLE V.1 W.1 h).hom).map
          (Scheme.ΓSpecIso Γ(Y, W.1)).inv.hom := by
        rw [CommRingCat.hom_comp, Ideal.map_map]

/-- Every point of `Y` lies in an affine open contained in the preimage of an affine
open of `X`. -/
lemma exists_affineOpens_le_preimage (f : Y ⟶ X) (y : Y) :
    ∃ (V : X.affineOpens) (W : Y.affineOpens), W.1 ≤ f ⁻¹ᵁ V.1 ∧ y ∈ W.1 := by
  have hfy : f y ∈ (⊤ : X.Opens) := trivial
  rw [← iSup_affineOpens_eq_top X] at hfy
  obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp hfy
  obtain ⟨-, ⟨W₀, hW₀, rfl⟩, hyW₀, hsub⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ ((f ⁻¹ᵁ V.1 : Y.Opens) : Set Y) from hV) (f ⁻¹ᵁ V.1).isOpen
  exact ⟨V, ⟨W₀, hW₀⟩, fun z hz ↦ hsub hz, hyW₀⟩

/-- **Inverse images of ideal sheaves commute with products** (for arbitrary
morphisms). -/
theorem Scheme.IdealSheafData.comap_mul (f : Y ⟶ X) (I J : X.IdealSheafData) :
    (I * J).comap f = I.comap f * J.comap f := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (ι := {p : X.affineOpens × Y.affineOpens // p.2.1 ≤ f ⁻¹ᵁ p.1.1})
    (fun p ↦ p.1.2) ?_ ?_
  · rw [eq_top_iff]
    intro y _
    obtain ⟨V, W, hle, hyW⟩ := exists_affineOpens_le_preimage f y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(V, W), hle⟩, hyW⟩
  · rintro ⟨⟨V, W⟩, hle⟩
    have hmul : (I * J).ideal V = I.ideal V * J.ideal V := by
      rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
    have hmul' : (I.comap f * J.comap f).ideal W =
        (I.comap f).ideal W * (J.comap f).ideal W := by
      rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
    rw [Scheme.IdealSheafData.ideal_comap_eq_map_appLE_of_le f (I * J) V W hle, hmul, hmul',
      Ideal.map_mul, Scheme.IdealSheafData.ideal_comap_eq_map_appLE_of_le f I V W hle,
      Scheme.IdealSheafData.ideal_comap_eq_map_appLE_of_le f J V W hle]

/-- **Inverse images of ideal sheaves commute with powers** (for arbitrary
morphisms), by induction from `AlgebraicGeometry.Scheme.IdealSheafData.comap_mul`. -/
theorem Scheme.IdealSheafData.comap_pow (f : Y ⟶ X) (I : X.IdealSheafData) (d : ℕ) :
    (I ^ d).comap f = (I.comap f) ^ d := by
  induction d with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

end ComapAffineLocality

end AlgebraicGeometry
