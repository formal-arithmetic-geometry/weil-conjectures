module

public import Sheaf.Paper.ClopenCommonCompactSupport
public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
import Sheaf.AlgebraicGeometry.ProEtaleIdentityOpenScalarRestriction
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin

/-! # Finite proper normalization

Source: latest Weil blueprint, sec-zeta-weil/sk-input-weights,
prop-weil-proper-compact-coincidence.proof.md, first paragraph;
Stacks Tags 03DI, 03CY and 0D6E (blueprint: lem-weil-proper-finite-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

/-- The canonical identity-compactification normalization: descend identity open
extension termwise and apply the ordinary derived direct image.
Source: latest blueprint proper-coincidence proof, first paragraph; Stacks Tag 03DI
(blueprint: lem-weil-proper-finite-normalization). -/
def properFiniteIdentityNormalization (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    sfIntrinsicCompactSupport (Compactification.ofIsProper f) A ≅
      proEtaleConstantDerivedDirectImage f A :=
  Functor.isoWhiskerRight (sfIntrinsicDerivedOpenId A X) _ ≪≫ Functor.leftUnitor _

private theorem properFiniteIdentityNormalization_restrictScalars
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (φ : A →+* B) :
    Functor.whiskerLeft (proEtaleCoefficientRestrictScalars X φ).mapDerivedCategory
        (properFiniteIdentityNormalization A f).hom ≫
      (sfDerivedImageRestriction f φ).hom =
    (sfCompactSupportRestriction (Compactification.ofIsProper f) φ).hom ≫
      Functor.whiskerRight (properFiniteIdentityNormalization B f).hom
        (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory := by
  ext K
  have ho := congr_app (sfIdentityOpenRestriction X φ) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at ho
  have hn := (sfDerivedImageRestriction f φ).hom.naturality
    ((sfIntrinsicDerivedOpenId B X).hom.app K)
  simp only [Functor.comp_map, Functor.id_obj] at hn
  have he :
      (proEtaleConstantDerivedDirectImage f A).map
          ((sfIntrinsicDerivedOpenId A X).hom.app
            ((proEtaleCoefficientRestrictScalars X φ).mapDerivedCategory.obj K)) ≫
        (sfDerivedImageRestriction f φ).hom.app K =
      (proEtaleConstantDerivedDirectImage f A).map
          ((sfOpenRestrictionDerived (𝟙 X) φ).hom.app K) ≫
        (sfDerivedImageRestriction f φ).hom.app
          ((sfIntrinsicDerivedOpen B (𝟙 X)).obj K) ≫
        (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory.map
          ((proEtaleConstantDerivedDirectImage f B).map
            ((sfIntrinsicDerivedOpenId B X).hom.app K)) := by
    rw [ho, Functor.map_comp, Category.assoc]
    exact congrArg ((proEtaleConstantDerivedDirectImage f A).map
      ((sfOpenRestrictionDerived (𝟙 X) φ).hom.app K) ≫ ·) hn
  dsimp only [properFiniteIdentityNormalization, sfCompactSupportRestriction,
    Compactification.ofIsProper, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  erw [Category.comp_id, Category.comp_id]
  dsimp only [sfOpenRestrictionDerived, Functor.mapDerivedCategorySquareIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, sfIntrinsicDerivedOpen] at he
  exact he.trans (Category.assoc _ _ _).symm

private theorem properFiniteImageRestriction_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C] (φ : A →+* B) (ψ : B →+* C)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (l : ℕ) [Fact l.Prime] (hl : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : proEtaleDerivedCategory X C) :
    (proEtaleConstantDerivedDirectImage f A).map
        ((sfDerivedCoefficientRestrictionComp X φ ψ).hom.app K) ≫
      (sfDerivedImageRestriction f (ψ.comp φ)).hom.app K =
    (sfDerivedImageRestriction f φ).hom.app
        ((proEtaleCoefficientRestrictScalars X ψ).mapDerivedCategory.obj K) ≫
      (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory.map
        ((sfDerivedImageRestriction f ψ).hom.app K) ≫
      (sfDerivedCoefficientRestrictionComp Y φ ψ).hom.app
        ((proEtaleConstantDerivedDirectImage f C).obj K) := by
  have hφ := congr_app (properFiniteIdentityNormalization_restrictScalars f φ)
    ((proEtaleCoefficientRestrictScalars X ψ).mapDerivedCategory.obj K)
  have hψ := congr_app (properFiniteIdentityNormalization_restrictScalars f ψ) K
  have hc := congr_app (properFiniteIdentityNormalization_restrictScalars f (ψ.comp φ)) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    at hφ hψ hc
  have hn := (properFiniteIdentityNormalization A f).hom.naturality
    ((sfDerivedCoefficientRestrictionComp X φ ψ).hom.app K)
  have ht := (sfDerivedCoefficientRestrictionComp Y φ ψ).hom.naturality
    ((properFiniteIdentityNormalization C f).hom.app K)
  simp only [Functor.comp_map] at ht
  have hs := sfCompactSupportRestriction_comp l f hl (Compactification.ofIsProper f) φ ψ K
  change (sfIntrinsicCompactSupport (Compactification.ofIsProper f) A).map
      ((sfDerivedCoefficientRestrictionComp X φ ψ).hom.app K) ≫
    (sfCompactSupportRestriction (Compactification.ofIsProper f) (ψ.comp φ)).hom.app K =
    (sfCompactSupportRestriction (Compactification.ofIsProper f) φ).hom.app
        ((proEtaleCoefficientRestrictScalars X ψ).mapDerivedCategory.obj K) ≫
      (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory.map
        ((sfCompactSupportRestriction (Compactification.ofIsProper f) ψ).hom.app K) ≫
      (sfDerivedCoefficientRestrictionComp Y φ ψ).hom.app
        ((sfIntrinsicCompactSupport (Compactification.ofIsProper f) C).obj K) at hs
  apply (cancel_epi ((properFiniteIdentityNormalization A f).hom.app
    ((proEtaleCoefficientRestrictScalars X φ).mapDerivedCategory.obj
      ((proEtaleCoefficientRestrictScalars X ψ).mapDerivedCategory.obj K)))).mp
  dsimp only [sfAmbientCompactSupportCandidate, sfIntrinsicCompactSupport] at hφ hψ hc hn ht hs
  dsimp only [sfAmbientCompactSupportCandidate, sfIntrinsicCompactSupport]
  erw [← reassoc_of% hn, hc, reassoc_of% hs, ← ht]
  erw [reassoc_of% hφ, ← (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory.map_comp_assoc,
    ← hψ, (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory.map_comp]
  simp only [Category.assoc]

variable (P : PurityFiniteSetting.{u})
  {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]

/-- The comparison obtained by the prescribed common-refinement comparison to the
identity compactification, then the canonical identity-open normalization.
Source: blueprint proper-coincidence proof, first paragraph
(blueprint: lem-weil-proper-finite-normalization). -/
def properFiniteComparison (c : Compactification f) :
    (intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      P.level P.level_pos X).ι ⋙ sfIntrinsicCompactSupport c P.Ring ≅
    (intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      P.level P.level_pos X).ι ⋙ proEtaleConstantDerivedDirectImage f P.Ring :=
  P.clopenSupportCanonicalComparison c (Compactification.ofIsProper f) ≪≫
    Functor.isoWhiskerLeft _ (properFiniteIdentityNormalization P.Ring f)


/-- The next finite level of the same coefficient datum; this changes only the
positive integer exponent, keeping the field, extension, valuation ring and uniformizer.
Source: blueprint finite proper normalization, quotient paragraph
(blueprint: lem-weil-proper-finite-normalization). -/
def properNextLevel (P : PurityFiniteSetting.{u}) : PurityFiniteSetting.{u} :=
  { P with level := P.level + 1, level_pos := Nat.le_add_left 1 P.level }

/-- Bounded constructible inputs admit bounded constructible etale origins, and the
prescribed normalization commutes with every compactification comparison.
Source: latest blueprint proper-coincidence proof, first paragraph
(blueprint: lem-weil-proper-finite-normalization).

Proof: (1) For the identity open immersion every site object factors uniquely.
The extension presheaf is the original sheaf. Its sheafification unit has the unique
inverse supplied by the universal property (def-weil-presheaf-modules-sheafification).
This is the identity-open isomorphism sfIntrinsicOpenId, not an arbitrary isomorphism.
(2) Exactness (lem-weil-extension-by-zero-exact) descends this identification termwise
using lem-weil-pbc-exact-functor-derived-factorization. Whisker by Rf_* to get the
properFiniteIdentityNormalization on the whole unbounded category.
(3) Apply lem-sf-proetale-constructible-origin to obtain a bounded constructible etale
antecedent of each input. Bounded implies bounded below, so retain this as the origin
witness required by prop-compactification-coherence-detailed. The published unique
comparison clopenSupportCanonicalComparison is characterized on every such witness;
it is therefore independent of the witness and of the common refinement. Its cocycle
identity gives C(c,c') followed by alpha(c') equal to alpha(c). All maps are natural
isomorphisms on the full bounded constructible subcategory. -/
theorem properFiniteNormalization
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (_hf : f ≫ aY = aX) :
    (∀ K : (intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
        P.level P.level_pos X).FullSubcategory,
      ∃ L : DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)),
        Etale.DerivedCategory.isBoundedConstructible P.Coefficient X L.obj ∧
        Nonempty ((sfIntrinsicDerivedEquivalence X P.Ring).functor.obj
          ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj L.obj) ≅ K.obj)) ∧
    (∀ c c' : Compactification f,
      P.clopenSupportCanonicalComparison c c' ≪≫ P.properFiniteComparison f c' =
        P.properFiniteComparison f c) := by
  constructor
  · intro K
    have : (ProEtale.finiteCoefficientIntrinsicRealization X P.Ring).Additive :=
      ProEtale.finiteCoefficientIntrinsicRealization_additive X P.Ring
    have : PreservesFiniteLimits (ProEtale.finiteCoefficientIntrinsicRealization X P.Ring) :=
      ProEtale.finiteCoefficientIntrinsicRealization_preservesFiniteLimits X P.Ring
    have : PreservesFiniteColimits (ProEtale.finiteCoefficientIntrinsicRealization X P.Ring) :=
      ProEtale.finiteCoefficientIntrinsicRealization_preservesFiniteColimits X P.Ring
    obtain ⟨a, ha⟩ := K.property.1.bddBelow
    obtain ⟨b, hb⟩ := K.property.1.bddAbove
    have hv (q : ℤ) (hq : q < min a b ∨ max a b < q) :
        IsZero ((DerivedCategory.homologyFunctor _ q).obj K.obj) := by
      by_contra hz
      rcases hq with hq | hq
      · exact (not_lt_of_ge ((min_le_left a b).trans (ha hz))) hq
      · exact (not_lt_of_ge ((hb hz).trans (le_max_right a b))) hq
    obtain ⟨L, ⟨e⟩⟩ := (finiteRing_constructibleDerived_origin X P.Ring).2.2.1 K.obj
      |>.mpr ⟨K.property.2, min a b, max a b, min_le_max, hv⟩
    obtain ⟨c, d, hcd, hd⟩ := L.property.2
    have hplus : DerivedCategory.TStructure.t.plus L.obj :=
      ⟨c, (DerivedCategory.isGE_iff L.obj c).mpr (fun q hq ↦ hd q (Or.inl hq))⟩
    refine ⟨⟨L.obj, hplus⟩, L.property, ⟨?_⟩⟩
    exact ((Functor.mapDerivedCategoryCompIso
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X)
      (ProEtale.finiteCoefficientIntrinsicRealization X P.Ring)).app L.obj).symm ≪≫ e
  · intro c c'
    unfold properFiniteComparison
    rw [← Iso.trans_assoc,
      (P.clopenSupportCanonicalComparison_coherence c c' (Compactification.ofIsProper f)).2]


/-- The quotient square is an equality of natural transformations on the entire
unbounded derived category, with exactly the published open/proper restriction map.
Source: blueprint proper-coincidence proof, finite-level coefficient comparisons;
Stacks Tags 03CY and 0D6E (blueprint: lem-weil-proper-finite-normalization).

Proof: (4) Put S=Res_phi and let b be sfOpenRestriction at the identity open.
The maps a_A S and (S a_B)b are the same extension of the identity presheaf map.
Uniqueness of sheafification gives their equality, termwise and after localization.
The specified rho_! is F_A(b) followed by rho_* at the extended object, exactly
sfCompactSupportRestriction. Naturality of rho_* at a_B yields the displayed square.
(5) All its arrows are components of natural transformations, so this is natural
in every unbounded input, without requiring restriction to preserve K-injectives. -/
theorem properFiniteNormalization_quotient
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (_hf : f ≫ aY = aX)
    (φ : P.properNextLevel.Ring →+* P.Ring) (_hφ : Function.Surjective φ) :
    Functor.whiskerLeft (proEtaleCoefficientRestrictScalars X φ).mapDerivedCategory
        (properFiniteIdentityNormalization P.properNextLevel.Ring f).hom ≫
      (sfDerivedImageRestriction f φ).hom =
    (sfCompactSupportRestriction (Compactification.ofIsProper f) φ).hom ≫
      Functor.whiskerRight (properFiniteIdentityNormalization P.Ring f).hom
        (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory := by
  exact properFiniteIdentityNormalization_restrictScalars f φ

/-- Successive quotient comparisons compose, for ordinary and compact-support
images, with the canonical termwise restriction associators.
Source: blueprint proper-coincidence proof, finite-level comparison maps
(blueprint: lem-weil-proper-finite-normalization).

Proof: (5) Paste the quotient square for phi at Res_psi K with Res_phi of the
square for psi. The middle alpha_B edge cancels. The composition clause of
lem-sf-compact-support-restriction-of-scalars identifies the compact-support
composite with rho_!(psi phi). Compare with the square for the composite quotient;
cancel the invertible alpha_A to identify the ordinary direct-image composite too.
Thus the pasted square is exactly the square for the composite quotient. The
restriction associators displayed below are the sectionwise identity identifications,
so this also gives compatibility with any longer successive quotient chain. -/
theorem properFiniteNormalization_successive
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (_hf : f ≫ aY = aX)
    (φ : P.properNextLevel.properNextLevel.Ring →+* P.properNextLevel.Ring)
    (ψ : P.properNextLevel.Ring →+* P.Ring)
    (_hφ : Function.Surjective φ) (_hψ : Function.Surjective ψ)
    (K : proEtaleDerivedCategory X P.Ring) :
    ((proEtaleConstantDerivedDirectImage f P.properNextLevel.properNextLevel.Ring).map
        ((sfDerivedCoefficientRestrictionComp X φ ψ).hom.app K) ≫
      (sfDerivedImageRestriction f (ψ.comp φ)).hom.app K =
    (sfDerivedImageRestriction f φ).hom.app
        ((proEtaleCoefficientRestrictScalars X ψ).mapDerivedCategory.obj K) ≫
      (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory.map
        ((sfDerivedImageRestriction f ψ).hom.app K) ≫
      (sfDerivedCoefficientRestrictionComp Y φ ψ).hom.app
        ((proEtaleConstantDerivedDirectImage f P.Ring).obj K)) ∧
    ((sfIntrinsicCompactSupport (Compactification.ofIsProper f)
        P.properNextLevel.properNextLevel.Ring).map
        ((sfDerivedCoefficientRestrictionComp X φ ψ).hom.app K) ≫
      (sfCompactSupportRestriction (Compactification.ofIsProper f) (ψ.comp φ)).hom.app K =
    (sfCompactSupportRestriction (Compactification.ofIsProper f) φ).hom.app
        ((proEtaleCoefficientRestrictScalars X ψ).mapDerivedCategory.obj K) ≫
      (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory.map
        ((sfCompactSupportRestriction (Compactification.ofIsProper f) ψ).hom.app K) ≫
      (sfDerivedCoefficientRestrictionComp Y φ ψ).hom.app
        ((sfIntrinsicCompactSupport (Compactification.ofIsProper f) P.Ring).obj K)) ∧
    (Functor.whiskerLeft
        (proEtaleCoefficientRestrictScalars X (ψ.comp φ)).mapDerivedCategory
        (properFiniteIdentityNormalization P.properNextLevel.properNextLevel.Ring f).hom ≫
      (sfDerivedImageRestriction f (ψ.comp φ)).hom =
    (sfCompactSupportRestriction (Compactification.ofIsProper f) (ψ.comp φ)).hom ≫
      Functor.whiskerRight (properFiniteIdentityNormalization P.Ring f).hom
        (proEtaleCoefficientRestrictScalars Y (ψ.comp φ)).mapDerivedCategory) := by
  have hl := P.coefficientPrime_isUnit_stalk Y aY
  refine ⟨properFiniteImageRestriction_comp φ ψ f P.coefficients.l hl K, ?_, ?_⟩
  · exact sfCompactSupportRestriction_comp P.coefficients.l f hl
      (Compactification.ofIsProper f) φ ψ K
  · exact properFiniteIdentityNormalization_restrictScalars f (ψ.comp φ)

end WeilConjectures.PurityFiniteSetting
