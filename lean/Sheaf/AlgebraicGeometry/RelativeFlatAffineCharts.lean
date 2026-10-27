module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.RingTheory.OpenFlatLocus

/-! # Compatible affine charts and the flat stalk locus

Source: Stacks Project, Tag 05VJ, `lemma-base-change-criterion-flatness-fibre`, first two
proof sentences; Tag 02FV, `lemma-finite-presentation-permanence` (1); Tags 0399 and 00RC,
`theorem-openness-flatness`; Tags 01HV and 00HT (2).
(blueprint: lem-sfb-relative-flat-affine-charts)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem germ_appLE {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (Z : X.Opens) (hZV : Z ≤ f ⁻¹ᵁ V) (z : Z) (b : Γ(Y, V)) :
    f.stalkMap z (Y.presheaf.germ V (f z) (hZV z.2) b) =
      X.presheaf.germ Z z z.2 (f.appLE V Z hZV b) := by
  rw [f.germ_stalkMap_apply]
  exact (X.presheaf.germ_res_apply (homOfLE hZV) z z.2 (f.app V b)).symm

private theorem localized_flat_iff {B C : Type u} [CommRing B] [CommRing C]
    (φ : B →+* C) (r : PrimeSpectrum C) :
    ((algebraMap C (Localization.AtPrime r.asIdeal)).comp φ).Flat ↔
      (Localization.localRingHom (r.comap φ).asIdeal r.asIdeal φ rfl).Flat := by
  let : Algebra B C := φ.toAlgebra
  let ψ := Localization.localRingHom (r.comap φ).asIdeal r.asIdeal φ rfl
  let : Algebra (Localization.AtPrime (r.comap φ).asIdeal)
      (Localization.AtPrime r.asIdeal) := ψ.toAlgebra
  have : IsScalarTower B (Localization.AtPrime (r.comap φ).asIdeal)
      (Localization.AtPrime r.asIdeal) :=
    .of_algebraMap_eq fun b ↦ (Localization.localRingHom_to_map _ _ _ rfl b).symm
  have hcomp : (algebraMap C (Localization.AtPrime r.asIdeal)).comp φ =
      algebraMap B (Localization.AtPrime r.asIdeal) :=
    (IsScalarTower.algebraMap_eq B C (Localization.AtPrime r.asIdeal)).symm
  rw [hcomp, RingHom.flat_algebraMap_iff]
  exact (Module.flat_iff_of_isLocalization
    (Localization.AtPrime (r.comap φ).asIdeal) (r.comap φ).asIdeal.primeCompl
    (Localization.AtPrime r.asIdeal)).symm

private theorem isOpen_localized_flat {B C : Type u} [CommRing B] [CommRing C]
    (φ : B →+* C) (hφ : φ.FinitePresentation) :
    IsOpen {r : PrimeSpectrum C |
      ((algebraMap C (Localization.AtPrime r.asIdeal)).comp φ).Flat} := by
  let : Algebra B C := φ.toAlgebra
  have : Algebra.FinitePresentation B C := hφ
  have heq (r : PrimeSpectrum C) :
      ((algebraMap C (Localization.AtPrime r.asIdeal)).comp φ).Flat ↔
        Module.Flat B (LocalizedModule r.asIdeal.primeCompl C) := by
    have hcomp : (algebraMap C (Localization.AtPrime r.asIdeal)).comp φ =
        algebraMap B (Localization.AtPrime r.asIdeal) :=
      (IsScalarTower.algebraMap_eq B C (Localization.AtPrime r.asIdeal)).symm
    rw [hcomp, RingHom.flat_algebraMap_iff]
  simpa only [heq] using
    (Module.isOpen_setOf_flat_localizedModule (R := B) (S := C) (M := C))

private theorem affine_stalk_coordinates {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (Z : X.Opens) (hV : IsAffineOpen V) (hZ : IsAffineOpen Z)
    (hZV : Z ≤ f ⁻¹ᵁ V) :
    ∀ z : Z,
        (hZ.primeIdealOf z).comap (f.appLE V Z hZV).hom =
          hV.primeIdealOf ⟨f z, hZV z.2⟩ ∧
        ∃ (eC : X.presheaf.stalk z ≃+*
            Localization.AtPrime (hZ.primeIdealOf z).asIdeal)
          (eB : Y.presheaf.stalk (f z) ≃+*
            Localization.AtPrime
              ((hZ.primeIdealOf z).comap (f.appLE V Z hZV).hom).asIdeal),
          (∀ c : Γ(X, Z), eC (X.presheaf.germ Z z z.2 c) =
            algebraMap Γ(X, Z) (Localization.AtPrime (hZ.primeIdealOf z).asIdeal) c) ∧
          (∀ b : Γ(Y, V), eB (Y.presheaf.germ V (f z) (hZV z.2) b) =
            algebraMap Γ(Y, V)
              (Localization.AtPrime
                ((hZ.primeIdealOf z).comap (f.appLE V Z hZV).hom).asIdeal) b) ∧
          ∀ b, eC (f.stalkMap z (eB.symm b)) =
            Localization.localRingHom
              ((hZ.primeIdealOf z).comap (f.appLE V Z hZV).hom).asIdeal
              (hZ.primeIdealOf z).asIdeal (f.appLE V Z hZV).hom rfl b := by
  intro z
  have hp := IsAffineOpen.comap_primeIdealOf_appLE V hV Z hZ hZV z.2
  refine ⟨hp, ?_⟩
  let : Algebra Γ(X, Z) (X.presheaf.stalk z) := X.presheaf.algebra_section_stalk z
  let : Algebra Γ(Y, V) (Y.presheaf.stalk (f z)) :=
    Y.presheaf.algebra_section_stalk ⟨f z, hZV z.2⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk z)
      (hZ.primeIdealOf z).asIdeal :=
    hZ.isLocalization_stalk z
  have : IsLocalization.AtPrime (Y.presheaf.stalk (f z))
      ((hZ.primeIdealOf z).comap (f.appLE V Z hZV).hom).asIdeal := by
    rw [hp]
    exact hV.isLocalization_stalk ⟨f z, hZV z.2⟩
  let eC := IsLocalization.algEquiv (hZ.primeIdealOf z).asIdeal.primeCompl
    (X.presheaf.stalk z)
    (Localization.AtPrime (hZ.primeIdealOf z).asIdeal)
  let eB := IsLocalization.algEquiv
    ((hZ.primeIdealOf z).comap (f.appLE V Z hZV).hom).asIdeal.primeCompl
    (Y.presheaf.stalk (f z))
    (Localization.AtPrime
      ((hZ.primeIdealOf z).comap (f.appLE V Z hZV).hom).asIdeal)
  refine ⟨eC.toRingEquiv, eB.toRingEquiv, eC.commutes, eB.commutes, ?_⟩
  have heq : eC.toRingEquiv.toRingHom.comp
      ((f.stalkMap z).hom.comp eB.symm.toRingEquiv.toRingHom) =
      Localization.localRingHom
        ((hZ.primeIdealOf z).comap (f.appLE V Z hZV).hom).asIdeal
        (hZ.primeIdealOf z).asIdeal (f.appLE V Z hZV).hom rfl := by
    apply IsLocalization.ringHom_ext
      ((hZ.primeIdealOf z).comap (f.appLE V Z hZV).hom).asIdeal.primeCompl
    ext b
    change eC (f.stalkMap z (eB.symm (algebraMap _ _ b))) = _
    rw [eB.symm.commutes]
    change eC (f.stalkMap z (Y.presheaf.germ V (f z) (hZV z.2) b)) = _
    rw [germ_appLE]
    exact (eC.commutes _).trans (Localization.localRingHom_to_map _ _ _ rfl b).symm
  exact fun b ↦ DFunLike.congr_fun heq b

/-- Compatible affine neighborhoods of a morphism over a base, with canonical stalk
localization coordinates and the open flat locus. The coordinate rings are the section
rings of `W`, `V`, and `Z`. The normalization on germs specifies the canonical ring
isomorphisms, and the displayed local-ring homomorphism uses the inverse-image prime.

Source: Stacks Project, Tags 05VJ (first two proof sentences), 02FV (1), 0399, 00RC,
01IT, 01HV, and 00HT (2).
(blueprint: lem-sfb-relative-flat-affine-charts)

Proof:
1. Use `lem-weil-pbc-affine-opens-basis` to choose W around p(x), V inside q inverse W,
   and Z inside p inverse W intersect f inverse V. Refine the intersection by an affine
   open; it need not itself be affine. The structure-sheaf maps give the section-ring
   maps, whose composite is p's map by f followed by q = p and restriction functoriality
   (`def-weil-affine-spectrum`, `def-weil-locally-ringed-space-morphism`).
2. By `lem-a1-map-over-base-finite-presentation` (02FV), f is locally finitely presented.
   Apply `lem-weil-pbc-lft-affine-pairs` to (q,V,W), and
   `lem-weil-pbc-lfp-affine-opens-finite-presentation` to (p,Z,W) and (f,Z,V).
   These give B finite type over A and C finitely presented over both A and B.
3. By `lem-weil-pbc-affine-open-stalk-localization` (01HV), the prime of f(z) is the
   inverse image of that of z, and the two stalks are their section-ring localizations.
   The canonical equivalences send germs to fractions with denominator one. The stalk
   map sends the germ of b to the germ of its image, so sends b/t to phi(b)/phi(t).
4. Apply `lem-weil-pbc-openness-of-flatness` (00RC) with base B, algebra C, and module C.
   C is a finitely presented B-algebra by step 2 and a free rank-one C-module, so the
   locus where C localized at a prime is B-flat is open.
5. By `lem-weil-pbc-flat-over-localization` (00HT (2)), this localized ring is flat
   over B exactly when it is flat over B localized at the inverse-image prime.
   Step 3 identifies the latter with flatness of the stalk map, which is flatness of f
   at z (`def-weil-flat-morphism`). None of these steps requires p to be flat. -/
theorem exists_relative_flat_affine_charts {S X Y : Scheme.{u}}
    (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y) (hf : f ≫ q = p)
    [LocallyOfFinitePresentation p] [LocallyOfFiniteType q] (x : X) :
    ∃ (W : S.Opens) (V : Y.Opens) (Z : X.Opens)
      (_hW : IsAffineOpen W) (hV : IsAffineOpen V) (hZ : IsAffineOpen Z)
      (_hxW : p x ∈ W) (_hxV : f x ∈ V) (_hxZ : x ∈ Z)
      (hVW : V ≤ q ⁻¹ᵁ W) (hZW : Z ≤ p ⁻¹ᵁ W) (hZV : Z ≤ f ⁻¹ᵁ V),
      q.appLE W V hVW ≫ f.appLE V Z hZV = p.appLE W Z hZW ∧
      (q.appLE W V hVW).hom.FiniteType ∧
      (p.appLE W Z hZW).hom.FinitePresentation ∧
      (f.appLE V Z hZV).hom.FinitePresentation ∧
      (∀ z : Z,
        (hZ.primeIdealOf z).comap (f.appLE V Z hZV).hom =
          hV.primeIdealOf ⟨f z, hZV z.2⟩ ∧
        ∃ (eC : X.presheaf.stalk z ≃+*
            Localization.AtPrime (hZ.primeIdealOf z).asIdeal)
          (eB : Y.presheaf.stalk (f z) ≃+*
            Localization.AtPrime
              ((hZ.primeIdealOf z).comap (f.appLE V Z hZV).hom).asIdeal),
          (∀ c : Γ(X, Z), eC (X.presheaf.germ Z z z.2 c) =
            algebraMap Γ(X, Z) (Localization.AtPrime (hZ.primeIdealOf z).asIdeal) c) ∧
          (∀ b : Γ(Y, V), eB (Y.presheaf.germ V (f z) (hZV z.2) b) =
            algebraMap Γ(Y, V)
              (Localization.AtPrime
                ((hZ.primeIdealOf z).comap (f.appLE V Z hZV).hom).asIdeal) b) ∧
          ∀ b, eC (f.stalkMap z (eB.symm b)) =
            Localization.localRingHom
              ((hZ.primeIdealOf z).comap (f.appLE V Z hZV).hom).asIdeal
              (hZ.primeIdealOf z).asIdeal (f.appLE V Z hZV).hom rfl b) ∧
      IsOpen {r : PrimeSpectrum Γ(X, Z) |
        ((algebraMap Γ(X, Z) (Localization.AtPrime r.asIdeal)).comp
          (f.appLE V Z hZV).hom).Flat} ∧
      ∀ z : Z,
        ((algebraMap Γ(X, Z) (Localization.AtPrime (hZ.primeIdealOf z).asIdeal)).comp
          (f.appLE V Z hZV).hom).Flat ↔ (f.stalkMap z).hom.Flat := by
  have : LocallyOfFinitePresentation (f ≫ q) := hf.symm ▸ inferInstance
  have : LocallyOfFinitePresentation f := locallyOfFinitePresentation_of_comp f q
  obtain ⟨W, hW, hxW, _⟩ :=
    exists_isAffineOpen_mem_and_subset (show p x ∈ (⊤ : S.Opens) by simp)
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ q ⁻¹ᵁ W by simpa [← Scheme.Hom.comp_apply, hf] using hxW)
  obtain ⟨Z, hZa, hxZ, hsubZ⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ p ⁻¹ᵁ W ⊓ f ⁻¹ᵁ V from ⟨hxW, hxV⟩)
  have hZW : Z ≤ p ⁻¹ᵁ W := hsubZ.trans inf_le_left
  have hZV : Z ≤ f ⁻¹ᵁ V := hsubZ.trans inf_le_right
  refine ⟨W, V, Z, hW, hV, ‹IsAffineOpen Z›, hxW, hxV, hxZ, hVW, hZW, hZV,
    ?_, q.finiteType_appLE hW hV hVW, p.finitePresentation_appLE hW ‹_› hZW,
    f.finitePresentation_appLE hV ‹_› hZV,
    affine_stalk_coordinates f V Z hV hZa hZV,
    isOpen_localized_flat _ (f.finitePresentation_appLE hV ‹_› hZV), ?_⟩
  · rw [Scheme.Hom.appLE_comp_appLE]
    subst p
    rfl
  · intro z
    obtain ⟨_, eC, eB, _, _, hmap⟩ := affine_stalk_coordinates f V Z hV hZa hZV z
    have heq : eC.toRingHom.comp ((f.stalkMap z).hom.comp eB.symm.toRingHom) =
        Localization.localRingHom
          ((hZa.primeIdealOf z).comap (f.appLE V Z hZV).hom).asIdeal
          (hZa.primeIdealOf z).asIdeal (f.appLE V Z hZV).hom rfl := RingHom.ext hmap
    rw [localized_flat_iff, ← heq,
      RingHom.Flat.comp_iff_of_bijective_left eC.bijective,
      RingHom.Flat.comp_iff_of_bijective_right eB.symm.bijective]

end AlgebraicGeometry
