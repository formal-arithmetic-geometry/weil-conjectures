module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Finite common fixed rings and their affine sheaves

Source: Stacks Project, Tags 00CO, 01HV, 01I3, 0091 and 009O; the finite
common-exponent argument in the proof of the field-quotient ingredient of the
blueprint, `det-thm-sf-ctf-stability-direct-images`, proof (3).
(blueprint: lem-sfb-finite-fixed-endomorphism-sheaf)

The sheaf is specified as a subobject of the direct image: its inclusion is
componentwise injective with image exactly the common fixed subring. This specifies
both its sections and the inherited restrictions, independently of a choice of carrier.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Type v} (σ : I → R →+* R)

/-- The common fixed subring, with no action laws imposed on the family.
Source: the finite-endomorphism argument preceding Stacks Tag 01I3 in the node.
(blueprint: lem-sfb-finite-fixed-endomorphism-sheaf) -/
def commonFixedSubring : Subring R :=
  ⨅ i, (σ i).eqLocus (RingHom.id R)

/-- The spectrum map of the actual inclusion of the common fixed subring.
Source: Stacks, affine spectra and Tag 01I3.
(blueprint: lem-sfb-finite-fixed-endomorphism-sheaf) -/
noncomputable def commonFixedSpecMap : Spec (.of R) ⟶ Spec (.of (commonFixedSubring σ)) :=
  Spec.map (CommRingCat.ofHom (commonFixedSubring σ).subtype)

/-- The inclusion localized at a common fixed element.
Source: Stacks Tag 00CO, induced maps of localizations.
(blueprint: lem-sfb-finite-fixed-endomorphism-sheaf) -/
noncomputable def commonFixedLocalizedInclusion (f : commonFixedSubring σ) :
    Localization.Away f →+* Localization.Away (f : R) :=
  IsLocalization.map (M := Submonoid.powers f) (T := Submonoid.powers (f : R))
    _ (commonFixedSubring σ).subtype
    (Submonoid.powers_le.mpr (Submonoid.mem_powers (f : R)))

/-- The localized endomorphism, constructed by localization functoriality.
The proof term says that the image of the generator is the same generator.
Source: Stacks Tag 00CO, the node's finite-endomorphism argument, Step 1.
(blueprint: lem-sfb-finite-fixed-endomorphism-sheaf) -/
noncomputable def commonFixedLocalizedEndomorphism (f : commonFixedSubring σ) (i : I) :
    Localization.Away (f : R) →+* Localization.Away (f : R) :=
  IsLocalization.map (M := Submonoid.powers (f : R))
    (T := Submonoid.powers (f : R)) _ (σ i)
    (Submonoid.powers_le.mpr
      ⟨1, (pow_one (f : R)).trans (Subring.mem_iInf.mp f.property i).symm⟩)

/-- Every endomorphism preserves every open pulled back from the fixed spectrum.
Source: functoriality of affine spectra, as used in Step 1 of the node.
Proof: the fixed-subring inclusion j satisfies σ_i j = j. Contravariance gives
Spec(σ_i) followed by p equal to p. Taking inverse images of T gives the equality.
(blueprint: lem-sfb-finite-fixed-endomorphism-sheaf) -/
theorem commonFixedEndomorphism_preimage (i : I)
    (T : (Spec (.of (commonFixedSubring σ))).Opens) :
    Spec.map (CommRingCat.ofHom (σ i)) ⁻¹ᵁ (commonFixedSpecMap σ ⁻¹ᵁ T) =
      commonFixedSpecMap σ ⁻¹ᵁ T := by
  sorry

/-- Pullback on sections over the invariant inverse-image open. The transport is
along the proved equality of opens, so this is the actual structure-sheaf map.
Source: Stacks Tag 0091, morphisms of ringed spaces; Step 1 of the node.
(blueprint: lem-sfb-finite-fixed-endomorphism-sheaf) -/
noncomputable def commonFixedSectionEndomorphism (i : I)
    (T : (Spec (.of (commonFixedSubring σ))).Opens) :
    Γ(Spec (.of R), commonFixedSpecMap σ ⁻¹ᵁ T) →+*
      Γ(Spec (.of R), commonFixedSpecMap σ ⁻¹ᵁ T) :=
  ((Spec.map (CommRingCat.ofHom (σ i))).app (commonFixedSpecMap σ ⁻¹ᵁ T) ≫
    (Spec (.of R)).presheaf.map
      (eqToHom (commonFixedEndomorphism_preimage σ i T).symm).op).hom

/-- The structure sheaf of the common fixed ring is precisely the sheaf of common
fixed sections, with its canonical inclusion and its principal-localization components.
Source: Stacks Tags 01HV, 01I3 and 009O; Steps 1--6 of the node.
Proof: (1) use σ_i j = j to preserve inverse-image opens and to induce the section
endomorphisms. (2) the localized inclusion is injective by the zero-fraction criterion.
(3) clear all finitely many annihilating powers simultaneously to identify its image
with the common fixed ring, including the empty family. (4) compatible fixed sections
glue in the direct image structure sheaf; uniqueness of gluing shows the glued section
is fixed. Naturality gives the inherited restrictions and corestricts p-sharp.
(5) on D_A(f), the affine section-localization identifications of 01HV/01I3 identify
p-sharp with the localized inclusion and the section endomorphisms with σ_i localized:
check on r/1 and on the inverse of f/1. (6) the D_A(f) form a basis, so 009O promotes
the componentwise isomorphisms to a sheaf isomorphism. Naturality of this isomorphism
and its inverse gives compatibility with restrictions between every pair of opens.
(blueprint: lem-sfb-finite-fixed-endomorphism-sheaf) -/
theorem finite_fixed_endomorphism_sheaf [Finite I] :
    (∀ f : commonFixedSubring σ,
      Function.Injective (commonFixedLocalizedInclusion σ f) ∧
        (commonFixedLocalizedInclusion σ f).range =
          commonFixedSubring (commonFixedLocalizedEndomorphism σ f)) ∧
    ∃ (F : TopCat.Sheaf CommRingCat.{u} (Spec (.of (commonFixedSubring σ))).carrier)
      (ι : F.obj ⟶ (commonFixedSpecMap σ).base _* (Spec (.of R)).presheaf)
      (θ : (Spec (.of (commonFixedSubring σ))).sheaf ≅ F),
      θ.hom.hom ≫ ι = (commonFixedSpecMap σ).c ∧
      (∀ T : (Spec (.of (commonFixedSubring σ))).Opens,
        Function.Injective (ι.app (op T)) ∧
          (ι.app (op T)).hom.range =
            commonFixedSubring (fun i : I ↦ commonFixedSectionEndomorphism σ i T)) ∧
      (∀ (f : commonFixedSubring σ) (z : Localization.Away f),
        (ι.app (op (PrimeSpectrum.basicOpen f)))
            ((θ.hom.hom.app (op (PrimeSpectrum.basicOpen f)))
              (IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f)
                ((Spec.structureSheaf (commonFixedSubring σ)).obj.obj
                  (op (PrimeSpectrum.basicOpen f))) z)) =
          IsLocalization.algEquiv (Submonoid.powers (f : R))
            (Localization.Away (f : R))
            ((Spec.structureSheaf R).obj.obj (op (PrimeSpectrum.basicOpen (f : R))))
            (commonFixedLocalizedInclusion σ f z)) ∧
      (∀ (f : commonFixedSubring σ) (i : I) (z : Localization.Away (f : R)),
        commonFixedSectionEndomorphism σ i (PrimeSpectrum.basicOpen f)
            (IsLocalization.algEquiv (Submonoid.powers (f : R))
              (Localization.Away (f : R))
              ((Spec.structureSheaf R).obj.obj (op (PrimeSpectrum.basicOpen (f : R)))) z) =
          IsLocalization.algEquiv (Submonoid.powers (f : R))
            (Localization.Away (f : R))
            ((Spec.structureSheaf R).obj.obj (op (PrimeSpectrum.basicOpen (f : R))))
            (commonFixedLocalizedEndomorphism σ f i z)) := by
  sorry

end AlgebraicGeometry
