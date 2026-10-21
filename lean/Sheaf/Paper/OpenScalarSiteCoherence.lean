/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.SixFunctors.EtaleOpenTensor
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import Sheaf.Paper.WitnessCompatibility
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.CategoryTheory.RingedSliceExtensionTensor
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.AlgebraicGeometry.OpenComparisonTensorNormalization
import Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Open extension, scalar extension, and site comparison

Source: Stacks Project, Tags 0GL1, 0E8I, 09AF, 06YQ and 0G7E; the specified
scalar/site square and open composition laws
(blueprint: lem-sp-open-scalar-site-coherence).

## Main declarations

* `scalarOpen`: the canonical pro-etale scalar/open adjunction mate.
* `extension_flat_kflat`: preservation of the required flat models on both sites.
* `scalar_site_square`: the specified B-linear derived square.
* `etale_scalar_comp`, `proetale_scalar_comp`: scalar composition coherence.
* `etale_scalar_id`, `proetale_scalar_id`: scalar identity normalization.
* `site_comp`, `site_id`: derived site composition and identity coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.OpenScalarSite

/-- The recorded pro-etale coefficient realization, restricted along its canonical
commutative constant-ring comparison. The finite ring has its discrete topology.
Source: Stacks 00YV, 03CY and 03ER
(blueprint: lem-sp-open-scalar-site-coherence). -/
abbrev proRealization (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) :=
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  finiteCoefficientRealization X A ⋙
    SheafOfModules.restrictScalars (finiteCoefficientCommRingComparison A X)

/-- The sectionwise coefficient identification for pro-etale open restriction.
Source: Stacks 03EL, 03EK (blueprint: lem-sp-open-scalar-site-coherence). -/
def restrictScalarsIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    upperStar (ModuleCat.{u + 1} B) j ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology U) φ ≅
      Sheaf.restrictScalars (Scheme.ProEt.topology X) φ ⋙
        upperStar (ModuleCat.{u + 1} A) j :=
  Functor.isoWhiskerRight (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j) _ ≪≫
    (show openImmersionRestriction (ModuleCat.{u + 1} B) j ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology U) φ ≅
      Sheaf.restrictScalars (Scheme.ProEt.topology X) φ ⋙
        openImmersionRestriction (ModuleCat.{u + 1} A) j from
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)) ≪≫
    Functor.isoWhiskerLeft _
      (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).symm

/-- The canonical pro-etale scalar/open comparison. This is the mate of the literal
coefficient/restriction identification under the derived scalar and exact open
adjunctions. Thus it specifies the summand-preserving map, rather than choosing an
arbitrary isomorphism. Source: Stacks 0GL1, 0E8I, 06YY
(blueprint: lem-sp-open-scalar-site-coherence). -/
def scalarOpen {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        pbcFixedScalarExtension (Scheme.ProEt.topology X) φ ≅
      pbcFixedScalarExtension (Scheme.ProEt.topology U) φ ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory :=
  ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).comp
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ))).leftAdjointUniq
    (((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology U) φ)).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)).ofNatIsoRight
      (Functor.mapDerivedCategorySquareIso (restrictScalarsIso φ j)))

/-- Exact descent of the recorded pro-etale extension compositor.
Source: Stacks 03DI, 09AF (blueprint: lem-sp-open-scalar-site-coherence). -/
def extensionComp (A : Type (u + 1)) [CommRing A] {V U X : Scheme.{u}}
    (k : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion k] [IsOpenImmersion j] :=
  Functor.mapDerivedCategoryNatIso (proEtaleOpenExtensionComp A k j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The pro-etale identity extension identification, normalized by its adjunction.
Source: Stacks 03DI, 09AF (blueprint: lem-sp-open-scalar-site-coherence). -/
def extensionId (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  Functor.mapDerivedCategoryNatIso
    ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X)).leftAdjointUniq
      (Adjunction.id.ofNatIsoRight (upperStarId (ModuleCat.{u + 1} A) X).symm)) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Bounded flat models stay termwise flat and K-flat after extension by zero on
both sites (on the pro-etale site the input is the comparison pullback).
Source: Stacks 0GL1, 06YQ, 09AF (blueprint: lem-sp-open-scalar-site-coherence).
Proof: Restriction is exact and the sheaf projection formula identifies tensoring
with j!P with extension by zero of tensoring with P. Exactness of j! therefore
preserves flatness. Comparison inverse image is exact and preserves flat modules.
Apply these facts degreewise, then the bounded-flat-implies-K-flat lemma on each
site, using the canonical constant-coefficient realizations. -/
theorem extension_flat_kflat (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hflat : ∀ n : ℤ, Etale.etaleFlat U A (P.X n)) :
    (∀ n : ℤ, Etale.etaleFlat X A
      ((((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex
        (.up ℤ)).obj P).X n)) ∧
    Etale.etaleKFlat X A
      (((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex
        (.up ℤ)).obj P) ∧
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology X)
      (R := finiteCoefficientCommRing A X)
      ((proRealization A X).obj
        ((((comparisonUpperStar (ModuleCat.{u + 1} A) U ⋙
          openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex
            (.up ℤ)).obj P).X n))) ∧
    CochainComplex.IsKFlatIndependentCoefficients (J := Scheme.ProEt.topology X)
      (R := finiteCoefficientCommRing A X)
      (((comparisonUpperStar (ModuleCat.{u + 1} A) U ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} A) j ⋙ proRealization A X).mapHomologicalComplex
          (.up ℤ)).obj P) := by
  sorry

/-- The scalar/open/site square, in the ordinary fixed-coefficient derived
categories. All three comparisons are specified natural isomorphisms, so this
assertion is natural in L. Source: Stacks 0GL1, 0E8I, 09AF, 0G7E
(blueprint: lem-sp-open-scalar-site-coherence).
Proof: Resolve L by the bounded flat P. The preceding flatness result permits
all scalar comparisons to be computed on K-flat representatives. The ordinary
extension/tensor comparison preserves each extension summand; the site comparison
is normalized by its adjunction unit. Specialize the sheaf tensor/site square to
the constant B algebra, identifying its maps as the inverses of t and delta.
Rearrange this square in B-linear sheaves; no faithfulness of a derived forgetful
functor is used. Apply it degreewise to P and descend through localization.
Naturality and the representing isomorphism transport the result to L. -/
theorem scalar_site_square {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (L : Etale.DerivedCategoryModule A U)
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hflat : ∀ n : ℤ, Etale.etaleFlat U A (P.X n))
    (hrep : Nonempty ((DerivedCategory.Q.obj P) ≅ L)) :
    (pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).map
        ((mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} A) j).hom.app L) ≫
      (scalarOpen φ j).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj L) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((pbcComparisonReduction U φ).hom.app L) =
    (pbcComparisonReduction X φ).hom.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj L) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.map
        ((Etale.openScalarExtension φ j).hom.app L) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} B) j).hom.app
          ((Etale.scalarExtension φ U).obj L) := by
  sorry

/-- Scalar/open composition coherence on the etale site, with the canonical
open compositors. Source: Stacks 03DI, 0E8I, 0GL1
(blueprint: lem-sp-open-scalar-site-coherence).
Proof: The ordinary compositor composes the extension factorizations. Both
scalar routes send each generating section tensored with b to the same extension
generator with section s tensor b; if there is no factorization the source is
zero. The sheafification universal property gives equality of sheaf maps, also
through intermediate sheafification. Apply this calculation degreewise on K-flat
resolutions, preserved by open extension, and descend to the derived category.
Equivalently, compose the specified scalar/open adjunction mates and use their
uniqueness with the restriction compositor. -/
theorem etale_scalar_comp {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {V U X : Scheme.{u}}
    (k : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion k] [IsOpenImmersion j]
    (L : Etale.DerivedCategoryModule A V) :
    (Etale.scalarExtension φ X).map
        ((Etale.mapDerivedCategoryOpenImmersionLowerShriekComp
          (ModuleCat.{u + 1} A) k j).hom.app L) ≫
      (Etale.openScalarExtension φ j).hom.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj L) ≫
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((Etale.openScalarExtension φ k).hom.app L) ≫
      (Etale.mapDerivedCategoryOpenImmersionLowerShriekComp
        (ModuleCat.{u + 1} B) k j).inv.app ((Etale.scalarExtension φ V).obj L) =
    (Etale.openScalarExtension φ (k ≫ j)).hom.app L := by
  sorry

/-- The scalar/open comparison for the identity open is the identity after the
canonical identity identifications. Source: Stacks 03DI, 0E8I, 0GL1
(blueprint: lem-sp-open-scalar-site-coherence).
Proof: The unique identity factorization leaves every extension generator
unchanged. Tensoring its section gives the identity scalar comparison; apply the
sheafification universal property and descend on K-flat representatives.
The adjunction definition has exactly this identity normalization. -/
theorem etale_scalar_id {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (X : Scheme.{u})
    (L : Etale.DerivedCategoryModule A X) :
    (Etale.openScalarExtension φ (𝟙 X)).hom.app L ≫
      (Etale.mapDerivedCategoryOpenImmersionLowerShriekId
        (ModuleCat.{u + 1} B) X).hom.app ((Etale.scalarExtension φ X).obj L) =
    (Etale.scalarExtension φ X).map
      ((Etale.mapDerivedCategoryOpenImmersionLowerShriekId
        (ModuleCat.{u + 1} A) X).hom.app L) := by
  sorry

/-- Scalar/open composition coherence on the proetale site, with the canonical
open compositors. Source: Stacks 03DI, 0E8I, 0GL1
(blueprint: lem-sp-open-scalar-site-coherence).
Proof: The ordinary compositor composes the extension factorizations. Both
scalar routes send each generating section tensored with b to the same extension
generator with section s tensor b; if there is no factorization the source is
zero. The sheafification universal property gives equality of sheaf maps, also
through intermediate sheafification. Apply this calculation degreewise on K-flat
resolutions, preserved by open extension, and descend to the derived category.
Equivalently, compose the specified scalar/open adjunction mates and use their
uniqueness with the restriction compositor. -/
theorem proetale_scalar_comp {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {V U X : Scheme.{u}}
    (k : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion k] [IsOpenImmersion j]
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A))) :
    (pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).map ((extensionComp A k j).hom.app L) ≫
      (scalarOpen φ j).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj L) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((scalarOpen φ k).hom.app L) ≫
      (extensionComp B k j).inv.app ((pbcFixedScalarExtension (Scheme.ProEt.topology V) φ).obj L) =
    (scalarOpen φ (k ≫ j)).hom.app L := by
  sorry

/-- The scalar/open comparison for the identity open is the identity after the
canonical identity identifications. Source: Stacks 03DI, 0E8I, 0GL1
(blueprint: lem-sp-open-scalar-site-coherence).
Proof: The unique identity factorization leaves every extension generator
unchanged. Tensoring its section gives the identity scalar comparison; apply the
sheafification universal property and descend on K-flat representatives.
The adjunction definition has exactly this identity normalization. -/
theorem proetale_scalar_id {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (X : Scheme.{u})
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (scalarOpen φ (𝟙 X)).hom.app L ≫
      (extensionId B X).hom.app ((pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).obj L) =
    (pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).map ((extensionId A X).hom.app L) := by
  sorry

/-- Derived site comparisons compose with the same open compositors.
Source: Stacks 09AF (blueprint: lem-sp-open-scalar-site-coherence).
Proof: Use the recorded sheaf site-comparison composition identity, whose two
maps have the same transpose under the open adjunctions. Apply the degreewise
complex functor and localization. The derived functor composition isomorphisms
identify the resulting equation with this displayed equation. -/
theorem site_comp (R : Type (u + 1)) [CommRing R] [Finite R]
    {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j] (L : Etale.DerivedCategoryModule R V) :
    (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.map
        ((Etale.mapDerivedCategoryOpenImmersionLowerShriekComp
          (ModuleCat.{u + 1} R) k j).hom.app L) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} R) j).hom.app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) k).mapDerivedCategory.obj L) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.map
        ((mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} R) k).hom.app L) ≫
      (extensionComp R k j).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} R) V).mapDerivedCategory.obj L) =
    (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
      (ModuleCat.{u + 1} R) (k ≫ j)).hom.app L := by
  sorry

/-- The derived site comparison for the identity open is the identity after the
canonical identity identifications. Source: Stacks 09AF
(blueprint: lem-sp-open-scalar-site-coherence).
Proof: For the identity open, restriction and its comparison are identities.
The unit normalization of the site comparison forces the sheaf comparison to
be the identity. Apply degreewise complexes and localization to that recorded
identity, using the derived identity isomorphisms. -/
theorem site_id (R : Type (u + 1)) [CommRing R] [Finite R]
    (X : Scheme.{u}) (L : Etale.DerivedCategoryModule R X) :
    (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} R) (𝟙 X)).hom.app L ≫
      (extensionId R X).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.obj L) =
    (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.map
      ((Etale.mapDerivedCategoryOpenImmersionLowerShriekId
        (ModuleCat.{u + 1} R) X).hom.app L) := by
  sorry

end AlgebraicGeometry.ProEtale.OpenScalarSite
