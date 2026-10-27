/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Topology.InverseImageModule
public import WeilConjectures.Topology.RingedModuleSkyscraper
public import Sheaf.Algebra.Homology.SheafComplexDerivedTensorVanishes
public import WeilConjectures.AlgebraicGeometry.InverseImageStructureStalkIso
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Localization
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.AlgebraicGeometry.RelativeInverseImageStalkRestriction
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatStalkCriterion
import WeilConjectures.Algebra.Homology.InverseImageStalkScalarTransportNaturality
import Sheaf.Algebra.Homology.RingedKFlatSingleTensorComparison
import WeilConjectures.Algebra.Homology.StalkTensorComplex
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Derived relative affine stalk and base-skyscraper comparisons

Source: Stacks Project, perfect.tex, Tag 0DHY, opening stalk identifications;
sheaves.tex, Tags 008H, 008X, 0098, 009A; sites-cohomology.tex, Tag 06YU.
(blueprint: lem-trf-affine-relative-stalk-resolution-iso).

The helpers name the actual affine objects and scalar maps. The derived stalk functor
is specified by its localization factorization, without choosing a second exactness API.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u wB wT

open CategoryTheory TopologicalSpace MonoidalCategory

namespace AlgebraicGeometry
namespace AffineRelativeStalk

variable {R A : Type u} [CommRing R] [CommRing A]

/-- The ringed space `(Spec A, f⁻¹ O_Spec R)` of Stacks Tag 0DHY.
(blueprint: lem-trf-affine-relative-stalk-resolution-iso). -/
abbrev ringedSpace (φ : R →+* A) : RingedSpace.{u} where
  carrier := (Spec (.of A)).carrier
  presheaf := (TopCat.Sheaf.inverseImageRing (Spec.map (CommRingCat.ofHom φ)).base
    (Spec (.of R)).sheaf).obj
  IsSheaf := (TopCat.Sheaf.inverseImageRing (Spec.map (CommRingCat.ofHom φ)).base
    (Spec (.of R)).sheaf).property

/-- The canonical inverse-image ring stalk map: presheaf pullback followed by sheafification.
Source: Stacks Tags 008H, 007Z; this is the map used in Tag 0DHY.
(blueprint: lem-trf-affine-relative-stalk-resolution-iso). -/
def inverseImageStalkMap (φ : R →+* A) (x : PrimeSpectrum A) :
    (Spec (.of R)).presheaf.stalk (PrimeSpectrum.comap φ x) ⟶
      (ringedSpace φ).presheaf.stalk x :=
  TopCat.Presheaf.stalkPullbackHom CommRingCat.{u} (Spec.map (CommRingCat.ofHom φ)).base
      (Spec (.of R)).presheaf x ≫
    (TopCat.Presheaf.stalkFunctor (X := (Spec (.of A)).toTopCat) CommRingCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology (Spec (.of A)))
        ((TopCat.Presheaf.pullback CommRingCat.{u} (Spec.map (CommRingCat.ofHom φ)).base).obj
          (Spec (.of R)).presheaf))

/-- The specified map `e_x = k j`, from the affine germ map and canonical inverse-image map.
Source: Stacks Tag 0DHY, with Tags 01HV, 008H and 007Z.
(blueprint: lem-trf-affine-relative-stalk-resolution-iso). -/
def scalarMap (φ : R →+* A) (x : PrimeSpectrum A) :
    Localization.AtPrime (PrimeSpectrum.comap φ x).asIdeal →+*
      (ringedSpace φ).presheaf.stalk x :=
  ((Spec.stalkIso (.of R) (PrimeSpectrum.comap φ x)).inv ≫
    inverseImageStalkMap φ x).hom

/-- The module stalk at x followed by restriction along the specified `e_x`.
Source: Stacks Tag 0DHY, opening stalk calculation.
(blueprint: lem-trf-affine-relative-stalk-resolution-iso). -/
abbrev stalkFunctor (φ : R →+* A) (x : PrimeSpectrum A) :
    RingedSpace.Modules (ringedSpace φ) ⥤
      ModuleCat.{u} (Localization.AtPrime (PrimeSpectrum.comap φ x).asIdeal) :=
  RingedSpace.moduleStalkFunctor (ringedSpace φ) x ⋙
    ModuleCat.restrictScalars (scalarMap φ x)

/-- Restrict the termwise tilde complex along the actual inverse-image structure map.
Source: Stacks Tag 0DHY; Tag 06Z0 supplies termwise tilde.
(blueprint: lem-trf-affine-relative-stalk-resolution-iso). -/
def restrictedTilde (φ : R →+* A) (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex (RingedSpace.Modules (ringedSpace φ)) ℤ :=
  ((SheafOfModules.restrictScalars
    ((sheafCompose (Opens.grothendieckTopology (Spec (.of A)))
      (forget₂ CommRingCat.{u} RingCat.{u})).map
        (Scheme.Modules.tensorPullbackRingMap
          (Spec.map (CommRingCat.ofHom φ))))).mapHomologicalComplex
          (.up ℤ)).obj
    ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (tilde.functor (.of A)) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)

/-- Termwise localization at q, with scalars restricted along `R_p → A_q`.
The Mathlib localization functor uses the canonically isomorphic small model of LocalizedModule.
Source: Stacks Tag 0DHY, opening identification `E_x = M_q`.
(blueprint: lem-trf-affine-relative-stalk-resolution-iso). -/
def localizedComplex (φ : R →+* A) (x : PrimeSpectrum A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex
      (ModuleCat.{u} (Localization.AtPrime (PrimeSpectrum.comap φ x).asIdeal)) ℤ :=
  (((ModuleCat.localizedModuleFunctor x.asIdeal.primeCompl) ⋙
    ModuleCat.restrictScalars (Localization.localRingHom
      (PrimeSpectrum.comap φ x).asIdeal x.asIdeal φ rfl)).mapHomologicalComplex (.up ℤ)).obj M

/-- The base stalk viewed over `R_p` using the affine germ identification.
Source: Stacks Tags 01HV and 0DHY.
(blueprint: lem-trf-affine-relative-stalk-resolution-iso). -/
def baseStalkFunctor (φ : R →+* A) (x : PrimeSpectrum A) :
    RingedSpace.Modules (Spec (.of R)).toRingedSpace ⥤
      ModuleCat.{u} (Localization.AtPrime (PrimeSpectrum.comap φ x).asIdeal) :=
  RingedSpace.moduleStalkFunctor (Spec (.of R)).toRingedSpace (PrimeSpectrum.comap φ x) ⋙
    ModuleCat.restrictScalars (Spec.stalkIso (.of R) (PrimeSpectrum.comap φ x)).inv.hom

/-- The canonical topological inverse-image module, with no extension to O_Spec A.
Source: Stacks Tags 008X and 008Y, as used in Tag 0DHY.
(blueprint: lem-trf-affine-relative-stalk-resolution-iso). -/
def inverseImage (φ : R →+* A)
    (G : RingedSpace.Modules (Spec (.of R)).toRingedSpace) :
    RingedSpace.Modules (ringedSpace φ) :=
  TopCat.Sheaf.inverseImageModule (Spec.map (CommRingCat.ofHom φ)).base (Spec (.of R)).sheaf G

/-- The base skyscraper of an arbitrary R_p-module, transported to O_Spec R,p by j⁻¹.
Source: Stacks Tags 009A and 009B, used in the stalk argument of Tag 0DHY.
(blueprint: lem-trf-affine-relative-stalk-resolution-iso). -/
def skyscraper (φ : R →+* A) (x : PrimeSpectrum A)
    (L : ModuleCat.{u} (Localization.AtPrime (PrimeSpectrum.comap φ x).asIdeal)) :
    RingedSpace.Modules (Spec (.of R)).toRingedSpace :=
  (SheafOfModules.ringedModuleSkyscraperFunctor (Spec (.of R)).toRingedSpace
    (PrimeSpectrum.comap φ x)).obj
      ((ModuleCat.restrictScalars
        (Spec.stalkIso (.of R) (PrimeSpectrum.comap φ x)).hom.hom).obj L)

end AffineRelativeStalk
end AlgebraicGeometry

namespace AlgebraicGeometry.AffineRelativeStalk

variable {R A : Type u} [CommRing R] [CommRing A]

/-- S_x applied termwise, using the existing module stalk and scalar restriction functors.
Source: Stacks Tag 0DHY (blueprint: lem-trf-affine-relative-stalk-resolution-iso). -/
def complexStalkFunctor (φ : R →+* A) (x : PrimeSpectrum A) :
    CochainComplex (RingedSpace.Modules (ringedSpace φ)) ℤ ⥤
      CochainComplex
        (ModuleCat.{u} (Localization.AtPrime (PrimeSpectrum.comap φ x).asIdeal)) ℤ :=
  (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (RingedSpace.moduleStalkFunctor (ringedSpace φ) x)
    (RingedSpace.moduleStalkFunctor_preservesZeroMorphisms (ringedSpace φ) x) (.up ℤ)) ⋙
    (ModuleCat.restrictScalars (scalarMap φ x)).mapHomologicalComplex (.up ℤ)

/-- The actual sheaf derived tensor with the topological inverse image of G in degree zero.
Source: Stacks Tags 06YU and 0DHY.
(blueprint: lem-trf-affine-relative-stalk-resolution-iso). -/
def tensorWithInverseImage (φ : R →+* A)
    [HasDerivedCategory.{wB} (RingedSpace.Modules (ringedSpace φ))]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (G : RingedSpace.Modules (Spec (.of R)).toRingedSpace) :
    DerivedCategory (RingedSpace.Modules (ringedSpace φ)) :=
  (SheafOfModules.siteDerivedTensorIndependentCoefficients
    (Opens.grothendieckTopology (Spec (.of A))) (ringedSpace φ).sheaf).obj
      (DerivedCategory.Q.obj (restrictedTilde φ M),
        DerivedCategory.Q.obj
          ((HomologicalComplex.single _ (.up ℤ) 0).obj (inverseImage φ G)))

/-- The module derived tensor `Q(M_q) ⊗ᴸ N[0]` over R_p, using the K-flat monoidal tensor.
Source: Stacks Tags 06XZ, 06YU and 0DHY.
(blueprint: lem-trf-affine-relative-stalk-resolution-iso). -/
def localizedTensor (φ : R →+* A) (x : PrimeSpectrum A)
    [HasDerivedCategory.{wT}
      (ModuleCat.{u} (Localization.AtPrime (PrimeSpectrum.comap φ x).asIdeal))]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (N : ModuleCat.{u} (Localization.AtPrime (PrimeSpectrum.comap φ x).asIdeal)) :
    DerivedCategory
      (ModuleCat.{u} (Localization.AtPrime (PrimeSpectrum.comap φ x).asIdeal)) :=
  DerivedCategory.Q.obj (localizedComplex φ x M) ⊗
    (DerivedCategory.singleFunctor _ 0).obj N

end AlgebraicGeometry.AffineRelativeStalk

namespace AlgebraicGeometry

/-- Relative affine stalk comparisons, with arbitrary complexes and arbitrary base modules.
The derived functor S is characterized by its natural factorization of Q. All isomorphisms
are in D(R_p), before applying cohomology. No flatness, finiteness, boundedness or
Noetherian condition is assumed.

Source: Stacks Project, perfect.tex, Tag 0DHY, opening stalk identifications; sheaves.tex,
Tags 008H, 008X, 0098, 009A, 009B; sites-cohomology.tex, Tags 06YS and 06YU.
(blueprint: lem-trf-affine-relative-stalk-resolution-iso).

Proof (the six steps of the node):
1. Write y=f(x), T=R_p and B=(f⁻¹O_V)_x. The canonical k is stalkPullbackHom followed
   by the stalk of toSheafify. Both maps are invertible (Tags 008H and 007Z).
   Its composite with the stalk of tensorPullbackRingMap is f.stalkMap, checked on germs.
   Compose k with the affine germ isomorphism j to get e_x. Apply
   lem-pc-relative-inverse-image-stalk-restriction to the termwise tilde complex.
   The affine stalk-map formula identifies the scalar action with R_p → A_q.
   The tilde localization map sends the germ of a⁻¹ tau(m) to m/a. Tilde of a
   differential sends this to d(m)/a, so the degreewise identifications form a complex iso t.
2. Stalks are exact (lem-weil-pbc-module-stalk-exact); restriction along e_x is exact
   on underlying additive groups. Exact-functor derived factorization gives S and its
   natural factorization. Put theta=Q(t). A K-flat resolution u is a quasi-isomorphism;
   exactness makes S_x u a quasi-isomorphism, so Q(S_x u) followed by theta is invertible.
3. Choose a K-flat resolution over the inverse-image ring (lem-pc-kflat-resolution).
   By lem-pc-kflat-stalk-criterion its stalk is K-flat over B. Transport across the ring
   isomorphism e_x preserves acyclicity and balanced total tensors, hence K-flatness.
   This does not use flatness of R_p → A_q.
4. For H=f⁻¹G use lem-pc-ringed-inverse-image-stalk-scalar-transport-naturality.
   Its semilinear comparison uses exactly k. Since e_x=k j, its inverse is T-linear
   and identifies S_x H with G_y viewed over T.
5. By lem-sf-ringed-kflat-single-tensor-comparison compute the sheaf tensor on the
   chosen K-flat first factor. Apply the exact derived stalk. The stalk tensor iso of
   lem-pc-stalk-tensor-complex and transport along e_x identify its representative with
   the total module tensor. Use lem-pc-source-kflat-module-tensor-model, then apply
   the derived tensor bifunctor to theta Q(S_x u) and the comparison of Step 4.
6. For any T-module L form the base skyscraper after transporting L along j⁻¹.
   Every neighborhood of y has sections L with identity restrictions, so the germ map
   gives G_y ≅ L, linearly. Step 4 gives (f⁻¹G)_x ≅ L and Step 5 gives the tensor
   specialization. This works at nonclosed points and for the zero module.
-/
theorem exists_affineRelativeStalkResolutionIso
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    (x : PrimeSpectrum A) (M : CochainComplex (ModuleCat.{u} A) ℤ)
    [HasDerivedCategory.{wB} (RingedSpace.Modules (AffineRelativeStalk.ringedSpace φ))]
    [HasDerivedCategory.{wT}
      (ModuleCat.{u} (Localization.AtPrime (PrimeSpectrum.comap φ x).asIdeal))] :
    ∃ θ : DerivedCategory.Q.obj
          ((AffineRelativeStalk.complexStalkFunctor φ x).obj
            (AffineRelativeStalk.restrictedTilde φ M)) ≅
        DerivedCategory.Q.obj (AffineRelativeStalk.localizedComplex φ x M),
      (∀ (P : CochainComplex
          (RingedSpace.Modules (AffineRelativeStalk.ringedSpace φ)) ℤ)
        (u : P ⟶ AffineRelativeStalk.restrictedTilde φ M),
        CochainComplex.IsKFlatResolutionIndependentCoefficients u →
          IsIso (DerivedCategory.Q.map
            ((AffineRelativeStalk.complexStalkFunctor φ x).map u) ≫ θ.hom)) ∧
      ∃ S : DerivedCategory (RingedSpace.Modules (AffineRelativeStalk.ringedSpace φ)) ⥤
          DerivedCategory
            (ModuleCat.{u} (Localization.AtPrime (PrimeSpectrum.comap φ x).asIdeal)),
        Nonempty (DerivedCategory.Q ⋙ S ≅
          AffineRelativeStalk.complexStalkFunctor φ x ⋙ DerivedCategory.Q) ∧
        (∀ G : RingedSpace.Modules (Spec (.of R)).toRingedSpace,
          Nonempty (S.obj (AffineRelativeStalk.tensorWithInverseImage φ M G) ≅
            AffineRelativeStalk.localizedTensor φ x M
              ((AffineRelativeStalk.baseStalkFunctor φ x).obj G))) ∧
        ∀ L : ModuleCat.{u} (Localization.AtPrime (PrimeSpectrum.comap φ x).asIdeal),
          Nonempty ((AffineRelativeStalk.baseStalkFunctor φ x).obj
            (AffineRelativeStalk.skyscraper φ x L) ≅ L) ∧
          Nonempty ((AffineRelativeStalk.stalkFunctor φ x).obj
            (AffineRelativeStalk.inverseImage φ (AffineRelativeStalk.skyscraper φ x L)) ≅ L) ∧
          Nonempty (S.obj (AffineRelativeStalk.tensorWithInverseImage φ M
            (AffineRelativeStalk.skyscraper φ x L)) ≅
              AffineRelativeStalk.localizedTensor φ x M L) := by
  sorry

end AlgebraicGeometry
