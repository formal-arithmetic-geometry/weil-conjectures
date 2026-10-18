/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Triangulated.Functor
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.CategoryTheory.RightKanExtensionCoherentShift
import Sheaf.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Sheaf.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import Sheaf.CategoryTheory.LeftDerivedKanSourceTriangles
import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel

/-! # The counit-compatible shift of derived scalar extension

Source: Stacks Project, derived.tex, Tags 05SU(2), 05SE (left derived functor part),
and sites-cohomology.tex, Tag 06YY
(blueprint: lem-sbc-derived-scalar-extension-counit-shift).

The ordinary functor is identified on both objects and maps with the existing
change of rings. Its induced homotopy functor has the canonical shift comparison
induced by identity maps in each degree, not a freely chosen shift structure.
The conclusion specifies a natural degree-one isomorphism, uniqueness among all
natural isomorphisms satisfying the counit equation, and preservation of every
distinguished triangle with precisely that isomorphism on the last arrow.
This statement is re-recorded by group NM on 2026-10-17.
-/

@[expose] public section

set_option autoImplicit false

universe u v r wR wS

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace SheafOfModules

/-- The derived scalar-extension counit determines a unique natural shift comparison,
and this comparison makes derived scalar extension triangulated.
Source: Stacks Project, derived.tex, Tags 05SU(2), 05SE (LF part), and
sites-cohomology.tex, Tag 06YY
(blueprint: lem-sbc-derived-scalar-extension-counit-shift).

Here `E` is ordinary change of rings on module sheaves; its homotopy functor is the
statement's termwise functor. The objects and maps of `E` are fixed by `h` and `hmap`.
The `commShiftIso` of `E.mapHomotopyCategory` is induced by
`E.mapCochainComplexShiftIso`, whose degree components are identities. Thus the
right side of the equation is exactly the composite of the derived counit,
`Q_S(theta_P)` and the localization shift isomorphism, in that order.
No coherent shift structure on `F`, flatness of `S`, or bound on complexes is assumed.

Proof:
1. Termwise change of rings is additive. It preserves the cone biproduct and its
matrix differential, and carries a homotopy dh+hd to the corresponding homotopy.
Consequently it descends to the homotopy category and preserves cone triangles,
including the negative projection (def-pur-sheaf-tensor-product,
def-weil-abstract-derived-category, lem-pur-homotopy-category-triangulated).
2. Use the class of K-flat complexes with flat terms. Every complex has such a
resolution (lem-pc-kflat-resolution), and tensor inverts quasi-isomorphisms between
these resolutions (lem-pur-derived-change-of-rings). The resolving-class theorem
(lem-pur-left-derived-from-kflat-class) gives the everywhere-defined universal
pair, with invertible counit on that class. The given pair is such a left derived pair.
3. For every integer n, termwise tensor of the shifted complex and the shift of
its tensor have the same terms and signed differentials. Identity maps in every
degree give the coherent shift isomorphism. Composing with localization gives
the comparison of B = E.mapHomotopyCategory followed by Q_S.
4. Apply lem-pur-right-kan-extension-coherent-shift to Q_R, B and the given
universal pair F, epsilon. Its degree-one counit square is the displayed equation.
5. For uniqueness, postcomposition by shift preserves the right Kan property.
For two competing natural isomorphisms, cancel F(s_P) in their counit equations.
Injectivity of the Kan universal correspondence for the shifted target functor
identifies their natural transformations, hence their isomorphisms. Equivalently,
shift back and use the universal correspondence of
lem-pur-left-derived-from-kflat-class. No coherence or triangle preservation is
required of the competing degree-one isomorphism.
6. Quasi-isomorphisms are a saturated triangulated multiplicative system
(lem-pur-quasi-isos-saturated-triangulated). The same resolving class gives
essential constancy of the denominator diagrams
(lem-pur-resolving-class-essential-constancy). Apply
lem-pur-left-derived-kan-source-triangles with the counit-compatible coherent
shift from step 4: images of distinguished homotopy triangles are distinguished.
Every distinguished derived triangle is isomorphic to such an image
(lem-pur-localization-triangles-05r6). Applying F to the three isomorphisms gives
an isomorphism of image triangles; its last square uses naturality of sigma.
Closure under isomorphism proves the final clause for the very same sigma
(def-weil-triangulated-category). Exactness also gives additivity of F. -/
theorem derivedScalarExtension_counitShift
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
    [HasDerivedCategory.{wR} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S))]
    (E : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R) ⥤
      ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S))
    (h : ∀ M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R),
      E.obj M = changeOfRings.{v, u, r} φ M)
    (hmap : ∀ {M N : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)}
      (f : M ⟶ N),
      E.map f = eqToHom (h M) ≫ changeOfRingsHom.{v, u, r} φ M f ≫ eqToHom (h N).symm)
    [E.Additive]
    (F : DerivedCategory (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) ⥤
      DerivedCategory (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S)))
    (ε : DerivedCategory.Qh ⋙ F ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [F.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) (.up ℤ))] :
    ∃ σ : shiftFunctor _ (1 : ℤ) ⋙ F ≅ F ⋙ shiftFunctor _ (1 : ℤ),
      (∀ P : HomotopyCategory
          (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) (.up ℤ),
        F.map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app P) ≫
            σ.hom.app (DerivedCategory.Qh.obj P) ≫
            (shiftFunctor _ (1 : ℤ)).map (ε.app P) =
          ε.app ((shiftFunctor _ (1 : ℤ)).obj P) ≫
            DerivedCategory.Qh.map
              (((E.mapHomotopyCategory (.up ℤ)).commShiftIso (1 : ℤ)).hom.app P) ≫
            (DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app
              ((E.mapHomotopyCategory (.up ℤ)).obj P)) ∧
      (∀ τ : shiftFunctor _ (1 : ℤ) ⋙ F ≅ F ⋙ shiftFunctor _ (1 : ℤ),
        (∀ P : HomotopyCategory
            (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) (.up ℤ),
          F.map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app P) ≫
              τ.hom.app (DerivedCategory.Qh.obj P) ≫
              (shiftFunctor _ (1 : ℤ)).map (ε.app P) =
            ε.app ((shiftFunctor _ (1 : ℤ)).obj P) ≫
              DerivedCategory.Qh.map
                (((E.mapHomotopyCategory (.up ℤ)).commShiftIso (1 : ℤ)).hom.app P) ≫
              (DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app
                ((E.mapHomotopyCategory (.up ℤ)).obj P)) → τ = σ) ∧
      F.Additive ∧
      ∀ T : Triangle (DerivedCategory
          (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))),
        T ∈ distTriang _ →
          Triangle.mk (F.map T.mor₁) (F.map T.mor₂)
            (F.map T.mor₃ ≫ σ.hom.app T.obj₁) ∈ distTriang _ := by
  sorry

end SheafOfModules
