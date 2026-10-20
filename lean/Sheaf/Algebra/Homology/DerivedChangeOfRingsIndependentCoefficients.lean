/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups J1 and NF
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.Algebra.Homology.KFlat

/-!
# Derived change of rings on a ringed site

Source: literature/stacks-project/sites-cohomology.tex, Tags 06YT, 06YY, and
literature/stacks-project/derived.tex, Tag 06XN
(blueprint: lem-pur-derived-change-of-rings).

The change of rings `- ⊗_O O'` is the landed `SheafOfModules.changeOfRings φ` on objects
and `SheafOfModules.changeOfRingsHom φ` on morphisms (def-pur-sheaf-tensor-product); the
statement asserts an additive functor `E` with exactly these objects and maps, and uses
`E.mapHomologicalComplex` (termwise change of rings of complexes) and
`E.mapHomotopyCategory ⋙ DerivedCategory.Qh` (the functor `K(O) → D(O')`).

## Main definitions

- `derivedChangeRingIndependentCoefficients`: the underlying ring sheaf in independent site
  universes.

## Main statements

- `derivedChangeOfRingsIndependentCoefficients`: the full derived-change-of-rings statement without
  identifying the object and morphism universes of the site.
-/

@[expose] public section

universe w r u v

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Forget commutativity without identifying the two universes of the site.
Source: Stacks Tag 06YY (blueprint: lem-pur-derived-change-of-rings). -/
noncomputable abbrev derivedChangeRingIndependentCoefficients {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (O : Sheaf J CommRingCat.{r}) :=
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj O

/-- Derived change of rings along a morphism `φ : O ⟶ O'` of sheaves of commutative rings
on a site. There is an additive functor `E : Mod(O) ⥤ Mod(O')` whose objects and maps are
the change of rings `changeOfRings φ` / `changeOfRingsHom φ` (`- ⊗_O O'`), such that
(1) termwise change of rings `E.mapHomologicalComplex` sends every quasi-isomorphism between
K-flat complexes to a quasi-isomorphism, and (2) the functor
`K(O) → D(O')`, `G ↦ Q(G ⊗_O O')`, has an everywhere defined (pointwise) left derived
functor `Lφ^* : D(O) ⥤ D(O')` with counit `ε`, which is triangulated, and `ε` is an
isomorphism at every K-flat complex. Hence for a K-flat resolution `s : P → G` the canonical
map `Lφ^* G ≅ Lφ^* P → P ⊗_O O'` (inverse of `Lφ^*(s)` followed by `ε_P`) is an isomorphism,
and the comparison isomorphisms between two resolutions are composites of these, so
canonical and compatible with composition.
Source: Stacks Project, Tags 06YT, 06YY, and 06XN.
Proof:
1. Form the sectionwise extension-of-scalars functor from changeOfRingsPresheaf and
changeOfRingsHom_naturality (def-pur-sheaf-tensor-product), then compose with sheafification.
Identities and composition hold sectionwise. Both functors are additive by their
adjunctions to additive restriction or forgetful functors (Adjunction.left_adjoint_additive).
This gives E with exactly the specified objects and maps.
2. Apply lem-pur-change-of-rings-kflat-quasi-iso to E with these identifications to obtain
preservation of quasi-isomorphisms between K-flat complexes.
3. Let F be the induced homotopy functor followed by derived localization
(def-weil-abstract-derived-category); it commutes with shifts and is triangulated.
Use homotopy objects represented by K-flat complexes as the resolving class
(def-pc-kflat-complex). Resolve every representative by lem-pc-kflat-resolution and apply
quotient_map_mem_quasiIso_iff to its augmentation. For a quasi-isomorphism between objects
of this class, lift through the full homotopy quotient on chosen K-flat representatives.
Step 2 and localization make its F-image invertible. Apply
lem-pur-left-derived-from-kflat-class to obtain pointwise existence, the universal derived
pair, triangulatedness, and the counit isomorphism on every K-flat complex. The canonical
resolution comparisons are composites of these counit maps and inverses of images of
quasi-isomorphisms, hence are isomorphisms and compatible with a third resolution.
(blueprint: lem-pur-derived-change-of-rings) -/
theorem derivedChangeOfRingsIndependentCoefficients
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    {O O' : Sheaf J CommRingCat.{r}} (φ : O ⟶ O')
    [HasDerivedCategory.{w} (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O))]
    [HasDerivedCategory.{w} (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O'))] :
    ∃ (E : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O) ⥤ SheafOfModules.{r}
      (derivedChangeRingIndependentCoefficients J O'))
      (h : ∀ M : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O), E.obj M =
        changeOfRings.{v, u,
        r} φ M)
      (_ : ∀ {M N : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O)} (a : M ⟶ N),
        E.map a = eqToHom (h M) ≫ changeOfRingsHom.{v, u, r} φ M a ≫ eqToHom (h N).symm)
      (_ : E.Additive),
      (∀ {P Q : CochainComplex (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O))
        ℤ} (α : P ⟶ Q),
        P.IsKFlatIndependentCoefficients → Q.IsKFlatIndependentCoefficients → QuasiIso α →
          QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map α)) ∧
      (E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
          (HomotopyCategory.quasiIso (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J
            O))
            (ComplexShape.up ℤ)) ∧
      ∃ (LF : DerivedCategory (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O)) ⥤
          DerivedCategory (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O')))
        (ε : DerivedCategory.Qh ⋙ LF ⟶
          E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
        LF.IsLeftDerivedFunctor ε
            (HomotopyCategory.quasiIso (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients
              J O))
              (ComplexShape.up ℤ)) ∧
          (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
          ∀ P : CochainComplex (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O))
            ℤ, P.IsKFlatIndependentCoefficients →
            IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  sorry

end SheafOfModules
