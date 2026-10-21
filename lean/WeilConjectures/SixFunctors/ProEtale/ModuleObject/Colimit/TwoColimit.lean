/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.FilteredTwoColimit
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars
import Sheaf.AlgebraicGeometry.SplitCoefficientDerivedFaithful
import all Sheaf.Paper.CondensedFiniteModelProofAPI
import Sheaf.CategoryTheory.DirectedTriangulatedImage
import all Sheaf.Paper.CondensedFiniteModelExtensions
import Sheaf.Paper.CondensedFinitePresentationDescent
import Sheaf.Paper.CondensedSheafExtContinuity
import Sheaf.AlgebraicGeometry.CondensedCoefficientComplexPresentation
import all Sheaf.CategoryTheory.HomColimitExtension

/-!

# The bounded constructible `ℚ̄_ℓ`-complexes as the 2-colimit over the finite subextensions

Let `ℓ` be a prime and `X` a scheme. For a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`
(`PadicAlgCl.FiniteIntermediateField ℓ`), let `C_E(X) = D^b_cons(X, E)` be the bounded
constructible derived category of modules over `E_X = p_X^* E̲`
(`ProEtale.BoundedConstructible (padicSubfieldRingObj X ℓ E)`, the full subcategory of the
unbounded `D(Mod_{E_X})` of `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`),
and let `C_Ω(X) = D^b_cons(X, ℚ̄_ℓ)` be the one of modules over `ℚ̄_ℓ,X = p_X^* ℚ̲̄_ℓ`. The
derived extensions of scalars
```
T^X_{E,F} = F_X ⊗ᴸ_{E_X} - ,   T^X_{E,Ω} = ℚ̄_ℓ,X ⊗ᴸ_{E_X} -
```
of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` are
*assumed* to preserve bounded constructibility
(`ProEtale.boundedConstructible_derivedExtendScalarsSubfield_obj`,
`ProEtale.boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj`), and hence restrict to
functors
```
ProEtale.constructibleExtendScalars h : C_E(X) ⥤ C_F(X)   (E ≤ F),
ProEtale.constructibleToPadicAlgCl E : C_E(X) ⥤ C_Ω(X),
```
compatible with each other through the transitivity of extension of scalars
(`ProEtale.constructibleToPadicAlgClCompIso`). Together these form a cocone of categories
`ProEtale.constructibleCocone X ℓ` on the directed system `E ↦ C_E(X)`, with vertex `C_Ω(X)`,
in the sense of `WeilConjectures.CategoryTheory.FilteredTwoColimit`.

The main statement, **`ℚ̄_ℓ` is a 2-colimit** (`ProEtale.constructibleCocone_isFilteredTwoColimit`),
is that this cocone is a filtered 2-colimit: the comparison functor
`2-colim_E C_E(X) ⟶ C_Ω(X)`, `(E, K_E) ↦ T^X_{E,Ω} K_E`, is an equivalence of ordinary
categories. By `CategoryTheory.CategoryCocone.IsFilteredTwoColimit` this is the conjunction of

* **(Obj)** `ProEtale.constructibleCocone_essSurjObj`: every bounded constructible
  `ℚ̄_ℓ,X`-complex `K` is isomorphic to `T^X_{E,Ω} K_E` for some finite subextension `E` and some
  bounded constructible `E_X`-complex `K_E` (descent of constructible objects);
* **(Hom)** `ProEtale.constructibleCocone_homSurj` and `ProEtale.constructibleCocone_homInj`:
  every morphism `T^X_{E,Ω} K_E ⟶ T^X_{F,Ω} L_F` in `D(Mod_{ℚ̄_ℓ,X})` is defined over some finite
  subextension `H ⊇ E, F`, and two morphisms over `H` with the same image are equal over some
  finite subextension `H' ⊇ H`. Since the bounded constructible complexes are stable under
  shifts, this includes the statement for the shifted targets `L_F[n]`, which is what the
  compatibility with the triangulated structures requires.

These are stated for a topologically noetherian `X`, the setting in which the bounded
constructible complexes form a triangulated subcategory
(`ProEtale.isTriangulated_boundedConstructible`). They are *not* formal consequences of the
identification `ℚ̄_ℓ,X ≃ colim_E E_X` of `ProEtale.isColimitPadicAlgClRingObjCocone`, and they
are false for the unbounded derived categories; see the module docstring of
`WeilConjectures.CategoryTheory.FilteredTwoColimit` for the ordinary-category model of the
2-colimit that they describe.

## Sorried input

* `ProEtale.boundedConstructible_derivedExtendScalarsSubfield_obj` and
  `ProEtale.boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj`: extension of scalars
  along `E_X ⟶ F_X` and `E_X ⟶ ℚ̄_ℓ,X` preserves bounded constructible complexes. The extension
  of scalars is exact
  (`ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap`), so it
  is computed termwise and preserves boundedness, and it sends a locally finitely
  presented module on a stratum to a locally finitely presented one, the presentation being
  tensored up.
* **(Obj)** `ProEtale.constructibleCocone_essSurjObj`: constructible descent. A bounded
  constructible `ℚ̄_ℓ,X`-complex has finitely many constructible cohomology sheaves; each is
  locally, on the strata of a stratification, finitely presented, and a finite presentation
  involves finitely many sections of `ℚ̄_ℓ,X`, which are defined over a finite subextension since
  `ℚ̄_ℓ,X = colim_E E_X` (`ProEtale.isColimitPadicAlgClRingObjCocone`). A finite Postnikov
  induction on the length of the complex then descends the complex itself, the gluing data being
  morphisms which descend by (Hom).
* **(Hom)** `ProEtale.constructibleCocone_homSurj` and `ProEtale.constructibleCocone_homInj`:
  continuity of the derived hom. For a bounded constructible first argument `K_E` and a
  bounded below second argument, `Hom_{D(Mod_{ℚ̄_ℓ,X})}(T_{E,Ω} K_E, T_{E,Ω} L_E)` is the filtered
  colimit over `H ⊇ E` of the `Hom_{D(Mod_{H_X})}(T_{E,H} K_E, T_{E,H} L_E)`: `K_E` is a finite
  extension of shifts of locally finitely presented modules, for which the derived hom into a
  filtered colimit of uniformly bounded below complexes is the filtered colimit of the derived
  homs, and `ℚ̄_ℓ,X = colim_H H_X`.

This is the input needed to transport base change theorems from finite to `ℚ̄_ℓ`-coefficients:
by (Obj) every constructible `K` is `T^X_{E,Ω} K_E`, and the compatibility of the base change
maps with the extension of scalars (built from the (Pull) and (Push) comparisons of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`) then shows that the
base change map at `K` is the extension of scalars of the one at `K_E`. This compatibility of
the base change maps of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems`
with the extension of scalars is not yet formalized.

-/

attribute [local instance 20000]
  CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit
  CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape

set_option maxSynthPendingDepth 0

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Abelian ZeroObject

open scoped CategoryTheory.Obj CategoryTheory.Functor

section HomContinuity

set_option linter.unusedSectionVars false
universe v w vI
open Opposite
namespace CategoryTheory
variable {D : Type w} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {I : Type v} [SmallCategory I] [IsFiltered I] (N : I ⥤ D) (c : Cocone N)
private instance continuity_iso : (homColimitProperty N c).IsClosedUnderIsomorphisms where
  of_iso e h n := desc_iso_transfer N c _ _
    (Functor.isoWhiskerLeft (shiftFunctor D n)
      (preadditiveCoyoneda.mapIso e.symm.op)) (h n)
private instance continuity_shift : (homColimitProperty N c).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K h ↦ homColimitProperty_shift N c K h n⟩
private instance continuity_tri : (homColimitProperty N c).IsTriangulated where
  exists_zero := by
    refine ⟨0, isZero_zero D, fun n ↦ ?_⟩
    have h (Y : D) : IsZero ((preadditiveCoyoneda.obj (op (0 : D))).obj Y) := by
      apply (IsZero.iff_id_eq_zero _).2
      ext f
      exact (isZero_zero D).eq_of_src _ _
    apply (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.1
    exact ⟨IsColimit.ofIsZero _ ((Functor.isZero_iff _).2 (fun i ↦ h _)) (h _)⟩
  toIsTriangulatedClosed₂ := .mk' (homColimitProperty_extensions N c)
end CategoryTheory
end HomContinuity

set_option linter.unusedSectionVars true

namespace AlgebraicGeometry.ProEtale
open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The derived extensions of scalars and their transitivity -/

section ExtendScalars

/-- The derived extension of scalars `T^X_{E,F} = F_X ⊗ᴸ_{E_X} - : D(Mod_{E_X}) ⥤ D(Mod_{F_X})`
along the inclusion of finite subextensions `E ≤ F`. -/
noncomputable abbrev derivedExtendScalarsSubfield {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) :=
  L(Mod.extendScalars (padicSubfieldRingObjMap X ℓ h))

/-- The derived extension of scalars
`T^X_{E,Ω} = ℚ̄_ℓ,X ⊗ᴸ_{E_X} - : D(Mod_{E_X}) ⥤ D(Mod_{ℚ̄_ℓ,X})` along the inclusion of a finite
subextension `E` into `ℚ̄_ℓ`. -/
noncomputable abbrev derivedExtendScalarsToPadicAlgCl (E : FiniteIntermediateField ℓ) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ)) :=
  L(Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E))

/-- Transitivity of the derived extension of scalars: `T^X_{E,F} ⋙ T^X_{F,Ω} ≅ T^X_{E,Ω}` for
`E ≤ F`. The extensions of scalars being exact, the composite of their derived functors is the
derived functor of the composite, which is the extension of scalars along the composite
inclusion `E_X ⟶ F_X ⟶ ℚ̄_ℓ,X = E_X ⟶ ℚ̄_ℓ,X`. -/
noncomputable def derivedExtendScalarsCompIso {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    derivedExtendScalarsSubfield X ℓ h ⋙ derivedExtendScalarsToPadicAlgCl X ℓ F ≅
      derivedExtendScalarsToPadicAlgCl X ℓ E :=
  haveI : PreservesFiniteLimits (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h ≫
      padicSubfieldRingObjToPadicAlgCl X ℓ F)) :=
    preservesFiniteLimits_of_natIso
      (Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h)).symm
  (Functor.leftDerivedFunctorCompIso _ _).symm ≪≫
    Functor.leftDerivedFunctorNatIso _
      ((Mod.extendScalarsComp _ _).symm ≪≫
        Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h))

end ExtendScalars

/-! ### The bounded constructible categories and the functors between them -/

section Constructible

/-- The bounded constructible derived category `C_E(X) = D^b_cons(X, E)` of `E_X`-modules, for
a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. -/
noncomputable abbrev PadicSubfieldConstructible (E : FiniteIntermediateField ℓ) : Type _ :=
  BoundedConstructible (padicSubfieldRingObj X ℓ E)

/-- The bounded constructible derived category `C_Ω(X) = D^b_cons(X, ℚ̄_ℓ)` of
`ℚ̄_ℓ,X`-modules. -/
noncomputable abbrev PadicAlgClConstructible : Type _ :=
  BoundedConstructible (padicAlgClRingObj X ℓ)

/-- Extension of scalars along `E_X ⟶ F_X` preserves bounded constructible complexes. See the
module docstring. -/
lemma boundedConstructible_derivedExtendScalarsSubfield_obj {E F : FiniteIntermediateField ℓ}
    (h : E ≤ F)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (hK : boundedConstructible (padicSubfieldRingObj X ℓ E) K) :
    boundedConstructible (padicSubfieldRingObj X ℓ F)
      ((derivedExtendScalarsSubfield X ℓ h).obj K) :=
  boundedConstructible_leftDerivedExtendScalars_obj _ _ (padicSubfieldRingObjMap X ℓ h) K hK

/-- Extension of scalars along `E_X ⟶ ℚ̄_ℓ,X` preserves bounded constructible complexes. See the
module docstring. -/
lemma boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj (E : FiniteIntermediateField ℓ)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (hK : boundedConstructible (padicSubfieldRingObj X ℓ E) K) :
    boundedConstructible (padicAlgClRingObj X ℓ) ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K) :=
  boundedConstructible_leftDerivedExtendScalars_obj _ _
    (padicSubfieldRingObjToPadicAlgCl X ℓ E) K hK

/-- The extension of scalars `T^X_{E,F} : C_E(X) ⥤ C_F(X)` on bounded constructible complexes,
for finite subextensions `E ≤ F`. -/
noncomputable def constructibleExtendScalars {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    PadicSubfieldConstructible X ℓ E ⥤ PadicSubfieldConstructible X ℓ F :=
  (boundedConstructible (padicSubfieldRingObj X ℓ F)).lift
    ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙ derivedExtendScalarsSubfield X ℓ h)
    (fun K ↦ boundedConstructible_derivedExtendScalarsSubfield_obj X ℓ h K.obj K.property)

/-- The extension of scalars `T^X_{E,Ω} : C_E(X) ⥤ C_Ω(X)` on bounded constructible complexes,
for a finite subextension `E`: the functors of the cocone whose vertex is the bounded
constructible `ℚ̄_ℓ`-complexes. -/
noncomputable def constructibleToPadicAlgCl (E : FiniteIntermediateField ℓ) :
    PadicSubfieldConstructible X ℓ E ⥤ PadicAlgClConstructible X ℓ :=
  (boundedConstructible (padicAlgClRingObj X ℓ)).lift
    ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙ derivedExtendScalarsToPadicAlgCl X ℓ E)
    (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj X ℓ E K.obj K.property)

/-- The functors to the bounded constructible `ℚ̄_ℓ`-complexes are compatible with the extensions
of scalars between finite subextensions: `T^X_{E,F} ⋙ T^X_{F,Ω} ≅ T^X_{E,Ω}` on bounded
constructible complexes, by `derivedExtendScalarsCompIso` and the full faithfulness of the
inclusion of the bounded constructible complexes. -/
noncomputable def constructibleToPadicAlgClCompIso {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    constructibleExtendScalars X ℓ h ⋙ constructibleToPadicAlgCl X ℓ F ≅
      constructibleToPadicAlgCl X ℓ E :=
  Functor.fullyFaithfulCancelRight (boundedConstructible (padicAlgClRingObj X ℓ)).ι
    ((Iso.refl ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
        (derivedExtendScalarsSubfield X ℓ h ⋙ derivedExtendScalarsToPadicAlgCl X ℓ F)) :
      (constructibleExtendScalars X ℓ h ⋙ constructibleToPadicAlgCl X ℓ F) ⋙
          (boundedConstructible (padicAlgClRingObj X ℓ)).ι ≅
        (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
          (derivedExtendScalarsSubfield X ℓ h ⋙ derivedExtendScalarsToPadicAlgCl X ℓ F)) ≪≫
      Functor.isoWhiskerLeft (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι
        (derivedExtendScalarsCompIso X ℓ h))

/-- The cocone of categories `E ↦ C_E(X)` with vertex `C_Ω(X)`: the directed system of the
bounded constructible `E`-complexes over the finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, with the
extensions of scalars as transition functors, and the extensions of scalars to `ℚ̄_ℓ` as
functors to the vertex. -/
noncomputable def constructibleCocone :
    CategoryCocone (fun E : FiniteIntermediateField ℓ ↦ PadicSubfieldConstructible X ℓ E)
      (PadicAlgClConstructible X ℓ) where
  T h := constructibleExtendScalars X ℓ h
  Φ E := constructibleToPadicAlgCl X ℓ E
  iso h := constructibleToPadicAlgClCompIso X ℓ h

end Constructible

/-! ### `ℚ̄_ℓ` is a 2-colimit -/

section TwoColimit

set_option maxSynthPendingDepth 3

attribute [local instance 100]
  CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit
  CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape



variable [TopologicalSpace.NoetherianSpace X]

attribute [local instance] moduleTensorFour moduleTensorLeft moduleTensorRight

private instance moduleTensorColimits {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R),
      PreservesColimitsOfShape ℤ
        ((curriedTensor (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)).obj M) :=
  fun _ ↦ inferInstance

private instance moduleTensorFlipColimits {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R),
      PreservesColimitsOfShape ℤ
        ((curriedTensor (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)).flip.obj M) :=
  fun _ ↦ inferInstance

private instance moduleFlatResolution {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) := by infer_instance

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.CommShift.ofIso CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory

private lemma bounded_factors
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (N : J ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ℤ)
    [HasColimit N]
    (hN : ∃ a : ℤ, ∀ (i : J) (r : ℤ), r < a → IsZero ((N.obj i).X r))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (hK : boundedConstructible (padicSubfieldRingObj X ℓ E) K) :
    CategoryTheory.factors (DerivedCategory.Q.mapCocone (colimit.cocone N)) K := by
  let c := DerivedCategory.Q.mapCocone (colimit.cocone N)
  let Q := homColimitProperty (N ⋙ DerivedCategory.Q) c
  let P : ObjectProperty
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) :=
    ObjectProperty.isoClosure (IsConstructibleModuleObject (padicSubfieldRingObj X ℓ E))
  have hP : ∀ M, P M → Q ((DerivedCategory.singleFunctor _ 0).obj M) := by
    rintro M ⟨M', hM', ⟨e⟩⟩
    exact Q.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso e).symm
      (fun n ↦ isIso_constructible_condensed_sheaf_hom_colimit X ℓ E M' hM' N hN n)
  have hQ : Q K := DerivedCategory.prop_of_bounded Q P hP K hK.1
    (fun n ↦ ⟨_, hK.2 n, ⟨Iso.refl _⟩⟩)
  exact CategoryTheory.factors_iso c ((shiftFunctorZero _ ℤ).app K)
    (CategoryTheory.shiftFactors_of_hom_colimit N DerivedCategory.Q K hQ 0)

private lemma bounded_factors_cocone
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (N : J ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ℤ)
    (c : Cocone N) (hc : IsColimit c)
    (hN : ∃ a : ℤ, ∀ (i : J) (r : ℤ), r < a → IsZero ((N.obj i).X r))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (hK : boundedConstructible (padicSubfieldRingObj X ℓ E) K) :
    ∀ f : K ⟶ DerivedCategory.Q.obj c.pt,
      ∃ (i : J) (g : K ⟶ DerivedCategory.Q.obj (N.obj i)),
        f = g ≫ DerivedCategory.Q.map (c.ι.app i) := by
  let : HasColimit N := ⟨⟨c, hc⟩⟩
  exact CategoryTheory.factors_of_colimit_cocone N DerivedCategory.Q c hc K
    (bounded_factors X ℓ E N hN K hK)


omit [TopologicalSpace.NoetherianSpace X] in
private lemma tensorComp_hom {E F : FiniteIntermediateField ℓ} (h : E ≤ F)
    (K : PadicSubfieldConstructible X ℓ E) :
    ((constructibleToPadicAlgClCompIso X ℓ h).hom.app K).hom =
      (finiteCoefficientDerivedTensorCompIso X ℓ h).hom.app K.obj := by
  change (boundedConstructible (padicAlgClRingObj X ℓ)).ι.map _ = _
  unfold constructibleToPadicAlgClCompIso
  rw [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  exact Category.id_comp _

omit [TopologicalSpace.NoetherianSpace X] in
private lemma tensorComp_inv {E F : FiniteIntermediateField ℓ} (h : E ≤ F)
    (K : PadicSubfieldConstructible X ℓ E) :
    ((constructibleToPadicAlgClCompIso X ℓ h).inv.app K).hom =
      (finiteCoefficientDerivedTensorCompIso X ℓ h).inv.app K.obj := by
  change (boundedConstructible (padicAlgClRingObj X ℓ)).ι.map _ = _
  unfold constructibleToPadicAlgClCompIso
  rw [Functor.fullyFaithfulCancelRight_inv_app, Functor.map_preimage]
  simp only [Iso.trans_inv, Iso.refl_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Category.comp_id]
  rfl

attribute [local instance] algClCommShift algClTriangulated

attribute [local instance 2000] finiteBoundedTriangulated
attribute [local irreducible] algClDerivedIso algClCommShift


attribute [local irreducible] derivedExtendScalarsCompIso
  finiteCoefficientDerivedTensorCompIso finiteCoefficientDerivedHomEquiv
  finiteCoefficientDerivedAlgClHomEquiv finiteCoefficientDerivedRestriction
  finiteCoefficientDerivedFromAlgCl finiteCoefficientDerivedAdjunction
  finiteCoefficientDerivedAlgClAdjunction

private noncomputable def ambientCocone :
    CategoryCocone (fun E : FiniteIntermediateField ℓ ↦ PadicSubfieldConstructible X ℓ E)
      (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (padicAlgClRingObj X ℓ))) where
  T h := constructibleExtendScalars X ℓ h
  Φ E := (constructibleToPadicAlgCl X ℓ E) ⋙ (boundedConstructible (padicAlgClRingObj X ℓ)).ι
  iso h := (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (constructibleToPadicAlgClCompIso X ℓ h) _

set_option backward.isDefEq.respectTransparency true in
private noncomputable instance ambientCommShift (E : FiniteIntermediateField ℓ) :
    ((ambientCocone X ℓ).Φ E).CommShift ℤ :=
  @Functor.CommShift.comp _ _ _ _ _ _
    (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι
    (derivedExtendScalarsToPadicAlgCl X ℓ E) ℤ _ _ _ _
    (inferInstance) (algClCommShift X ℓ E)

set_option backward.isDefEq.respectTransparency true in
private instance ambientTriangulated (E : FiniteIntermediateField ℓ) :
    ((ambientCocone X ℓ).Φ E).IsTriangulated :=
  inferInstanceAs (((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
    derivedExtendScalarsToPadicAlgCl X ℓ E).IsTriangulated)


omit [TopologicalSpace.NoetherianSpace X] in
private lemma scalar_map_hom (E : FiniteIntermediateField ℓ)
    {K L : PadicSubfieldConstructible X ℓ E} (g : K ⟶ L) :
    ((constructibleToPadicAlgCl X ℓ E).map g).hom =
      (finiteCoefficientDerivedToAlgCl X ℓ E).map g.hom := rfl

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 400000 in
-- Four coefficient categories occur in the two derived adjunctions.
/-- **(Hom), surjectivity**: every morphism `T^X_{E,Ω} K_E ⟶ T^X_{F,Ω} L_F` between extensions of
scalars of bounded constructible complexes is the extension of scalars of a morphism
`T^X_{E,H} K_E ⟶ T^X_{F,H} L_F` for some finite subextension `H ⊇ E, F`. See the module
docstring. -/
theorem constructibleCocone_homSurj : (constructibleCocone X ℓ).HomSurj := by
  intro E F K L f
  let G := IsFiltered.max E F
  let I := AsSmall.{u + 1} (Under G)
  let H : I ⥤ FiniteIntermediateField ℓ :=
    (AsSmall.equiv (C := Under G)).inverse ⋙ Under.forget G
  have : H.Final := by dsimp [H]; infer_instance
  have he (i : I) : E ≤ H.obj i :=
    le_trans (leOfHom (IsFiltered.leftToMax E F)) (leOfHom (ULift.down i).hom)
  have hf (i : I) : F ≤ H.obj i :=
    le_trans (leOfHom (IsFiltered.rightToMax E F)) (leOfHom (ULift.down i).hom)
  obtain ⟨N, c, ⟨hc⟩, hN, eΩ, ei, hcomp⟩ :=
    exists_condensed_coefficient_complex_presentation X ℓ E F L.obj L.property.1.1 H he hf
  let adj := finiteCoefficientDerivedAlgClHomEquiv X ℓ E K.obj
    ((finiteCoefficientDerivedToAlgCl X ℓ F).obj L.obj)
  obtain ⟨i, g, hg⟩ := bounded_factors_cocone X ℓ E N c hc hN K.obj K.property
    (adj f.hom ≫ eΩ.inv)
  let gH : (finiteCoefficientDerivedExtension X ℓ (he i)).obj K.obj ⟶
      (finiteCoefficientDerivedExtension X ℓ (hf i)).obj L.obj :=
    (finiteCoefficientDerivedHomEquiv X ℓ (he i) K.obj _).symm (g ≫ (ei i).hom)
  have hfinite : f.hom =
      (finiteCoefficientDerivedTensorCompIso X ℓ (he i)).inv.app K.obj ≫
        (finiteCoefficientDerivedToAlgCl X ℓ (H.obj i)).map gH ≫
          (finiteCoefficientDerivedTensorCompIso X ℓ (hf i)).hom.app L.obj := by
    apply adj.injective
    have hh := hcomp i K.obj g
    have hh' : adj f.hom = (g ≫ DerivedCategory.Q.map (c.ι.app i)) ≫ eΩ.hom :=
      eΩ.comp_inv_eq.mp hg
    exact hh'.trans ((Category.assoc _ _ _).trans hh.symm)
  refine ⟨H.obj i, he i, hf i, ObjectProperty.homMk gH, ?_⟩
  apply ObjectProperty.hom_ext
  set_option backward.isDefEq.respectTransparency false in
    simpa only [constructibleCocone, ObjectProperty.ι_map,
      ObjectProperty.FullSubcategory.comp_hom, tensorComp_inv, tensorComp_hom,
      scalar_map_hom, ObjectProperty.homMk_hom] using hfinite

private lemma ambientHomSurj : (ambientCocone X ℓ).HomSurj := by
  intro i j K L f
  obtain ⟨k, hi, hj, g, hg⟩ := constructibleCocone_homSurj X ℓ i j K L
    (ObjectProperty.homMk f)
  refine ⟨k, hi, hj, g, ?_⟩
  simpa [ambientCocone, constructibleCocone] using congrArg (·.hom) hg

private lemma single_model (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (padicAlgClRingObj X ℓ)) (hM : IsConstructibleModuleObject (padicAlgClRingObj X ℓ) M) :
    ∃ E, ((ambientCocone X ℓ).Φ E).essImage ((DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨E, M_E, hE, ⟨e⟩⟩ := exists_constructible_finiteCoefficient_model X ℓ M hM
  refine ⟨E, ⟨(DerivedCategory.singleFunctor _ 0).obj M_E,
    single_bounded_constructible X (padicSubfieldRingObj X ℓ E) M_E hE⟩, ⟨?_⟩⟩
  exact (algClDerivedIso X ℓ E).app ((DerivedCategory.singleFunctor _ 0).obj M_E) ≪≫
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)
      |>.mapDerivedCategorySingleFunctor 0).app M_E ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso e


/-- **(Obj)**: every bounded constructible `ℚ̄_ℓ,X`-complex is isomorphic to the extension of
scalars `T^X_{E,Ω} K_E` of a bounded constructible `E_X`-complex `K_E` for some finite
subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. See the module docstring. -/
theorem constructibleCocone_essSurjObj : (constructibleCocone X ℓ).EssSurjObj := by
  intro K
  let P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))) :=
    fun Y ↦ ∃ E, ((ambientCocone X ℓ).Φ E).essImage Y
  have : P.IsTriangulated :=
    CategoryCocone.isTriangulated_exists_essImage (ambientCocone X ℓ) (ambientHomSurj X ℓ)
  have : P.IsClosedUnderIsomorphisms :=
    ⟨fun e ⟨E, hE⟩ ↦ ⟨E, ((ambientCocone X ℓ).Φ E).essImage.prop_of_iso e hE⟩⟩
  obtain ⟨E, M, ⟨e⟩⟩ := DerivedCategory.prop_of_bounded P
    (ObjectProperty.isoClosure (IsConstructibleModuleObject (padicAlgClRingObj X ℓ)))
    (by
      rintro M ⟨M', hM', ⟨e⟩⟩
      exact P.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso e).symm
        (single_model X ℓ M' hM')) K.obj K.property.1
    (fun n ↦ ⟨_, K.property.2 n, ⟨Iso.refl _⟩⟩)
  exact ⟨E, M, ⟨(boundedConstructible (padicAlgClRingObj X ℓ)).fullyFaithfulι.preimageIso e⟩⟩

set_option linter.unusedSectionVars false in
/-- **(Hom), injectivity**: two morphisms of bounded constructible `H_X`-complexes with the same
extension of scalars to `ℚ̄_ℓ,X` have the same extension of scalars to `H'_X` for some finite
subextension `H' ⊇ H`. See the module docstring. -/
theorem constructibleCocone_homInj : (constructibleCocone X ℓ).HomInj := by
  intro H K L g g' h
  have : (derivedExtendScalarsToPadicAlgCl X ℓ H).Faithful :=
    faithful_leftDerivedExtendScalarsToPadicAlgCl X ℓ H
  have hg : g = g' := by
    apply (boundedConstructible (padicSubfieldRingObj X ℓ H)).ι.map_injective
    apply (derivedExtendScalarsToPadicAlgCl X ℓ H).map_injective
    exact congrArg (fun f ↦ f.hom) h
  exact ⟨H, le_refl H, congrArg ((constructibleExtendScalars X ℓ (le_refl H)).map) hg⟩

/-- **`ℚ̄_ℓ` is a 2-colimit**: the bounded constructible derived category `D^b_cons(X, ℚ̄_ℓ)`
of `ℚ̄_ℓ,X`-modules, with the extensions of scalars from the bounded constructible derived
categories `D^b_cons(X, E)` of the finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, is the filtered
2-colimit of the latter: the comparison functor `2-colim_E D^b_cons(X, E) ⟶ D^b_cons(X, ℚ̄_ℓ)`,
`(E, K_E) ↦ ℚ̄_ℓ,X ⊗ᴸ_{E_X} K_E`, is an equivalence of ordinary categories. -/
theorem constructibleCocone_isFilteredTwoColimit :
    (constructibleCocone X ℓ).IsFilteredTwoColimit where
  essSurjObj := constructibleCocone_essSurjObj X ℓ
  homSurj := constructibleCocone_homSurj X ℓ
  homInj := constructibleCocone_homInj X ℓ

end TwoColimit

end AlgebraicGeometry.ProEtale
