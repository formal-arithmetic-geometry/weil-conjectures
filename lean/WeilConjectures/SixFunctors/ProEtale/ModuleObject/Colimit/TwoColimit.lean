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
import Sheaf.CategoryTheory.DirectedTriangulatedImage
import Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import Sheaf.Paper.CondensedFinitePresentationDescent

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
of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` preserve
bounded constructibility, as proved below
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

## Proof inputs and the remaining obligation

The preservation and object-descent clauses below are proved from the named inputs.
Hom injectivity uses a splitting of the coefficient inclusion on the entire derived category.
The original Hom-surjectivity obligation remains open.

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

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Abelian ZeroObject

open scoped CategoryTheory.Obj CategoryTheory.Functor

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
      ((derivedExtendScalarsSubfield X ℓ h).obj K) := by
  exact boundedConstructible_leftDerivedExtendScalars_obj _ _
    (padicSubfieldRingObjMap X ℓ h) K hK

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

variable [TopologicalSpace.NoetherianSpace X]

/-- **(Hom), surjectivity**: every morphism `T^X_{E,Ω} K_E ⟶ T^X_{F,Ω} L_F` between extensions of
scalars of bounded constructible complexes is the extension of scalars of a morphism
`T^X_{E,H} K_E ⟶ T^X_{F,H} L_F` for some finite subextension `H ⊇ E, F`. See the module
docstring. -/
theorem constructibleCocone_homSurj : (constructibleCocone X ℓ).HomSurj :=
  sorry

private noncomputable instance algClCommShift (E : FiniteIntermediateField ℓ) :
    (derivedExtendScalarsToPadicAlgCl X ℓ E).CommShift ℤ :=
  Functor.CommShift.ofIso
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)
      |>.leftDerivedFunctorIsoMapDerivedCategory).symm ℤ

private instance algClTriangulated (E : FiniteIntermediateField ℓ) :
    (derivedExtendScalarsToPadicAlgCl X ℓ E).IsTriangulated := by
  have := Functor.CommShift.ofIso_compatibility
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)
      |>.leftDerivedFunctorIsoMapDerivedCategory).symm ℤ
  exact Functor.isTriangulated_of_iso
    ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E))
      |>.leftDerivedFunctorIsoMapDerivedCategory).symm

private lemma finitePresentation_of_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) (e : M ≅ N) : Mod.IsFinitelyPresented R N := by
  rcases h with ⟨n, m, f, ⟨i⟩⟩
  exact ⟨n, m, f, ⟨e.symm ≪≫ i⟩⟩

private lemma localFinitePresentation_of_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : IsLocallyFinitelyPresented R M) (e : M ≅ N) : IsLocallyFinitelyPresented R N := by
  rcases h with ⟨U, hU⟩
  exact ⟨U, fun i ↦ finitePresentation_of_iso (hU i)
    (((upperStar Ab.{u + 1} (U.f i)).mapMod R).mapIso e)⟩

private lemma constructible_of_iso_model {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : IsConstructibleModuleObject R M) (e : M ≅ N) :
    IsConstructibleModuleObject R N := by
  rcases h with ⟨U, hU⟩
  exact ⟨U, fun i ↦ localFinitePresentation_of_iso (hU i)
    (((upperStar Ab.{u + 1} (U.immersion i)).mapMod R).mapIso e)⟩

private lemma fp_zero {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R} (hM : IsZero M) :
    Mod.IsFinitelyPresented R M := by
  have hF : IsZero (Mod.finiteFree R 0) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply biproduct.hom_ext
    intro j
    exact Fin.elim0 j
  exact ⟨0, 0, 0, ⟨hM.iso (IsZero.of_epi (cokernel.π (0 :
    Mod.finiteFree R 0 ⟶ Mod.finiteFree R 0)) hF)⟩⟩
private lemma constructible_zero {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R} (hM : IsZero M) :
    IsConstructibleModuleObject R M := by
  refine ⟨Scheme.Stratification.trivial X, fun i ↦ ?_⟩
  let F := upperStar Ab.{u + 1} ((Scheme.Stratification.trivial X).immersion i)
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ ?_⟩
  exact fp_zero _ (((upperStar Ab.{u + 1} (𝟙 X)).mapMod (F.obj R)).map_isZero
    ((F.mapMod R).map_isZero hM))
private lemma bounded_tri_of_serre {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (hker : ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) (f : M ⟶ N),
      IsConstructibleModuleObject R M → IsConstructibleModuleObject R N →
      IsConstructibleModuleObject R (kernel f) ∧ IsConstructibleModuleObject R (cokernel f))
    (hext : ∀ S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R),
      S.ShortExact → IsConstructibleModuleObject R S.X₁ →
      IsConstructibleModuleObject R S.X₃ → IsConstructibleModuleObject R S.X₂) :
    (boundedConstructible R).IsTriangulated := by
  let P : ObjectProperty (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :=
    IsConstructibleModuleObject R
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ constructible_of_iso_model h e⟩
  have : P.ContainsZero := ⟨0, isZero_zero _, constructible_zero R (isZero_zero _)⟩
  have : P.IsClosedUnderKernels := ⟨by
    rintro Z ⟨f, k, hk, h⟩
    exact P.prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso hk)
      (hker _ _ f h.1 h.2).1⟩
  have : P.IsClosedUnderCokernels := ⟨by
    rintro Z ⟨f, k, hk, h⟩
    exact P.prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso hk)
      (hker _ _ f h.1 h.2).2⟩
  have : P.IsClosedUnderExtensions := ⟨fun h h₁ h₃ ↦ hext _ h h₁ h₃⟩
  have := DerivedCategory.homologyProperty_isTriangulated P
  change (DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.homologyProperty P).IsTriangulated
  infer_instance


-- Build the specific condensed-field triangulated structures from their Serre closure
-- statements; no arbitrary-coefficient closure assertion is used.
private lemma finiteBoundedTriangulated (E : FiniteIntermediateField ℓ) :
    (boundedConstructible (padicSubfieldRingObj X ℓ E)).IsTriangulated := by
  obtain ⟨hk, he⟩ := isConstructibleModuleObject_serre_padicSubfield X ℓ E
  exact bounded_tri_of_serre _ hk he

attribute [local instance 2000] finiteBoundedTriangulated

private lemma algClBoundedTriangulated :
    (boundedConstructible (padicAlgClRingObj X ℓ)).IsTriangulated := by
  obtain ⟨hk, he⟩ := isConstructibleModuleObject_serre_padicAlgCl X ℓ
  exact bounded_tri_of_serre _ hk he

attribute [local instance 2000] algClBoundedTriangulated

private noncomputable def ambientCocone :
    CategoryCocone (fun E : FiniteIntermediateField ℓ ↦ PadicSubfieldConstructible X ℓ E)
      (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (padicAlgClRingObj X ℓ))) where
  T h := constructibleExtendScalars X ℓ h
  Φ E := (constructibleToPadicAlgCl X ℓ E) ⋙ (boundedConstructible (padicAlgClRingObj X ℓ)).ι
  iso h := (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (constructibleToPadicAlgClCompIso X ℓ h) _

private noncomputable instance ambientCommShift (E : FiniteIntermediateField ℓ) :
    ((ambientCocone X ℓ).Φ E).CommShift ℤ :=
  inferInstanceAs (((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
    derivedExtendScalarsToPadicAlgCl X ℓ E).CommShift ℤ)

private instance ambientTriangulated (E : FiniteIntermediateField ℓ) :
    ((ambientCocone X ℓ).Φ E).IsTriangulated :=
  inferInstanceAs (((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
    derivedExtendScalarsToPadicAlgCl X ℓ E).IsTriangulated)

private lemma ambientHomSurj : (ambientCocone X ℓ).HomSurj := by
  intro i j K L f
  obtain ⟨k, hi, hj, g, hg⟩ := constructibleCocone_homSurj X ℓ i j K L
    (ObjectProperty.homMk f)
  refine ⟨k, hi, hj, g, ?_⟩
  simpa [ambientCocone, constructibleCocone] using congrArg (·.hom) hg

omit [TopologicalSpace.NoetherianSpace X] in
private lemma single_bounded_constructible
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hM : IsConstructibleModuleObject R M) :
    boundedConstructible R ((DerivedCategory.singleFunctor _ 0).obj M) := by
  let K := (DerivedCategory.singleFunctor _ 0).obj M
  have hzero (n : ℤ) (hn : n ≠ 0) :
      IsZero ((DerivedCategory.homologyFunctor _ n).obj K) := by
    rcases lt_or_gt_of_ne hn with hn | hn
    · exact DerivedCategory.isZero_of_isGE _ 0 n hn
    · exact DerivedCategory.isZero_of_isLE _ 0 n hn
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
  by_cases hn : n = 0
  · subst n
    exact constructible_of_iso_model hM
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm
  · exact constructible_zero R (hzero n hn)

private lemma single_model (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (padicAlgClRingObj X ℓ)) (hM : IsConstructibleModuleObject (padicAlgClRingObj X ℓ) M) :
    ∃ E, ((ambientCocone X ℓ).Φ E).essImage ((DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨E, M_E, hE, ⟨e⟩⟩ := exists_constructible_finiteCoefficient_model X ℓ M hM
  refine ⟨E, ⟨(DerivedCategory.singleFunctor _ 0).obj M_E,
    single_bounded_constructible X (padicSubfieldRingObj X ℓ E) M_E hE⟩, ⟨?_⟩⟩
  exact (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)
    |>.singleFunctorCompLeftDerivedFunctorIso).app M_E ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso e

/-- **(Obj)**: every bounded constructible `ℚ̄_ℓ,X`-complex is isomorphic to the extension of
scalars `T^X_{E,Ω} K_E` of a bounded constructible `E_X`-complex `K_E` for some finite
subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. See the module docstring. -/
theorem constructibleCocone_essSurjObj : (constructibleCocone X ℓ).EssSurjObj := by
  intro K
  let Q : ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (padicAlgClRingObj X ℓ))) := fun Y ↦ ∃ E, ((ambientCocone X ℓ).Φ E).essImage Y
  have : Q.IsTriangulated :=
    (ambientCocone X ℓ).isTriangulated_exists_essImage (ambientHomSurj X ℓ)
  have : Q.IsClosedUnderIsomorphisms :=
    ⟨fun e ⟨E, h⟩ ↦ ⟨E, ((ambientCocone X ℓ).Φ E).essImage.prop_of_iso e h⟩⟩
  let P : ObjectProperty (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
    (padicAlgClRingObj X ℓ)) :=
      ObjectProperty.isoClosure
        (fun M ↦ IsConstructibleModuleObject (padicAlgClRingObj X ℓ) M)
  have hP : ∀ M, P M → Q ((DerivedCategory.singleFunctor _ 0).obj M) := by
    rintro M ⟨N, hN, ⟨e⟩⟩
    exact Q.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso e).symm
      (single_model X ℓ N hN)
  obtain ⟨E, L, ⟨e⟩⟩ := DerivedCategory.prop_of_bounded Q P hP K.obj K.property.1
    (fun n ↦ ⟨_, K.property.2 n, ⟨Iso.refl _⟩⟩)
  exact ⟨E, L, ⟨(boundedConstructible (padicAlgClRingObj X ℓ)).fullyFaithfulι.preimageIso e⟩⟩


set_option linter.unusedSectionVars false in
/-- **(Hom), injectivity**: two morphisms of bounded constructible `H_X`-complexes with the same
extension of scalars to `ℚ̄_ℓ,X` have the same extension of scalars to `H'_X` for some finite
subextension `H' ⊇ H`. See the module docstring. -/
theorem constructibleCocone_homInj : (constructibleCocone X ℓ).HomInj := by
  intro E K L f g h
  let := faithful_leftDerivedExtendScalarsToPadicAlgCl X ℓ E
  have h' : (derivedExtendScalarsToPadicAlgCl X ℓ E).map f.hom =
      (derivedExtendScalarsToPadicAlgCl X ℓ E).map g.hom := congrArg (·.hom) h
  have e : f = g := ObjectProperty.hom_ext _
    ((derivedExtendScalarsToPadicAlgCl X ℓ E).map_injective h')
  subst g
  exact ⟨E, le_refl E, rfl⟩

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
