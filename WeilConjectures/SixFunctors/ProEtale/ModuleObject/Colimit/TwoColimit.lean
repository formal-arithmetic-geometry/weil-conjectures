/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
public import WeilConjectures.CategoryTheory.FilteredTwoColimit
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.DerivedExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.PadicAlgClFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimitEssSurj
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimitHomSurj

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
of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.DerivedExtendScalars` are
shown to preserve bounded constructibility
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
(`ProEtale.isTriangulated_boundedConstructible_continuousMapRingObj`, for the rings `E_X`). They
are *not* formal consequences of the identification `ℚ̄_ℓ,X ≃ colim_E E_X` of
`ProEtale.isColimitPadicAlgClRingObjCocone`, and they are false for the unbounded derived
categories; see the module docstring of `WeilConjectures.CategoryTheory.FilteredTwoColimit` for
the ordinary-category model of the 2-colimit that they describe.

## Proofs

* `ProEtale.boundedConstructible_derivedExtendScalarsSubfield_obj` and
  `ProEtale.boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj`: the extension of scalars
  is exact, so it commutes with the cohomology sheaves, and it preserves constructibility
  (`ProEtale.boundedConstructible_leftDerivedExtendScalars_obj`).
* **(Obj)** `ProEtale.constructibleCocone_essSurjObj`: dévissage along the generation of
  `Dᵇc(X, ℚ̄_ℓ)` by extensions by zero of lisse sheaves, the cone step using (Hom), and lisse
  descent (`ProEtale.exists_iso_derivedExtendScalarsToPadicAlgCl_obj`).
* **(Hom)** `ProEtale.constructibleCocone_homSurj`: the continuity of `Hom` out of a bounded
  constructible complex and `ℚ̄_ℓ,X ⊗ Y = colim_H H_X ⊗ Y`
  (`ProEtale.exists_derivedExtendScalarsToPadicAlgCl_map_eq`);
  `ProEtale.constructibleCocone_homInj`: the extension of scalars to `ℚ̄_ℓ` is faithful, `E_X` being
  an `E_X`-linear direct summand of `ℚ̄_ℓ,X` (`ProEtale.faithful_derivedExtendScalarsToPadicAlgCl`).

The remaining sorried inputs are the blueprint nodes `sk-lem-constructible-ext-continuity` (1)
(`ProEtale.CondensedRing.constructibleExtContinuity_continuousMapRingObj`) and
`det-cor-coefficient-heart-ii-generation` of other subsections, and lisse descent
`det-lem-coefficient-finite-descent-lisse` (`ProEtale.exists_isLocallyFree_extendScalars_iso`).

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

open CategoryTheory Limits MonoidalCategory MonObj Abelian

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The bounded constructible categories and the functors between them -/

section Constructible

open scoped CondensedRing

/-- The bounded constructible derived category `C_E(X) = D^b_cons(X, E)` of `E_X`-modules, for
a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. -/
noncomputable abbrev PadicSubfieldConstructible (E : FiniteIntermediateField ℓ) : Type _ :=
  BoundedConstructible (padicSubfieldRingObj X ℓ E)

/-- The bounded constructible derived category `C_Ω(X) = D^b_cons(X, ℚ̄_ℓ)` of
`ℚ̄_ℓ,X`-modules. -/
noncomputable abbrev PadicAlgClConstructible : Type _ :=
  BoundedConstructible (padicAlgClRingObj X ℓ)

/-- Extension of scalars along `E_X ⟶ F_X` preserves bounded constructible complexes.
See the module docstring. -/
lemma boundedConstructible_derivedExtendScalarsSubfield_obj {E F : FiniteIntermediateField ℓ}
    (h : E ≤ F) (K : Dᵇc(X)⟦Profinite.continuousMapRingObj E⟧) :
    boundedConstructible (padicSubfieldRingObj X ℓ F)
      ((derivedExtendScalarsSubfield X ℓ h).obj K.obj) :=
  ProEtale.boundedConstructible_leftDerivedExtendScalars_obj _ _ _ K.obj K.property

/-- Extension of scalars along `E_X ⟶ ℚ̄_ℓ,X` preserves bounded constructible complexes.
See the module docstring. -/
lemma boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj (E : FiniteIntermediateField ℓ)
    (K : Dᵇc(X)⟦Profinite.continuousMapRingObj E⟧) :
    boundedConstructible (padicAlgClRingObj X ℓ)
      ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K.obj) :=
  ProEtale.boundedConstructible_leftDerivedExtendScalars_obj _ _ _ K.obj K.property

/-- The extension of scalars `T^X_{E,F} : C_E(X) ⥤ C_F(X)` on bounded constructible complexes,
for finite subextensions `E ≤ F`. -/
noncomputable def constructibleExtendScalars {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    PadicSubfieldConstructible X ℓ E ⥤ PadicSubfieldConstructible X ℓ F :=
  (boundedConstructible (padicSubfieldRingObj X ℓ F)).lift
    ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙ derivedExtendScalarsSubfield X ℓ h)
    (fun K ↦ boundedConstructible_derivedExtendScalarsSubfield_obj X ℓ h K)

/-- The extension of scalars `T^X_{E,Ω} : C_E(X) ⥤ C_Ω(X)` on bounded constructible complexes,
for a finite subextension `E`: the functors of the cocone whose vertex
is the bounded constructible `ℚ̄_ℓ`-complexes. -/
noncomputable def constructibleToPadicAlgCl (E : FiniteIntermediateField ℓ) :
    PadicSubfieldConstructible X ℓ E ⥤ PadicAlgClConstructible X ℓ :=
  (boundedConstructible (padicAlgClRingObj X ℓ)).lift
    ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙ derivedExtendScalarsToPadicAlgCl X ℓ E)
    (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj X ℓ E K)

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

/-- **(Obj)**: every bounded constructible `ℚ̄_ℓ,X`-complex is isomorphic to the extension of
scalars `T^X_{E,Ω} K_E` of a bounded constructible `E_X`-complex `K_E` for some finite
subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. See the module docstring. -/
theorem constructibleCocone_essSurjObj : (constructibleCocone X ℓ).EssSurjObj := fun K ↦ by
  obtain ⟨E, K', hK', ⟨e⟩⟩ := exists_iso_derivedExtendScalarsToPadicAlgCl_obj X ℓ
    (fun K hK L hL f ↦ exists_derivedExtendScalarsToPadicAlgCl_map_eq X ℓ K hK L hL f)
    K.obj K.property
  exact ⟨E, ⟨K', hK'⟩, ⟨(boundedConstructible _).fullyFaithfulι.preimageIso e⟩⟩

/-- **(Hom), surjectivity**: every morphism `T^X_{E,Ω} K_E ⟶ T^X_{F,Ω} L_F` between extensions of
scalars of bounded constructible complexes is the extension of scalars of a morphism
`T^X_{E,H} K_E ⟶ T^X_{F,H} L_F` for some finite subextension `H ⊇ E, F`. See the module
docstring. -/
theorem constructibleCocone_homSurj : (constructibleCocone X ℓ).HomSurj := by
  intro E F K L f
  have hiso {E F : FiniteIntermediateField ℓ} (h : E ≤ F) (K : PadicSubfieldConstructible X ℓ E) :
      (((constructibleCocone X ℓ).iso h).hom.app K).hom =
        (derivedExtendScalarsCompIso X ℓ h).hom.app K.obj :=
    ((boundedConstructible _).ι.map_preimage _).trans (Category.id_comp _)
  have hiso' {E F : FiniteIntermediateField ℓ} (h : E ≤ F) (K : PadicSubfieldConstructible X ℓ E) :
      (((constructibleCocone X ℓ).iso h).inv.app K).hom =
        (derivedExtendScalarsCompIso X ℓ h).inv.app K.obj :=
    ((boundedConstructible _).ι.map_preimage _).trans (Category.comp_id _)
  have hΦ {H : FiniteIntermediateField ℓ} {K L : PadicSubfieldConstructible X ℓ H} (g : K ⟶ L) :
      (((constructibleCocone X ℓ).Φ H).map g).hom =
        (derivedExtendScalarsToPadicAlgCl X ℓ H).map g.hom := rfl
  obtain ⟨H, hE, hF, g, hg⟩ := exists_derivedExtendScalarsToPadicAlgCl_map_eq X ℓ
    K.obj K.property L.obj L.property
    (f.hom : (derivedExtendScalarsToPadicAlgCl X ℓ E).obj K.obj ⟶
      (derivedExtendScalarsToPadicAlgCl X ℓ F).obj L.obj)
  let g' : (constructibleExtendScalars X ℓ hE).obj K ⟶ (constructibleExtendScalars X ℓ hF).obj L :=
    InducedCategory.homMk g
  refine ⟨H, hE, hF, g', InducedCategory.hom_ext ?_⟩
  refine hg.trans ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom, hiso, hiso', hΦ]
  rfl

omit [TopologicalSpace.NoetherianSpace X] in
/-- **(Hom), injectivity**: two morphisms of bounded constructible `H_X`-complexes with the same
extension of scalars to `ℚ̄_ℓ,X` have the same extension of scalars to `H'_X` for some finite
subextension `H' ⊇ H`. See the module docstring. -/
theorem constructibleCocone_homInj : (constructibleCocone X ℓ).HomInj :=
  fun k _ _ g g' h ↦ by
    have hΦ {K L : PadicSubfieldConstructible X ℓ k} (g : K ⟶ L) :
        (((constructibleCocone X ℓ).Φ k).map g).hom =
        (derivedExtendScalarsToPadicAlgCl X ℓ k).map g.hom := rfl
    have h' := congrArg InducedCategory.Hom.hom h
    rw [hΦ, hΦ] at h'
    rw [InducedCategory.hom_ext
      ((derivedExtendScalarsToPadicAlgCl X ℓ k).map_injective h')]
    exact ⟨k, le_rfl, rfl⟩

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
