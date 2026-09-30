/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Claude
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.Algebra.Homology.Precylinder
public import Mathlib.AlgebraicTopology.ModelCategory.LeftHomotopy
public import Mathlib.CategoryTheory.GuitartExact.Quotient
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfLocalizedEquivalences
public import Mathlib.CategoryTheory.Localization.OfQuotient
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.FromJoel.CategoryTheory.Localization.Composition
public import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions

/-!
# Left derivability structures on the homotopy category given by functorial resolutions

Let `A` be an abelian category and `P` a triangulated property of objects of the homotopy
category `K(A)` which is closed under isomorphisms. Suppose that there is a functorial
resolution `p : ρ ⟶ 𝟭` on cochain complexes, whose components are quasi-isomorphisms and
such that `P` holds for the image of `ρ K` in `K(A)` for every `K`. Then the inclusion of
the full subcategory of `K(A)` given by `P`, with the quasi-isomorphisms, is a left
derivability structure (`HomotopyCategory.isLeftDerivabilityStructure_quasiIsoLocalizerMorphism`).

This generalises the K-flat left derivability structure of
`WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat`, and the proof follows it: the
statement is first obtained on the category of cochain complexes, and then transferred to
`K(A)`, the quotient functor being a localized equivalence on both sides.

## Main definitions and results

- `HomotopyCategory.quasiIsoLocalizerMorphism P`: the localizer morphism given by the inclusion
  of the full subcategory of `K(A)` defined by `P`, with the quasi-isomorphisms.
- `HomotopyCategory.isLeftDerivabilityStructure_quasiIsoLocalizerMorphism`: it is a left
  derivability structure as soon as `P` contains functorial resolutions.

-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex HomotopicalAlgebra

namespace HomotopyCategory

variable {A : Type*} [Category A] [Abelian A]
  (P : ObjectProperty (HomotopyCategory A (.up ℤ)))

/-- The localizer morphism given by the inclusion of the full subcategory of the homotopy
category defined by `P`, with the quasi-isomorphisms on both sides. -/
@[simps]
def quasiIsoLocalizerMorphism :
    LocalizerMorphism ((quasiIso A (.up ℤ)).inverseImage P.ι) (quasiIso A (.up ℤ)) where
  functor := P.ι
  map := by rfl

instance : (quasiIsoLocalizerMorphism P).functor.Full := inferInstanceAs P.ι.Full

instance : (quasiIsoLocalizerMorphism P).functor.Faithful := inferInstanceAs P.ι.Faithful

namespace quasiIsoLocalizerMorphism

/-! The commutative square of localizer morphisms used to transfer the left derivability
structure from cochain complexes to the homotopy category:
```
 P.inverseImage quotient ---T---> CochainComplex A ℤ
          |                              |
          L                              R
          v                              v
          P  -----------B-----------> K(A)
```
-/

/-- The property of cochain complexes whose image in the homotopy category satisfies `P`. -/
abbrev cochainProp : ObjectProperty (CochainComplex A ℤ) :=
  P.inverseImage (quotient A (.up ℤ))

/-- The inclusion of the complexes satisfying `cochainProp P`, with the quasi-isomorphisms. -/
@[simps]
def T : LocalizerMorphism
    ((HomologicalComplex.quasiIso A (.up ℤ)).inverseImage (cochainProp P).ι)
    (HomologicalComplex.quasiIso A (.up ℤ)) where
  functor := (cochainProp P).ι
  map := by rfl

instance : (T P).functor.Full := inferInstanceAs (cochainProp P).ι.Full

instance : (T P).functor.Faithful := inferInstanceAs (cochainProp P).ι.Faithful

/-- The quotient functor, restricted to the complexes satisfying `cochainProp P`. -/
def L : LocalizerMorphism
    ((HomologicalComplex.quasiIso A (.up ℤ)).inverseImage (cochainProp P).ι)
    ((quasiIso A (.up ℤ)).inverseImage P.ι) where
  functor := ObjectProperty.lift _ ((cochainProp P).ι ⋙ quotient _ _) (fun K ↦ K.2)
  map := by
    rintro ⟨K, hK⟩ ⟨L, hL⟩ ⟨f : K ⟶ L⟩ hf
    simpa [quotient_map_mem_quasiIso_iff] using hf

variable (A) in
/-- The quotient functor from cochain complexes to the homotopy category. -/
abbrev R : LocalizerMorphism (HomologicalComplex.quasiIso A (.up ℤ)) (quasiIso A (.up ℤ)) where
  functor := quotient _ _
  map _ _ _ _ := by simpa [quotient_map_mem_quasiIso_iff]

/-- The square of localizer morphisms commutes (definitionally). -/
def iso :
    (T P).functor ⋙ (R A).functor ≅ (L P).functor ⋙ (quasiIsoLocalizerMorphism P).functor :=
  Iso.refl _

/-- The homotopy equivalences between complexes satisfying `cochainProp P`. -/
def WL : MorphismProperty (cochainProp P).FullSubcategory :=
  (homotopyEquivalences A (.up ℤ)).inverseImage (T P).functor

instance : (L P).functor.EssSurj where
  mem_essImage := by
    rintro ⟨K, hK⟩
    obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
    exact ⟨⟨K, hK⟩, ⟨Iso.refl _⟩⟩

instance : (L P).functor.Full where
  map_surjective {K L} f := by
    obtain ⟨g, hg⟩ := (quotient _ _).map_surjective f.hom
    exact ⟨ObjectProperty.homMk g, by cat_disch⟩

variable [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]

set_option backward.defeqAttrib.useBackward true in
variable {P} in
lemma cochainProp_cylinder (K : CochainComplex A ℤ) (hK : cochainProp P K) :
    cochainProp P K.cylinder := by
  apply ObjectProperty.ext_of_isTriangulatedClosed₃ _ _ (mappingCone_triangleh_distinguished _)
  · exact hK
  · have := preservesBinaryBiproducts_of_preservesBiproducts (quotient A (.up ℤ))
    refine P.prop_of_iso ((biprod.isoProd _ _).symm ≪≫ ((quotient _ _).mapBiprod K K).symm) ?_
    exact P.prop_prod _ _ hK hK

set_option backward.isDefEq.respectTransparency false in
instance : (L P).functor.IsLocalization (WL P) :=
  Functor.isLocalization_of_essSurj_of_full_of_exists_cylinders _ _
    (fun _ _ f hf ↦ by
      have := (NatIso.isIso_map_iff (iso P) f).1
        (quotient_inverts_homotopyEquivalences _ _ _ hf)
      dsimp only [Functor.comp_map] at this
      exact isIso_of_reflects_iso _ (quasiIsoLocalizerMorphism P).functor) (by
      rintro ⟨K₁, hK₁⟩ ⟨K₂, hK₂⟩ (f₀ f₁) hf
      refine ⟨K₁.precylinder.toFullSubcategory (by exact cochainProp_cylinder _ hK₁),
        ?_, ?_⟩
      · exact Precylinder.LeftHomotopy.fullSubcategoryEquiv.symm
          { h := cylinder.desc _ _
                (homotopyOfEq _ _ ((ObjectProperty.ι _).congr_map hf)) }
      · exact ⟨cylinder.homotopyEquiv K₁ (fun n ↦ ⟨n - 1, by simp⟩), rfl⟩)

instance : (L P).IsLocalizedEquivalence :=
  (L P).isLocalizedEquivalence_of_isLocalization (WL P)
    (fun _ _ _ hf ↦ homotopyEquivalences_le_quasiIso _ _ _ hf) (by
      rintro ⟨K, hK⟩ ⟨L, hL⟩ f hf
      obtain ⟨K, rfl⟩ := quotient_obj_surjective K
      obtain ⟨L, rfl⟩ := quotient_obj_surjective L
      obtain ⟨f, rfl⟩ := ObjectProperty.homMk_surjective f
      obtain ⟨f, rfl⟩ := (quotient _ _).map_surjective f
      refine ⟨⟨K, hK⟩, ⟨L, hL⟩, ObjectProperty.homMk f, ?_, ⟨Iso.refl _⟩⟩
      simpa [quotient_map_mem_quasiIso_iff] using hf)

instance : (R A).IsLocalizedEquivalence := by
  have : (HomologicalComplex.quasiIso A (.up ℤ)).HasLocalization := .standard _
  exact LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization (R A)
    HomologicalComplexUpToQuasiIso.Qh

instance : (R A).functor.EssSurj := by
  dsimp [R]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
instance : TwoSquare.GuitartExact (iso P).inv :=
  TwoSquare.GuitartExact.quotient_of_nonempty_leftHomotopy (iso P).symm (by
    rintro ⟨K₁, hK₁⟩ K₂ (f₀ f₁ : K₁ ⟶ K₂) hf
    refine ⟨K₁.precylinder.toFullSubcategory (by exact cochainProp_cylinder K₁ hK₁),
      ?_, ⟨?_⟩⟩
    · ext : 1
      exact eq_of_homotopy _ _
        (cylinder.homotopy₀₁ _ (fun n ↦ ⟨n - 1, by simp⟩))
    · exact { h := cylinder.desc _ _ (homotopyOfEq _ _ hf) })

end quasiIsoLocalizerMorphism

open quasiIsoLocalizerMorphism in
set_option backward.isDefEq.respectTransparency false in
/-- Let `P` be a triangulated property of objects of `K(A)`, closed under isomorphisms. If
there is a functorial resolution `p : ρ ⟶ 𝟭` of cochain complexes by quasi-isomorphisms
such that the image of `ρ K` in `K(A)` satisfies `P` for every `K`, then the inclusion of
the full subcategory defined by `P` is a left derivability structure for the
quasi-isomorphisms. -/
lemma isLeftDerivabilityStructure_quasiIsoLocalizerMorphism
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    {ρ : CochainComplex A ℤ ⥤ CochainComplex A ℤ} (p : ρ ⟶ 𝟭 _)
    (hp : ∀ K, QuasiIso (p.app K)) (hρ : ∀ K, P ((quotient A (.up ℤ)).obj (ρ.obj K))) :
    (quasiIsoLocalizerMorphism P).IsLeftDerivabilityStructure := by
  have : (T P).IsInduced := ⟨rfl⟩
  have : (T P).IsLeftDerivabilityStructure :=
    (T P).isLeftDerivabilityStructure_of_functorial_resolutions
      (ρ := ObjectProperty.lift _ ρ hρ) p
      (fun K ↦ by rw [HomologicalComplex.mem_quasiIso_iff]; exact hp K) rfl
  exact LocalizerMorphism.isLeftDerivabilityStructure_of_isLocalizedEquivalence (iso P)

end HomotopyCategory
