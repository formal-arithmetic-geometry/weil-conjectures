/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q94
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Homology.HomComplex
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Adjunction.Basic
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Sheaf.Algebra.Homology.HomComplexGlobalHomotopy
import Sheaf.Algebra.Homology.HomTensorTotal
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # K-injective models for internal Hom and its derived global sections

Source: Stacks Project, sites-cohomology.tex, Section 08J7 (section-internal-hom),
Lemmas 0A95, 0A96, 08JA and 08J9
(blueprint: lem-sfb-derived-internal-hom-sections-model).

The tensor functor is characterized by its natural total-complex models on K-flat
representatives. The internal Hom is the existing Hom-complex localization. All
representative comparisons are natural isomorphisms, including the full derived
complex of global sections, rather than only its zeroth cohomology.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe c v r w z

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory.DerivedInternalHomSectionsModel

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max c v r})

/-- The recorded module category, with sections in a universe containing the site.
Source: Stacks, Section 08J7
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
abbrev Modules := ringedSiteModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)

/-- Unbounded cochain complexes in the recorded module category.
Source: Stacks, Section 08J7
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
abbrev Complexes := CochainComplex (Modules.{c, v, r} R) ℤ

variable [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- The recorded unbounded derived category, with its chosen morphism universe.
Source: Stacks, Section 08J7
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
abbrev Derived [HasDerivedCategory.{w} (Modules.{c, v, r} R)] :=
  DerivedCategory (Modules.{c, v, r} R)

/-- Ordinary global sections are morphisms from the unit module sheaf.
Source: Stacks, Section 07A5 and Lemma 08JA
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
noncomputable abbrev sections : Modules.{c, v, r} R ⥤ AddCommGrpCat.{max c v r} :=
  preadditiveCoyoneda.obj (op (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))

variable [HasDerivedCategory.{w} (Modules.{c, v, r} R)]
  [HasDerivedCategory.{z} AddCommGrpCat.{max c v r}]

/-- The full right derived global-sections functor underlying the recorded
zeroth-hypercohomology construction. It uses the same canonical K-injective replacement.
Source: Stacks, Section 07A5 and Lemma 08JA
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
noncomputable def derivedSections :
    Derived.{c, v, r, w} R ⥤ DerivedCategory.{z} AddCommGrpCat.{max c v r} :=
  letI : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, r} R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  (sections.{c, v, r} R).rightDerivedFunctor

/-- The existing internal-Hom bifunctor, in curried form.
Source: Stacks, Section 08J7
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
noncomputable abbrev internalHom :
    (Derived.{c, v, r, w} R)ᵒᵖ ⥤ Derived.{c, v, r, w} R ⥤ Derived.{c, v, r, w} R :=
  Functor.curry.obj (derivedInternalHomOfUniverses.{c, v, r, w} J R)

/-- The full subcategory of K-injective complexes; no condition on the source is imposed.
Source: Stacks, Definition 070H and Section 08J7
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
def injectiveProperty : ObjectProperty (Complexes.{c, v, r} R) :=
  fun I ↦ CochainComplex.IsKInjective I

/-- Restrict the recorded derived internal Hom to arbitrary source complexes and
K-injective target complexes.
Source: Stacks, Section 08J7
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
noncomputable def representedInternalHom :
    (Complexes.{c, v, r} R)ᵒᵖ × (injectiveProperty.{c, v, r} R).FullSubcategory ⥤
      Derived.{c, v, r, w} R :=
  (DerivedCategory.Q.op.prod ((injectiveProperty.{c, v, r} R).ι ⋙ DerivedCategory.Q)) ⋙
    derivedInternalHomOfUniverses.{c, v, r, w} J R

/-- The recorded sheaf Hom complex on the same pairs of representatives.
Source: Stacks, Section 08J7 and Section 0A8X
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
noncomputable def representativeHom :
    (Complexes.{c, v, r} R)ᵒᵖ × (injectiveProperty.{c, v, r} R).FullSubcategory ⥤
      Complexes.{c, v, r} R :=
  (𝟭 (Complexes.{c, v, r} R)ᵒᵖ).prod (injectiveProperty.{c, v, r} R).ι ⋙
    Functor.uncurry.obj (homComplexFunctor (R := R))

/-- The ordinary complex of global Hom cochains, functorially in both representatives.
Source: Stacks, Section 0A8X, equation-global-cohomology-hom-complex
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
noncomputable def globalHom :
    (Complexes.{c, v, r} R)ᵒᵖ × (injectiveProperty.{c, v, r} R).FullSubcategory ⥤
      CochainComplex AddCommGrpCat.{max c v r} ℤ :=
  representativeHom.{c, v, r} R ⋙ (sections.{c, v, r} R).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Total tensor complexes, using precisely the recorded sheaf tensor and Koszul signs.
Source: Stacks, Section 06YL and Section 08J7
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
noncomputable def totalTensor :
    Complexes.{c, v, r} R ⥤ Complexes.{c, v, r} R ⥤ Complexes.{c, v, r} R :=
  letI := (SheafOfModules.isMonoidal_W_independentCoefficients R)
  letI := SheafOfModules.monoidalCategory R
  letI := (SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R)
  letI := (SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R)
  (curriedTensor (Modules.{c, v, r} R)).map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)

/-- Any right adjoint of the derived tensor functor is naturally the recorded internal Hom.
The hypothesis on T spells out the node's definition of derived tensor: for every K-flat
representative P of K, its value on any complex is the localized total tensor P tensor N.
It imposes no flatness or boundedness on the source representative used in the conclusions.

Source: Stacks, Section 08J7 (equation-internal-hom), Lemmas 08J9, 0A95 and 0A96
(blueprint: lem-sfb-derived-internal-hom-sections-model).

Proof: Choose a K-flat representative P of K and a K-injective representative I of M.
Hom(P,I) is K-injective by 0A96. The total-tensor/Hom-complex currying isomorphism
identifies Hom(N,Hom(P,I)) with Hom(Tot(N tensor P),I), with the standard signs.
Use symmetry of the sheaf tensor to identify this total complex with Tot(P tensor N).
Taking global sections and zeroth cohomology identifies these groups with derived
morphisms by 08JA. The given total-tensor comparison identifies the latter object with
T(N). This is natural in N and M and therefore gives T adjoint to internalHom(K,-).
Uniqueness of right adjoints identifies any specified H with this functor. Replacing
P by an arbitrary representative A does not change Hom(A,I) after localization,
by 0A95; thus no K-flatness of A is required. -/
theorem tensorRightAdjoint_iso
    (K : Derived.{c, v, r, w} R) (T H : Derived.{c, v, r, w} R ⥤ Derived.{c, v, r, w} R)
    (model : ∀ (P : Complexes.{c, v, r} R),
      CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
      (DerivedCategory.Q.obj P ≅ K) →
      Nonempty (DerivedCategory.Q ⋙ T ≅ (totalTensor.{c, v, r} R).obj P ⋙ DerivedCategory.Q))
    (adj : T ⊣ H) :
    Nonempty (H ≅ (internalHom.{c, v, r, w} R).obj (op K)) := by
  sorry

/-- Natural K-injective models for the internal Hom, its full derived global sections,
and all of its hypercohomology groups. The third comparison identifies the ordinary
sections complex with the usual global Hom complex, including its differential and
its degree-n product of morphism groups.

Source: Stacks, Section 08J7, Lemmas 08JA, 08J9, 0A95 and 0A96
(blueprint: lem-sfb-derived-internal-hom-sections-model).

Proof: First compare the canonical functorial K-injective replacement of I with I
itself. Its resolution map is a quasi-isomorphism between K-injectives. Applying
Hom(A,-) and Q inverts it by 0A95. The resulting comparison with the localized
internal Hom is natural in every source chain map and every map between K-injectives.
Next replace A by a K-flat P. Hom(P,I) is K-injective by 0A96, hence RΓ is computed
by ordinary sections on it. A quasi-isomorphism P to A induces quasi-isomorphisms
on both sheaf Hom complexes and global Hom complexes, since I is K-injective.
This transports the full-complex comparison back to A. Functorial resolutions and
naturality of pre- and postcomposition give the displayed natural isomorphism.
In each degree, sections commute with products and sections of sheaf Hom are global
module maps. These identifications give the third chain isomorphism: its differential
is d_I f - (-1)^n f d_A. The same component formula gives the naturality equation below.
Finally the cohomology of the global Hom complex is homotopy classes A to I[n].
K-injectivity identifies these with derived morphisms. Transport along representatives
of K and M gives the last assertion for every integer n, including negative n.
Zero complexes and the empty site are included; no boundedness or flatness of A is used. -/
theorem derived_internalHom_sections_model :
    Nonempty (representedInternalHom.{c, v, r, w} R ≅
      representativeHom.{c, v, r} R ⋙ DerivedCategory.Q) ∧
    Nonempty (representedInternalHom.{c, v, r, w} R ⋙ derivedSections.{c, v, r, w, z} R ≅
      globalHom.{c, v, r} R ⋙ DerivedCategory.Q) ∧
    (∃ e : ∀ (A I : Complexes.{c, v, r} R),
        ((sections.{c, v, r} R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (homComplex (R := R) A I) ≅ CochainComplex.HomComplex A I,
      ∀ (A A' I I' : Complexes.{c, v, r} R) (f : A' ⟶ A) (g : I ⟶ I')
        (n p q : ℤ) (hpq : p + n = q)
        (s : (((sections.{c, v, r} R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (homComplex (R := R) A I)).X n),
        ((e A' I').hom.f n
          ((((sections.{c, v, r} R).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (((homComplexFunctor (R := R)).map f.op).app I ≫
              ((homComplexFunctor (R := R)).obj (op A')).map g)).f n s)).v p q hpq =
          f.f p ≫ ((e A I).hom.f n s).v p q hpq ≫ g.f q) ∧
    (∀ (K M : Derived.{c, v, r, w} R) (n : ℤ),
      Nonempty (((DerivedCategory.homologyFunctor.{z} AddCommGrpCat.{max c v r} n).obj
        ((derivedSections.{c, v, r, w, z} R).obj
          (((internalHom.{c, v, r, w} R).obj (op K)).obj M))) ≃+
          (K ⟶ M⟦n⟧))) := by
  sorry

end CategoryTheory.DerivedInternalHomSectionsModel
