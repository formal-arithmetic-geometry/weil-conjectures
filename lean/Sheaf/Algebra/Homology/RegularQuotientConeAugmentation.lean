/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Normalized principal-quotient cone augmentation

Source: Stacks Project, sites-cohomology.tex, Tags 06YP, 06YS, 06YT, 06YY and 07A6.
(blueprint: lem-cbc-regular-quotient-cone-augmentation).

The cone is Mathlib's cone, with unshifted summand second in its biproduct API.
The ordinary extension is the existing sheafified tensor, whose pure tensors have
scalar first. All computation maps below use the universal derived counit.
-/

@[expose] public section
set_option autoImplicit false

universe u v r wR wS
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules.RegularQuotientCone

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]

/-- The recorded module category, as a transparent abbreviation.
Source: Stacks 06YY (blueprint: lem-cbc-regular-quotient-cone-augmentation). -/
abbrev Modules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)

/-- The recorded restriction functor, as a transparent abbreviation.
Source: Stacks 03D7 (blueprint: lem-cbc-regular-quotient-cone-augmentation). -/
noncomputable abbrev restriction {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S) :
    Modules S ⥤ Modules R :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)

/-- Multiplication by the compatible family of local scalars defining a global section.
Source: Stacks 06YP, principal-resolution construction
(blueprint: lem-cbc-regular-quotient-cone-augmentation). -/
noncomputable def scalar (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections) :
    𝟭 (Modules R) ⟶ 𝟭 (Modules R) where
  app M := { val := {
    app := fun U ↦ ModuleCat.ofHom (LinearMap.lsmul (R.obj.obj U) (M.val.obj U) (t.val U))
    naturality := by
      intro U V f
      ext x
      change t.val V • M.val.map f x = M.val.map f (t.val U • x)
      rw [M.val.map_smul]
      congr 1
      exact (t.property f).symm } }
  naturality {M N} f := by
    ext U x
    change t.val U • f.val.app U x = f.val.app U (t.val U • x)
    exact ((f.val.app U).hom.map_smul (t.val U) x).symm

/-- The map of unit modules induced by the ring-sheaf map.
Source: Stacks 06YP, principal-resolution construction
(blueprint: lem-cbc-regular-quotient-cone-augmentation). -/
noncomputable def ringMap {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S) :
    unit (derivedChangeRingIndependentCoefficients J R) ⟶
      (restriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) :=
  ((restriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S))).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk (fun U ↦ (1 : S.obj.obj U))
      (fun {_ _} f ↦ map_one (S.obj.map f).hom))

/-- Multiplication by the global section on an unbounded cochain complex.
Source: Stacks 06YP, principal-resolution construction
(blueprint: lem-cbc-regular-quotient-cone-augmentation). -/
noncomputable def complexScalar (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections) :
    𝟭 (CochainComplex (Modules R) ℤ) ⟶ 𝟭 (CochainComplex (Modules R) ℤ) where
  app P := {
    f := fun n ↦ (scalar R t).app (P.X n)
    comm' := fun i j _ ↦ ((scalar R t).naturality (P.d i j)).symm }
  naturality {_P _Q} f := by
    ext n : 1
    exact (scalar R t).naturality (f.f n)

variable [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]

/-- The strict cone functor, with diagonal action on chain maps.
Source: Stacks 06YP, principal quotient construction
(blueprint: lem-cbc-regular-quotient-cone-augmentation). -/
noncomputable def cone (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections) :
    CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ where
  obj P := CochainComplex.mappingCone ((complexScalar R t).app P)
  map {_P _Q} h := CochainComplex.mappingCone.map _ _ h h
    ((complexScalar R t).naturality h).symm
  map_id _P := CochainComplex.mappingCone.map_id _
  map_comp _f _g := CochainComplex.mappingCone.map_comp _ _ _ _ _ _ _ _ _

/-- The canonical inclusion into the unshifted summand of the cone.
Source: Stacks 06YP (blueprint: lem-cbc-regular-quotient-cone-augmentation). -/
noncomputable def inclusion (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections) :
    𝟭 (CochainComplex (Modules R) ℤ) ⟶ cone R t where
  app P := CochainComplex.mappingCone.inr ((complexScalar R t).app P)
  naturality {P Q} h := by
    ext n : 1
    simp [cone, CochainComplex.mappingCone.map]

variable [EssentiallySmall.{r} C]
  {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
  [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wS} (Modules S)]

/-- The chain augmentation and its normalized descent, with the existing universal
change-of-rings model. The section equation fixes the coefficient unit, and the cone
component equation fixes the augmentation, including its zero shifted component.
The factorization isomorphisms specify localizations, not freely chosen comparisons.
Source: Stacks 06YP, 06YY and 07A6
(blueprint: lem-cbc-regular-quotient-cone-augmentation). -/
structure Augmentation
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (d : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ) where
  /-- The ordinary coefficient unit on complexes. -/
  ρ : 𝟭 (CochainComplex (Modules R) ℤ) ⟶
    d.E.mapHomologicalComplex (.up ℤ) ⋙ (restriction φ).mapHomologicalComplex (.up ℤ)
  /-- Its local formula is the sheafification of `1 ⊗ x`, in scalar-first convention. -/
  ρ_sections : ∀ (P : CochainComplex (Modules R) ℤ) (n : ℤ) (U : Cᵒᵖ)
    (x : (P.X n).val.obj U),
    (eqToHom (d.obj_eq (P.X n))).val.app U (((ρ.app P).f n).val.app U x) =
      (((PresheafOfModules.sheafificationAdjunction.{r}
        (J := J) (R := derivedChangeRingIndependentCoefficients J S)
        (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)).unit.app
        (changeOfRingsPresheaf φ (P.X n))).app U
        ((ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).unit.app
          ((P.X n).val.obj U) x))
  /-- The chain augmentation, natural for chain maps (in particular K-flat ones). -/
  a : cone R t ⟶
    d.E.mapHomologicalComplex (.up ℤ) ⋙ (restriction φ).mapHomologicalComplex (.up ℤ)
  /-- In coordinates `(y,x)` it is `y ⊗ 1`; the shifted component is zero. -/
  a_components : ∀ (P : CochainComplex (Modules R) ℤ) (n : ℤ),
    (a.app P).f n =
      (CochainComplex.mappingCone.snd ((complexScalar R t).app P)).v n n (add_zero n) ≫
        (ρ.app P).f n
  /-- The augmentation is a quasi-isomorphism for every K-flat complex. -/
  quasiIso : ∀ P : CochainComplex (Modules R) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P → QuasiIso (a.app P)
  /-- The strict equality before localization. -/
  augmentation_inclusion : inclusion R t ≫ a = ρ
  /-- Cone formation preserves quasi-isomorphisms between K-flat complexes. -/
  cone_preserves : ∀ {P Q : CochainComplex (Modules R) ℤ} (h : P ⟶ Q),
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
    CochainComplex.IsKFlatIndependentCoefficients (R := R) Q → QuasiIso h →
      QuasiIso ((cone R t).map h)
  /-- The restricted ordinary tensor preserves the same quasi-isomorphisms. -/
  tensor_preserves : ∀ {P Q : CochainComplex (Modules R) ℤ} (h : P ⟶ Q),
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
    CochainComplex.IsKFlatIndependentCoefficients (R := R) Q → QuasiIso h →
      QuasiIso (((d.E.mapHomologicalComplex (.up ℤ)) ⋙
        (restriction φ).mapHomologicalComplex (.up ℤ)).map h)
  /-- Restriction on derived categories, characterized by exact termwise restriction. -/
  V : DerivedCategory (Modules S) ⥤ DerivedCategory (Modules R)
  /-- The canonical factorization comparison for restriction. -/
  restriction_factor : DerivedCategory.Q ⋙ V ≅
    (restriction φ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  /-- The actual derived coefficient adjunction. -/
  adjunction : d.T ⊣ V
  /-- Its unit is normalized by the ordinary coefficient map on K-flat models. -/
  unit_normalization : ∀ P : CochainComplex (Modules R) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
      adjunction.unit.app (DerivedCategory.Q.obj P) ≫ V.map (d.ε.app P) ≫
        restriction_factor.hom.app ((d.E.mapHomologicalComplex (.up ℤ)).obj P) =
          DerivedCategory.Q.map (ρ.app P)
  /-- The localized cone functor. -/
  D : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules R)
  /-- Cone formation is localized on all complexes. -/
  cone_factor : DerivedCategory.Q ⋙ D ≅ cone R t ⋙ DerivedCategory.Q
  /-- The localized cone inclusion. -/
  i : 𝟭 (DerivedCategory (Modules R)) ⟶ D
  /-- Its component is the localization of the strict inclusion. -/
  inclusion_components : ∀ P : CochainComplex (Modules R) ℤ,
    i.app (DerivedCategory.Q.obj P) ≫ cone_factor.hom.app P =
      DerivedCategory.Q.map ((inclusion R t).app P)
  /-- Natural for every derived morphism, including resolution-comparison roofs. -/
  A : D ≅ d.T ⋙ V
  /-- The component at every K-flat complex uses exactly the universal counit. -/
  A_components : ∀ P : CochainComplex (Modules R) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
      A.hom.app (DerivedCategory.Q.obj P) ≫ V.map (d.ε.app P) ≫
        restriction_factor.hom.app ((d.E.mapHomologicalComplex (.up ℤ)).obj P) =
          cone_factor.hom.app P ≫ DerivedCategory.Q.map (a.app P)
  /-- After localization the inclusion becomes the actual scalar-extension unit. -/
  unit_identity : i ≫ A.hom = adjunction.unit

/-- The normalized principal-quotient augmentation, without termwise flatness.
The zero composite says precisely `φ(t) = 0`; short exactness is in module sheaves,
so no surjectivity on sections or existence of points is assumed.

Source: Stacks Project, sites-cohomology.tex, Tags 06YP, 06YS, 06YT, 06YY and 07A6
(blueprint: lem-cbc-regular-quotient-cone-augmentation).

Proof:
1. The exact principal quotient sequence gives a quasi-isomorphism from the two-term
cone `B = C(t : R[0] → R[0])` to the restricted `S[0]`, by
lem-pc-cone-short-exact-quasi-iso.
2. Right tensoring with P identifies `B ⊗ P` with `C(t id_P)` by
lem-weil-pbc-total-tensor-homotopy-cone-signs: its differential is `(dy+tx,-dx)`.
The unit and symmetry identify the tensor of the degree-zero quotient with restricted
ordinary scalar extension, and the tensor map is exactly `(y,x) ↦ 1 ⊗ y`.
Tag 06YP makes it a quasi-isomorphism for arbitrary K-flat P.
3. The balanced sectionwise formulas give the chain map, its naturality for every h,
and `a i = ρ`. They descend through sheafification; no sectionwise epimorphism is used.
4. B is K-flat: tensoring an acyclic complex with B gives the scalar cone of that
acyclic complex, which is acyclic by lem-pur-quasi-iso-cone-acyclic. Thus the tensor-cone
comparison proves cone invariance. Derived change of rings and exact restriction
(lem-pur-derived-change-of-rings, lem-pur-sheaf-ring-derived-coefficient-adjunction)
prove restricted scalar-extension invariance; both constructions respect homotopies.
5. Localize the cone and its inclusion using lem-weil-pbc-localization-universal-property.
On flat-term K-flat complexes the augmentation gives a natural isomorphism. Descend it
using lem-weil-pbc-site-derived-tensor-descent, obtaining A on the whole derived category.
6. For arbitrary K-flat P choose a flat-term K-flat resolution F → P using
lem-pc-kflat-resolution. Naturality of A and of the universal computation counit,
and chain naturality of a, identify their two expressions after the invertible cone
image of F → P. Cancel that image to obtain A_components for P.
7. The normalized derived coefficient adjunction identifies its unit on flat-term
K-flat models with Q(ρ). The equality `a i = ρ` and uniqueness under localization
therefore give unit_identity on every derived object.
8. For resolutions s : P → X and t : P' → X, apply naturality of A to
`Q(s) ≫ inv Q(t)`. For a third resolution the two adjacent factors cancel, giving
the cocycle. The same naturality applies to every derived morphism. -/
theorem nonempty_augmentation
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (ht : (scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R)) ≫
      ringMap φ = 0)
    (_hexact : (ShortComplex.mk
      ((scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R)))
      (ringMap φ) ht).ShortExact)
    (d : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ) :
    Nonempty (Augmentation φ t d) := by
  sorry

end SheafOfModules.RegularQuotientCone
