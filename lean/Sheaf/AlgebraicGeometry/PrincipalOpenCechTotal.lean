/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Data.Finset.Sort
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Alternating total Čech complexes on finite principal covers

Source: Stacks Project, Cohomology, Sections 20.25 and 20.40, and Tag 08D2
(blueprint: def-sc-principal-open-alternating-total).
Nonempty subsets index the alternating rows; the empty cover gives the zero complex.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe uC wC vC

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

variable (A : Type uC) [CommRing A]

/-- Sections on an affine scheme, with the A-action supplied by Mathlib's
`modulesSpecToSheaf`. Source: Stacks, Tag 08D2
(blueprint: def-sc-principal-open-alternating-total). -/
def affineOpenSections (U : (Spec (.of A)).Opens) :
    SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace) ⥤ ModuleCat.{uC} A where
  obj F := (modulesSpecToSheaf.obj F).obj.obj (op U)
  map g := (modulesSpecToSheaf.map g).hom.app (op U)
  map_id F := congrArg (fun g ↦ g.hom.app (op U)) (modulesSpecToSheaf.map_id F)
  map_comp g h := congrArg (fun g ↦ g.hom.app (op U)) (modulesSpecToSheaf.map_comp g h)

/-- Sections are additive, including after restriction of scalars from Γ(U,O).
Source: Stacks, Tag 08D2 (blueprint: def-sc-principal-open-alternating-total).
Proof: sheaf-module morphisms add sectionwise, and evaluation and restriction of scalars
preserve their addition. -/
theorem affineOpenSections_additive_proof (U : (Spec (.of A)).Opens) :
    (affineOpenSections A U).Additive := by
  sorry

/-- The additive instance for A-module sections.
Source: Stacks, Tag 08D2 (blueprint: def-sc-principal-open-alternating-total). -/
instance affineOpenSections_additive (U : (Spec (.of A)).Opens) :
    (affineOpenSections A U).Additive := affineOpenSections_additive_proof A U

variable {A} (r : ℕ) (f : Fin r → A)

/-- The intersection belonging to a finite subset of cover indices.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total). -/
def principalCechIntersection (J : Finset (Fin r)) : (Spec (.of A)).Opens :=
  PrimeSpectrum.basicOpen (∏ j ∈ J, f j)

/-- Erasing an index enlarges a principal intersection.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total).
Proof: the product for J is the erased product times f_j. Its basic open is their
intersection, hence contained in the erased basic open. -/
theorem principalCechIntersection_erase_le (J : Finset (Fin r)) (j : Fin r) :
    principalCechIntersection r f J ≤ principalCechIntersection r f (J.erase j) := by
  sorry

/-- The union of the principal opens is contained in each singleton's covering space.
Source: Stacks, Tag 08D2 (blueprint: def-sc-principal-open-alternating-total).
Proof: a singleton product is f_j, and each D(f_j) is contained in their supremum. -/
theorem principalCechIntersection_singleton_le (j : Fin r) :
    principalCechIntersection r f {j} ≤ ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i) := by
  sorry

/-- Deleting an index gives the same vertical degree in the incoming horizontal row.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total).
Proof: card(J.erase j) = card(J)-1 when j belongs to J; subtract this identity in ℤ. -/
theorem principalCech_erase_degree (J : Finset (Fin r)) (j : Fin r) (hj : j ∈ J) (n : ℤ) :
    n + 1 - ((J.erase j).card : ℤ) = (n + 1) + 1 - (J.card : ℤ) := by
  sorry

variable (F : CochainComplex
  (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)

/-- Total Čech cochains, with row p = card(J)-1 and vertical degree n-p.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total). -/
def principalCechTerms (n : ℤ) : ModuleCat.{uC} A :=
  ModuleCat.of A (∀ J : {J : Finset (Fin r) // J.Nonempty},
    (affineOpenSections A (principalCechIntersection r f J.val)).obj
      (F.X (n + 1 - (J.val.card : ℤ))))

/-- The signed total differential: alternating horizontal restriction and
`(-1)^p d_F` in row p. Empty erased subsets contribute zero.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total). -/
def principalCechDifferentialValue (n : ℤ) (s : principalCechTerms r f F n) :
    principalCechTerms r f F (n + 1) :=
  fun J ↦
    (-1 : A) ^ (J.val.card - 1) •
      (affineOpenSections A (principalCechIntersection r f J.val)).map
        (F.d (n + 1 - (J.val.card : ℤ)) ((n + 1) + 1 - (J.val.card : ℤ))) (s J) +
    @id ((affineOpenSections A (principalCechIntersection r f J.val)).obj
      (F.X ((n + 1) + 1 - (J.val.card : ℤ)))) (∑ j : J.val, if h : (J.val.erase j.val).Nonempty then
      (-1 : A) ^ ((J.val.filter (fun i ↦ i < j.val)).card) •
        (modulesSpecToSheaf.obj (F.X ((n + 1) + 1 - (J.val.card : ℤ)))).obj.map
          (homOfLE (principalCechIntersection_erase_le r f J.val j.val)).op
          ((affineOpenSections A (principalCechIntersection r f (J.val.erase j.val))).map
            (eqToHom (congrArg F.X
              (principalCech_erase_degree r J.val j.val j.property n)))
            (s ⟨J.val.erase j.val, h⟩))
    else 0)

/-- Existence of the linear total differential, with exactly the displayed value.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total).
Proof: every restriction and coefficient differential is A-linear; multiplication by a
sign and finite sums preserve linearity. -/
theorem principalCechDifferential_exists (n : ℤ) :
    ∃ d : principalCechTerms r f F n ⟶ principalCechTerms r f F (n + 1),
      ∀ s, d s = principalCechDifferentialValue r f F n s := by
  sorry

/-- The A-linear total differential, selected from its fully specified formula.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total). -/
def principalCechDifferential (n : ℤ) :
    principalCechTerms r f F n ⟶ principalCechTerms r f F (n + 1) :=
  (principalCechDifferential_exists r f F n).choose

/-- Consecutive total Čech differentials compose to zero.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total).
Proof: two horizontal deletions cancel with opposite signs; vertical squares are zero;
the mixed terms cancel because the vertical sign changes between adjacent rows.
Restrictions commute with the coefficient differential. -/
theorem principalCechDifferential_square (n : ℤ) :
    principalCechDifferential r f F n ≫ principalCechDifferential r f F (n + 1) = 0 := by
  sorry

/-- The alternating Čech total complex, including unbounded coefficient complexes.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total). -/
def principalCechTotal : CochainComplex (ModuleCat.{uC} A) ℤ :=
  CochainComplex.of (principalCechTerms r f F) (principalCechDifferential r f F)
    (principalCechDifferential_square r f F)

/-- The Čech totalization extends to an additive functor, with componentwise maps.
Its augmentation restricts sections of the union to the singleton rows and is zero
on all larger subsets. Source: Stacks, Tag 08D2
(blueprint: def-sc-principal-open-alternating-total).
Proof: apply a coefficient chain map to each subset's sections; naturality commutes with
restrictions and the vertical differential. Identities and composition are componentwise.
The alternating differential of restrictions is zero; restrictions commute with d_F. -/
theorem principalCechFunctor_exists :
    ∃ (C : CochainComplex
      (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ ⥤
        CochainComplex (ModuleCat.{uC} A) ℤ) (hC : C.Additive),
      (∀ F, C.obj F = principalCechTotal r f F) ∧
      (∀ (F G : CochainComplex
        (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) (g : F ⟶ G)
        (n : ℤ) (s : principalCechTerms r f F n) (J : {J : Finset (Fin r) // J.Nonempty})
        (hF : C.obj F = principalCechTotal r f F)
        (hG : C.obj G = principalCechTotal r f G),
        ((eqToHom hF.symm ≫ C.map g ≫ eqToHom hG).f n) s J =
          (affineOpenSections A (principalCechIntersection r f J.val)).map
            (g.f (n + 1 - (J.val.card : ℤ)))
            (s J)) := by
  sorry


/-- The alternating total Čech functor with its componentwise action.
Source: Stacks, Tag 08D2 (blueprint: def-sc-principal-open-alternating-total). -/
def principalCechFunctor := (principalCechFunctor_exists r f).choose

/-- Its chosen objects are the explicitly constructed total complexes.
Source: Stacks, Tag 08D2 (blueprint: def-sc-principal-open-alternating-total). -/
def principalCechObjIso : (principalCechFunctor r f).obj F ≅ principalCechTotal r f F :=
  eqToIso ((principalCechFunctor_exists r f).choose_spec.choose_spec.1 F)

/-- A singleton Čech row has vertical degree n.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total).
Proof: a singleton has cardinality one, so n + 1 - 1 = n. -/
theorem principalCech_singleton_degree (j : Fin r) (n : ℤ) :
    n = n + 1 - (({j} : Finset (Fin r)).card : ℤ) := by
  sorry

/-- The augmentation from sections of U to alternating Čech cochains.
It is restriction on singleton rows and zero on larger subsets.
Source: Stacks, Tag 08D2 (blueprint: def-sc-principal-open-alternating-total).
Proof: the restrictions agree on pairwise intersections, so their alternating
horizontal differential vanishes; restrictions also commute with d_F.
This gives a chain map, natural in the coefficient complex. -/
theorem principalCechAugmentation_exists :
    ∃ α : (affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⟶ principalCechFunctor r f,
      (∀ (F : CochainComplex
        (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) (n : ℤ)
        (s : (affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))).obj (F.X n))
        (j : Fin r),
        ((α.app F ≫ (principalCechObjIso r f F).hom).f n) s ⟨{j}, by simp⟩ =
          (modulesSpecToSheaf.obj
            (F.X (n + 1 - (({j} : Finset (Fin r)).card : ℤ)))).obj.map
              (homOfLE (principalCechIntersection_singleton_le r f j)).op
              ((affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))).map
                (eqToHom (congrArg F.X (principalCech_singleton_degree r j n))) s)) ∧
      (∀ (F : CochainComplex
        (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) (n : ℤ)
        (s : (affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))).obj (F.X n))
        (J : {J : Finset (Fin r) // J.Nonempty}), 1 < J.val.card →
          ((α.app F ≫ (principalCechObjIso r f F).hom).f n) s J = 0) := by
  sorry

/-- The canonical restriction augmentation.
Source: Stacks, Tag 08D2 (blueprint: def-sc-principal-open-alternating-total). -/
def principalCechAugmentation := (principalCechAugmentation_exists r f).choose

/-- On a K-injective complex, the Čech augmentation is a quasi-isomorphism.
Source: Stacks, Cohomology, Tag 08C2 (blueprint: def-sc-principal-open-alternating-total).
Proof: resolve by injectives and use the augmented Čech contraction locally on a cover
member. Sections of injective module sheaves are Čech-acyclic. A finite cover gives a
bounded horizontal direction; totalization therefore preserves the columnwise comparison,
including unbounded vertical complexes. K-injective replacement identifies the result
with derived sections, and the section-to-Čech augmentation is the displayed comparison. -/
theorem principalCechAugmentation_quasiIso
    (J : CochainComplex
      (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) [J.IsKInjective] :
    QuasiIso ((principalCechAugmentation r f).app J) := by
  sorry

variable [HasDerivedCategory.{wC}
  (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace))]
  [HasDerivedCategory.{vC} (ModuleCat.{uC} A)]

/-- The canonical derived Čech comparison, characterized by every K-injective resolution.
Source: Stacks, Tag 08C2 (blueprint: def-sc-principal-open-alternating-total).
Proof: choose F → J a K-injective resolution. Invert the Čech augmentation on J,
which is a quasi-isomorphism by principalCechAugmentation_quasiIso, and identify the
sections of J with the right derived functor using rightDerivedFunctorObjQIso.
The resulting roof is independent of the resolution: maps between K-injective
resolutions and naturality of the augmentation give the displayed commuting square.
Its uniqueness follows since both the resolution and the augmentation become invertible. -/
theorem principalCechDerivedComparison_exists :
    ∃ β : DerivedCategory.Q.obj ((principalCechFunctor r f).obj F) ⟶
      (affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))).rightDerivedFunctor.obj
        (DerivedCategory.Q.obj F),
      ∀ (J : CochainComplex
        (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
        [J.IsKInjective] (i : F ⟶ J) [QuasiIso i],
        β ≫
          (affineOpenSections A (⨆ i, PrimeSpectrum.basicOpen (f i))).rightDerivedFunctor.map
            (DerivedCategory.Q.map i) ≫
          ((affineOpenSections A (⨆ i, PrimeSpectrum.basicOpen (f i))).rightDerivedFunctorObjQIso
            J).hom ≫ DerivedCategory.Q.map ((principalCechAugmentation r f).app J) =
          DerivedCategory.Q.map ((principalCechFunctor r f).map i) := by
  sorry

/-- The canonical map Tot(Č_alt(U,F)) → RΓ(U,F), as a roof through a K-injective resolution.
Source: Stacks, Tag 08D2 (blueprint: def-sc-principal-open-alternating-total). -/
def principalCechDerivedComparison :
    DerivedCategory.Q.obj ((principalCechFunctor r f).obj F) ⟶
      (affineOpenSections A (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))).rightDerivedFunctor.obj
        (DerivedCategory.Q.obj F) :=
  (principalCechDerivedComparison_exists r f F).choose

end
end AlgebraicGeometry
