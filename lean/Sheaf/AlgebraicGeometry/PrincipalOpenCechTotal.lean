/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Alternating total Čech complexes on finite principal covers

Source: Stacks Project, Cohomology, Sections 20.25 and 20.40, and Tag 08D2
(blueprint: def-sc-principal-open-alternating-total).
Nonempty subsets index the alternating rows; the empty cover gives the zero complex.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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
  constructor
  intro F G g h
  rfl

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
  classical
  unfold principalCechIntersection
  by_cases hj : j ∈ J
  · rw [← Finset.mul_prod_erase J f hj]
    exact PrimeSpectrum.basicOpen_mul_le_right _ _
  · simp [Finset.erase_eq_of_notMem hj]

/-- Each singleton principal open is contained in the union of the principal opens.
Source: Stacks, Tag 08D2 (blueprint: def-sc-principal-open-alternating-total).
Proof: a singleton product is f_j, and each D(f_j) is contained in their supremum. -/
theorem principalCechIntersection_singleton_le (j : Fin r) :
    principalCechIntersection r f {j} ≤ ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i) := by
  simpa [principalCechIntersection] using
    (le_iSup (fun i : Fin r ↦ PrimeSpectrum.basicOpen (f i)) j)

/-- Deleting an index gives the same vertical degree in the incoming horizontal row.
Source: Stacks, Tag 08D1 (blueprint: def-sc-principal-open-alternating-total).
Proof: card(J.erase j) = card(J)-1 when j belongs to J; subtract this identity in ℤ. -/
theorem principalCech_erase_degree (J : Finset (Fin r)) (j : Fin r) (hj : j ∈ J) (n : ℤ) :
    n + 1 - ((J.erase j).card : ℤ) = (n + 1) + 1 - (J.card : ℤ) := by
  have h := Finset.card_erase_add_one hj
  omega

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
  classical
  refine ⟨ModuleCat.ofHom
    { toFun := principalCechDifferentialValue r f F n
      map_add' := ?_
      map_smul' := ?_ }, fun _ ↦ rfl⟩
  · intro s t
    funext J
    simp only [principalCechDifferentialValue, Pi.add_apply, id_eq]
    simp only [map_add, smul_add]
    rw [add_add_add_comm, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    split <;> simp only [add_zero]
  · intro a s
    funext J
    simp only [principalCechDifferentialValue, Pi.smul_apply, id_eq]
    simp only [map_smul, RingHom.id_apply, smul_add, Finset.smul_sum]
    congr 1
    · exact smul_comm _ _ _
    · apply Finset.sum_congr rfl
      intro j _
      split
      · rw [smul_comm]
      · exact (smul_zero a).symm

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

private theorem principalCech_transport_naturality
    {G : CochainComplex
      (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ}
    (g : F ⟶ G) (m k : ℤ) (e : m = k) (U : (Spec (.of A)).Opens) :
    (affineOpenSections A U).map (g.f m) ≫
        (affineOpenSections A U).map (eqToHom (congrArg G.X e)) =
      (affineOpenSections A U).map (eqToHom (congrArg F.X e)) ≫
        (affineOpenSections A U).map (g.f k) := by
  subst k
  simp

set_option linter.unusedVariables false in
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
  classical
  let φ (F G : CochainComplex
      (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
      (g : F ⟶ G) (n : ℤ) :
      principalCechTerms r f F n ⟶ principalCechTerms r f G n :=
    ModuleCat.ofHom
      { toFun := fun s J ↦
          (affineOpenSections A (principalCechIntersection r f J.val)).map
            (g.f (n + 1 - (J.val.card : ℤ))) (s J)
        map_add' := fun s t ↦ by
          funext J
          exact map_add _ _ _
        map_smul' := fun a s ↦ by
          funext J
          exact ((affineOpenSections A (principalCechIntersection r f J.val)).map
            (g.f (n + 1 - (J.val.card : ℤ)))).hom.map_smul a (s J) }
  have hcomm (F G : CochainComplex
      (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
      (g : F ⟶ G) (n : ℤ) :
      φ F G g n ≫ (principalCechTotal r f G).d n (n + 1) =
        (principalCechTotal r f F).d n (n + 1) ≫ φ F G g (n + 1) := by
    ext s
    simp only [principalCechTotal, CochainComplex.of_d, ModuleCat.comp_apply]
    change (principalCechDifferential_exists r f G n).choose (φ F G g n s) =
      φ F G g (n + 1) ((principalCechDifferential_exists r f F n).choose s)
    rw [(principalCechDifferential_exists r f G n).choose_spec,
      (principalCechDifferential_exists r f F n).choose_spec]
    dsimp only [φ]
    funext J
    let τ := (affineOpenSections A (principalCechIntersection r f J.val)).map
      (g.f ((n + 1) + 1 - (J.val.card : ℤ)))
    change _ = τ _
    simp only [principalCechDifferentialValue, id_eq]
    rw [τ.hom.map_add, τ.hom.map_smul, map_sum τ.hom]
    apply congrArg₂ (· + ·)
    · apply congrArg (_ • ·)
      change ((affineOpenSections A (principalCechIntersection r f J.val)).map
        (g.f (n + 1 - (J.val.card : ℤ))) ≫
        (affineOpenSections A (principalCechIntersection r f J.val)).map
        (G.d (n + 1 - (J.val.card : ℤ)) ((n + 1) + 1 - (J.val.card : ℤ)))) (s J) =
        ((affineOpenSections A (principalCechIntersection r f J.val)).map
        (F.d (n + 1 - (J.val.card : ℤ)) ((n + 1) + 1 - (J.val.card : ℤ))) ≫
        τ) (s J)
      dsimp only [τ]
      rw [← Functor.map_comp, ← Functor.map_comp, g.comm]
    · apply Finset.sum_congr rfl
      intro j _
      split
      next h =>
        rw [τ.hom.map_smul]
        apply congrArg (_ • ·)
        have hres := (modulesSpecToSheaf.map (g.f
          ((n + 1) + 1 - (J.val.card : ℤ)))).hom.naturality
            (homOfLE (principalCechIntersection_erase_le r f J.val j.val)).op
        have hcast := principalCech_transport_naturality F g
          (n + 1 - ((J.val.erase j.val).card : ℤ))
          ((n + 1) + 1 - (J.val.card : ℤ))
          (principalCech_erase_degree r J.val j.val j.property n)
          (principalCechIntersection r f (J.val.erase j.val))
        have hcast' := ConcreteCategory.congr_hom hcast (s ⟨J.val.erase j.val, h⟩)
        have hres' := ConcreteCategory.congr_hom hres
          ((affineOpenSections A (principalCechIntersection r f (J.val.erase j.val))).map
            (eqToHom (congrArg F.X
              (principalCech_erase_degree r J.val j.val j.property n)))
            (s ⟨J.val.erase j.val, h⟩))
        simp only [ModuleCat.comp_apply] at hcast' hres'
        exact (congrArg
          ((modulesSpecToSheaf.obj (G.X ((n + 1) + 1 - (J.val.card : ℤ)))).obj.map
            (homOfLE (principalCechIntersection_erase_le r f J.val j.val)).op)
          hcast').trans hres'.symm
      next h => exact τ.hom.map_zero.symm
  let C : CochainComplex
      (SheafOfModules.{uC} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ ⥤
      CochainComplex (ModuleCat.{uC} A) ℤ :=
    { obj := principalCechTotal r f
      map := fun g ↦ CochainComplex.ofHom (φ _ _ g) (hcomm _ _ g)
      map_id := fun F ↦ by
        ext n s
        dsimp only [φ]
        funext J
        simp
        rfl
      map_comp := fun g h ↦ by
        ext n s
        dsimp only [φ]
        funext J
        simp
        rfl }
  refine ⟨C, ?_, (fun _ ↦ rfl), ?_⟩
  · constructor
    intro F G g h
    ext n s
    dsimp only [C, φ]
    funext J
    simp
    rfl
  · intro F G g n s J hF hG
    have hF' : hF = (rfl : C.obj F = principalCechTotal r f F) := Subsingleton.elim _ _
    have hG' : hG = (rfl : C.obj G = principalCechTotal r f G) := Subsingleton.elim _ _
    subst hF'
    subst hG'
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl


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
  simp

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
