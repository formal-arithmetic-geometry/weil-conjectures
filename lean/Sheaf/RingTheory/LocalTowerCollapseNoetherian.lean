/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.RingHom.EssFiniteType
import WeilConjectures.RingTheory.TensorLocalizationTowerTransition
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Noetherian collapse on a supplied local ring tower diagram

Source: Stacks Project, Algebra, Tags 00R7, 07DS, 00FN, and 00FP(3)
(blueprint: lem-trf-local-tower-collapse-noetherian).

The diagrams and cocones below are supplied, rather than replaced by approximating ones.
`RingHom.IsTensorLocalizationSquare` spells out the repeated canonical-map hypothesis
and conclusion using the pure-tensor formula and the usual localization predicate.
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RingHom

/-- The map from the tensor product associated to a ring square is a localization.
The pure-tensor formula uniquely specifies the comparison map: it is not an arbitrary
map with the same source and target. `Submonoid.IsLocalizationMap` says that denominators
map to units, every target element is a fraction, and equality is killed by a denominator.

Source: Stacks Project, Algebra, Tag 00R7, the two adjacent tensor-localization comparisons
and their composite (blueprint: lem-trf-local-tower-collapse-noetherian). -/
def IsTensorLocalizationSquare
    {R : Type u} {S : Type v} {R' : Type w} {S' : Type t}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (r : R →+* R') (s : S →+* S') (f' : R' →+* S') : Prop :=
  letI := f.toAlgebra
  letI := r.toAlgebra
  ∃ φ : S ⊗[R] R' →+* S',
    (∀ (x : S) (y : R'), φ (x ⊗ₜ[R] y) = s x * f' y) ∧
    ∃ W : Submonoid (S ⊗[R] R'), W.IsLocalizationMap φ

private theorem isTensorLocalizationSquare_comp
    {A B C A' B' C' : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [CommRing A'] [CommRing B'] [CommRing C']
    (f : A →+* B) (g : B →+* C) (f' : A' →+* B') (g' : B' →+* C')
    (r : A →+* A') (s : B →+* B') (t : C →+* C')
    (hB : IsTensorLocalizationSquare f r s f')
    (hC : IsTensorLocalizationSquare g s t g') :
    IsTensorLocalizationSquare (g.comp f) r t (g'.comp f') := by
  let := f.toAlgebra
  let := g.toAlgebra
  let := (g.comp f).toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let := f'.toAlgebra
  let := g'.toAlgebra
  let := (g'.comp f').toAlgebra
  have : IsScalarTower A' B' C' := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have hB' :
      letI := r.toAlgebra
      ∃ φ : B ⊗[A] A' →+* B',
        (∀ b a, φ (b ⊗ₜ[A] a) = s b * algebraMap A' B' a) ∧
        (letI := φ.toAlgebra; ∃ W : Submonoid (B ⊗[A] A'), IsLocalization W B') := by
    obtain ⟨φ, hφ, W, hW⟩ := hB
    refine ⟨φ, hφ, ?_⟩
    let := φ.toAlgebra
    exact ⟨W, ⟨hW⟩⟩
  have hC' :
      letI := s.toAlgebra
      ∃ φ : C ⊗[B] B' →+* C',
        (∀ c b, φ (c ⊗ₜ[B] b) = t c * algebraMap B' C' b) ∧
        (letI := φ.toAlgebra; ∃ W : Submonoid (C ⊗[B] B'), IsLocalization W C') := by
    obtain ⟨φ, hφ, W, hW⟩ := hC
    refine ⟨φ, hφ, ?_⟩
    let := φ.toAlgebra
    exact ⟨W, ⟨hW⟩⟩
  obtain ⟨φ, W, hφ, hW⟩ :=
    Module.tensorLocalization_tower_transition A B C A' B' C' r s t hB' hC'
  exact ⟨φ, hφ, W, hW.toIsLocalizationMap⟩

end RingHom

namespace Module

set_option linter.unusedVariables false in
/-- Collapse two adjacent tensor-localization comparisons on the original supplied diagrams.
All stage rings are Noetherian, the composite stage maps are essentially of finite type
and localizations of finitely presented algebras, and the composite comparison maps are
localizations both at transitions and at the supplied colimit. The final four clauses are
the elementwise colimit descriptions for the supplied base and top cocones.

Source: Stacks Project, Algebra, Tags 00R7 (approximation paragraphs), 07DS, 00FN,
00FP(3), 00D6, and 00D7 (blueprint: lem-trf-local-tower-collapse-noetherian).

Proof, following the six steps of the node:
1. Every ideal of the integers is principal: for a nonzero ideal choose its least positive
   element and use Euclidean division. Hence the integers are Noetherian.
2. For each stage, express its base as a localization of a finite type integer algebra.
   Apply `lem-weil-pbc-finite-type-algebra-noetherian` and
   `lem-weil-pbc-localization-noetherian`. Repeat over that base for the middle ring and
   then over the middle ring for the top ring. These are the supplied rings throughout.
3. Apply `lem-weil-pbc-essentially-finite-type-composition` to the two stage maps.
   The definition gives a finite type algebra whose localization is the top ring.
   Its base is Noetherian by step 2, so
   `lem-weil-pbc-finite-type-noetherian-finite-presentation` makes this algebra finitely
   presented. The same localization gives the required factorization.
4. Apply `lem-weil-pbc-tensor-localization-tower-transition` to each pair of stages.
   The two given tensor localizations and the commuting squares give its hypotheses.
   Its pure-tensor formula identifies the resulting map with the composite comparison.
5. Apply the same lemma to each stage and the limit tower, using the supplied cocone
   squares and the two limit-comparison localization hypotheses. No Noetherian property
   of a limit ring is used.
6. A nonempty directed preorder is filtered. Apply
   `lem-pc-filtered-colimit-commrings-elementwise` to the supplied base and top cocones:
   it gives stage representatives and equality at a common later stage, in both cases.
   Together with steps 2 through 5 these give every asserted clause on the same diagrams.
-/
theorem local_tower_collapse_noetherian
    (I : Type u) [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (DA DB DC : I ⥤ CommRingCat.{u})
    [∀ i : I, IsLocalRing (DA.obj i)]
    [∀ i : I, IsLocalRing (DB.obj i)]
    [∀ i : I, IsLocalRing (DC.obj i)]
    (ρ : DA ⟶ DB) (σ : DB ⟶ DC)
    (LA : Cocone DA) (LB : Cocone DB) (LC : Cocone DC)
    [IsLocalRing LA.pt] [IsLocalRing LB.pt] [IsLocalRing LC.pt]
    (f : LA.pt ⟶ LB.pt) (g : LB.pt ⟶ LC.pt)
    (hρ : ∀ i : I, IsLocalHom (ρ.app i).hom)
    (hσ : ∀ i : I, IsLocalHom (σ.app i).hom)
    (hf : IsLocalHom f.hom) (hg : IsLocalHom g.hom)
    (ha : ∀ (i j : I) (h : i ≤ j), IsLocalHom (DA.map (homOfLE h)).hom)
    (hb : ∀ (i j : I) (h : i ≤ j), IsLocalHom (DB.map (homOfLE h)).hom)
    (hc : ∀ (i j : I) (h : i ≤ j), IsLocalHom (DC.map (homOfLE h)).hom)
    (hα : ∀ i : I, IsLocalHom (LA.ι.app i).hom)
    (hβ : ∀ i : I, IsLocalHom (LB.ι.app i).hom)
    (hγ : ∀ i : I, IsLocalHom (LC.ι.app i).hom)
    (hAB : ∀ i : I, ρ.app i ≫ LB.ι.app i = LA.ι.app i ≫ f)
    (hBC : ∀ i : I, σ.app i ≫ LC.ι.app i = LB.ι.app i ≫ g)
    (hLA : IsColimit LA) (hLB : IsColimit LB) (hLC : IsColimit LC)
    (hZA : ∀ i : I, Algebra.EssFiniteType ℤ (DA.obj i))
    (hABft : ∀ i : I, (ρ.app i).hom.EssFiniteType)
    (hBCft : ∀ i : I, (σ.app i).hom.EssFiniteType)
    (hABtr : ∀ (i j : I) (h : i ≤ j),
      RingHom.IsTensorLocalizationSquare (ρ.app i).hom (DA.map (homOfLE h)).hom
        (DB.map (homOfLE h)).hom (ρ.app j).hom)
    (hBCtr : ∀ (i j : I) (h : i ≤ j),
      RingHom.IsTensorLocalizationSquare (σ.app i).hom (DB.map (homOfLE h)).hom
        (DC.map (homOfLE h)).hom (σ.app j).hom)
    (hABlim : ∀ i : I,
      RingHom.IsTensorLocalizationSquare (ρ.app i).hom (LA.ι.app i).hom
        (LB.ι.app i).hom f.hom)
    (hBClim : ∀ i : I,
      RingHom.IsTensorLocalizationSquare (σ.app i).hom (LB.ι.app i).hom
        (LC.ι.app i).hom g.hom) :
    (∀ i : I, IsNoetherianRing (DA.obj i) ∧ IsNoetherianRing (DB.obj i) ∧
      IsNoetherianRing (DC.obj i)) ∧
    (∀ i : I, ((σ.app i).hom.comp (ρ.app i).hom).EssFiniteType) ∧
    (∀ i : I, ∃ (P : CommRingCat.{u}) (p : DA.obj i →+* P) (q : P →+* DC.obj i),
      p.FinitePresentation ∧ q.comp p = (σ.app i).hom.comp (ρ.app i).hom ∧
      ∃ W : Submonoid P, W.IsLocalizationMap q) ∧
    (∀ (i j : I) (h : i ≤ j),
      RingHom.IsTensorLocalizationSquare ((σ.app i).hom.comp (ρ.app i).hom)
        (DA.map (homOfLE h)).hom (DC.map (homOfLE h)).hom
        ((σ.app j).hom.comp (ρ.app j).hom)) ∧
    (∀ i : I,
      RingHom.IsTensorLocalizationSquare ((σ.app i).hom.comp (ρ.app i).hom)
        (LA.ι.app i).hom (LC.ι.app i).hom (g.hom.comp f.hom)) ∧
    (∀ x : LA.pt, ∃ (i : I) (a : DA.obj i), (LA.ι.app i).hom a = x) ∧
    (∀ (i j : I) (a : DA.obj i) (b : DA.obj j),
      (LA.ι.app i).hom a = (LA.ι.app j).hom b ↔
        ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
          (DA.map (homOfLE hik)).hom a = (DA.map (homOfLE hjk)).hom b) ∧
    (∀ x : LC.pt, ∃ (i : I) (c : DC.obj i), (LC.ι.app i).hom c = x) ∧
    (∀ (i j : I) (c : DC.obj i) (d : DC.obj j),
      (LC.ι.app i).hom c = (LC.ι.app j).hom d ↔
        ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
          (DC.map (homOfLE hik)).hom c = (DC.map (homOfLE hjk)).hom d) := by
  have hN (i : I) : IsNoetherianRing (DA.obj i) ∧ IsNoetherianRing (DB.obj i) ∧
      IsNoetherianRing (DC.obj i) := by
    have := hZA i
    have := Algebra.EssFiniteType.isNoetherianRing ℤ (DA.obj i)
    let := (ρ.app i).hom.toAlgebra
    have : Algebra.EssFiniteType (DA.obj i) (DB.obj i) := hABft i
    have := Algebra.EssFiniteType.isNoetherianRing (DA.obj i) (DB.obj i)
    let := (σ.app i).hom.toAlgebra
    have : Algebra.EssFiniteType (DB.obj i) (DC.obj i) := hBCft i
    exact ⟨inferInstance, inferInstance,
      Algebra.EssFiniteType.isNoetherianRing (DB.obj i) (DC.obj i)⟩
  have hft (i : I) : ((σ.app i).hom.comp (ρ.app i).hom).EssFiniteType :=
    (hABft i).comp (hBCft i)
  refine ⟨hN, hft, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have := (hN i).1
    let := ((σ.app i).hom.comp (ρ.app i).hom).toAlgebra
    have : Algebra.EssFiniteType (DA.obj i) (DC.obj i) := hft i
    obtain ⟨P, W, hP, hW⟩ :=
      (Algebra.essFiniteType_iff_exists_subalgebra (DA.obj i) (DC.obj i)).mp (hft i)
    have := hP
    have := hW
    refine ⟨CommRingCat.of P, algebraMap (DA.obj i) P, P.val.toRingHom, ?_, rfl, W, ?_⟩
    · exact RingHom.finitePresentation_algebraMap.mpr
        (Algebra.FinitePresentation.of_finiteType.mp hP)
    · exact hW.toIsLocalizationMap
  · intro i j h
    exact RingHom.isTensorLocalizationSquare_comp _ _ _ _ _ _ _ (hABtr i j h) (hBCtr i j h)
  · intro i
    exact RingHom.isTensorLocalizationSquare_comp _ _ _ _ _ _ _ (hABlim i) (hBClim i)
  · exact Concrete.isColimit_exists_rep DA hLA
  · intro i j a b
    constructor
    · intro h
      obtain ⟨k, hik, hjk, heq⟩ :=
        (Concrete.isColimit_rep_eq_iff_exists DA hLA a b).mp h
      exact ⟨k, leOfHom hik, leOfHom hjk, heq⟩
    · rintro ⟨k, hik, hjk, heq⟩
      exact (Concrete.isColimit_rep_eq_iff_exists DA hLA a b).mpr
        ⟨k, homOfLE hik, homOfLE hjk, heq⟩
  · exact Concrete.isColimit_exists_rep DC hLC
  · intro i j c d
    constructor
    · intro h
      obtain ⟨k, hik, hjk, heq⟩ :=
        (Concrete.isColimit_rep_eq_iff_exists DC hLC c d).mp h
      exact ⟨k, leOfHom hik, leOfHom hjk, heq⟩
    · rintro ⟨k, hik, hjk, heq⟩
      exact (Concrete.isColimit_rep_eq_iff_exists DC hLC c d).mpr
        ⟨k, homOfLE hik, homOfLE hjk, heq⟩

end Module
