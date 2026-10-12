/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.KInjectiveBridge
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Termwise products of K-injective complexes

Source: Stacks Project, Derived Categories, Lemma 13.31.5, Tag 0BK6
(blueprint: lem-pc-ringed-space-product-kinjective).
-/

@[expose] public section

universe w v u t

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

private noncomputable def productHomotopy
    {C : Type u} [Category.{v} C] [Abelian C] {T : Type t}
    (I : T → CochainComplex C ℤ)
    [∀ n : ℤ, HasLimit (Discrete.functor I ⋙ HomologicalComplex.eval C (.up ℤ) n)]
    {K : CochainComplex C ℤ}
    {f g : K ⟶ (HomologicalComplex.coneOfHasLimitEval (Discrete.functor I)).pt}
    (H : ∀ j, Homotopy
      (f ≫ (HomologicalComplex.coneOfHasLimitEval (Discrete.functor I)).π.app ⟨j⟩)
      (g ≫ (HomologicalComplex.coneOfHasLimitEval (Discrete.functor I)).π.app ⟨j⟩)) :
    Homotopy f g := by
  let P := HomologicalComplex.coneOfHasLimitEval (Discrete.functor I)
  let hPq (q : ℤ) : IsLimit ((HomologicalComplex.eval C (.up ℤ) q).mapCone P) :=
    limit.isLimit _
  let h : ∀ p q, K.X p ⟶ P.pt.X q := fun p q ↦
    (hPq q).lift
      { pt := K.X p
        π := Discrete.natTrans (fun j ↦ (H j.as).hom p q) }
  have key (p q : ℤ) (j : T) : h p q ≫ (P.π.app ⟨j⟩).f q = (H j).hom p q :=
    (hPq q).fac _ ⟨j⟩
  refine { hom := h, zero := ?_, comm := ?_ }
  · intro p q hpq
    apply (hPq q).hom_ext
    intro ⟨j⟩
    change h p q ≫ (P.π.app ⟨j⟩).f q = 0 ≫ (P.π.app ⟨j⟩).f q
    rw [key, (H j).zero p q hpq, zero_comp]
  · intro p
    apply (hPq p).hom_ext
    intro ⟨j⟩
    change f.f p ≫ (P.π.app ⟨j⟩).f p =
      (dNext p h + prevD p h + g.f p) ≫ (P.π.app ⟨j⟩).f p
    rw [Preadditive.add_comp, Preadditive.add_comp,
      ← dNext_comp_right, ← prevD_comp_right]
    simpa only [key, HomologicalComplex.comp_f] using (H j).comm p

private noncomputable def mapProduct
    {A : Type u} [Category.{v} A] {B : Type u} [Category.{w} B]
    {T : Type t} (F : A ⥤ B) [F.EssSurj] (K : Discrete T ⥤ A) (P : Cone K) (hP : IsLimit P)
    (hpt : ∀ X : A, Function.Bijective (F.map : (X ⟶ P.pt) → _))
    (hK : ∀ (X : A) (j : Discrete T), Function.Bijective (F.map : (X ⟶ K.obj j) → _)) :
    IsLimit (F.mapCone P) := by
  classical
  let pre (s : Cone (K ⋙ F)) : Cone K :=
    { pt := F.objPreimage s.pt
      π := Discrete.natTrans fun j ↦
        (Equiv.ofBijective _ (hK (F.objPreimage s.pt) j)).symm
          ((F.objObjPreimageIso s.pt).hom ≫ s.π.app j) }
  have key (s : Cone (K ⋙ F)) (j : Discrete T) :
      F.map ((pre s).π.app j) = (F.objObjPreimageIso s.pt).hom ≫ s.π.app j :=
    (Equiv.ofBijective _ (hK (F.objPreimage s.pt) j)).apply_symm_apply _
  refine
    { lift := fun s ↦ (F.objObjPreimageIso s.pt).inv ≫ F.map (hP.lift (pre s))
      fac := ?_
      uniq := ?_ }
  · intro s j
    dsimp only [Functor.mapCone_π_app]
    rw [Category.assoc, ← F.map_comp, hP.fac, key]
    simp
  · intro s m hm
    dsimp only [Functor.mapCone_π_app] at hm
    obtain ⟨m', hm'⟩ := (hpt (F.objPreimage s.pt)).surjective
      ((F.objObjPreimageIso s.pt).hom ≫ m)
    have eq : m' = hP.lift (pre s) := by
      apply hP.uniq (pre s) m'
      intro j
      apply (hK (F.objPreimage s.pt) j).injective
      rw [F.map_comp, hm', Category.assoc, hm j, key]
    rw [← eq, hm']
    simp

/-- The termwise product of a family of K-injective complexes is K-injective and, with the
images of its projections, is a product in the derived category.
Source: Stacks Project, Tag 0BK6, Lemma 13.31.5
(blueprint: lem-pc-ringed-space-product-kinjective).

The degreewise product assumption is expressed as existence of the limits of the discrete
family after evaluation in each integer degree. Mathlib's `coneOfHasLimitEval` constructs
exactly the termwise product complex, with its induced differentials and projections.
K-injectivity is the `IsKInjective` convention of `def-sp-kinjective-bridge`; the chosen
localization universe is that of `def-weil-abstract-derived-category`.

Proof:
1. For a map from an acyclic complex `K` into the termwise product, choose a
   null-homotopy of each composite with a projection, using K-injectivity of the factors.
   Assemble the homotopy components using the degreewise limits. The homotopy identities
   hold after every projection, hence hold by limit extensionality. Thus the product is
   K-injective; no exactness assumption on products in `C` is needed.
2. Lift each leg of a cone in the homotopy category to a chain map and use the limit of
   complexes to obtain its lift. Equality of projections gives component homotopies;
   assembling these as in Step 1 proves uniqueness in the homotopy category.
3. Mathlib's K-injective Hom comparison (`lem-weil-pbc-kinjective-hom-derived`) gives
   bijections on morphisms into the product and each factor. Essential surjectivity of
   `Qh` lets us pull back any cone in the derived category to the homotopy category.
   The Hom bijections transfer its unique lift. Finally `quotientCompQhIso` identifies
   the resulting limiting cone with `DerivedCategory.Q.mapCone P`, preserving the
   images of the original projections. -/
theorem termwise_product_isKInjective_and_isLimit
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {T : Type t} (I : T → CochainComplex C ℤ) [∀ s : T, (I s).IsKInjective]
    [∀ n : ℤ, HasLimit (Discrete.functor I ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) n)] :
    let P := HomologicalComplex.coneOfHasLimitEval (Discrete.functor I)
    IsKInjective P.pt ∧ Nonempty (IsLimit (DerivedCategory.Q.mapCone P)) := by
  classical
  -- Assemble null-homotopies directly, avoiding exactness of products in Ab.
  let P := HomologicalComplex.coneOfHasLimitEval (Discrete.functor I)
  have hPI : IsKInjective P.pt := by
    refine ⟨fun f hK ↦ ?_⟩
    exact ⟨productHomotopy I fun j ↦ by
      letI : IsKInjective ((Discrete.functor I).obj ⟨j⟩) := inferInstanceAs
        (IsKInjective (I j))
      simpa using IsKInjective.homotopyZero (f ≫ P.π.app ⟨j⟩) hK⟩
  let := hPI
  let q := HomotopyCategory.quotient C (.up ℤ)
  let hP := HomologicalComplex.isLimitConeOfHasLimitEval (Discrete.functor I)
  have hq : IsLimit (q.mapCone P) := by
    refine
      { lift := fun s ↦ q.map (hP.lift
          { pt := s.pt.as
            π := Discrete.natTrans (fun j ↦ q.preimage (s.π.app j)) })
        fac := ?_
        uniq := ?_ }
    · intro s j
      dsimp only [Functor.mapCone_π_app]
      rw [← Functor.map_comp, hP.fac]
      exact q.map_preimage _
    · intro s m hm
      obtain ⟨m', rfl⟩ := q.map_surjective (X := s.pt.as) m
      apply HomotopyCategory.eq_of_homotopy
      apply productHomotopy I
      intro j
      apply HomotopyCategory.homotopyOfEq
      rw [Functor.map_comp, hP.fac]
      exact (hm ⟨j⟩).trans (q.map_preimage (s.π.app ⟨j⟩)).symm
  have hd : IsLimit (DerivedCategory.Qh.mapCone (q.mapCone P)) := by
    exact mapProduct DerivedCategory.Qh (Discrete.functor I ⋙ q) (q.mapCone P) hq
      (fun X ↦ IsKInjective.Qh_map_bijective X P.pt)
      (fun X j ↦ IsKInjective.Qh_map_bijective X (I j.as))
  exact ⟨hPI, ⟨IsLimit.mapConeEquiv (DerivedCategory.quotientCompQhIso C) hd⟩⟩

end CochainComplex
