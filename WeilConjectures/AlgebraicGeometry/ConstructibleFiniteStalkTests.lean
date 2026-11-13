/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.IrreducibleLisseStrata
import WeilConjectures.AlgebraicGeometry.LisseGenericKernel
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Finitely many stalk tests for a constructible source

## References

* Stacks Project, Tag 09Z6
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Local constancy is invariant under isomorphism: use the same trivializing cover
and transport constancy after restriction.
Source: Mathlib `Sheaf.isConstant_congr`. -/
private theorem locallyConstant_of_iso {T : Scheme.{u}}
    {F G : Sheaf T.smallEtaleTopology (Type (u + 1))} (e : F ≅ G)
    (hF : IsLocallyConstantEtaleSheafOfSets F) :
    IsLocallyConstantEtaleSheafOfSets G := by
  obtain ⟨𝒰, h𝒰⟩ := hF
  refine ⟨𝒰, fun i => ?_⟩
  have := h𝒰 i
  exact Sheaf.isConstant_congr _
    ((T.smallEtaleTopology.overPullback (Type (u + 1))
      (𝒰.etalePrecoverageToEtale i)).mapIso e)

/-- The geometric point at the image of an immersion lifts to the specified source point.
Source: `Scheme.exists_comp_eq_of_mem_range`, using surjectivity on stalks;
injectivity of the immersion identifies the image of the lift. -/
private theorem geometricPoint_lift {T X : Scheme.{u}} (f : T ⟶ X) [IsImmersion f]
    (y : T) : ∃ s : Spec (.of (AlgebraicClosure (X.residueField (f y)))) ⟶ T,
      s ≫ f = X.algClosurePoint (f y) ∧ s default = y := by
  obtain ⟨s, hs⟩ := exists_comp_eq_of_mem_range f (X.algClosurePoint (f y))
    (by simp)
  refine ⟨s, hs, ?_⟩
  apply f.isEmbedding.injective
  have h := congrArg (fun g => g default) hs
  simpa using h

/-- Finitely many finite geometric stalks test monomorphisms out of a constructible sheaf.
The chosen points depend only on the source sheaf, not on the target or the morphism.
(Stacks, Tag 09Z6) -/
theorem exists_finite_stalk_tests_of_constructible
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F)) :
    ∃ P : Finset X,
      (∀ x : P, Finite
        (((pointSmallEtale (X.algClosurePoint x.val)).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj F)) ∧
      (∀ (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (φ : F ⟶ G),
        (∀ x : P, Function.Injective
          (((pointSmallEtale (X.algClosurePoint x.val)).sheafFiber
            (A := AddCommGrpCat.{u + 1})).map φ)) → Mono φ) := by
  classical
  -- Stalks here use diagrams of size u, while the coefficients live in u + 1.
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    Limits.preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{u + 1})
  have : CategoryTheory.AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    CategoryTheory.AB5OfSize_of_univLE.{u, u, u + 1, u + 1} AddCommGrpCat.{u + 1}
  obtain ⟨S, hS⟩ := exists_irreducible_lisse_stratification X F hF
  have hirr (i : Fin S.n) : IrreducibleSpace (S.domain i) := (hS i).1
  let η : ∀ i : Fin S.n, S.domain i := fun i => genericPoint (S.domain i)
  let x : Fin S.n → X := fun i => S.immersion i (η i)
  let P := Finset.univ.image x
  have hlift (i : Fin S.n) := geometricPoint_lift (S.immersion i) (η i)
  choose s hs hsη using hlift
  let ea (i : Fin S.n) :=
    (etaleInverseImageAlgebraicStructures (S.domain i) X (S.immersion i)).2.choose
  have hlc (i : Fin S.n) : IsLocallyConstantEtaleSheafOfSets
      ((sheafCompose (S.domain i).smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} (S.immersion i)).obj F)) :=
    locallyConstant_of_iso ((ea i).app F).symm (hS i).2.1
  refine ⟨P, ?_, ?_⟩
  · intro z
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp z.property
    have hfin := ((ConcreteCategory.isFinitelyGenerated_iff_finite _).mp
      ((hS i).2.2.isFinitelyGenerated_sheafFiber _ (s i)))
    let e₁ := (pointSmallEtale (s i)).sheafFiber.mapIso ((ea i).app F)
    let e₂ := ((pointSmallEtale (s i)).sheafFiberCompIso
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).app
        ((Etale.upperStar AddCommGrpCat.{u + 1} (S.immersion i)).obj F)
    let e₃ := (Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1}
      (S.immersion i) (s i)).app F
    have hfin' : Finite (((pointSmallEtale (s i)).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} (S.immersion i)).obj F)) := by
      exact @Finite.of_equiv _ _ hfin ((e₁.symm ≪≫ e₂).toEquiv)
    have hfin'' : Finite (((pointSmallEtale (s i ≫ S.immersion i)).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj F) :=
      @Finite.of_equiv _ _ hfin' e₃.addCommGroupIsoToAddEquiv.toEquiv
    rw [hs i] at hfin''
    change x i = z.val at hi
    change Finite (((pointSmallEtale (X.algClosurePoint (x i))).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj F) at hfin''
    rw [hi] at hfin''
    exact hfin''
  · intro G φ hφ
    have hmono (i : Fin S.n) :
        Mono ((Etale.upperStar AddCommGrpCat.{u + 1} (S.immersion i)).map φ) := by
      have htest : Mono (((pointSmallEtale (X.algClosurePoint (x i))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).map φ) :=
        (AddCommGrpCat.mono_iff_injective _).2
          (hφ ⟨x i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
      let e := Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1}
        (S.immersion i) (s i)
      have htest' : Mono (((pointSmallEtale (s i ≫ S.immersion i)).sheafFiber
          (A := AddCommGrpCat.{u + 1})).map φ) := by
        rw [hs i]
        exact htest
      have hcomp : Mono (e.hom.app F ≫
          ((pointSmallEtale (s i ≫ S.immersion i)).sheafFiber.map φ)) := inferInstance
      rw [← e.hom.naturality φ] at hcomp
      have hgeneric : Mono (((pointSmallEtale (s i)).sheafFiber).map
          ((Etale.upperStar AddCommGrpCat.{u + 1} (S.immersion i)).map φ)) :=
        @mono_of_mono _ _ _ _ _ _ (e.hom.app G) hcomp
      exact mono_of_mono_generic_stalk (S.domain i)
        (IrreducibleSpace.isIrreducible_univ _) inferInstance (η i)
        (genericPoint_spec _) _ (s i) (hsη i) _ _ (hlc i) _ hgeneric
    constructor
    intro H a b hab
    apply sheafHom_ext_of_sheafFiber_map_algClosurePoint
    intro z
    have hz : z ∈ ⋃ i, S.stratum i := by rw [S.iUnion_stratum_eq_univ]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    rw [← S.range_immersion i] at hi
    obtain ⟨y, hy⟩ := hi
    obtain ⟨t, ht⟩ := exists_comp_eq_of_mem_range (S.immersion i)
      (X.algClosurePoint z) (by simpa using (show z ∈ Set.range (S.immersion i)
        from ⟨y, hy⟩))
    let e := Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1}
      (S.immersion i) t
    have hm : Mono ((Etale.upperStar AddCommGrpCat.{u + 1} (S.immersion i)).map φ) :=
      hmono i
    have hm' : Mono (((pointSmallEtale t).sheafFiber).map
        ((Etale.upperStar AddCommGrpCat.{u + 1} (S.immersion i)).map φ)) := inferInstance
    have : Mono ((Etale.upperStar AddCommGrpCat.{u + 1} (S.immersion i) ⋙
        (pointSmallEtale t).sheafFiber).map φ) := hm'
    have hcomp : Mono (e.inv.app F ≫ ((Etale.upperStar AddCommGrpCat.{u + 1}
        (S.immersion i) ⋙ (pointSmallEtale t).sheafFiber).map φ)) := inferInstance
    rw [← e.inv.naturality φ] at hcomp
    have hmz : Mono (((pointSmallEtale (t ≫ S.immersion i)).sheafFiber
        (A := AddCommGrpCat.{u + 1})).map φ) := @mono_of_mono _ _ _ _ _ _ (e.inv.app G) hcomp
    rw [ht] at hmz
    have : Mono (((pointSmallEtale (X.algClosurePoint z)).sheafFiber
        (A := AddCommGrpCat.{u + 1})).map φ) := hmz
    apply (cancel_mono (((pointSmallEtale (X.algClosurePoint z)).sheafFiber).map φ)).1
    simp only [← Functor.map_comp, hab]

end AlgebraicGeometry.Scheme
