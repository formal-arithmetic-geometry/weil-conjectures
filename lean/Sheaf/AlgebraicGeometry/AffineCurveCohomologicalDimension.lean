/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.ArbitraryCurveCohomologicalDimension
import Sheaf.CategoryTheory.RightDerivedSingleZeroUnit

/-!
# Cohomology of a smooth affine curve

Source: blueprint, smooth base change, unit sk-thm-vanishing;
Stacks Project, Tag 03SC (2), and Tag 03P5 for constant sections
(blueprint: sbc-thm-cohomological-dimension-of-an-affine-curve).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The canonical constant-section map to degree-zero derived étale cohomology.
Start with the unit of constant sheaf/global sections, place sections in degree zero,
and apply degree-zero homology to the unit of the total right derived global-sections
functor. The single-complex comparison identifies the source with the coefficient group.
Source: Stacks Project, Tags 03P5, 013K, 05TD
(blueprint: sbc-thm-cohomological-dimension-of-an-affine-curve). -/
noncomputable def Scheme.constantZModToDerivedCohomologyZero (C : Scheme.{u}) (d : ℕ) :
    AddCommGrpCat.of (ULift.{u + 1} (ZMod d)) ⟶
      (Etale.cohomology AddCommGrpCat.{u + 1} C 0).obj
        ((DerivedCategory.singleFunctor _ 0).obj (C.constantZMod d)) :=
  (constantSheafΓAdj C.smallEtaleTopology AddCommGrpCat.{u + 1}).unit.app
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod d))) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso AddCommGrpCat.{u + 1} 0).inv.app
      ((Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (C.constantZMod d)) ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
      (DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1})
          (ComplexShape.up ℤ) 0).inv.app (C.constantZMod d))) ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
      ((Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj
          ((CochainComplex.singleFunctor _ 0).obj (C.constantZMod d))))

/-- Higher cohomology of a smooth affine curve vanishes; on a connected curve the canonical
constant-section map identifies degree-zero cohomology with the coefficient group.
Source: Stacks Project, Tag 03SC (2), Tag 03P5, and blueprint sk-thm-vanishing
(blueprint: sbc-thm-cohomological-dimension-of-an-affine-curve).

Proof plan:
1. The constant sheaf of Z/d is torsion: each local representative is killed by d.
2. For connected dimension-one curves, apply thm-sc-affine-cohomology with n = d.
3. In all nonempty cases, apply thm-sc-affine-torsion-cd: the separably closed field has
   torsion cohomological dimension zero, and IsCurve bounds the dimension by one.
4. On an empty scheme the empty-cover sheaf condition makes all section groups zero,
   so every term of derived global sections, and hence its cohomology, is zero.
5. The Grothendieck abelian sheaf category has enough injectives. A nonnegative injective
   resolution is K-injective. Left exactness of global sections identifies H0 with sections
   via the canonical derived-functor unit (the degree-zero injective-resolution lemma).
6. On a connected (hence nonempty) scheme, constant sections give all sections uniquely,
   by lem-weil-pbc-constant-sheaf-sections-connected. Compose with Step 5.
This last argument also applies to connected zero-dimensional curves. -/
theorem affineCurve_constantZMod_cohomology
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsCurve f] [Smooth f] [IsAffine C]
    (d : ℕ) (hd : 1 ≤ d) (hchar : IsUnit (d : k)) :
    (∀ (q : ℕ), 1 < q →
      Subsingleton ((Etale.cohomology AddCommGrpCat.{u + 1} C q).obj
        ((DerivedCategory.singleFunctor _ 0).obj (C.constantZMod d)))) ∧
    (ConnectedSpace C → IsIso (C.constantZModToDerivedCohomologyZero d)) := by
  have _ := hchar
  constructor
  · obtain ⟨_, hC⟩ | ⟨hC, _⟩ :=
      torsionEtaleCohomologicalDimensionLE_of_dim_le_one f
        (IsCurve.krullDim_le_one (f := f))
    · exact hC _ (C.isTorsion_constantZMod (Nat.ne_of_gt hd))
    · exact (hC inferInstance).elim
  · intro hC
    let A := AddCommGrpCat.of (ULift.{u + 1} (ZMod d))
    let F := C.constantZMod d
    let Γ := Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}
    let T : C.Etale := Scheme.Etale.mk (𝟙 C)
    let hT : Limits.IsTerminal T := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale _
    have hsec := C.bijective_toSheafify_app_terminal A
    have hunit : IsIso ((constantSheafΓAdj C.smallEtaleTopology
        AddCommGrpCat.{u + 1}).unit.app A) := by
      have hc : Function.Bijective ((constantSheafAdj C.smallEtaleTopology
          AddCommGrpCat.{u + 1} hT).unit.app A).hom := by
        change Function.Bijective ((toSheafify C.smallEtaleTopology
          ((Functor.const C.Etaleᵒᵖ).obj A)).app (Opposite.op T))
        exact hsec
      have hc' : IsIso ((constantSheafAdj C.smallEtaleTopology
          AddCommGrpCat.{u + 1} hT).unit.app A) :=
        (ConcreteCategory.isIso_iff_bijective _).2 hc
      have hn := Adjunction.unit_rightAdjointUniq_hom_app
        (constantSheafΓAdj C.smallEtaleTopology AddCommGrpCat.{u + 1})
        (constantSheafAdj C.smallEtaleTopology AddCommGrpCat.{u + 1} hT) A
      have : IsIso ((Sheaf.ΓNatIsoSheafSections C.smallEtaleTopology
          AddCommGrpCat.{u + 1} hT).hom.app F) := inferInstance
      rw [← hn] at hc'
      let : IsIso ((constantSheafΓAdj C.smallEtaleTopology
          AddCommGrpCat.{u + 1}).unit.app A ≫
            (Sheaf.ΓNatIsoSheafSections C.smallEtaleTopology
              AddCommGrpCat.{u + 1} hT).hom.app F) := hc'
      exact IsIso.of_isIso_comp_right _ ((Sheaf.ΓNatIsoSheafSections
        C.smallEtaleTopology AddCommGrpCat.{u + 1} hT).hom.app F)
    let e := Γ.homologyRightDerivedFunctorObjSingleFunctorIso F 0 ≪≫
      Γ.rightDerivedZeroIsoSelf.app F
    have hz : IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
        (Γ.rightDerivedSingleUnit F)) := by
      have he := Γ.rightDerivedSingleUnit_zero F
      have : IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
          (Γ.rightDerivedSingleUnit F) ≫ e.hom) := by
        rw [he]
        infer_instance
      exact IsIso.of_isIso_comp_right _ e.hom
    change IsIso (_ ≫ _ ≫ _ ≫ _)
    rw [← Functor.map_comp]
    change IsIso ((constantSheafΓAdj C.smallEtaleTopology
      AddCommGrpCat.{u + 1}).unit.app A ≫ _ ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
          (Γ.rightDerivedSingleUnit F))
    infer_instance

end AlgebraicGeometry
