/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P5
-/
module

public import Sheaf.Algebra.Homology.LocalRHomCocycleComparison
import Sheaf.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import Mathlib.Algebra.Category.Grp.EpiMono

/-!
# Naturality of the local Hom-complex comparison in the homotopy category

Source: Stacks Project, Tag 0A8Y, Equation (21.34.0.1).
(blueprint: lem-per-local-rhom-canonical-naturality)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v r w
open CategoryTheory Opposite
namespace CategoryTheory

/-- The component-characterized local derived comparison is natural in both complexes.
Source: Stacks Project, Tags 0A8Y and 0A94.
(blueprint: lem-per-local-rhom-canonical-naturality).

Proof: lift a homology class to a cocycle. The Hom-complex projection formula
identifies the image family with precomposition and postcomposition of its local
chain map. Apply the defining localization formula to both cycle classes.
Localization preserves composition, which gives the result. -/
theorem localRHom_canonical_naturality
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J CommRingCat.{max u v r}) (U : C)
    [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{max u v r}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    [∀ V : C, HasDerivedCategory.{w} (SheafOfModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R).over V))]
    {I' I L' L : CochainComplex
      (SheafOfModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)) ℤ}
    (s : I' ⟶ I) (t : L' ⟶ L) [I'.IsKInjective] [I.IsKInjective] (n : ℤ) :
    let E := (LocalRHom.Cocycle.evaluation.{u, v, r} J R U).mapHomologicalComplex (.up ℤ)
    let res := LocalRHom.complexRes.{u, v, r} J R U
    let f := E.map (((homComplexFunctor (R := R)).map t.op).app I' ≫
      ((homComplexFunctor (R := R)).obj (op L')).map s)
    ∀ x, LocalRHom.Cocycle.cohomologyEquiv.{u, v, r, w} J R L' I U n
      (HomologicalComplex.homologyMap f n x) =
        DerivedCategory.Q.map (res.map t) ≫
          LocalRHom.Cocycle.cohomologyEquiv.{u, v, r, w} J R L I' U n x ≫
            DerivedCategory.Q.map ((shiftFunctor _ n).map (res.map s)) := by
  classical
  let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R
  let E := (LocalRHom.Cocycle.evaluation.{u, v, r} J R U).mapHomologicalComplex (.up ℤ)
  let res := LocalRHom.complexRes.{u, v, r} J R U
  let Q := DerivedCategory.Q.{w} (C := SheafOfModules.{max u v r} (R₀.over U))
  let f := E.map (((homComplexFunctor (R := R)).map t.op).app I' ≫
    ((homComplexFunctor (R := R)).obj (op L')).map s)
  let S := E.obj (homComplex (R := R) L I')
  let T := E.obj (homComplex (R := R) L' I)
  let π := Classical.choose
    (homComplex_projections_exists.{u, v, max u v r, max u v r} (J := J) (R := R))
  have hmap := (Classical.choose_spec
    (homComplex_projections_exists.{u, v, max u v r, max u v r} (J := J) (R := R))).2.2
  let e := LocalRHom.Cocycle.cyclesEquiv.{u, v, r, w} J R L I' U n
  let e' := LocalRHom.Cocycle.cyclesEquiv.{u, v, r, w} J R L' I U n
  let a := LocalRHom.Cocycle.cohomologyEquiv.{u, v, r, w} J R L I' U n
  let b := LocalRHom.Cocycle.cohomologyEquiv.{u, v, r, w} J R L' I U n
  have he' := LocalRHom.Cocycle.cyclesEquiv_component.{u, v, r, w} J R L' I U n
  change ∀ x, b (HomologicalComplex.homologyMap f n x) =
    Q.map (res.map t) ≫ a x ≫ Q.map ((shiftFunctor _ n).map (res.map s))
  intro x
  obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (S.homologyπ n)).mp inferInstance x
  have hz : e' (HomologicalComplex.cyclesMap f n z) =
      ((e z).precomp (res.map t)).postcomp (res.map s) := by
    apply CochainComplex.HomComplex.Cocycle.ext
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    apply SheafOfModules.hom_ext
    ext W y
    change (((e' (HomologicalComplex.cyclesMap f n z)).val.v p q hpq).val.app W).hom y = _
    have hez := he' (HomologicalComplex.cyclesMap f n z) p q hpq W
    change ((e' (HomologicalComplex.cyclesMap f n z)).val.v p q hpq).val.app W = _
      at hez
    rw [hez]
    have hci := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i f n) z
    change T.iCycles n (HomologicalComplex.cyclesMap f n z) =
      f.f n (S.iCycles n z) at hci
    change ((((π L' I n p q hpq).val.app (op U))
      (T.iCycles n (HomologicalComplex.cyclesMap f n z))).app W).hom y = _
    rw [hci]
    have hm0 : (((homComplexFunctor (R := R)).map t.op).app I' ≫
        ((homComplexFunctor (R := R)).obj (op L')).map s).f n ≫ π L' I n p q hpq =
        π L I' n p q hpq ≫ SheafOfModules.homObjMap (R := R) (t.f p) (s.f q) :=
      hmap L L' I' I t s n p q hpq
    have hm := congrArg
      (fun k : (homComplex (R := R) L I').X n ⟶
          SheafOfModules.homObj (R := R) (L'.X p) (I.X q) ↦
        (k.val.app (op U)) (S.iCycles n z))
      hm0
    change ((π L' I n p q hpq).val.app (op U)) (f.f n (S.iCycles n z)) =
      (SheafOfModules.homObjMap (R := R) (t.f p) (s.f q)).val.app (op U)
        (((π L I' n p q hpq).val.app (op U)) (S.iCycles n z)) at hm
    rw [hm]
    simp only [CochainComplex.HomComplex.Cocycle.postcomp_coe,
      CochainComplex.HomComplex.Cocycle.precomp_coe,
      CochainComplex.HomComplex.Cochain.comp_zero_cochain_v,
      CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
      CochainComplex.HomComplex.Cochain.ofHom_v]
    have hev := LocalRHom.Cocycle.cyclesEquiv_component.{u, v, r, w} J R L I' U n z p q hpq W
    have hc := congrArg (fun k ↦ k.hom (((res.map t).f p).val.app W y)) hev
    have hc' := congrArg (((res.map s).f q).val.app W) hc
    rw [homObjMap_section_component.{u, v, r}]
    exact hc'.symm
  change b (HomologicalComplex.homologyMap f n (S.homologyπ n z)) =
    Q.map (res.map t) ≫ a (S.homologyπ n z) ≫
      Q.map ((shiftFunctor _ n).map (res.map s))
  have hn := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality f n) z
  change HomologicalComplex.homologyMap f n (S.homologyπ n z) =
    T.homologyπ n (HomologicalComplex.cyclesMap f n z) at hn
  calc
    b (HomologicalComplex.homologyMap f n (S.homologyπ n z)) =
        b (T.homologyπ n (HomologicalComplex.cyclesMap f n z)) := congrArg b hn
    _ = Q.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm
        (e' (HomologicalComplex.cyclesMap f n z))) :=
      LocalRHom.Cocycle.cohomologyEquiv_π.{u, v, r, w} J R L' I U n _
    _ = Q.map (res.map t) ≫
        Q.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm (e z)) ≫
          Q.map ((shiftFunctor _ n).map (res.map s)) := by
      rw [hz, CochainComplex.HomComplex.Cocycle.equivHomShift_symm_postcomp,
        CochainComplex.HomComplex.Cocycle.equivHomShift_symm_precomp,
        Q.map_comp, Q.map_comp, Category.assoc]
    _ = _ := congrArg (fun k ↦ Q.map (res.map t) ≫ k ≫
      Q.map ((shiftFunctor _ n).map (res.map s)))
        (LocalRHom.Cocycle.cohomologyEquiv_π.{u, v, r, w} J R L I' U n z).symm

end CategoryTheory
