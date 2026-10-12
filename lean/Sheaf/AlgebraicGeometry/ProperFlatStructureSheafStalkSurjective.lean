/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
import Sheaf.AlgebraicGeometry.PerfectLocalDegreeZeroUnit
import Sheaf.AlgebraicGeometry.FlatDerivedStructureUnit
import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem surjective_of_comp_isIso {A B C : Ab.{u}} (a : A ⟶ B) (b : B ⟶ C)
    [IsIso b] (h : Function.Surjective (a ≫ b)) : Function.Surjective a := by
  intro y
  obtain ⟨x, hx⟩ := h (b y)
  refine ⟨x, (ConcreteCategory.bijective_of_isIso b).1 ?_⟩
  simpa only [ConcreteCategory.comp_apply] using hx

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Surjective part of the local proper-flat structure-sheaf criterion.
Source: Stacks Project, Tag 0E62, proof of `perfect-lemma-proper-flat-h0`, localized
at the fixed point; the rank-minimal finite free model is Tag 0BCD.
(blueprint: lem-sc-proper-flat-structure-sheaf-stalk-surjective).

Proof: Properness makes the locally finitely presented morphism quasi-compact and
quasi-separated, hence finitely presented. The structure sheaf is finitely presented
and relatively flat. Perfect direct image and base change therefore give a perfect
complex E = Rf_* O_X whose derived fibre is RΓ(X_s, O). Its negative cohomology vanishes,
and its degree-zero cohomology is κ(s) via the canonical map in the hypothesis.
Take the affine bounded finite free model of Tag 0BCD, with term ranks equal to the
fibre cohomology dimensions. It has no negative terms, and its degree-zero term is
free of rank one. The differentials after passage to κ(s) are zero: in each degree,
the cohomology dimension equals the term dimension, so both adjacent differential
ranks are zero. Thus its degree-zero term identifies with degree-zero fibre cohomology.

On this affine, projectivity of O in degree zero lets us represent the derived unit
O[0] → E by a chain map into the bounded projective model. Localize at s. Its degree-zero
component is a map between rank-one free modules whose residue is the assumed canonical
isomorphism. It is multiplication by an element outside the maximal ideal, hence a unit.
The chain-map equation d^0 u^0 = 0 forces d^0 = 0 in the local ring. There are no negative
terms, so degree-zero cohomology of the model is its degree-zero term at s.

Left exactness of direct image identifies H^0(E) with f_* O_X and the degree-zero unit
with the ordinary structure map. Under the canonical tensor identification f^* O_S ≅ O_X,
the section formula in `exists_tensorPullbackAdjunction` identifies the chosen unit,
followed by pushforward of that identification, with the ordinary structure map.
Pushforward and passage to stalks preserve this isomorphism.
For any output germ, transport it to the degree-zero free module, multiply by
the inverse unit, and transport back to obtain a preimage under the stated stalk map.
-/
theorem surjective_structureSheafMap_stalk_of_proper_flat_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (s : S)
    (hs : IsIso (f.fiberToSpecResidueField s).appTop) :
    Function.Surjective
      (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app
        (SheafOfModules.unit S.ringCatSheaf)).stalkLinearMap s) := by
  classical
  let : ∀ Y : Scheme.{u},
      HasDerivedCategory.{u + 1} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    fun Y ↦ HasDerivedCategory.standard _
  let : ∀ U : S.Opens, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) :=
    fun U ↦ HasDerivedCategory.standard _
  let : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive := by
    intro Y Z k
    let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)
    let : (Scheme.Modules.tensorPullback k).IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
    exact CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _ (by
      rw [CategoryTheory.rightExactFunctor_iff]
      infer_instance)
  let OX := SheafOfModules.unit X.ringCatSheaf
  let E := (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj OX)
  have : SheafOfModules.IsInvertible.{u, u, u} OX := inferInstance
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} OX := inferInstance
  have : OX.IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation OX
  have hflat : Scheme.Modules.IsFlatOver OX f :=
    Scheme.Modules.isFlatOver_of_isInvertible f OX
  have hperfect : Scheme.IsPerfect S E :=
    (perfect_derivedDirectImage_baseChange f OX hflat).1
  obtain ⟨a, e₀, e₁, hcomp, hnegative, hfibre⟩ :=
    exists_flat_derived_structure_unit f
  have hsurj := surjective_stalk_homology_of_perfect_local_unit S E hperfect a s
    (hnegative s) (hfibre s hs)
  let F := SheafOfModules.forget S.ringCatSheaf ⋙
    PresheafOfModules.toPresheaf S.ringCatSheaf.obj ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} s
  have hsurj' : Function.Surjective (F.map
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map a)) := hsurj
  let q : SheafOfModules.unit S.ringCatSheaf ⟶
      (Scheme.Modules.pushforward f).obj OX :=
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have hcomp' : F.map ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map a) ≫ F.map e₁.hom =
      F.map e₀.hom ≫ F.map q := by
    simpa only [Functor.map_comp] using
      congrArg (fun t ↦ F.map t) hcomp
  have hord : Function.Surjective
      (F.map q) := by
    intro y
    obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso (F.map e₁.hom)).2 y
    obtain ⟨x, hx⟩ := hsurj' z
    refine ⟨F.map e₀.hom x, ?_⟩
    have h := congrArg (fun q ↦ q x) hcomp'
    simpa only [ConcreteCategory.comp_apply, hx, hz] using h.symm
  obtain ⟨hb, hunit⟩ := Scheme.Modules.tensorPullbackObjUnitToUnit_isIso f
  let b := (Scheme.Modules.pushforward f).map
    (Scheme.Modules.tensorPullbackObjUnitToUnit f)
  have : IsIso (Scheme.Modules.tensorPullbackObjUnitToUnit f) := hb
  have : IsIso b := Functor.map_isIso _ _
  let η := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app
    (SheafOfModules.unit S.ringCatSheaf)
  have hunit' : F.map η ≫ F.map b = F.map q := by
    simpa only [Functor.map_comp] using congrArg (fun t ↦ F.map t) hunit
  change Function.Surjective (F.map η)
  apply surjective_of_comp_isIso (F.map η) (F.map b)
  rw [hunit']
  exact hord

end AlgebraicGeometry
