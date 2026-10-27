/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.Paper.TowerP1SingleLevelData
import Sheaf.Paper.TowerP1SingleLevelConstruction
import Sheaf.Paper.TowerP1SingleLevelTransport

/-! # Reflection of single-level projective-line triangles

Source: the Levels argument of det-sp-tower-p1-adjunction.
(blueprint: lem-sp-tower-p1-single-level-triangles).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
  AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerP1

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (n : ℕ) [Finite (SpTowerShriek.R l E n)]

private theorem nu_map_injective (T : Scheme.{u})
    (X : Etale.DerivedCategoryModule (levelRing l E n) T)
    (hX : DerivedCategory.TStructure.t.plus X) (f g : X ⟶ X)
    (hfg : (nu l E n T).map f = (nu l E n T).map g) : f = g := by
  let R := (realization l E n T).mapDerivedCategory
  have hfg' :
      (comparisonUpperStar (ModuleCat.{u + 1} (levelRing l E n)) T).mapDerivedCategory.map f =
      (comparisonUpperStar (ModuleCat.{u + 1} (levelRing l E n)) T).mapDerivedCategory.map g :=
    R.map_injective hfg
  obtain ⟨ff⟩ := (boundedBelowComparison T (levelRing l E n)).2.1
  have := ff.faithful
  let X' : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (levelRing l E n))) := ⟨X, hX⟩
  let f' : X' ⟶ X' := ObjectProperty.homMk f
  let g' : X' ⟶ X' := ObjectProperty.homMk g
  have heq :
      (comparisonUpperStar (ModuleCat.{u + 1} (levelRing l E n)) T).mapDerivedCategoryPlus.map
          f' =
      (comparisonUpperStar (ModuleCat.{u + 1} (levelRing l E n)) T).mapDerivedCategoryPlus.map
          g' := by
    apply ObjectProperty.hom_ext
    exact hfg'
  exact congrArg (fun a ↦ a.hom)
    ((comparisonUpperStar (ModuleCat.{u + 1} (levelRing l E n)) T).mapDerivedCategoryPlus
      |>.map_injective heq)

private theorem nu_plus_of_origin {T : Scheme.{u}}
    (X : Etale.DerivedCategoryModule (levelRing l E n) T)
    {b : SpTowerShriek.Base l E} {M : SpTowerShriek.D l E T}
    (o : SpTowerShriek.Origin l E b T n M)
    (e : (nu l E n T).obj X ≅ (SpTowerShriek.Ev l E T n).obj M) :
    DerivedCategory.TStructure.t.plus X := by
  let R := realization l E n T
  let V := comparisonUpperStar (ModuleCat.{u + 1} (levelRing l E n)) T
  obtain ⟨a, ha⟩ := o.level.property
  have : DerivedCategory.IsGE o.level.obj a := ha
  have hR : DerivedCategory.IsGE (R.mapDerivedCategory.obj o.level.obj) a :=
    R.isGE_mapDerivedCategory_obj _ a
  have : DerivedCategory.IsGE
      ((sfIntrinsicModuleEquivalence T (SpTowerShriek.R l E n)).functor.mapDerivedCategory.obj
        o.level.obj) a := hR
  have : DerivedCategory.IsGE ((SpTowerShriek.Ev l E T n).obj M) a :=
    DerivedCategory.TStructure.t.isGE_of_iso o.realization a
  have hnu : DerivedCategory.IsGE ((nu l E n T).obj X) a :=
    DerivedCategory.TStructure.t.isGE_of_iso e.symm a
  have hV : DerivedCategory.IsGE (V.mapDerivedCategory.obj X) a :=
    (DerivedCategory.isGE_iff _ a).2 fun i hi ↦
      R.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
        ((DerivedCategory.isGE_iff _ a).1 hnu i hi)
  exact ⟨a, (DerivedCategory.isGE_iff X a).2 fun i hi ↦
    V.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      ((DerivedCategory.isGE_iff _ a).1 hV i hi)⟩

omit [Finite (SpTowerShriek.R l E n)] in
/-- Single-level realization, canonical operation/formula comparison, and reflection
of the two tower triangle identities on the ordinary bounded-below etale categories.
No tower adjunction, normalization, finite-Tor hypothesis or transition-compatible
choice of etale representatives is assumed.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md, Levels;
det-sp-tower-p1-adjunction, steps 10--11
(blueprint: lem-sp-tower-p1-single-level-triangles).

Proof: singleLevelConstruction supplies the exact zero-off-n realizations and
normalized natural operation comparisons (the construction part of the Levels
argument). singleLevelTransport gives the unconditional commuting square for
each composite word. Substitute the assumed tower identity at the appropriate
singleton input and apply exact level evaluation. Cancel the push or pull
comparison component. The resulting equality is the image under nu of the
finite triangle identity. The retained origin of FJ or GJ, together with the
comparison component, proves that the finite endpoint is bounded below:
realization and comparison are faithful exact functors, so their cohomology
comparisons reflect vanishing below a bound. Finally boundedBelowComparison
makes comparison faithful on D+, and derived realization is an equivalence;
nu_map_injective therefore reflects the equality. No faithfulness of tower
evaluation on arbitrary derived morphisms is used.
-/
theorem towerP1SingleLevelTriangles (S : Scheme.{u}) (hS : IsUnit (l : Γ(S, ⊤)))
    (p : Presentation l E S hS) (d : Maps l E p) (h : EtaleOriginComparisons l E p d) :
    @singleLevelTrianglesStatement l _ E _ _ _ n (p.classes.base.finite n) S hS p d h := by
  let : Finite (SpTowerShriek.R l E n) := p.classes.base.finite n
  obtain ⟨c⟩ := singleLevelConstruction l E n S hS p d h
  obtain ⟨hpush, hpull⟩ := singleLevelTransport l E n S hS p d h c
  refine ⟨c, fun ht ↦ ⟨?_, ?_⟩⟩
  · intro L
    let M := (c.projective.J l E n).obj L
    let FM := (left l E d).obj M
    obtain ⟨o⟩ := FM.property.2 n
    have hbounded := nu_plus_of_origin l E n
      ((singleLevelF l E n S).obj L.obj) o (c.push.app L)
    apply nu_map_injective l E n S _ hbounded
    apply (cancel_mono (c.push.hom.app L)).1
    have heq := congrArg ((SpTowerShriek.Ev l E S n).map) (ht.1 M)
    erw [CategoryTheory.Functor.map_id] at heq
    have heq' := (congrArg (fun f ↦ c.push.hom.app L ≫ f) heq).trans
      (Category.comp_id _)
    have hid : (nu l E n S).map (𝟙 ((singleLevelF l E n S).obj L.obj)) ≫
        c.push.hom.app L = c.push.hom.app L := by
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact ((hpush L).trans heq').trans hid.symm
  · intro H
    let K := (c.base.J l E n).obj H
    let GK := (rightRestricted l E d).obj K
    obtain ⟨o⟩ := GK.property.2 n
    have hbounded := nu_plus_of_origin l E n
      ((singleLevelG l E n S).obj H.obj) o (c.pull.app H)
    apply nu_map_injective l E n (ProjectiveLine S) _ hbounded
    apply (cancel_mono (c.pull.hom.app H)).1
    have heq := congrArg ((SpTowerShriek.Ev l E (ProjectiveLine S) n).map) (ht.2 K)
    erw [CategoryTheory.Functor.map_id] at heq
    have heq' := (congrArg (fun f ↦ c.pull.hom.app H ≫ f) heq).trans
      (Category.comp_id _)
    have hid : (nu l E n (ProjectiveLine S)).map
        (𝟙 ((singleLevelG l E n S).obj H.obj)) ≫ c.pull.hom.app H = c.pull.hom.app H := by
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact ((hpull H).trans heq').trans hid.symm

end AlgebraicGeometry.ProEtale.SpTowerP1

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
