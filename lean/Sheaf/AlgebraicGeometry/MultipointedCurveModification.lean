/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import Sheaf.TraceFormula.MultipointedCurve
public import Sheaf.Paper.OrgogozoInductionData
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Data.Set.Card

/-! # Morphisms, semistability and stable modifications of multipointed curves

Source: Temkin, Stable modification of relative curves, §1.2 and §4
(blueprint: def-trf-multipointed-curve-modification).

The multipointed curves are the landed `AlgebraicGeometry.MultipointedCurve`
(def-trf-multipointed-curve): flat finitely presented curve and marking, with neither
properness nor separatedness over the base imposed. Nodal completed local rings reuse
Orgogozo's existing ordinary-double-point predicate. Stability is relative to the specified
morphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

attribute [instance] MultipointedCurve.lfp_X

/-- A morphism of multipointed curves is a compatible pair of morphisms over the base.
Source: Temkin §1.2 (blueprint: def-trf-multipointed-curve-modification). -/
structure MultipointedCurve.Hom {T : Scheme.{u}} (P Q : MultipointedCurve T) where
  curve : P.X ⟶ Q.X
  marking : P.D ⟶ Q.D
  curve_over : curve ≫ Q.x = P.x
  marking_over : marking ≫ Q.d = P.d
  comm : marking ≫ Q.i = P.i ≫ curve

/-- The canonical base change of the curve map in a morphism of multipointed curves.
Source: Temkin §1.2 (blueprint: def-trf-multipointed-curve-modification). -/
def MultipointedCurve.Hom.curveBaseChange {T S : Scheme.{u}} {P Q : MultipointedCurve T}
    (f : P.Hom Q) (s : S ⟶ T) : pullback P.x s ⟶ pullback Q.x s :=
  pullback.map P.x s Q.x s f.curve (𝟙 S) (𝟙 T)
    ((Category.comp_id _).trans f.curve_over.symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- The canonical base change of the marking map in a morphism of multipointed curves.
Source: Temkin §1.2 (blueprint: def-trf-multipointed-curve-modification). -/
def MultipointedCurve.Hom.markingBaseChange {T S : Scheme.{u}} {P Q : MultipointedCurve T}
    (f : P.Hom Q) (s : S ⟶ T) : pullback P.d s ⟶ pullback Q.d s :=
  pullback.map P.d s Q.d s f.marking (𝟙 S) (𝟙 T)
    ((Category.comp_id _).trans f.marking_over.symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- The marking inclusion after base change, with both pullbacks over the same base.
Source: Temkin §1.2 (blueprint: def-trf-multipointed-curve-modification). -/
def MultipointedCurve.markingBaseChange {T S : Scheme.{u}} (P : MultipointedCurve T)
    (s : S ⟶ T) : pullback P.d s ⟶ pullback P.x s :=
  pullback.map P.d s P.x s P.i (𝟙 S) (𝟙 T)
    ((Category.comp_id _).trans P.comm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- Semistability of a multipointed curve: nodal geometric fibres, étale marking and marking
in the relative smooth locus. The algebraic-closure fibre over each base point is used.
Source: Temkin §1.2 (blueprint: def-trf-multipointed-curve-modification). -/
def MultipointedCurve.IsSemistable {T : Scheme.{u}} (P : MultipointedCurve T) : Prop :=
  (∀ (t : T) (x : pullback (C := Scheme) P.x (Orgogozo.geometricPoint T t)),
    x ∈ (pullback.snd P.x (Orgogozo.geometricPoint T t)).smoothLocus ∨
      Orgogozo.IsOrdinaryDoublePoint
        (pullback.snd P.x (Orgogozo.geometricPoint T t)) x) ∧
  Etale P.d ∧ ∀ e : P.D, P.i e ∈ P.x.smoothLocus

/-- An eta-modification is proper on both parts, an isomorphism between schematically dense
opens on both parts, and an isomorphism on the specified generic fibres. Schematic density
is stated as injectivity on sections of every open of the structure-sheaf map.
Source: Temkin §1.2 and §4 (blueprint: def-trf-multipointed-curve-modification). -/
def MultipointedCurve.Hom.IsEtaModification {T S : Scheme.{u}}
    {P Q : MultipointedCurve T} (f : P.Hom Q) (η : S ⟶ T) : Prop :=
  IsProper f.curve ∧ IsProper f.marking ∧
  (∃ U : Q.X.Opens,
    (∀ W : Q.X.Opens, Function.Injective (U.ι.app W)) ∧
    (∀ W : P.X.Opens, Function.Injective ((f.curve ⁻¹ᵁ U).ι.app W)) ∧
    IsIso (pullback.snd f.curve U.ι)) ∧
  (∃ U : Q.D.Opens,
    (∀ W : Q.D.Opens, Function.Injective (U.ι.app W)) ∧
    (∀ W : P.D.Opens, Function.Injective ((f.marking ⁻¹ᵁ U).ι.app W)) ∧
    IsIso (pullback.snd f.marking U.ι)) ∧
  IsIso (f.curveBaseChange η) ∧ IsIso (f.markingBaseChange η)

/-- Special points of a geometric fibre are the union of the marking and nonsmooth points.
Source: Temkin §1.2 (blueprint: def-trf-multipointed-curve-modification). -/
def MultipointedCurve.specialPoints {T : Scheme.{u}} (P : MultipointedCurve T) (t : T) :
    Set (pullback (C := Scheme) P.x (Orgogozo.geometricPoint T t)) :=
  Set.range (P.markingBaseChange (Orgogozo.geometricPoint T t)) ∪
    {x | x ∉ (pullback.snd P.x (Orgogozo.geometricPoint T t)).smoothLocus}

/-- Stability relative to a map: no contracted geometric component is a projective line
with at most two special points. A projective-line component is represented by its closed
embedding, over the algebraically closed residue field, with irreducible-component image.
Source: Temkin §1.2 (blueprint: def-trf-multipointed-curve-modification). -/
def MultipointedCurve.Hom.IsStable {T S : Scheme.{u}} {P Q : MultipointedCurve T}
    (f : P.Hom Q) (η : S ⟶ T) : Prop :=
  f.IsEtaModification η ∧ P.IsSemistable ∧
  ∀ (t : T)
    (i : ProjectiveLine (Spec (.of (AlgebraicClosure (T.residueField t)))) ⟶
      pullback (C := Scheme) P.x (Orgogozo.geometricPoint T t)),
    IsClosedImmersion i →
    i ≫ pullback.snd P.x (Orgogozo.geometricPoint T t) =
      ProjectiveLine (Spec (.of (AlgebraicClosure (T.residueField t)))) ↘
        Spec (.of (AlgebraicClosure (T.residueField t))) →
    Set.range i ∈
      irreducibleComponents (pullback (C := Scheme) P.x (Orgogozo.geometricPoint T t)) →
    (Set.range i ∩ P.specialPoints t).encard ≤ 2 →
    ¬ (Set.range (i ≫ f.curveBaseChange (Orgogozo.geometricPoint T t))).Subsingleton

end AlgebraicGeometry
