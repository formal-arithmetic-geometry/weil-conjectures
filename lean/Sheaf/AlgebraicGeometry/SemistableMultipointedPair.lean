/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.TraceFormula.MultipointedCurve
public import Sheaf.Paper.OrgogozoInductionData
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Data.Set.Card

/-! # Multipointed curves and geometric stability

Source: Temkin, Stable Modification of Relative Curves, §1.2, pp. 2–3
(blueprint: def-trf-semistable-multipointed-pair).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An underlying pair over a scheme, before imposing any geometric properties.
Source: Temkin §1.2 (blueprint: def-trf-semistable-multipointed-pair). -/
structure MultipointedPair (T : Scheme.{u}) where
  curve : Over T
  marking : Over T
  inclusion : marking ⟶ curve

namespace MultipointedPair

/-- Canonical base change of the two schemes and their inclusion, using the pullback functor.
Source: Temkin §1.2 (blueprint: def-trf-semistable-multipointed-pair). -/
def baseChange {T T' : Scheme.{u}} (P : MultipointedPair T) (g : T' ⟶ T) :
    MultipointedPair T' where
  curve := (Over.pullback g).obj P.curve
  marking := (Over.pullback g).obj P.marking
  inclusion := (Over.pullback g).map P.inclusion

/-- Forget the property fields of the existing multipointed-curve structure.
Source: Temkin §1.2 (blueprint: def-trf-semistable-multipointed-pair). -/
def ofCurve {T : Scheme.{u}} (C : MultipointedCurve T) : MultipointedPair T where
  curve := Over.mk C.x
  marking := Over.mk C.d
  inclusion := Over.homMk C.i C.comm.symm

/-- A raw pair is multipointed precisely when it underlies an existing `MultipointedCurve`.
The equality fixes both schemes, both structural maps and the marking; the existential only
bundles the property proofs already specified by that structure. No new geometric definition
or choice of data is introduced. Empty markings and nonseparated curves remain permitted.
Source: Temkin §1.2 (blueprint: def-trf-semistable-multipointed-pair). -/
def IsMultipointed {T : Scheme.{u}} (P : MultipointedPair T) : Prop :=
  ∃ C : MultipointedCurve T, ofCurve C = P

/-- Semistability on the chosen algebraic-closure geometric fibres: each nonsmooth point is
an ordinary double point with its specified scalar field. The marking is etale and its image
is in the relative smooth locus. Source: Temkin §1.2, Stacks 0C56
(blueprint: def-trf-semistable-multipointed-pair). -/
def IsSemistable {T : Scheme.{u}} (P : MultipointedPair T) : Prop :=
  P.IsMultipointed ∧ Etale P.marking.hom ∧
    (∀ d : P.marking.left, (P.curve.hom.stalkMap (P.inclusion.left d)).hom.FormallySmooth) ∧
    ∀ t : T, ∀ x : (P.baseChange (Orgogozo.geometricPoint T t)).curve.left,
      ¬ (((P.baseChange (Orgogozo.geometricPoint T t)).curve.hom).stalkMap x).hom.FormallySmooth →
        Orgogozo.IsOrdinaryDoublePoint
          (P.baseChange (Orgogozo.geometricPoint T t)).curve.hom x

/-- No exceptional component on a chosen geometric fibre. A projective-line component is
represented by a closed immersion whose range is an irreducible component, over the scalar
field. Its contracted image is a singleton; it must then have more than two distinct special
points. Special points are counted on the component, without counting normalization branches.
Source: Temkin §1.2 (blueprint: def-trf-semistable-multipointed-pair). -/
def HasGeometricStability {T : Scheme.{u}} (P Q : MultipointedPair T)
    (f : P.curve ⟶ Q.curve) : Prop :=
  ∀ t : T,
    ∀ j : ProjectiveLine (Spec (.of (AlgebraicClosure (T.residueField t)))) ⟶
        (P.baseChange (Orgogozo.geometricPoint T t)).curve.left,
      IsClosedImmersion j → Set.range j ∈
        irreducibleComponents (P.baseChange (Orgogozo.geometricPoint T t)).curve.left →
      j ≫ (P.baseChange (Orgogozo.geometricPoint T t)).curve.hom =
        (ProjectiveLine (Spec (.of (AlgebraicClosure (T.residueField t)))) ↘
          Spec (.of (AlgebraicClosure (T.residueField t)))) →
      (Set.range (j ≫ ((Over.pullback (Orgogozo.geometricPoint T t)).map f).left)).Subsingleton →
      2 < Set.encard {x | x ∈ Set.range j ∧
        (x ∈ Set.range (P.baseChange (Orgogozo.geometricPoint T t)).inclusion.left ∨
          ¬ (((P.baseChange (Orgogozo.geometricPoint T t)).curve.hom).stalkMap
            x).hom.FormallySmooth)}

end MultipointedPair
end AlgebraicGeometry
