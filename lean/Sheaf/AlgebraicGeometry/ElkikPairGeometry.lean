/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import Sheaf.AlgebraicGeometry.RigRegularFormalGeometry
public import Sheaf.AlgebraicGeometry.RegularSchemeMorphism
public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

/-! # Elkik pairs and their finite disjoint unions

Source: Temkin, Non-embedded Desingularization, §§3.2.3--3.2.4 and 3.3.1
(blueprint: def-per-elkik-pair-geometry).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Elkik

/-- An affine Elkik pair, with an arbitrary characteristic-zero field of definition.
The generator is a non-zero-divisor, and the absolute nonregular locus lies in its
zero locus. Source: Temkin §§3.2.3--3.2.4, 3.3.1
(blueprint: def-per-elkik-pair-geometry). -/
structure AffinePair where
  ring : CommRingCat.{u}
  field : CommRingCat.{u}
  isField : IsField field
  charZero : CharZero field
  structureMap : Spec ring ⟶ Spec field
  finiteType : LocallyOfFiniteType structureMap
  quasiCompact : QuasiCompact structureMap
  generator : ring
  nonZeroDivisor : generator ∈ nonZeroDivisors ring
  singularSupport : ∀ x : Spec ring,
    ¬ IsRegularLocalRing ((Spec ring).presheaf.stalk x) →
      x ∈ (affineFormalIdeal ring (Ideal.span {generator})).support

/-- Finite disjoint unions of Elkik pairs, with the ideal on the whole union.
The presentation is a proposition, so no selected decomposition affects a rule.
Fields and generators may vary between pieces, and the empty union is allowed.
Source: Temkin §§2.3.5--2.3.6, 3.3.8, 3.4.1
(blueprint: def-per-elkik-pair-geometry). -/
structure Pair where
  scheme : Scheme.{u}
  ideal : scheme.IdealSheafData
  presentation : ∃ (n : ℕ) (P : Fin n → AffinePair.{u})
    (e : (∐ fun i ↦ Spec (P i).ring) ≅ scheme),
    ∀ i, ideal.comap (Sigma.ι (fun j ↦ Spec (P j).ring) i ≫ e.hom) =
      affineFormalIdeal (P i).ring (Ideal.span {(P i).generator})

/-- The actual thick fibre, including the harmless order-zero empty fibre.
Source: Temkin §3.3.1 (blueprint: def-per-elkik-pair-geometry). -/
def Pair.fibre (X : Pair.{u}) (t : ℕ) : Scheme.{u} :=
  (adicThickeningDiagram X.ideal).obj t

/-- The distinguished ideal on the thick fibre is the extended ideal, not its radical.
Source: Temkin §3.3.1 (blueprint: def-per-elkik-pair-geometry). -/
def Pair.fibreIdeal (X : Pair.{u}) (t : ℕ) : (X.fibre t).IdealSheafData :=
  X.ideal.comap (X.ideal ^ t).subschemeι

/-- Generically reduced finite disjoint unions of finite-type schemes over arbitrary
characteristic-zero fields. On a Noetherian scheme, generic reducedness is equivalently
reducedness on a dense open. No separation assumption is imposed.
Source: Temkin §§1.2.1, 2.3.3--2.3.6, 3.3.8
(blueprint: def-per-elkik-pair-geometry). -/
def IsVarietyUnion (X : Scheme.{u}) : Prop :=
  ∃ (n : ℕ) (V : Fin n → Scheme.{u}) (k : Fin n → CommRingCat.{u})
    (s : ∀ i, V i ⟶ Spec (k i)),
    Nonempty ((∐ V) ≅ X) ∧ ∀ i,
      IsField (k i) ∧ CharZero (k i) ∧ LocallyOfFiniteType (s i) ∧ QuasiCompact (s i) ∧
      ∃ U : (V i).Opens, Dense (U : Set (V i)) ∧ IsReduced U.toScheme

/-- The source's strong and all-regular-morphism functoriality hypotheses.
An assignment is indexed by schemes; values outside `IsVarietyUnion` are immaterial.
Every such source rule extends to this indexing using the length-zero identity tower
on other schemes. In particular no field-linearity condition is imposed on a map.
Source: Temkin §§2.3.1--2.3.6, Proposition 3.3.5
(blueprint: def-per-elkik-pair-geometry). -/
def IsStrongRegularRule (F : ∀ X : Scheme.{u}, OrdinaryBlowupTower X) : Prop :=
  (∀ (X : Scheme.{u}), IsVarietyUnion X →
    (∀ i : Fin (F X).length,
      RingedSpace.IsCoherent ((F X).level i.castSucc).toRingedSpace
        ((F X).center i).toModules ∧
      Set.Nonempty (((F X).center i).support : Set ((F X).level i.castSucc)) ∧
      IsRegularScheme ((F X).center i).subscheme ∧
      ∀ x : (F X).level i.castSucc, x ∈ ((F X).center i).support →
        ¬ IsRegularLocalRing (X.presheaf.stalk ((F X).toBase i.castSucc x))) ∧
    IsRegularScheme ((F X).level ⟨(F X).length, Nat.lt_succ_self _⟩)) ∧
  ∀ (X Y : Scheme.{u}), IsVarietyUnion X → IsVarietyUnion Y →
    ∀ h : Y ⟶ X, IsRegularSchemeMorphism h →
      Nonempty (OrdinaryResolutionComparison h (F X) (F Y))

end AlgebraicGeometry.Elkik
