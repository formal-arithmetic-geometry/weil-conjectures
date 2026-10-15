/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import Sheaf.Paper.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections

/-!
# Global sections at a geometric point and pullback stalks

Source: literature/stacks-project/etale-cohomology.tex, Tags 04JQ, 04JN and 03Q1 (3)
(blueprint: lem-weil-pbc-geometric-point-pullback-stalk).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- On the spectrum of an algebraically closed field, global sections are an exact
 equivalence for abelian sheaves and for sheaves of modules over any coefficient ring.
 For a geometric point of any scheme, global sections of its inverse image are naturally
 isomorphic to its stalk.

 Source: Stacks Project, Tags 04JQ, 04JN and 03Q1 (3).
 (blueprint: lem-weil-pbc-geometric-point-pullback-stalk).

 Proof:
 1. `lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant` identifies a sheaf of
    sets on `Spec Ω` with the constant sheaf of its global sections. Its canonical
    restriction maps respect addition and scalar multiplication, giving the same
    natural counit isomorphism for abelian sheaves and module sheaves.
 2. `Spec Ω` is connected. By `lem-weil-pbc-constant-sheaf-sections-connected`, the
    unit from an abelian group to the global sections of its constant sheaf is an
    isomorphism. The same map is linear for modules. Thus constant sheaf and global
    sections are quasi-inverse; an equivalence of abelian categories is exact.
 3. Apply the identity-point stalk clause of the constancy lemma to the inverse image
    of `G`: its global sections identify naturally with its stalk at `id (Spec Ω)`.
 4. `lem-weil-pbc-inverse-image-stalk-germ`, applied to `y` and the identity point,
    identifies that stalk naturally with `G_y`. Compose the two natural isomorphisms.
-/
theorem geometricPoint_pullback_stalk (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    ((sheafSections (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op (Etale.mk (𝟙 (Spec (.of Ω)))))).IsEquivalence ∧
    PreservesFiniteLimits
      ((sheafSections (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op (Etale.mk (𝟙 (Spec (.of Ω)))))) ∧
    PreservesFiniteColimits
      ((sheafSections (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op (Etale.mk (𝟙 (Spec (.of Ω)))))) ∧
    (∀ (Λ : Type (u + 1)) [Ring Λ],
      ((sheafSections (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (op (Etale.mk (𝟙 (Spec (.of Ω)))))).IsEquivalence ∧
      PreservesFiniteLimits
        ((sheafSections (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (op (Etale.mk (𝟙 (Spec (.of Ω)))))) ∧
      PreservesFiniteColimits
        ((sheafSections (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (op (Etale.mk (𝟙 (Spec (.of Ω))))))) ∧
    (∀ (Y : Scheme.{u}) (y : Spec (.of Ω) ⟶ Y),
      Nonempty (AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} y ⋙
        (sheafSections (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (op (Etale.mk (𝟙 (Spec (.of Ω))))) ≅
        (pointSmallEtale y).sheafFiber)) := by
  sorry

end AlgebraicGeometry.Scheme
