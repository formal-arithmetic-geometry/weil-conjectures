/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.RingHom.Etale

/-!
# The geometric point over a point of a scheme

For a point `y` of a scheme `Y`, `Scheme.fromSpecResidueField` is the canonical morphism
`Spec κ(y) ⟶ Y`. This file names its composite with `Spec κ(y)‾ ⟶ Spec κ(y)`, where `κ(y)‾` is
the algebraic closure of `κ(y)`.

We also record that whether a residue field extension is étale, that is finite separable, is
insensitive to composing with a morphism inducing isomorphisms of residue fields, such as an open
immersion.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The geometric point `Spec κ(y)‾ ⟶ Y` over a point `y` of a scheme `Y`, where `κ(y)‾` is the
algebraic closure of the residue field `κ(y)`. It is the composite

```
  Spec κ(y)‾ ──▶ Spec κ(y) ── fromSpecResidueField y ──▶ Y
```
-/
noncomputable def fromSpecAlgebraicClosureResidueField (Y : Scheme.{u}) (y : Y) :
    Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) (AlgebraicClosure _))) ≫
    Y.fromSpecResidueField y

/-- If `g` induces an isomorphism of residue fields at `x`, then `κ(x)` is étale over the residue
field of its image under `g ≫ h` if and only if `κ(g x)` is. -/
lemma Hom.etale_residueFieldMap_comp_iff_left {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (x : X) [IsIso (g.residueFieldMap x)] :
    ((g ≫ h).residueFieldMap x).hom.Etale ↔ (h.residueFieldMap (g x)).hom.Etale := by
  rw [residueFieldMap_comp]
  exact RingHom.Etale.respectsIso.cancel_right_isIso _ _

/-- If `h` induces an isomorphism of residue fields at `g x`, then `κ(x)` is étale over the
residue field of its image under `g ≫ h` if and only if it is étale over `κ(g x)`. -/
lemma Hom.etale_residueFieldMap_comp_iff_right {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (x : X) [IsIso (h.residueFieldMap (g x))] :
    ((g ≫ h).residueFieldMap x).hom.Etale ↔ (g.residueFieldMap x).hom.Etale := by
  rw [residueFieldMap_comp]
  exact RingHom.Etale.respectsIso.cancel_left_isIso (h.residueFieldMap (g x))
    (g.residueFieldMap x)

lemma Hom.etale_residueFieldMap_congr {X Y : Scheme.{u}} {g h : X ⟶ Y} (e : g = h) (x : X) :
    (g.residueFieldMap x).hom.Etale ↔ (h.residueFieldMap x).hom.Etale := by
  subst e
  rfl

/-- A morphism `p : Spec K ⟶ X` from the spectrum of a field factors through `Spec κ(x)` for its
image point `x`, through a field embedding `κ(x) ⟶ K`. -/
lemma exists_eq_spec_map_comp_fromSpecResidueField {K : Type u} [Field K] {X : Scheme.{u}}
    (p : Spec (.of K) ⟶ X) (x : X) (hx : p.base (IsLocalRing.closedPoint K) = x) :
    ∃ ι : X.residueField x ⟶ .of K, p = Spec.map ι ≫ X.fromSpecResidueField x := by
  subst hx
  exact ⟨_, ((SpecToEquivOfField K X).left_inv p).symm⟩

end AlgebraicGeometry.Scheme
