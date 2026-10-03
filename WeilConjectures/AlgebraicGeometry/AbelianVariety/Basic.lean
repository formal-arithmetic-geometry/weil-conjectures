/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Group.Abelian
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Abelian varieties are geometrically integral, and commutative

An abelian variety, defined as a proper smooth connected group scheme over a field, is
automatically irreducible and geometrically integral; combined with Mathlib's
`AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral` this makes it a
commutative group scheme.

The converse direction — a proper connected smooth group scheme is an abelian variety — is true
by definition, so together the statements below say that abelian varieties and complete group
varieties are the same thing.

## Main statements

- `AlgebraicGeometry.IsAbelianVariety.geometricallyIntegral`: an abelian variety is
  geometrically integral over the base field.
- `AlgebraicGeometry.IsAbelianVariety.irreducibleSpace`: its underlying space is irreducible.
- `AlgebraicGeometry.IsAbelianVariety.isCommMonObj`: an abelian variety is commutative.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- Blueprint `sk-prop-av-char`: Abelian varieties are the complete group varieties.

Let `G` be a group scheme over a field `K` which is proper, connected and smooth over `K`, that
is, an abelian variety in the sense of `AlgebraicGeometry.IsAbelianVariety`. Then `G` is
geometrically integral over `K`: it has a rational point, the unit, so connectedness gives
geometric connectedness; a smooth morphism with geometrically connected fibres is geometrically
irreducible; and smoothness gives geometric reducedness.

This is also blueprint `lem-sc-abelian-variety-characterization`. -/
instance IsAbelianVariety.geometricallyIntegral (G : Over (Spec (.of K))) [GrpObj G]
    [IsAbelianVariety G] : GeometricallyIntegral G.hom := by
  have hη : η[G].left ≫ G.hom = 𝟙 _ := by simp
  have := GeometricallyConnected.of_connectedSpace_of_section G.hom η[G].left hη
  have := GeometricallyIrreducible.of_smooth_of_geometricallyConnected G.hom
  exact .of_geometricallyReduced_of_geometricallyIrreducible _

/-- Blueprint `sk-prop-av-char`: Abelian varieties are the complete group varieties.

The underlying space of an abelian variety is irreducible, being geometrically irreducible over
the one-point space `Spec K`.

This is also blueprint `lem-sc-abelian-variety-characterization`. -/
instance IsAbelianVariety.irreducibleSpace (G : Over (Spec (.of K))) [GrpObj G]
    [IsAbelianVariety G] : IrreducibleSpace G.left :=
  GeometricallyIrreducible.irreducibleSpace_of_subsingleton G.hom

/-- Blueprint `sk-cor-av-commutative`: Abelian varieties are commutative

Let `A` be an abelian variety over `K`. Then `m ∘ s = m`, where `s` is the swap of the two
factors of `A ⊗ A`; that is, `A` is a commutative group object, and in particular `A(K)` is an
abelian group.

This is Mathlib's `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral` applied
to `AlgebraicGeometry.IsAbelianVariety.geometricallyIntegral`. The blueprint instead deduces it
from the rigidity lemma `AlgebraicGeometry.exists_eq_snd_comp`, which is recorded in
`WeilConjectures.AlgebraicGeometry.AbelianVariety.Rigidity`, whose hypotheses on `X` an abelian
variety satisfies (see Stacks 04KV for geometric connectedness). -/
instance IsAbelianVariety.isCommMonObj (A : Over (Spec (.of K))) [GrpObj A]
    [IsAbelianVariety A] : IsCommMonObj A :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A

end AlgebraicGeometry
