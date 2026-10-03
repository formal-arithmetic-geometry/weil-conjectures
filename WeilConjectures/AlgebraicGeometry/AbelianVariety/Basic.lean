/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Group.Abelian
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs

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

- `AlgebraicGeometry.AbelianVariety.geometricallyIntegral`: an abelian variety is
  geometrically integral over the base field.
- `AlgebraicGeometry.AbelianVariety.irreducibleSpace`: its underlying space is irreducible.
- `AlgebraicGeometry.AbelianVariety.isCommMonObj`: an abelian variety is commutative.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- Blueprint `sk-prop-av-char`: Abelian varieties are the complete group varieties.

Let `A` be a group scheme over a field `K` which is proper, connected and smooth over `K`, that
is, an abelian variety in the sense of `AlgebraicGeometry.AbelianVariety`. Then `A` is
geometrically integral over `K`: it has a rational point, the unit, so connectedness gives
geometric connectedness, and smoothness gives geometric reducedness. -/
instance AbelianVariety.geometricallyIntegral (A : AbelianVariety K) :
    GeometricallyIntegral A.toOver.hom :=
  sorry

/-- Blueprint `sk-prop-av-char`: Abelian varieties are the complete group varieties.

The underlying space of an abelian variety is irreducible, being geometrically irreducible over
the one-point space `Spec K`. -/
instance AbelianVariety.irreducibleSpace (A : AbelianVariety K) : IrreducibleSpace A.toOver.left :=
  GeometricallyIrreducible.irreducibleSpace_of_subsingleton A.toOver.hom

/-- Blueprint `sk-cor-av-commutative`: Abelian varieties are commutative

Let `A` be an abelian variety over `K`. Then `m ∘ s = m`, where `s` is the swap of the two
factors of `A ⊗ A`; that is, `A` is a commutative group object, and in particular `A(K)` is an
abelian group.

This is Mathlib's `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral` applied
to `AlgebraicGeometry.AbelianVariety.geometricallyIntegral`. The blueprint instead deduces it
from the rigidity lemma `AlgebraicGeometry.exists_eq_snd_comp`, which is recorded in
`WeilConjectures.AlgebraicGeometry.AbelianVariety.Rigidity`, whose hypotheses on `X` an abelian
variety satisfies (see Stacks 04KV for geometric connectedness). -/
instance AbelianVariety.isCommMonObj (A : AbelianVariety K) : IsCommMonObj A.toOver :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A.toOver

end AlgebraicGeometry
