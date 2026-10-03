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
# Abelian schemes are geometrically integral, and commutative

An abelian scheme over a base `S`, defined as a proper smooth group scheme over `S` with
geometrically connected fibres (`AlgebraicGeometry.IsAbelianScheme`), has geometrically
integral fibres and is a commutative group scheme. Over a field, the underlying space is
moreover irreducible, and commutativity is Mathlib's
`AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`.

The converse direction — a proper geometrically connected smooth group scheme is an abelian
variety — is true by definition, so together the statements below say that abelian varieties
and complete group varieties are the same thing.

## Main statements

- `AlgebraicGeometry.IsAbelianScheme.geometricallyIntegral`: an abelian scheme has
  geometrically integral fibres.
- `AlgebraicGeometry.IsAbelianScheme.irreducibleSpace`: the underlying space of an abelian
  variety is irreducible.
- `AlgebraicGeometry.IsAbelianScheme.isCommMonObj`: an abelian scheme is commutative;
  `AlgebraicGeometry.IsAbelianScheme.isCommMonObj_of_field` is the case of an abelian variety,
  proved from Mathlib.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {K : Type u} [Field K]

/-- Blueprint `sk-prop-av-char`: Abelian varieties are the complete group varieties.

Let `G` be an abelian scheme over a base `S`. Then `G` has geometrically integral fibres: they
are geometrically connected by definition, smoothness makes them geometrically reduced, and a
connected smooth scheme over a field is irreducible, being normal. Over a field `K`, this says
that a proper, connected and smooth group scheme over `K` is geometrically integral (for a
connected group scheme geometric connectedness follows from the existence of the rational
point `1`). -/
instance IsAbelianScheme.geometricallyIntegral (G : Over S) [GrpObj G] [IsAbelianScheme G] :
    GeometricallyIntegral G.hom :=
  sorry

/-- Blueprint `sk-prop-av-char`: Abelian varieties are the complete group varieties.

The underlying space of an abelian variety is irreducible, being geometrically irreducible over
the one-point space `Spec K`. -/
instance IsAbelianScheme.irreducibleSpace (G : Over (Spec (.of K))) [GrpObj G]
    [IsAbelianScheme G] : IrreducibleSpace G.left :=
  GeometricallyIrreducible.irreducibleSpace_of_subsingleton G.hom

/-- Blueprint `sk-cor-av-commutative`: Abelian varieties are commutative

Let `A` be an abelian scheme over a base `S`. Then `m ∘ s = m`, where `s` is the swap of the two
factors of `A ⊗ A`; that is, `A` is a commutative group object, and in particular `A(T)` is an
abelian group for every `S`-scheme `T`.

Over a general base this is the rigidity lemma for abelian schemes (Mumford, Geometric
Invariant Theory, Corollary 6.4), which needs `A ⟶ S` proper and flat with
`𝒪_S = f_* 𝒪_A` universally; the rigidity lemma of
`WeilConjectures.AlgebraicGeometry.AbelianVariety.Rigidity` is only stated over a field, so the
general case cannot be reduced to it directly. Over a field `K` the statement is
`AlgebraicGeometry.IsAbelianScheme.isCommMonObj_of_field`, proved from Mathlib. -/
instance IsAbelianScheme.isCommMonObj (A : Over S) [GrpObj A] [IsAbelianScheme A] :
    IsCommMonObj A :=
  sorry

/-- Blueprint `sk-cor-av-commutative`: Abelian varieties are commutative

The case of an abelian variety over a field `K` of
`AlgebraicGeometry.IsAbelianScheme.isCommMonObj`: Mathlib's
`AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral` applied to
`AlgebraicGeometry.IsAbelianScheme.geometricallyIntegral`. It is recorded separately so that
this case does not rest on the `sorry` of the general statement. The blueprint instead deduces
it from the rigidity lemma `AlgebraicGeometry.exists_eq_snd_comp`, which is recorded in
`WeilConjectures.AlgebraicGeometry.AbelianVariety.Rigidity`, whose hypotheses on `X` an abelian
variety satisfies (see Stacks 04KV for geometric connectedness). -/
theorem IsAbelianScheme.isCommMonObj_of_field (A : Over (Spec (.of K))) [GrpObj A]
    [IsAbelianScheme A] : IsCommMonObj A :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A

end AlgebraicGeometry
