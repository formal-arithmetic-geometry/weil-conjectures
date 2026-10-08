/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Group.Abelian
public import WeilConjectures.AlgebraicGeometry.AbelianScheme.Defs

/-!
# Abelian schemes are geometrically integral, and commutative

An abelian scheme over a base `S`, defined as a proper smooth group scheme over `S` with
geometrically connected fibres (`AlgebraicGeometry.IsAbelianScheme`), has geometrically
integral fibres and is a commutative group scheme. Over an irreducible base the underlying space
is moreover irreducible.

The converse direction — a proper geometrically connected smooth group scheme is an abelian
variety — is true by definition, so together the statements below say that abelian varieties
and complete group varieties are the same thing.

## Main statements

- `AlgebraicGeometry.IsAbelianScheme.geometricallyIntegral`: an abelian scheme has
  geometrically integral fibres.
- `AlgebraicGeometry.IsAbelianScheme.irreducibleSpace`: the underlying space of an abelian
  scheme over an irreducible base is irreducible; in particular an abelian variety is
  irreducible.
- `AlgebraicGeometry.IsAbelianScheme.isCommMonObj`: an abelian scheme is commutative.
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

The underlying space of an abelian scheme `G` over an irreducible base `S` is irreducible: the
structure morphism is open, being smooth, and has geometrically irreducible fibres
(`AlgebraicGeometry.IsAbelianScheme.geometricallyIntegral`), so the irreducible components of
`G` are those of `S`. In particular the underlying space of an abelian variety is irreducible,
the one-point space `Spec K` being irreducible. -/
instance IsAbelianScheme.irreducibleSpace (G : Over S) [GrpObj G] [IsAbelianScheme G]
    [IrreducibleSpace S] : IrreducibleSpace G.left :=
  GeometricallyIrreducible.irreducibleSpace G.hom
    (isOpenMap_of_generalizingMap G.hom (Flat.generalizingMap G.hom))

/-- Blueprint `sk-cor-av-commutative`: Abelian varieties are commutative

Let `A` be an abelian scheme over a base `S`. Then `m ∘ s = m`, where `s` is the swap of the two
factors of `A ⊗ A`; that is, `A` is a commutative group object, and in particular `A(T)` is an
abelian group for every `S`-scheme `T`.

Over a general base this follows from the rigidity lemma
`AlgebraicGeometry.exists_eq_snd_comp` (Mumford, Geometric Invariant Theory, Corollary 6.4),
whose hypotheses on `A ⟶ S`, proper, flat and of finite presentation with geometrically
connected and geometrically reduced fibres, hold since the structure morphism of an abelian
scheme is proper and smooth with geometrically connected fibres. Over a field `K` the statement
is also Mathlib's `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral` applied
to `AlgebraicGeometry.IsAbelianScheme.geometricallyIntegral`. It cannot be deduced from that
case over an arbitrary base, since an equality of morphisms is not detected on the fibres when
the base is not reduced.

This is a theorem rather than an instance: `CategoryTheory.IsCommMonObj A` has to be supplied
explicitly where it is needed. -/
theorem IsAbelianScheme.isCommMonObj (A : Over S) [GrpObj A] [IsAbelianScheme A] :
    IsCommMonObj A :=
  sorry

end AlgebraicGeometry
