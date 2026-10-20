# AlgebraicGeometry.Etale.exists_ordinaryFiniteP1Adjunction

## Reason

Record the proof-local transparency controls and private helper attribute flagged by
preflight's conservative interface scan. Derived-category monoidal instances expand
heavily when elaborating the generic adjunction constructor and trace equations.
The new private constructor is irreducible and has proved unit/counit equations;
the existing functor wrappers are irreducible only locally in this module.
No existing public declaration signature, definition body, public import or global
attribute changes. No adopted source-library file changes. The proof is replaced by
an actual assembly from the two recorded geometric source results.

## Old

The public signature, verbatim:

```lean
theorem exists_ordinaryFiniteP1Adjunction (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) :
    ∃ (t : OrdinaryFiniteTwistTransport A N hA)
      (d : ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
        OrdinaryFiniteP1Datum A N hA t S hS), OrdinaryFiniteP1BaseChange A N hA t d
```

There were no proof-local irreducibility commands or private adjunction constructor
in the original item module.

## New

The public signature, verbatim and unchanged:

```lean
theorem exists_ordinaryFiniteP1Adjunction (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) :
    ∃ (t : OrdinaryFiniteTwistTransport A N hA)
      (d : ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
        OrdinaryFiniteP1Datum A N hA t S hS), OrdinaryFiniteP1BaseChange A N hA t d
```

The new local command is:

```lean
attribute [local irreducible] ordinaryFinitePullback ordinaryFinitePushforward
  ordinaryFiniteTensor
```

The new private `adjunctionOfComponentTriangles` definition has `@[irreducible]`.
Its body is the standard `Adjunction.mkOfUnitCounit` construction. The private
`adjunctionOfComponentTriangles_unit` and `_counit` lemmas explicitly unfold it and
prove the projection equations. This helper occurs only in theorem proofs and
exports no public definition or signature.

## Users

Computed with `tools/downstream.py Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
--uses AlgebraicGeometry.Etale.exists_ordinaryFiniteP1Adjunction`.
The 649 transitive importing modules see the same public theorem type. The four
modules with textual declaration uses are listed below. Claim records were checked
on 2026-10-21. No consumer needs an adaptation: all changes to existing wrappers'
transparency are local, and the new constructor is private.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineSpaceTopTrace | unclaimed | Same theorem signature; no change needed. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction | B2 | Complete proof assembly and private helpers; no signature change. |
| Sheaf.AlgebraicGeometry.ProjectiveLineTrace | unclaimed | Same theorem signature; no change needed. |
| Sheaf.Paper.VectorPurityNormalization | unclaimed | Same theorem signature; no change needed. |

The four new modules have no pre-existing consumers. They are compiled together
with the item through lcompile.py. There are no forced adaptations.

## Status

landed 20261020T211629-L-3480845 2026-10-20 (merge of deliver/B2/Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction)
