# Sheaf.SixFunctors.FieldTensor proof context

## Reason

Prove the rational tensor-closure theorem using coefficient-isomorphism transport and
two localizing minimality arguments. The interface scanner notices added namespace opens
and local elaboration attributes. These changes provide proof context only: no definition,
public import, public signature, global instance or global attribute changes.

## Old

The existing public declaration has the following signature:

```lean
theorem tensorClosureRational
    (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] (p : ℕ) [CharP k p]
    (hp : 0 < p) (hpl : p ≠ ℓ)
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))) :
    (∀ (K M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X))),
      constantModelBoundedConstructible Λ X K →
      constantModelBoundedConstructible Λ X M →
      constantModelBoundedConstructible Λ X
        (((derivedTensor Λ X).obj K).obj M)) ∧
    (∀ (A B : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X))),
      CategoryTheory.localizingClosure
          (constantModelBoundedConstructible Λ X) A →
      CategoryTheory.localizingClosure
          (constantModelBoundedConstructible Λ X) B →
      CategoryTheory.localizingClosure
          (constantModelBoundedConstructible Λ X)
            (((derivedTensor Λ X).obj A).obj B))
```

The existing opens were `CategoryTheory`, `CategoryTheory.Limits`,
`AlgebraicGeometry`, `Scheme`, and scoped `CategoryTheory.Obj`.
The proof was `by sorry`.

## New

The signature above and all five public imports are identical. The proof is complete.
Six private, proved helpers express inverse-image localizing closure, the two-variable
minimality argument, generic derived tensor transport, its constant-model specialization, and the equality of the derived-tensor wrapper with
the canonical bifunctor. The generic helpers accept explicit wrapper equalities and
eliminate them abstractly, avoiding expensive conversions of concrete monoidal structures.
The added `MonoidalCategory` and `MonObj` opens resolve names in these proofs.
The local irreducibility of the derived comparison constructions prevents unnecessary
unfolding. No local attribute is exported as a global registration.

## Users

`tools/downstream.py Sheaf.SixFunctors.FieldTensor --uses tensorClosureRational` finds
228 transitive importers and no external textual use of this declaration. The only
reported occurrence is its declaration in the item. All importers retain exactly the same
public imports and theorem signature. No consumer is edited or needs adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.FieldTensor | G2 | Proof and private context changed; public interface preserved. |

## Status

landed 20261020T051310-L-1626215 2026-10-20 (merge of deliver/G2/Sheaf.SixFunctors.FieldTensor)
