# CategoryTheory.RingedHomUniverses.LeftFormula

## Reason

Remove the identity Hom map induced by the canonical degree identification of a shifted
complex. For the equality proof `rfl`, `shiftFunctorObjXIso` is the identity isomorphism;
`homObjMap_id` and `Category.comp_id` therefore make the two predicates equivalent.
This keeps the unsigned target reindexing and the signed source reindexing unchanged.
The redundant map forced expensive unfolding of the concrete sheaf Hom construction
when specializing the abstract product argument. Public declaration signatures and
all target statements stay verbatim. Because these predicates specify target-facing
normalizations, the independent statement review should check this equivalence too.


The local predicate now names `homComplexπ` directly. This is the same fixed
projection: `homComplex_projections_exists` is proved by applying
`Classical.choose_spec` to `homComplex_exists`, exactly the existence specification
selected by the original `coefficientHomComponent`. Proof irrelevance identifies
the existence proofs. This local change avoids changing the shared coefficient
projection definition and removes the need to adapt its consumers. The source
API is publicly imported because these predicate definitions use it. Its
signatures and statements introduce no additional assumptions.

## Old

```lean
def LeftFormula (L F : Complex.{c, v, r} J R) (s : ℤ)
    (e : (complexHom.{c, v, r} J R L F)⟦-s⟧ ≅ complexHom.{c, v, r} J R (L⟦s⟧) F) : Prop :=
  ∀ (k p q : ℤ) (h : p + k = q),
    e.hom.f k ≫ WeilConjectures.coefficientHomComponent.{r, c, v} J R (L⟦s⟧) F k p q h =
      (s * k).negOnePow •
        (WeilConjectures.coefficientHomComponent.{r, c, v} J R L F (k + -s) (p + s) q
          (by omega) ≫ SheafOfModules.homObjMap (R := R)
            (L.shiftFunctorObjXIso s p (p + s) rfl).hom (𝟙 (F.X q)))
```

## New

```lean
def LeftFormula (L F : Complex.{c, v, r} J R) (s : ℤ)
    (e : (complexHom.{c, v, r} J R L F)⟦-s⟧ ≅ complexHom.{c, v, r} J R (L⟦s⟧) F) : Prop :=
  ∀ (k p q : ℤ) (h : p + k = q),
    e.hom.f k ≫ homComplexπ.{c, v, max c v r, max c v r} (R := R) (L⟦s⟧) F k p q h =
      (s * k).negOnePow •
        (homComplexπ.{c, v, max c v r, max c v r} (R := R) L F (k + -s) (p + s) q
          (by omega))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses | S6 | Complete the normalized shift proof using the equivalent projection formula. |

`tools/downstream.py --uses` finds this as the only textual user. No other
consumer needs adaptation and no public signature changes.

## Status

landed 20261020T221346-L-4177964 2026-10-20 (merge of deliver/S6/Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses)
