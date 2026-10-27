# WeilConjectures.isomorphismFieldTransportCommonStage

## Reason

Close the assigned common-stage transport proof. The static interface detector flags
new section, open and local attribute commands. They support the proof and do not
change any existing signature, public import, global instance or global attribute.
The new irreducibility attributes are local to this module and prevent elaboration
from unfolding the large chosen pullback functors. The section variables generalize
private helpers only. Added proof imports are private.

## Old

```lean
theorem isomorphismFieldTransportCommonStage
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [IsNoetherian X] [IsNoetherian Y]
    (hDimX : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (hDimY : ∃ n : ℕ, topologicalKrullDim Y ≤ n)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (S : ∀ E : Index l Ω,
      IsomorphismFieldTransportStage l (Coefficient.{u} l Ω E) g hX hY)
    (R : ∀ E : Index l Ω,
      IsomorphismFieldTransportStage l (Coefficient.{u} l Ω E) (inv g) hY hX)
    (hS : ∀ (E L : Index l Ω) (h : E ≤ L),
      isomorphismFieldTransportRationalScalarLaw l
        (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h) g hX hY (S E) (S L))
    (hR : ∀ (E L : Index l Ω) (h : E ≤ L),
      isomorphismFieldTransportRationalScalarLaw l
        (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h) (inv g) hY hX (R E) (R L)) :
    Nonempty (IsomorphismFieldTransportCommon l Ω g hX hY S)
```

The proof was `by sorry`. The original public imports are
`Sheaf.Paper.IsomorphismFieldTransportClauses` and `Mathlib.AlgebraicGeometry.Noetherian`.

## New

```lean
theorem isomorphismFieldTransportCommonStage
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [IsNoetherian X] [IsNoetherian Y]
    (hDimX : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (hDimY : ∃ n : ℕ, topologicalKrullDim Y ≤ n)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (S : ∀ E : Index l Ω,
      IsomorphismFieldTransportStage l (Coefficient.{u} l Ω E) g hX hY)
    (R : ∀ E : Index l Ω,
      IsomorphismFieldTransportStage l (Coefficient.{u} l Ω E) (inv g) hY hX)
    (hS : ∀ (E L : Index l Ω) (h : E ≤ L),
      isomorphismFieldTransportRationalScalarLaw l
        (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h) g hX hY (S E) (S L))
    (hR : ∀ (E L : Index l Ω) (h : E ≤ L),
      isomorphismFieldTransportRationalScalarLaw l
        (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h) (inv g) hY hX (R E) (R L)) :
    Nonempty (IsomorphismFieldTransportCommon l Ω g hX hY S)
```

The signature and both public imports are verbatim unchanged. The proof constructs
its stage comparison, prescribed shift, exactness, equivalence and epsilon, and uses
the existing object and representative specifications. Three new proved modules
provide normalized quotient descent, epsilon naturality and shift descent. Their
public declarations are new; no adopted source-library declaration is altered.
No hypothesis or target statement changes.

## Users

`tools/downstream.py --uses isomorphismFieldTransportCommonStage` reports only the
item and its direct parent as textual declaration users (among the transitive
importers). No importer needs adaptation because the existing interface is unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IsomorphismFieldTransportCommonStage | Q9 | Complete proof; unchanged signature and public imports. |
| Sheaf.Paper.IsomorphismFieldTransport | unclaimed in local snapshot | Existing application keeps exactly the same type; no edits. |
| Sheaf.Paper.CommonStagePullbackNormalizedDescent | new in Q9 delivery | Proved normalized quotient identification and its explicit comparison definition. |
| Sheaf.Paper.IsomorphismFieldTransportEpsilonNaturality | new in Q9 delivery | Proved naturality of the prescribed own-stage epsilon. |
| Sheaf.Paper.IsomorphismFieldTransportShiftDescent | new in Q9 delivery | Proved descent and restriction compatibility of the supplied shifts. |

## Status

landed 20261027T103510-L-1090992 2026-10-27 (merge of deliver/Q9/Sheaf.Paper.IsomorphismFieldTransportCommonStage)
