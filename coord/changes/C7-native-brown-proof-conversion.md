# Sheaf.Paper.NativeGeometricBrownConstructibleComparison: proof conversion

## Reason

The published module is already slow, independently of this delivery: the reviewer compiled
the unchanged published file with lcompile against the published build (74.9 s, 74.0 s CPU)
and against the delivered data, item and split modules (75.9 s, 74.9 s CPU), both over the
60-second limit. The adaptation is therefore not forced by the relocation; it is a
proof-speed repair of an unclaimed module, accepted by the reviewer (2026-10-27) because it
changes no statement, signature, public attribute, import or definition body and brings the
module to 8.9 s against the delivery. The cost was in one `refine` step. Two file-local
irreducibility declarations keep the private generic adjunction constructors and the standard
derived-category construction from unfolding during the native proof. The same proof then
exposes a reflexive source-Hom type equality in its `convert`; it is discharged before the
existing pointwise transpose argument. No mathematical route changes.

The module was unclaimed at the audit. The edit adds no theorem, hole or instance; the local
attributes do not leave the file.

## Old

The private adjunction helpers and the standard derived-category construction had no
local irreducibility declarations in this file. The affected proof fragment was:

```lean
      convert (e₁.trans ((adj.homEquiv Ac M).symm.trans
        (e₃.trans ((ambientAdj.homEquiv _ _).trans e₂)))).bijective using 1
      funext a
      exact congrArg (fun f ↦ f.hom) (htranspose Ac M (e₁ a))
```

## New

Before the native declarations, use these file-local proof settings:

```lean
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] transportLeftIso transportAdj
```

The proof fragment is:

```lean
      convert (e₁.trans ((adj.homEquiv Ac M).symm.trans
        (e₃.trans ((ambientAdj.homEquiv _ _).trans e₂)))).bijective using 1 <;> try rfl
      all_goals
        funext a
        exact congrArg (fun f ↦ f.hom) (htranspose Ac M (e₁ a))
```

Every existing declaration signature and public definition body is verbatim unchanged.
The private helpers still have the same definitions. Only the proof elaboration context
and the explicit conversion subgoals change.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NativeGeometricBrownConstructibleComparison | unclaimed | local proof opacity and explicit reflexive conversion goals; public interface unchanged |
| Sheaf.WeilSheaf.CompactSupportBrownConstructibility | unclaimed | sole direct importer; checked unchanged against the repair |

## Status

landed 20261027T021303-L-2752918 2026-10-27 (merge of deliver/C7/Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization)
