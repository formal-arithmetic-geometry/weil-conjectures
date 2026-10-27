# Finite-span comparison declaration placement

## Reason

The scalar transport construction must be a separate stage-3 item. Its statement uses
Data and the fixed operations, while the main theorem uses that construction. Move
the existing definitions to a data module to avoid an import cycle. All 25 existing names and signatures, instance registrations and reducibility
attributes are retained. Of their bodies, 21 are byte-identical. The predicates
Properties and ExchangeProperty factor their final field formulas through two new
scheme-level abbreviations, DerivedNormalization and ExchangeEquation. Each abbreviation
is exactly the corresponding original formula, with the scheme arguments abstracted;
every field, finiteness, characteristic, square and complex binder is retained.
The existing module publicly imports the data module. The main theorem statement is unchanged.
No target changes meaning, and no datum is chosen from an unproved existence statement.
Private local irreducibility in the main proof only keeps the derived-functor formulas
from being expanded during categorical pasting; it changes no exported attribute.

The internal and native derived adjunction abbreviations keep their canonical defining
expressions. The exchange maps and normalization formula use these shared names.

## Old

The declarations from `nativeAb` through `ExchangeProperty` were defined in
`Sheaf.Paper.FiniteSpanModuleDerivedComparison`. For example, verbatim:

```lean
def equivalence (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [IsCommMonObj (nativeAb l X)]
    (theta : condensedRingObj (Profinite.padicAlgClRingObj l) X ≅ nativeAb l X)
    [IsMonHom theta.hom] : internal l X ≌ modules l X :=
  (Mod.comapEquivalenceOfIsIso theta.inv).trans (nativeEquivalence l X)
```

## New

The same block is defined in `Sheaf.Paper.FiniteSpanModuleComparisonData`,
with every signature unchanged and 21 bodies byte-identical to the original.
The final formulas of Properties and ExchangeProperty use the new abbreviations.
internalExchange and nativeExchange share the named canonical derived adjunctions;
their defining expressions are unchanged. For example, verbatim:

```lean
def equivalence (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [IsCommMonObj (nativeAb l X)]
    (theta : condensedRingObj (Profinite.padicAlgClRingObj l) X ≅ nativeAb l X)
    [IsMonHom theta.hom] : internal l X ≌ modules l X :=
  (Mod.comapEquivalenceOfIsIso theta.inv).trans (nativeEquivalence l X)
```

The normalization formula is now elaborated for an arbitrary scheme morphism as
DerivedNormalization, and the exchange formula for an arbitrary square as ExchangeEquation.
Properties retains its field-normalization binders and applies DerivedNormalization to f.left.
ExchangeProperty retains all of its binders and applies ExchangeEquation to s and K.
The split construction uses the same DerivedNormalization abbreviation.
The canonical DerivedComparisonFrame uses the actual derived category universe levels,
objects u+2 and morphisms u+1, with no redundant universe parameters. It is constructed
explicitly from the existing
derived categories, functors, adjunctions, compositors and comparison maps. Both the
normalization mate and exchange formula specialize MateCondition and PullbackExchangeCondition,
which are stated on an abstract bundle. PullbackExchangeCondition extracts s.toCommSq
there and applies ExchangeCondition. Their category instances are its projections,
without reconstructing fresh derived-category instances at specialization. Expanding
the projections recovers the original formulas. The exchange object binder uses the
bundle's C field, which is literally the original internal derived category. No
operation, assumption, comparison map or object range is changed. The frame projection
instances are registered locally during elaboration, adding no exported instance attribute.

This prevents field-dependent auxiliary instance wrappers. Diagnostic comparison found
Properties._proof_19 (commutativity), _proof_20 (sheafification), _proof_21 (locally
bijective morphisms) and _proof_38 (Grothendieck abelianity) being compared with the
canonical scheme-level instances. Kernel checking repeatedly unfolded sheafification
choices and hit its deterministic budget although elaboration was fast. The new
abbreviations fix those instances before introducing the field binders. Their formulas
are literal abstractions of the old formulas, so this changes neither the assumptions
nor the conclusions. Reducibility of every existing operation is retained.

The original module's public interface is supplied by:

```lean
public import Sheaf.Paper.FiniteSpanModuleComparisonData
```

All of its earlier public imports are retained transitively through that module.
The main theorem now invokes the supplied-theta scalar transport theorem, fills the
chart and coefficient-square clauses from the proved coefficient realization theorem,
and proves the exchange assertion by localized compositor pasting and exchangeMate_cube.

## Users

| module | delivery action | effect |
| --- | --- | --- |
| Sheaf.Paper.NativeEncodingDerivedOperations | verification only | Same names, signatures and instance attributes; two predicate formulas factored; re-exported through the data module. No consumer edit. |
| Sheaf.Paper.NativeForgetConstructibleCriterion | transitive name search | Same names, signatures and instance attributes; two predicate formulas factored; re-exported through the data module. No consumer edit. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | verification only | Same names, signatures and instance attributes; two predicate formulas factored; re-exported through the data module. No consumer edit. |
| Sheaf.WeilSheaf.NativeProperNaturalBaseChange | verification only | Same names, signatures and instance attributes; re-exported definitions. No consumer edit. |

The direct importers are NativeEncodingDerivedOperations, NativeWeilScalarFrobeniusCounit
and NativeProperNaturalBaseChange. The third appeared during this session and is included
in the final verification. NativeForgetConstructibleCriterion is a transitive user.
The downstream name search finds only an unrelated short-name `adjunction` occurrence
in NativeWeilScalarFrobeniusCounit. All three direct consumers are checked unchanged against
the delivered overlay; none is included in the delivery.

## Status

landed 20261026T222606-L-671605 2026-10-26 (merge of deliver/C8/Sheaf.Paper.FiniteSpanModuleDerivedComparison)
