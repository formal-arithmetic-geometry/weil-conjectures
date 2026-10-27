# RationalPurityPresentation scalar-model relocation

## Reason

New finite-adjunction and exact-descent obligations need the existing scalar models
without importing the final theorem which uses those obligations. Move the already
proved prefix through pbcPurityStageC to RationalPurityScalarModels and publicly
re-export it. No signature, definition body, theorem proof, attribute or visibility
of the relocated declarations changes. This is a dependency separation for the proof.

## Old

The relocated primary declaration has this verbatim signature:

```lean
def pbcPurityCoefficientChange :
    PurCompactSupport.Change (pbcPurityCoefficients l E) (pbcPurityCoefficients l F)
```

It and the other declarations pbcPurityAmbientProperties through pbcPurityStageC
occur in lean/Sheaf/Paper/RationalPurityPresentation.lean. Their exact source is
the unchanged prefix of that module, including private fraction-naturality and
inverse-normalization helpers. The node lists every relocated public declaration.

## New

The signature is unchanged:

```lean
def pbcPurityCoefficientChange :
    PurCompactSupport.Change (pbcPurityCoefficients l E) (pbcPurityCoefficients l F)
```

The exact declaration prefix occurs in lean/Sheaf/Paper/RationalPurityScalarModels.lean,
closed by end AlgebraicGeometry.Scheme. The item publicly imports the new module.
Every signature and body in the moved prefix is byte-for-byte identical. The
descent and Karoubi public imports remain visible through the presentation-data
module; the new scalar API needs only PbcScalarExtension from that part of the
original import interface.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RationalPurityPresentation | A2 | Public re-export; unchanged signatures and definitions |

The read-only downstream.py query reports zero downstream Lean modules. A separate
import search also finds zero direct importers. DAG parents remain intact, including
the theorem's Lean attachment and statement dependencies; no withdrawal is proposed.
No adopted source-library module changes.

## Status

landed 20261027T012758-L-2329497 2026-10-27 (merge of deliver/A2/Sheaf.Paper.RationalPurityPresentation)

## Further performance split

The unchanged coherence theorem, twisted-system construction and all five
presentation predicates also move to Sheaf.Paper.RationalPurityPresentationData,
publicly re-exported by the item. Their original public names, signatures and
bodies remain identical. The original coherence obligation is attached to
def-pur-rational-purity-presentation-data; it is neither closed nor duplicated.
The added Sheaf.Paper.RationalPurityIdentityDescent proves a formal specialization
of StageSystem descent with abstract bound hypotheses. This keeps the concrete
component calculation separate from geometric-bound terms in the final theorem.
No interface of another existing module is changed, and no consumer adaptation
is required.
