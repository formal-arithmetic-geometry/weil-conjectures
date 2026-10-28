# AlgebraicGeometry.ProEtale.CondensedRing.smoothTrace

## Reason

Continue the declared native reconstruction argument and certify the missing trace
normalization. The current `existsUnique_smoothTrace` predicate asks only for Hom
bijections; a nontrivial automorphism of the representing object preserves those
bijections. Its existing disputed diagnosis therefore also affects the choice
made by the source definition. The counterexample uses the actual bounded
constructible unit and compact-support adjunction of a geometric point.

This is partial proof work. It does not claim to repair that definition or the
false unconditional purity instance. All existing public declaration signatures,
attributes, public imports, instances and non-theorem bodies remain verbatim.
The upstream exception table does not authorize changing the missing smoothness
binder. No target statement or meaning is changed by this delivery.

## Old

The item had no private declarations named
`smoothTrace_normalizedIntegralSystem`,
`smoothTrace_reconstructedInverseSemilinearSquare`, or
`smoothTrace_representing_not_unique_at_point`.

The module `Sheaf.SmoothPurity.TraceNonuniqueness` did not exist. Seven generic
private calculation helpers also did not exist. The existing concrete counit,
inverse-square and composite-adjunction proofs repeatedly rewrote the large
geometric terms. The open-normalization proof used broad simplification.

The public purity instance is unchanged:

```lean
instance isIso_smoothPurityMap : IsIso (smoothPurityMap ℓ f d) :=
  sorry
```

## New

The new private integral-system lemma retains the actual strict Tate and unit
towers, their level comparisons, both projection normalizations, both
reconstruction assertions, the exceptional identification and all inverse quotient
squares. Witnesses are extracted only inside the proof. The new semilinear-square
lemma transposes the inverse coefficient-linear equation under the actual scalar
adjunction. Two reconstruction predicates are locally irreducible while extracting
the reconstruction package; these attributes do not escape their section.

Add the completely proved module `Sheaf.SmoothPurity.TraceNonuniqueness`, exposing
`AlgebraicGeometry.ProEtale.CondensedRing.not_existsUnique_representing_trace_at_point`.
Its statement is recorded verbatim in the new node
`lem-pur-geometric-point-trace-not-unique`. All other helpers in that new module are
proved and private. Its generic representing-pair proof reuses the existing
`representing_trace_of_iso` proof verbatim. Its proof imports provide full
faithfulness of the single functor and the monoidal point comparison. The public statement supplies ordinary identity-map finiteness proofs as local
instances in its type, without exposing private helpers or adding assumptions.

The geometric-point proof evaluates the condensed sign at a singleton and the
section one, transports its inequality through faithful pullback and the faithful
single functor, and uses the actual open-unit comparison to construct distinct
representing traces. It uses neither the disputed trace theorem nor the disputed
purity instance. Privately import that module in the item and apply its theorem
before the disputed instance. Add a diagnostic comment at `smoothTrace`, preserving
its body. Update the owning node's proof, proof dependencies and proof origin.

The seven additional proved private helpers are `smoothTrace_map_unit_square`,
`smoothTrace_inverse_reduction_square`, `smoothTrace_semilinear_square`, and
`smoothTrace_composite_adjunct_square`, `smoothTrace_inverse_comparison_square`,
`smoothTrace_map_inverse_comparison_square`, and `smoothTrace_comp_eq_of_map_inv`.
The existing private
`smoothTrace_openUnit_counit`, `smoothTrace_openComposite_counit`,
`smoothTrace_reconstructedInverseQuotientSquare`, and
`smoothPurityMap_comp_of_trace_transitivity`,
`smoothPurityIso_comp_of_reconstructed_traces`, and
`smoothPurityIso_comp_of_trace_transitivity` now apply these abstract calculations.
Their signatures and mathematical proofs are unchanged. The public theorem
`smoothPurityIso_zero_of_isOpenImmersion` uses explicit branch rewriting and a
direct term conversion instead of broad simplification. Its existing dependence
on the disputed uniqueness theorem is retained; it is not claimed as new proof
progress. Locally keep `smoothTrace` irreducible to prevent implicit unfolding;
the public definition body and exported attributes are unchanged.

The combined file was profiled after exceeding 60 seconds. After reducing
unnecessary unfolding and using an explicit unit conversion, the self-contained
counterexample was moved to the new module; the brief permits this final split.
Further profiling after a 61.8-second run showed repeated categorical elaboration
and typeclass work. Following `Derived.UpperLowerStar`, keep the module monoidal
structures, internal Hom construction, point pullback and derived-functor
constructors locally irreducible in the Purity section. These attributes do not
escape the section; no public definition body or exported attribute changes.
There are no new holes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SmoothPurity.Defs | A2 | Ten proved private helpers; factor seven existing proofs; diagnostic comment. |
| Sheaf.SmoothPurity.TraceNonuniqueness | new in this delivery | One proved public counterexample, with private helpers. |
| Sheaf.Targets.SmoothPurityQbar | not queried; not adapted | Identical public interface and definitions. |
| WeilConjectures.PoincareDuality.Poincare | not queried; not adapted | Identical public interface and definitions. |
| WeilConjectures.TraceFormula.Dualizing | not queried; not adapted | Identical public interface and definitions. |
| TargetsCheck | not queried; not adapted | Identical target statements and imports. |
| WeilConjectures | not queried; not adapted | Identical public interface and definitions. |

These are all direct source importers. No existing module besides the item is
changed; no consumer adaptation or target-statement review is introduced.

## Status

landed 20261028T034647-L-3528504 2026-10-28 (merge of deliver/A2/WeilConjectures.SmoothPurity.Defs)
