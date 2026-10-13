## What changed

Completed `AlgebraicGeometry.Scheme.Modules.valuation_zero_section_relative_cartier` with its
original signature and public imports unchanged. Compare the chosen tensor-pullback adjunction
with ordinary pullback, deduce that the closed-fibre zero ideal is nonzero, and apply the proved
upstream locally principal integral ideal criterion. Properness and `fibre_cartier_local`
provide neighbourhoods on the support; the complement has unit ideal and empty subscheme.
Glue invertibility and flatness over this cover. Proof-only namespace openings and elaboration
options support the proof. The docstring describes the actual closed-fibre argument.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.Modules.valuation_zero_section_relative_cartier`
(node `lem-sc-valuation-zero-section-relative-cartier`). Holes added: none. No `sorry` remains
in the delivered module; no declarations were split off. This is one proof from existing
statements, rather than a decomposition. Its axiom check lists `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx`: imported statements, including `fibre_cartier_local`, remain open.
It is not yet an axiom-clean proof of the full dependency closure.

## No longer needed

Removed actual baseline proof-only imports:
- `Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier`;
- `WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme`.

Of the old `proof_deps`, `lem-pc-nonzero-section-integral-cartier` is no longer used; the
proved upstream tool `lem-pc-nonzero-locally-principal-ideal-invertible` replaces it. The
zero-scheme properties are used directly from `Modules.ZeroLocus`, so the aggregate
`Picard.ZeroScheme` import is unnecessary. All other old proof dependencies remain used.
No claim is made that these modules become globally unreachable from every target.

## Where the brief, the DAG or earlier work was wrong

The earlier report incorrectly named PullbackFreeGenerator and ProjectionFormula as the
removed baseline imports. The current baseline instead imports NonzeroSectionIntegralCartier
and Picard.ZeroScheme. The earlier report also said the DAG route was retained verbatim,
but no node update described the direct upstream integral-ideal argument. Both are corrected.
The earlier unqualified ideal-sheaf namespace opening failed outside AlgebraicGeometry;
the delivered opening is fully qualified. The preflight requires a change record for changed top-level namespace openings and
elaboration options, despite unchanged theorem semantics. The corrected record is
`coord/changes/valuation-zero-section-relative-cartier-open.md`.

## Second reading by W3

1. Compared the entire delivered module with the repository by `diff`. The only existing
   declaration's signature is byte for byte identical. No definitions, hypotheses, conclusions,
   or public imports changed; namespace openings and options affect proof elaboration only.
2. Compiled the module locally with `lcompile.py`, cleanly. Compiled a scratch copy with
   `#print axioms AlgebraicGeometry.Scheme.Modules.valuation_zero_section_relative_cartier`:
   only the three permitted axioms and `sorryAx` occur. No forbidden declaration or attribute,
   new definition, or literal `sorry` occurs in the delivered module. The chosen adjunction
   is the existing canonical unit-pinned adjunction; no arbitrary existence witness is introduced.
3. There are no new or split-off statements. Checked the integral locally principal ideal
   criterion in the upstream source; zero ideal is explicitly excluded, while the unit ideal
   is allowed. The empty-support case is explicitly handled by the complement branch.
4. Read the proof downward: its fibre step already uses a proved upstream criterion rather
   than a new hole. Searched the library for alternative valuation/Cartier results; no matching
   simpler full theorem was found. Kept the local fibre-Cartier route and specialization step.
   Read `dag/units/sk-prop-av-cube.json`: its `realized` lists are empty and this node is an
   auxiliary node, so the unit route is unchanged. Both removed imports are proof-only;
   remaining imports provide the statements or the local criterion. Pruning is reported above.
5. Repaired the existing node's `proof`, `proof_deps`, and `proof_origin` to match the actual
   adjunction comparison, direct integral-ideal criterion, specialization, and gluing.
   No new nodes are needed. The node statement, Lean signature record, unit, chapter, and
   all other metadata are unchanged.

Second reading changed the report and dependency proof metadata, and corrected the namespace-opening
change record required by the preflight. The compiling proof itself was retained.
