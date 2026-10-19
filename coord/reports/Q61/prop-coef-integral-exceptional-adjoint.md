# Worker report: prop-coef-integral-exceptional-adjoint

## Files written

- `dag/nodes/sec-six-functors/prop-coef-integral-exceptional-adjoint.json`: copied the existing seven-step stage-1 split and marked it `split`; no statement or dependency was changed.
- `citations.json`: 42 verbatim statement quotations, one for every cited node in every proof step.
- No new DAG nodes were created: every helper used by the split already exists in `dag/nodes/sec-six-functors/` or another chapter of the shared DAG.

## Attachments

None. The project declaration `AlgebraicGeometry.Etale.boundedConstructibleIntegral_exceptionalAdjoint` in `WeilConjectures/SixFunctors/Etale/Derived/IntegralCoefficients.lean:321` still contains `sorry`, so it is not an attachment under the stage-1 rule.

## WANTED

None.

## What was checked and corrected

The item statement and proof were read against `dag/nodes/sec-six-functors/prop-coef-integral-exceptional-adjoint.json`, the unit `dag/units/sk-prop-sf-biduality-general.json`, the chapter `dag/chapters/sec-six-functors.json`, and the blueprint source `literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/prop-coef-integral-exceptional-adjoint.md`. The item keeps the separated finite-type hypotheses, the completed coefficient tower, the finite exceptional functors, the completed pullback and Verdier dual, the reduction isomorphisms, the adjunction, and the stated Tor interval. No coefficient category was silently identified with another one.

No source, DAG, or Lean statement error was found. The shared split already repaired the earlier reconstruction and mapping-complex issues; this delivery preserves those repairs. In particular, it uses the specified reduction/limit calculus and normalized-tower effectivity to construct the actual reconstruction unit, and it forms the finite enriched exceptional comparison before taking the derived inverse limit. It does not invoke an arbitrary lift from evaluated maps or an unproved integral Hom/tensor base-change theorem.

## Review by Q61

I read the statement of every node cited by each step and copied each exact statement into `citations.json`; all 42 `(step, node)` pairs have a verbatim quote. Step 1 uses the integral Verdier theorem for constructibility and duality bounds, completed-pullback preservation, and pullback Tor-amplitude preservation. Step 2 uses the coherent reduction/limit adjunction, normalized-DVR effectivity, the integral constructible triangulated category, exact derived reduction, the Roos completeness definition, and the zero-cone criterion; these statements supply the claimed reconstruction isomorphism and its hypotheses. Step 3 uses the finite-adjunction diagram realization, coherent evaluation calculus, finite exceptional coefficient-change maps, integral Verdier and completed-pullback preservation, normalized effectivity, the integral dualizing object, and the completed-pullback definition; their statements provide every constituent of the displayed natural system isomorphism. Step 4 uses the evaluation calculus, the derived scalar-extension/restriction adjunction, and the global derived-Hom identification, which exactly give the mapping-complex comparison and its projections. Step 5 uses integral compact-support reduction, etale-origin and site-comparison results, finite-type Noetherianity and Nagata compactification, the ordinary finite exceptional adjunction, compact-support comparison, the exceptional-inverse-image definition, global Hom comparison, finite exceptional compatibility, the coherent diagram realization and effectivity, derived pushforward composition, and the dimension bound; I checked the finite-type, boundedness, and Tor hypotheses where each is applied. Step 6 applies total derived inverse limit to that actual system map and uses the same calculus, finite adjunction data, and Roos triangle to define the unit, counit, triangle identities, and their finite reductions. Step 7 specializes the defining tower for the structure morphism and checks that it is the same tower as the integral dualizing object.

I also inspected the two mechanically long steps (3 and 5, each over 2000 characters) for hidden sublemmas. Step 3 is a single explicit composition of the cited natural isomorphisms (with the variance of the dual spelled out), and step 5 is the one finite enriched comparison followed by its strict-system transport; no additional independent claim is hidden beyond the cited node statements. Empty schemes and zero dimension bounds are handled in the cited dimension and finite-exceptional statements. The recorded Mathlib searches for the item were rerun with `msearch.py`; they found no Mathlib declaration of this project-specific proposition.
