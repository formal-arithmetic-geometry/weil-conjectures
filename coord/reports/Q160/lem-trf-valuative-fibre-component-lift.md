# Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-valuative-fibre-component-lift.json` — split statement, four proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-valuation-ring-specialization-lift.json` — statement-only dependency, attached to the closed project declaration `AlgebraicGeometry.Scheme.exists_valuationSubring_of_specializes`.
- `citations.json` — verbatim quotes for every cited node in every proof step.

Attachments:

- `AlgebraicGeometry.Scheme.exists_valuationSubring_of_specializes` belongs to `lem-trf-valuation-ring-specialization-lift` (`WeilConjectures/Mathlib/AlgebraicGeometry/ValuativeCriterion.lean:218`, proof through line 238, no `sorry`).

WANTED: none.

I read Stacks Project `more-morphisms.tex`, Tag 0GSH (`lemma-make-base-change`) including its full proof, and the project specialization theorem used for its valuation-ring input. The item statement retains all four source clauses: arbitrary scheme morphism, reduced closure of `y`, a chosen generic point of a fibre component, valuation base, generic-fibre component lift, and special-fibre component lift. I found no exact declaration for the item itself in either read-only Lean source checkout. The only existing DAG result with the same valuation-specialization content was the closed project theorem recorded as the new dependency; no duplicate node or blueprint node states the combined component-lifting lemma.

No statement correction was needed. The generic point `y` is the generic point of the irreducible fibre `Y_t` because every point of that fibre lies in the closure of `y`; this is used explicitly when proving `g'(y') = y`. The base-change section comes from the fibre-product universal property. For the special fibre, the chosen component containing the section's closed-point image supplies `x'`; its image specializes to `x`, and genericity of `x` in its component forces equality. Small cases checked were `X=Y=Spec(k[t])` with `y` generic and `x` the closed point, the identity morphism (taking `A` to be the valuation ring supplied by the specialization theorem), and the case `s=t` where the generic and closed fibres coincide. The valuation-ring theorem's Lean statement was checked line by line against its node and its proof is complete.

## Review by Q160

I checked the item against Tag 0GSH clause by clause and read all three source proof paragraphs. Step 1 uses exactly the specialization-to-valuation-ring statement of `lem-trf-valuation-ring-specialization-lift`; its hypotheses are met because `x` lies in the closure of `y`. Step 2 uses the stated fibre-product and base-change universal properties to form `X'` and the section, and the factorization through `Y` is the closure definition. Step 3 uses the definitions of scheme fibre, irreducible component, and generic point; the component is chosen through `σ(t')`, and the source's genericity argument gives `g'(y')=y`. Step 4 uses the same definitions after taking the reduced closure `Y'`; the component through `σ(s')` gives `x'`, and the specialization plus genericity argument gives `g'(x')=x`. I opened each cited node and copied the exact statement text into `citations.json`; every proof dependency is the union of the step uses. The new dependency is strictly smaller than the item, carries no proof or hollow data, records all required Mathlib searches, and its Lean declaration is closed and sorry-free. No SGA source, altered hypothesis, duplicate, cycle, or hidden long lemma was introduced.

What was corrected from the imported node: the imported unsplit item had no proof or citation record. I added the four source-directed steps, the closed valuation-specialization dependency, exact blueprint ancestry, and the required citation quotes while preserving the imported statement and search results.

## Not duplicates

lem-trf-valuation-ring-specialization-lift vs lem-coef-infinity-lax-comma-target-fibration: the former is a scheme-theoretic valuation-ring realization of a specialization (Stacks 01KE); the latter is a quasicategorical lax-comma cocartesian-fibration theorem and its 01KE reference is a Kerodon label, so the statements have different objects and conclusions.

lem-trf-valuation-ring-specialization-lift vs lem-trf-proper-geometric-specialization-lift: the former constructs a valuation-ring morphism for an arbitrary specialization of two scheme points; the latter lifts a prescribed étale-topos geometric specialization through a proper surjective morphism after extending algebraically closed residue fields, with no valuation-ring conclusion.
