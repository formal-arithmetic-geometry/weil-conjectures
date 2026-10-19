# Stage 1 report: lem-coef-arrow-target-cartesian-pullbacks

## Files written

- `dag/nodes/sec-six-functors/lem-coef-arrow-target-cartesian-pullbacks.json`: repaired statement node and four-step proof; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-infinity-cartesian-mapping-criterion.json`: existing unsplit prerequisite, with its HTT source wording corrected to the Cartesian form.
- `dag/nodes/sec-six-functors/lem-coef-infinity-space-cospan-limit-path-pullback.json`: new unsplit statement-only prerequisite; no Mathlib match.
- `citations.json`: verbatim statement quotes for every cited node in every item step.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, blueprint tag, declaration names, and target-evaluation/Cartesian-pullback phrases; no sorry-free project declaration states the item.

## WANTED

WANTED: archival copies of Lurie, *Higher Topos Theory*, Lemma 6.1.1.1 and Proposition 2.4.4.3, and Kerodon Proposition 3.4.1.11 (Tag 0110). The cited pages were read online on 2026-10-17.

## Not duplicates

- `lem-coef-infinity-space-cospan-limit-path-pullback` vs `lem-coef-infinity-homotopy-pullback-pasting`: the new node identifies the path-space model as a cospan limit; the existing node pastes already specified homotopy-pullback squares.
- `lem-coef-infinity-space-cospan-limit-path-pullback` vs `lem-coef-infinity-arrow-morphism-square`: the existing node computes mapping spaces in an arrow quasicategory; the new node states the universal property of the path-space cospan model in spaces.
- `lem-coef-arrow-target-cartesian-pullbacks` vs `lem-coef-infinity-cartesian-mapping-criterion`: the item constructs and characterizes target-evaluation Cartesian edges; the prerequisite is the general iff criterion for one edge of an arbitrary inner fibration.

## What was wrong or corrected

The returned version overclaimed transport on all coherent slice categories and transformations. I removed the unsupported coherent-slice terminology and restricted the conclusion to the objectwise Cartesian lift over a base arrow. Step 1 now describes the fiber only as the degreewise pullback of target evaluation. Steps 2 and 3 explicitly cite the existing homotopy-pullback pasting lemma and the new path-space cospan-limit node, covering the two reductions that had previously been hidden. The mapping-criterion source now cites HTT Proposition 2.4.4.3 in its Cartesian form rather than calling it an opposite-category dual. No hypothesis on terminal objects, presentability, or a global choice of pullbacks was added.

## Review by Q41

I reread the item, the fixed chapter and unit records, the blueprint ancestry, and the online HTT Lemma 6.1.1.1 proof. I checked the archived source tree for an exact completed declaration and found none. I searched the whole DAG and blueprint for arrow-target Cartesian fibrations, path-space cospan limits, mapping criteria, and homotopy-pullback pasting before retaining the existing prerequisites and creating the one new node.

Step 1 uses `lem-cbc-enhanced-functor-cone-calculus` for functor quasicategories, `lem-coef-infinity-isofibration-exponentiation` for exponentiation along the endpoint inclusion, and `def-coef-infinity-fibrations` for inner fibrations and degreewise fibers. These statements support the target-evaluation inner fibration and its fiber of arrows with fixed target, including higher simplices.

Step 2 uses `lem-coef-infinity-arrow-morphism-square` for the arrow mapping-space formula, `lem-coef-infinity-space-cospan-limit-path-pullback` for identifying the path-space model with the cospan limit in spaces, and `lem-coef-infinity-homotopy-pullback-pasting` for the comparison pastings. `lem-coef-infinity-yoneda-presheaf-limits` supplies the mapping-space characterization of a limiting cone, while `lem-coef-infinity-cartesian-mapping-criterion` converts the resulting homotopy-pullback square into Cartesianity. The cospan hypothesis is used exactly to choose the limiting cone on $z\to c\leftarrow c'$.

Step 3 applies the same cited statements to a Cartesian coherent square and tests it on every identity arrow $1_w$. The arrow formula reduces the criterion to the mapping-space tests for the square in $C$; the path-space model and pasting lemma justify the homotopy-pullback identification; the Yoneda/limit criterion then proves the square is a pullback cone. I checked the orientations of target evaluation and all four square edges.

Step 4 now states only the objectwise conclusion actually supported by Step 2: the constructed pullback projection is the Cartesian lift over $f$ with target $z\to c$. It makes no claim about transformations or higher coherent transport. The only cited definition is `def-coef-infinity-fibrations`, whose Cartesian-fibration clause supplies the terminology.

For the new path-space node I checked the cospan statement against Kerodon Tag 0110, searched the DAG and blueprint for duplicates, and ran LeanFinder, Loogle, grep, and LeanSearch. The Mathlib hits were ordinary-category pullbacks or model-category path objects, so the node remains an unsplit non-Mathlib statement. For every item step, `citations.json` quotes the complete statement text of each cited node verbatim. No Lean files, compiler, Lake, or build tools were run.
