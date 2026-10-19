# Stage-1 report: lem-trf-formal-power-series-continuous-differentials

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-formal-power-series-continuous-differentials.json`: split statement with four proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-formal-power-series-continuous-free.json`: new unsplit statement; no exact Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-formal-power-series-continuous-conormal.json`: new unsplit statement; no exact Mathlib match.
- `dag/nodes/sec-trace-formula/def-trf-formal-power-series-partial-derivative.json`: new Mathlib leaf, `MvPowerSeries.pderiv` in `Mathlib/RingTheory/MvPowerSeries/Derivative.lean:118`.
- `citations.json`: verbatim statement quotes for every cited node in every item proof step.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by item id, formal-power-series terms, continuous-differential terms, and Jacobian terms; no project declaration states this item without `sorry`.

## WANTED

None. The cited Stacks sources are present locally in `literature/stacks-project/`.

## What was wrong or incomplete in the imported node

The imported item had no proof and did not define the formal partial derivative used in its Jacobian matrix. I added the Mathlib-backed derivative definition as a statement dependency and made the derivative termwise explicit in the item. The proof is split at the two genuine mathematical interfaces: the free continuous differential module of the ambient power-series ring and the continuous conormal exact sequence for a quotient. The final step is only the matrix/cokernel identification after these interfaces, so no new node restates the item's conclusion.

I searched the whole DAG and both blueprint snapshots for continuous conormal or formal-power-series differential nodes. The only related nodes were the ordinary Kähler differential definition, polynomial differential basis, and finite-level modulo-power comparison; none states either continuous lemma, so the two new unsplit nodes are not duplicates. The formal derivative node is a Mathlib leaf rather than a new proof node because `MvPowerSeries.pderiv` gives the exact derivation and coefficient formula.

## Not duplicates

- `lem-trf-formal-power-series-continuous-free` vs `lem-trf-completed-jacobian-differentials`: the former concerns only the ambient formal power-series ring's continuous differential basis; the latter concerns a completed local algebra and its Jacobian quotient comparison.
- `lem-trf-formal-power-series-continuous-conormal` vs `lem-weil-pbc-kahler-differentials-first-exact-sequence`: the former is an inverse-limit exact sequence for adic continuous differentials of a formal power-series quotient; the latter is the ordinary finite-level Kähler sequence for arbitrary ring towers.
- `def-trf-formal-power-series-partial-derivative` vs `def-weil-pbc-polynomial-partial-derivative`: the former differentiates multivariate formal power series termwise; the latter defines derivatives only on polynomial rings.

## Review by NG

I read the imported item and its source pointer, the unit `dag/units/sk-i-curve-zero.json`, the chapter record, and the Stacks passages in `literature/stacks-project/curves.tex` around Tag 0C4D and in `algebra.tex` for Tags 00RS, 00RX, and 02HQ. I also read the existing DAG statements for `def-weil-pbc-multivariate-power-series`, `def-weil-pbc-kahler-differentials`, `lem-weil-pbc-polynomial-ring-kahler-basis`, `lem-weil-pbc-kahler-differentials-mod-power-ideal`, and `lem-weil-pbc-kahler-differentials-first-exact-sequence` before deciding what could be cited.

Step 1 uses exactly the statement of `lem-trf-formal-power-series-continuous-free`: it supplies the free basis of the inverse-limit module and the derivative formula. Step 2 uses exactly the statement of `lem-trf-formal-power-series-continuous-conormal`: it supplies the right-exact sequence and the map on each relation `f_j`. Step 3 checks the coefficient formula from the free statement against the Mathlib leaf `def-trf-formal-power-series-partial-derivative`, so the relation map is the displayed Jacobian matrix after reduction modulo `I`. Step 4 uses the basis isomorphism and the exact sequence to identify the matrix cokernel with `\\widehat\\Omega_{R/F}` and checks the image of every standard basis vector. All hypotheses (`F` a field, `f_j` in the variable ideal, and the stated adic systems) are carried into the two new statements and match the item.

I tested edge cases at the statement level: for `n=0` the ambient ring is `F` and both modules are zero; for `I=0` the conormal map has zero source and the free basis statement gives the expected `D^{\\oplus n}`; for `I=(t_1,\\ldots,t_n)` the quotient is `F` and the Jacobian map has the expected identity columns. I checked every proof step's cited statement and recorded verbatim quotes in `citations.json`. No proof step exceeds 2000 characters, there is no cycle, and no SGA source or off-unit tool use is involved.

## What could not be finished

The two continuous statements are intentionally delivered as unsplit stage-1 nodes: they require the inverse-limit argument over truncated power-series quotients and are not stated by Mathlib. No Lean code or compiler was used, per the stage-1 instructions.

Additional tag-level duplicate checks required by preflight:

- `def-trf-formal-power-series-partial-derivative` vs `lem-trf-formal-power-series-continuous-differentials`: the definition gives the derivative operator; the item gives a quotient differential isomorphism.
- `def-trf-formal-power-series-partial-derivative` vs `lem-trf-completed-jacobian-differentials`: the definition gives the derivative operator; the existing node concerns completed local Kähler differentials and a Jacobian cokernel.
- `def-trf-formal-power-series-partial-derivative` vs `lem-trf-completion-kahler-differential-comparison`: the definition gives the derivative operator; the existing node compares completion with continuous differentials.
- `def-trf-formal-power-series-partial-derivative` vs `lem-trf-geometric-field-stalk-descent`: the definition gives the derivative operator; the existing node is a geometric field/stalk descent statement.
- `def-trf-formal-power-series-partial-derivative` vs `lem-trf-nodal-curve-lci-criterion`: the definition gives the derivative operator; the existing node characterizes nodal curves by an LCI and Jacobian condition.
- `def-trf-formal-power-series-partial-derivative` vs `lem-trf-nodal-normalization-adjunction`: the definition gives the derivative operator; the existing node is a normalization and adjunction statement for nodal curves.
- `def-trf-formal-power-series-partial-derivative` vs `lem-trf-nodal-point-local-criterion`: the definition gives the derivative operator; the existing node gives a pointwise nodal criterion.
- `def-trf-formal-power-series-partial-derivative` vs `lem-trf-rational-node-quadratic-completion`: the definition gives the derivative operator; the existing node identifies a completed quadratic node.
- `def-trf-formal-power-series-partial-derivative` vs `lem-trf-separable-closed-point-formal-presentation`: the definition gives the derivative operator; the existing node constructs a separable closed-point presentation and invokes a completed Jacobian theorem.
- `lem-trf-formal-power-series-continuous-conormal` vs `lem-trf-formal-power-series-continuous-differentials`: the new node is only right exactness of the continuous conormal sequence; the item asserts the resulting Jacobian cokernel isomorphism.
- `lem-trf-formal-power-series-continuous-conormal` vs `lem-weil-pbc-kahler-differentials-polynomial-extension`: the new node is an inverse-limit adic conormal sequence for formal power series; the existing node concerns ordinary polynomial extension.
- `lem-trf-formal-power-series-continuous-conormal` vs `lem-weil-pbc-simple-transcendental-differential-decomposition`: the new node is an adic quotient sequence; the existing node decomposes differentials for a simple transcendental field extension.
- `lem-trf-formal-power-series-continuous-conormal` vs `lem-trf-completion-kahler-differential-comparison`: the new node gives quotient exactness for formal series; the existing node compares a local ring's completion with continuous differentials.
- `lem-trf-formal-power-series-continuous-conormal` vs `lem-weil-pbc-kahler-differentials-mod-power-ideal-bijective`: the new node takes an inverse limit over all powers and a formal-series quotient; the existing node is one finite-level bijectivity statement.
- `lem-trf-formal-power-series-continuous-conormal` vs `lem-weil-pbc-kahler-differentials-mod-power-ideal`: the new node is the full continuous conormal exact sequence; the existing node compares differentials modulo one fixed power.
- `lem-trf-formal-power-series-continuous-free` vs `lem-trf-formal-power-series-continuous-differentials`: the new node gives the ambient free module and derivative formula; the item adds quotient relations and identifies their cokernel.
- `lem-trf-formal-power-series-continuous-free` vs `def-weil-pbc-polynomial-partial-derivative`: the new node concerns inverse-limit differentials of formal series; the existing node defines polynomial partial derivatives.
- `lem-trf-formal-power-series-continuous-free` vs `lem-weil-pbc-kahler-differentials-polynomial-extension`: the new node is a continuous formal-series basis; the existing node is an ordinary polynomial extension result.
- `lem-trf-formal-power-series-continuous-free` vs `lem-weil-pbc-naive-cotangent-complex-cokernel-kahler`: the new node gives a free continuous differential module; the existing node identifies a cokernel of a naive cotangent complex with ordinary Kähler differentials.
- `lem-trf-formal-power-series-continuous-free` vs `lem-weil-pbc-polynomial-ring-kahler-basis-any-variables`: the new node is an adic inverse-limit result for formal series; the existing node is a polynomial-ring basis theorem.
- `lem-trf-formal-power-series-continuous-free` vs `lem-weil-pbc-polynomial-ring-kahler-basis`: the new node is a formal-series continuous basis; the existing node is the ordinary polynomial basis and derivative formula.
- `lem-trf-formal-power-series-continuous-free` vs `lem-weil-pbc-simple-transcendental-differential-decomposition`: the new node concerns formal-series adic differentials; the existing node concerns a transcendental field extension.
- `lem-trf-formal-power-series-continuous-free` vs `lem-weil-pbc-smooth-conormal-chart-differential-basis`: the new node is a global formal-series inverse-limit basis; the existing node is a localized smooth conormal chart basis.
- `lem-trf-formal-power-series-continuous-free` vs `lem-trf-completion-kahler-differential-comparison`: the new node computes the ambient formal-series module; the existing node compares completion of a finite-type local algebra with continuous differentials.
- `lem-trf-formal-power-series-continuous-free` vs `lem-weil-pbc-kahler-differentials-mod-power-ideal-bijective`: the new node is the limit free-basis theorem; the existing node is finite-level transition bijectivity.
- `lem-trf-formal-power-series-continuous-free` vs `lem-weil-pbc-kahler-differentials-mod-power-ideal`: the new node computes the inverse-limit module; the existing node compares a single quotient level modulo a power.

Plain pair records for duplicate audit:
def-trf-formal-power-series-partial-derivative vs lem-trf-formal-power-series-continuous-differentials: derivative definition versus quotient Jacobian theorem.
def-trf-formal-power-series-partial-derivative vs lem-trf-completed-jacobian-differentials: derivative definition versus completed local Jacobian comparison.
def-trf-formal-power-series-partial-derivative vs lem-trf-completion-kahler-differential-comparison: derivative definition versus completion comparison.
def-trf-formal-power-series-partial-derivative vs lem-trf-geometric-field-stalk-descent: derivative definition versus geometric stalk descent.
def-trf-formal-power-series-partial-derivative vs lem-trf-nodal-curve-lci-criterion: derivative definition versus nodal LCI criterion.
def-trf-formal-power-series-partial-derivative vs lem-trf-nodal-normalization-adjunction: derivative definition versus normalization adjunction.
def-trf-formal-power-series-partial-derivative vs lem-trf-nodal-point-local-criterion: derivative definition versus pointwise nodal criterion.
def-trf-formal-power-series-partial-derivative vs lem-trf-rational-node-quadratic-completion: derivative definition versus quadratic completion.
def-trf-formal-power-series-partial-derivative vs lem-trf-separable-closed-point-formal-presentation: derivative definition versus separable point presentation.
lem-trf-formal-power-series-continuous-conormal vs lem-trf-formal-power-series-continuous-differentials: conormal right exactness versus the final Jacobian isomorphism.
lem-trf-formal-power-series-continuous-conormal vs lem-weil-pbc-kahler-differentials-polynomial-extension: formal adic quotient versus ordinary polynomial extension.
lem-trf-formal-power-series-continuous-conormal vs lem-weil-pbc-simple-transcendental-differential-decomposition: adic quotient sequence versus transcendental field decomposition.
lem-trf-formal-power-series-continuous-conormal vs lem-trf-completion-kahler-differential-comparison: quotient exactness versus completion comparison.
lem-trf-formal-power-series-continuous-conormal vs lem-weil-pbc-kahler-differentials-mod-power-ideal-bijective: inverse-limit conormal sequence versus one finite-level bijection.
lem-trf-formal-power-series-continuous-conormal vs lem-weil-pbc-kahler-differentials-mod-power-ideal: inverse-limit conormal sequence versus one fixed-power comparison.
lem-trf-formal-power-series-continuous-free vs lem-trf-formal-power-series-continuous-differentials: ambient free module versus quotient Jacobian isomorphism.
lem-trf-formal-power-series-continuous-free vs def-weil-pbc-polynomial-partial-derivative: formal-series continuous basis versus polynomial derivative definition.
lem-trf-formal-power-series-continuous-free vs lem-weil-pbc-kahler-differentials-polynomial-extension: formal-series basis versus polynomial extension.
lem-trf-formal-power-series-continuous-free vs lem-weil-pbc-naive-cotangent-complex-cokernel-kahler: continuous free module versus ordinary cotangent cokernel.
lem-trf-formal-power-series-continuous-free vs lem-weil-pbc-polynomial-ring-kahler-basis-any-variables: formal-series inverse limit versus polynomial basis.
lem-trf-formal-power-series-continuous-free vs lem-weil-pbc-polynomial-ring-kahler-basis: formal-series basis versus polynomial basis.
lem-trf-formal-power-series-continuous-free vs lem-weil-pbc-simple-transcendental-differential-decomposition: formal adic module versus transcendental field decomposition.
lem-trf-formal-power-series-continuous-free vs lem-weil-pbc-smooth-conormal-chart-differential-basis: global formal basis versus localized smooth chart basis.
lem-trf-formal-power-series-continuous-free vs lem-trf-completion-kahler-differential-comparison: ambient formal module versus completion comparison.
lem-trf-formal-power-series-continuous-free vs lem-weil-pbc-kahler-differentials-mod-power-ideal-bijective: inverse-limit free basis versus finite-level bijection.
lem-trf-formal-power-series-continuous-free vs lem-weil-pbc-kahler-differentials-mod-power-ideal: inverse-limit free basis versus fixed-power comparison.
