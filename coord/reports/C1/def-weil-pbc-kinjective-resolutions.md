# Stage 1 delivery: `def-weil-pbc-kinjective-resolutions`

## Files written

- `dag/nodes/sec-curve-estimates/def-weil-pbc-kinjective-resolutions.json`: clarified the definition and its existing dependencies; no new nodes. Mathlib verdict: `CochainComplex.IsKInjective` is a candidate, not an exact leaf.
- `coord/reports/C1/def-weil-pbc-kinjective-resolutions.md`: this worker report.

## Attachments

None. `rg` of the exact blueprint id in the read-only slopmaster2 `WeilConjectures/` and `Comparator/` trees found no declaration or docstring tag. A concept search for `K-injective` found uses and construction theorems, including `CochainComplex.toKInjectiveResolution` in `WeilConjectures/CategoryTheory/GrothendieckAbelian/KInjectiveResolution.lean:149`, but no declaration defining both clauses with this node's Hom-complex criterion. Nothing was attached and the source checkout was neither changed nor built.

## WANTED:

WANTED: none for this split. The blueprint master file named in the imported node is not regenerated in this clone, but the imported statement is present in the node and the relevant Stacks source is available at `/tmp/c1-lead-current/literature/stacks-project/derived.tex`.

## Source and changes

Stacks `derived.tex:9619-9625`, Definition 070H (`definition-K-injective`), defines K-injectivity for a complex in an abelian category by vanishing of `Hom` from every acyclic complex in its homotopy category. Its next paragraph, lines 9627-9630, applies the same vanishing to every shift of an acyclic complex. The imported blueprint clause says instead that the full external Hom complex is acyclic. These are mathematically equivalent: degree-`n` cohomology of `Hom^bullet(A,I)` consists of degree-`n` cochain maps modulo homotopy, hence is `Hom` in the homotopy category from a shift of `A` to `I`; all shifts of an acyclic `A` are acyclic. The node now states the external Hom complex explicitly, with degree-`n` term and differential, to fix the meaning of this clause. This Hom complex is of abelian groups, not the internal sheaf-Hom complex of `def-pur-hom-complex`.

Stacks `derived.tex:9767-9772`, Lemma 070K (`lemma-enough-K-injectives-implies`), uses the hypothesis that each complex has a quasi-isomorphism toward a K-injective complex. This is precisely the second clause of the blueprint definition of a K-injective resolution. The node now specifies `Mod(T_et,R)` for a scheme `T` and commutative ring `R`, citing `def-weil-pbc-derived-categories`, and cites the existing cochain, acyclic-complex, and quasi-isomorphism definition nodes for its remaining notions. The abelian-sheaf case is `R = Z`. No existence claim was added; that belongs to `prop-weil-pbc-kinjective-resolutions-exist`.

The whole-blueprint search `python3 tools/blueprint_refs.py search K-injective` found the item's own imported node, `def-sp-kinjective-bridge` (which adds existence and derived-functor data), and uses in other nodes. No separate blueprint node states just this definition. Thus `blueprint.same_as` is `[]`; no new node was created. The unit record `sk-prop-h2` and chapter record `sec-curve-estimates` were read; this definition is not the unit's key theorem and does not alter its route.

Mathlib `Mathlib/Algebra/Homology/HomotopyCategory/KInjective.lean:35-43` defines `CochainComplex.IsKInjective` by null homotopies of maps from acyclic complexes. Lines 35-39 explicitly leave equivalence to acyclicity of `HomComplex` as a TODO. `Mathlib/Algebra/Homology/HomotopyCategory/HomComplex.lean:562-570` supplies the external cochain complex. LeanSearch, Loogle, and a source grep are recorded in the node. The difference from the blueprint definition needs the shift argument above and a Lean theorem; it is not a one-line specialization, so `mathlib_match` remains null and `mathlib_candidate` records the class. This also means the sorry-free slopmaster2 construction theorem mentioned above is not an exact declaration for this definition.

## What could not be finished, and why

No Lean equivalence theorem is present in the inspected Mathlib source, so this definition cannot yet be closed as a Mathlib leaf. Stage 1 writes no Lean. No new node remains to split.

`python3 tools/review_split.py def-weil-pbc-kinjective-resolutions` passes. `python3 tools/check_dag.py` reports zero cycles and seven pre-existing reachability warnings for unrelated constructible nodes; no warning concerns this item.

## Review by C1

I read the imported item and the revised node against Stacks `derived.tex` Definition 070H (`definition-K-injective`) and Lemma 070K (`lemma-enough-K-injectives-implies`). The item retains the blueprint's two clauses: acyclicity of the external Hom complex from each acyclic complex, and a quasi-isomorphism into such a complex. Stacks defines the first by vanishing of morphisms in the homotopy category and immediately states vanishing after every shift; the degree-zero cocycle/homotopy quotient of the external Hom complex is precisely that morphism group. The statement introduces the scheme, coefficient ring, category, cochain degrees, differential and acyclicity without importing a sheaf-internal Hom in place of external Hom. It asserts no existence theorem.

I opened the statements of `def-weil-pbc-derived-categories`, `def-pc-cochain-complex-modules`, `def-pc-acyclic-complex-modules`, and `def-pc-quasi-iso-modules`. They respectively provide the small etale module-sheaf category, complexes, degreewise acyclicity, and quasi-isomorphisms used in the revised statement. There are no proof steps or new nodes in this definition, so the step-citation and new-node checks B-D have no instances. The blueprint search and read-only slopmaster2 search recorded above found no duplicate node or exact declaration. I also read Mathlib `HomotopyCategory/KInjective.lean:35-43`: its `IsKInjective` definition is the null-homotopy condition, and its TODO names the missing equivalence to Hom-complex acyclicity. It is therefore a candidate, not an exact Mathlib match.

For the small cases, an acyclic zero complex has zero external Hom, and taking the coefficient ring `R = Z` gives the abelian-sheaf case stated in the blueprint. No extra hypothesis is used. The worker's initial source comparison required no correction; I retained the candidate verdict and the explicit differential after checking its cochain signs. Delivery shape, citations, noncircularity, and hypotheses were checked against delivery-errors A-E.
