## What changed

Proved `CategoryTheory.localizedHomComplex_cycles_bijective` from the evaluated degree-zero
product cone and a new cycle-lifting theorem. Its signature and public imports are unchanged.
Added proof-only imports of Sheaf.Limits, Grp.EpiMono and LocalizedHomComplexCycleLift.
The injective half is fully proved: product projections detect equality of included cycles,
and monicity of iCycles detects equality of cycles. Surjectivity uses cycle lifting followed
by extensionality. The node now records this route.

## Proved and sorry left

Closed the sole original hole, `CategoryTheory.localizedHomComplex_cycles_bijective`.
Added one strictly smaller hole, `CategoryTheory.localizedHomComplex_cycle_lift`
(node `lem-pur-localized-hom-complex-cycle-lift`). This is a decomposition, net zero holes,
with injectivity proved and surjectivity split off. No sorry remains in the original module.
The new statement asserts existence of a preimage for each chain map; it asserts neither
injectivity nor bijectivity of an arbitrary function with the projection formula.

## No longer needed

None of the original imports or planned dependency nodes were removed. No unit statement or
unit proof step is bypassed; the unit's realized statement and steps are empty.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The source construction at Stacks 0A8X agrees with the node.
The repository has no local sites-cohomology.tex, so the source was read at
https://stacks.math.columbia.edu/tag/0A8X. Direct proof development of the new lift encountered
expensive dependent internal-Hom section elaboration; attempted component-family assembly
reached the 60-second compilation limit. The delivered lift has a named sorry with the full
product/differential/kernel proof in its docstring, rather than a partial proof.

## New nodes

`lem-pur-localized-hom-complex-cycle-lift` states the surjectivity construction only, in
`Sheaf.Algebra.Homology.LocalizedHomComplexCycleLift`. Its source is Stacks 0A8X before 0A8Y.
Edge cases: the zero chain map has the zero-cycle preimage; zero complexes give the same;
no bound or finite-support condition is needed since evaluation preserves arbitrary
integer-indexed products. Empty sites introduce no case because U is a given object.
Searches: Lean Finder found only sheaf cohomology and locally bijective presheaf results;
Loogle found generic Fan lifting/extensionality tools; Mathlib and local rg searches found
no independent localized lift. LeanSearch returned HTTP 500, recorded as unavailable.
Blueprint search for Hom complex found only the unrelated K-injective bridge;
ancestor tracing through def-pur-hom-complex identifies def-weil-derived-pullback-tensor-hom.
No definitions, existing signatures or visibility were changed; no forced adaptations.

## Second reading by K2

1. PASS: diffed both delivered modules against the repository (the lifting module is new).
   The existing theorem signature is byte-for-byte identical, and all existing public imports
   remain identical. There are no definitions or forced adaptations in the delivery, and no
   statement-change record is needed. Existing-node JSON changes only proof, proof_deps and
   proof_origin; JSON escaping changes no field value.
2. PASS: compiled both modules in import order through lcompile.py without errors or warnings.
   The only delivered sorry is localizedHomComplex_cycle_lift, exactly the named theorem
   reported above. No forbidden declaration or hollow definition occurs. Scratch #print axioms
   checks allow only propext, Classical.choice, Quot.sound and sorryAx from the open lift.
3. PASS: read the lifting statement, its full docstring argument and its matching node against
   Stacks 0A8X (https://stacks.math.columbia.edu/tag/0A8X), before Equation 0A8Y. Slice chain-map
   components are precisely internal-Hom sections. In degree zero the differential is
   d_I g - g d_L, so their chain-map equations give zero; preserved products and the cycles
   kernel give the claimed preimage. Zero maps lift to zero, zero complexes cause no exception,
   and complexes concentrated in degree zero reduce to the ordinary internal-Hom section
   identification. Infinite products impose no support or boundedness condition. The lemma
   asserts only lifting and is strictly part of the bijectivity argument, not a renamed copy.
   Independent Lean Finder, Loogle and grep searches, with different queries, found only
   generic product/kernel tools and ordinary Hom complexes. No split hole can be closed by a
   short application of those tools: assembly and the sheaf differential comparison remain.
4. PASS: read the proof from the bijectivity goal downward. Injectivity is actually proved by
   preserved degree-zero products and monicity, followed by the separate surjectivity lift.
   All original proof_deps remain used, so No longer needed is complete. All added imports are
   proof-only. Tested removing Grp.EpiMono in a scratch copy: compilation loses
   AddCommGrpCat.mono_iff_injective, so retained it. Sheaf.Limits supplies preservation by the
   sheaf forgetful functor; the lifting module supplies the surjectivity reduction. The unit
   sk-def-sf-operations has empty realized.statement and realized.steps; no unit route changes.
5. PASS: matched both node lean.statement fields verbatim to their declarations. The parent's
   two proof steps and dependencies match the product-injectivity and lifting proof exactly;
   the lift's source, proof, proof_deps, proof_origin, searches, created, blueprint, chapter,
   unit and lean records are present and describe its remaining construction.

Changes by the second reader: added independent search evidence to the new node and this
review section. Retained the Lean proofs and statements unchanged. One original hole is
closed and one smaller hole is added: this delivery is a decomposition with net zero holes,
not a complete proof without sorryAx. No modules are pruned.
