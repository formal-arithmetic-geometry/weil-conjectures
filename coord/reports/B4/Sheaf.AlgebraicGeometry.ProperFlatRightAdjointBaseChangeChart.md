## What changed

Replaced the sorry in `AlgebraicGeometry.proper_flat_rightAdjoint_baseChange_chart`
with a compiling proof. It constructs `f ∣_ V`, `g.resLE V W hWV`, the actual
pullback lift from `f'⁻¹(W)`, and both local right adjoints, obtains ordinary
base change using the existing proper-flat theorem, and applies `haffine`.
An arrow isomorphism comparison then transfers invertibility to the restricted
global mate. The original signature and public imports remain unchanged.

Added `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison`,
which states the remaining comparison of two actual morphisms as an arrow
isomorphism. Its hypotheses do not assume `haffine` or invertibility of either
mate. Updated the chart node's proof and dependencies to match the Lean.

## Proved and sorry left

Closed: `AlgebraicGeometry.proper_flat_rightAdjoint_baseChange_chart`
(`lem-sc-proper-flat-right-adjoint-basechange-chart`), one of one original holes.
There is no sorry in the item's module.

Added, still sorry: `AlgebraicGeometry.proper_flat_rightAdjoint_chart_mate_comparison`
(`lem-sc-proper-flat-right-adjoint-chart-mate-comparison`), exactly one new hole.
This delivery is a decomposition: one upper hole closed, one lower hole added,
net zero holes. The remaining statement is the restriction/pasting comparison;
the chart geometry, right-adjoint existence, application of the affine hypothesis,
and preservation/transfer of invertibility are proved in the item's module.
Existing imported dependencies retain their own proofs or holes unchanged.

Validation: both modules compile cleanly with lcompile.py. The comparison was
checked against Stacks Tags 0E9S and 0AAB online (the local literature text is
absent on this machine). Empty charts and identity/top charts satisfy the same
pullback construction. Empty charts have zero derived categories; for identity
charts the comparison reduces to uniqueness of right adjoints. The statement
allows arbitrary local adjunction choices, handled by their canonical uniqueness
isomorphisms, and imposes both necessary projection equations on q.

## No longer needed

No nodes or modules are pruned from the dependency closure. The direct proof
import of `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen` was
removed from the item's module and retained in the new comparison module:
its role is to construct the comparison endpoint isomorphisms, so it remains
needed transitively. The item's new proof imports are
`Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeHbeta` and
`Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison`.
All original statement imports remain needed; no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The chart node's single planned proof dependency states only invertibility of
open-unit arrows in Lean. It does not expose the comparison of canonical mates
needed for the last step. The new node isolates that step without repeating the
chart invertibility assertion. Ordinary base change on the local square is
already stated in `ProperFlatRightAdjointBaseChangeHbeta`; no new ordinary
base-change lemma is necessary.

`blueprint_refs.py ancestor` returns None for this item because older created.item
entries contain module names instead of DAG IDs. The new node records the
existing declared blueprint ancestor `lem-sc-finite-duality` and its intermediate
route, as recorded by the proper-flat base-change and restriction nodes.

## New nodes

`lem-sc-proper-flat-right-adjoint-chart-mate-comparison` in
`Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison` states the
arrow isomorphism of Remark 48.6.1 (Tag 0E9S), with a complete proof sketch using
Tag 0E4J and the canonical mate formula. Its conclusion supplies compatibility
of two maps, with no affine-case theorem or invertibility hypothesis on the
mates; the parent proves invertibility using the actual affine assumption.
LeanFinder and Loogle found only underived or generic adjunction lemmas;
LeanSearch returned HTTP 500, recorded as unavailable; grep and blueprint
searches found no existing declaration of this comparison. No change record
is needed: no existing signature or definition was changed.

## Second reading by B4

1. **Visible declarations unchanged — PASS.** Compared the delivered chart module with
   the repository by `diff -u`. Its existing theorem signature is byte for byte
   unchanged, including every hypothesis, its affine-case assumption and conclusion;
   its docstring and all public imports are unchanged. Only proof imports and the
   proof body differ. The comparison module is new, and no existing definition is
   changed. The existing node differs only in `proof`, `proof_deps`, `proof_origin`.
   No change record or forced adaptation is required.

2. **Kernel and data checks — PASS with the reported hole.** Ran `lcompile.py --all`
   on the two delivered modules in dependency order: both compiled without warnings
   or errors. A separate scratch module imported the sandbox outputs and printed
   axioms of both declarations: exactly `propext`, `Classical.choice`, `Quot.sound`
   and `sorryAx`. A source scan found exactly one `sorry`, the whole proof of
   `AlgebraicGeometry.proper_flat_rightAdjoint_chart_mate_comparison`, and none of
   the forbidden declarations or attributes. There are no new definitions.
   The chart map q is explicitly `pullback.lift`, not an arbitrary existence
   witness. The selected local right adjoints are determined by their adjunction
   universal properties up to the canonical right-adjoint isomorphisms used in
   the remaining comparison; they satisfy the data-selection exception.

3. **Split-off statement and searches — PASS.** Independently checked Stacks
   [Remark 48.6.1, Tag 0E9S](https://stacks.math.columbia.edu/tag/0E9S) and
   [Lemma 48.12.2, Tag 0E4J](https://stacks.math.columbia.edu/tag/0E4J).
   Flatness gives the Tor independence required by the remark; properness and
   local finite presentation give finite presentation here. Affine opens are
   quasi-compact, so the open compatibility applies on both bases. The equations
   hq₁ and hq₂ determine q uniquely by monicity of the open inclusions and the
   pullback universal property, and pasting identifies it as an isomorphism.
   Both displayed arrows live in the derived category of the same open U'.
   Changing the supplied local right adjoints and adjunctions changes their
   identification by canonical uniqueness isomorphisms, so no normalization
   assumption is missing. Empty W gives empty U' and empty chart pullback;
   empty V forces empty W. Identity maps and top charts reduce to the usual
   right-adjoint uniqueness and pullback-composition comparisons. These checks
   reveal no extra hypothesis or counterexample. The statement compares actual
   morphisms without haffine or an IsIso assumption on either mate; it isolates
   the compatibility step, rather than restating chart invertibility. Its
   docstring supplies the geometric identification, endpoint isomorphisms and
   mate-pasting argument, and its node matches it.

   Searched independently with LeanFinder for “Beck Chevalley mates compatibility
   pasting open immersion right adjoints derived categories”, Loogle for
   `CategoryTheory.Arrow.mk, CategoryTheory.IsIso`, and grep for
   `mateEquiv_hcomp|conjugateEquiv.*comp|restrict.*[Bb]ase[Cc]hange` in Mathlib's
   CategoryTheory. These searches are recorded in `searches.jsonl`. Found the
   Arrow transfer lemma already used and generic mate-pasting results, plus
   underived open-restriction comparisons; none supplies the required derived
   scheme comparison. Also searched lean/Sheaf and lean/WeilConjectures and read
   the restriction-open, ordinary-base-change, canonical-mate, derived-open-map
   and open-support-criterion modules. Closing the comparison requires derived
   open endpoint identifications and their compatibility, not a short direct
   application of the existing open-unit theorem.

4. **Top-down reduction and pruning — PASS.** The chart proof constructs the actual
   local geometry and adjunctions, uses the existing ordinary-base-change theorem
   and quasi-coherent-pullback theorem, applies haffine, and transfers invertibility
   across the comparison using the existing Mathlib Arrow lemma. No shorter
   available declaration bypasses the remaining compatibility argument. New
   proof-only imports are plain imports; Arrow is public in the new module because
   it occurs in its signature. The removed direct restriction-open dependency is
   named in “No longer needed” and remains a dependency of the new comparison,
   so no module or node is pruned. The ordinary-base-change module was already
   imported by the parent proper-flat base-change module in the target closure.
   Read `dag/units/sk-thm-picard-duality.json`: no unit statement, proof step,
   realization entry or chapter route is changed or bypassed. Its pre-existing
   empty `realized` entries are not filled by this delivery. One original hole
   closes and one lower hole is added: a decomposition, net zero holes.

5. **DAG alignment — PASS.** Checked both node Lean signatures against their files
   byte for byte. The chart node's proof steps follow the construction, adjoint
   selection, local ordinary base change, haffine application and Arrow transfer
   in Lean; its proof_deps are the corresponding four nodes. The comparison node
   has the required source, complete statement, dependencies, stepwise proof,
   proof_origin, recorded searches, split status, creation and blueprint lineage,
   chapter/unit and verbatim Lean record. Its restriction-open dependency is
   used for the two endpoint identifications, not claimed to prove the entire
   arrow comparison by itself.

Second-reading changes: added this independent review and its search/axiom
validation evidence. No Lean proof, statement, definition, import or node needed
repair; the one split-off comparison remains open.
