## What changed

The existing theorem `AlgebraicGeometry.Etale.abelianRawPullback_coherent` keeps its
signature and now combines two strictly smaller obligations: existence of the raw natural
maps with identity/composition laws, and the cocone equation for any maps with the prescribed
components. Two proof-only imports introduce the new modules
`Sheaf.AlgebraicGeometry.AbelianRawPullbackCoherenceBase` and
`Sheaf.AlgebraicGeometry.AbelianRawPullbackCoherenceExtend`.

The second reader corrected the new helper docstrings and nodes to describe only their own
claims. Their proof plans now name the existing derived inverse-image coherence and
single-complex composition results; these dependencies are imported privately for proof use.
No existing definition, signature, visibility, or public import changed.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.Etale.abelianRawPullback_coherent`, by destructing
the base existence theorem and supplying the cocone conjunct with the extension theorem.

Added two holes, each the entire proof of a public named theorem:

- `AlgebraicGeometry.Etale.abelianRawPullback_coherent_base`, node
  `lem-sbc-abelian-raw-pullback-coherence-base`.
- `AlgebraicGeometry.Etale.abelianRawPullback_coherent_extend`, node
  `lem-sbc-abelian-raw-pullback-coherence-extend`.

This is a decomposition, not an axiom-clean proof of the original mathematical result.
It closes 1 original hole and adds 2 lower holes (net -1 before any closure pruning).
Both helpers remain open; no data is chosen from an unproved existence theorem in a
definition. The final proof only eliminates an existential inside a theorem of Prop.

## No longer needed

No imports or modules were removed. The original node's direct proof dependencies
`lem-weil-pbc-inverse-image-composition` and `prop-weil-pbc-derived-inverse-image-adjunction`
are replaced at that node by the two new helper nodes. The former remains an ingredient of
the base argument. The latter is no longer invoked as a theorem by either helper plan:
exact derived functor coherence, rather than derived adjunction, is the required tool.
Its module is already transitively needed by the unchanged public definition imports, so
no global module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The first report called the original theorem proved without distinguishing decomposition
from completion. The helper nodes copied the entire original proof: the base node included
a cocone conclusion it did not state, while the extension node described a new existential
witness instead of its actual stronger conclusion for the supplied maps. Both docstrings
also repeated the entire original argument. These descriptions and dependency plans have
been repaired without changing the existing theorem's statement.

Searches found `preadditiveYonedaMap`, `colimit.w`,
`AlgebraicGeometry.Etale.abelianPullbackSingleComposition`,
`AlgebraicGeometry.Etale.derivedInverseImageComposition`, and the canonical-coefficient
`abelianHigherDirectImage_core_comp`. They supply ingredients, not the two complete helper
claims. In particular, equality after sheafification from the natural comparison cannot
prove equality of raw classes, because sheafification need not be injective on components.
The ModuleCat fixed-coefficient raw composition theorem is also not the varying-coefficient
AddCommGrpCat statement. No easy closure of either helper was found.

## New nodes

`lem-sbc-abelian-raw-pullback-coherence-base` records construction and naturality of the raw
maps and their identity/composition laws. It omits precisely the cocone conclusion.

`lem-sbc-abelian-raw-pullback-coherence-extend` records only the cocone law, conditional on
arbitrary natural transformations whose components equal the explicit raw formulas. It
does not assume the identity/composition laws from the base theorem. Its node is now
self-contained and matches that Lean quantification. Each new node has its source,
complete proof plan, statement dependencies, actual searches, creation record, blueprint,
chapter/unit, and Lean record. No change record is needed: the existing interface is intact.

## Second reading by W2

1. Compared the existing module with the repository using diff and the declaration reader.
   The entire existing theorem signature is unchanged byte for byte; only two private
   imports and its proof change. No existing declaration is removed or data altered.
   The original public imports are still required by the signature, notably upperStarId
   and the explicit raw-presheaf definitions. Verdict: pass.
2. Compiled all three sandbox modules in import order with lcompile.py. The original
   theorem contains no sorry; exactly the two reported public helper theorems have sorry
   as their whole proofs. There is no axiom/unsafe/opaque/implemented_by/extern, no hollow
   definition, and no additional data declaration. A scratch copy prints the axioms of
   all three declarations; the delivery tool also probes every declaration. The printed axioms for each of the three are exactly propext, Classical.choice,
   Quot.sound, and sorryAx; the last is expected from the two reported lower holes. Verdict:
   valid conditional proof, with the two documented lower obligations still open.
3. Read the helper signatures and five-factor raw construction. The base helper is a
   proper part of the original conclusion; the extension proves only the remaining
   cocone equation and does not reassert existence. Checked empty indices (all indexed
   claims vacuous), a singleton/identity transition (unit comparisons cancel), zero
   coefficients/classes (additivity), empty test objects, and p = 0 (shift zero).
   No limit, directedness, qcqs, or nonemptiness assumption is consumed. The coefficient
   equation is obtained by precomposing colimit.w with eH_i.inv and substituting hH,
   cancelling eH_i.inv followed by eH_i.hom. This gives the i-th leg exactly, with the
   correct orientation. Searched with different wording using leanfinder, loogle, grep,
   and local rg; LeanSearch was also attempted and returned Internal Server Error,
   recorded as unavailable. The available results do not duplicate the helper claims.
   Verdict: mathematically sound strict decomposition; lower claims not Lean-proved.
4. Checked the original dependencies and dag/units/sk-lem-failure-field.json. Its realized
   arrays are empty and these are below-unit construction steps, so no realized unit
   node is bypassed or removed. Kept the existing public signature imports. The natural
   sheafification comparison cannot shortcut raw coherence. The helper plans use already
   available derived and single-complex coherence rather than duplicating those results.
   No longer needed names both replaced original direct dependencies and explains the
   surviving transitive use. Verdict: route preserved, no module pruning claimed.
5. Checked each JSON record against its Lean declaration, including proof-dependency
   unions, module paths, declarations and signatures. Removed the spurious cocone step
   from the base node; replaced the extension's existential description by its actual
   universally quantified conclusion; corrected created.by to worker, normalized TeX,
   and recorded searches actually run by this reader. The parent proof records the exact
   two-helper assembly used by Lean. Verdict: records agree after these repairs.

Second reading changed the helper docstrings, new-node statements/proof plans/search
records, and private dependency imports; it corrected progress accounting and supplied
this review. It did not change any existing declaration signature or close a lower hole.
