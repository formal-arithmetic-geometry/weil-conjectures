## What changed

Replaced the sole sorry in Sheaf.AlgebraicGeometry.ResidueHomologyRankOneCoefficient
by a complete proof from the new naturality comparison in
Sheaf.AlgebraicGeometry.ResidueStalkHomologyMapComparison. Existing signatures and
visibility are unchanged. Added two proved private helpers: injective homology gives
an injective degree-zero component for a source with zero adjacent differentials;
and injective residue scalar extension of a framed rank-one map forces its coefficient
residue to be nonzero. The second argument explicitly uses tensor balancing and the
tensor right unitor, rather than assuming that a stalk map is already invertible.
The new comparison statement is precisely the geometric step before the algebra:
it has no frames, no coefficient, and no assumption about negative terms. Its source,
complete proof in words, and separate DAG node are supplied. No data is chosen from
an unproved existence statement. All writes were made in the item sandbox.

## Proved and sorry left

Closed AlgebraicGeometry.residue_ne_zero_rankOne_stalk_coefficient
(node lem-sc-residue-homology-rank-one-coefficient), from one new comparison theorem.
The item has zero remaining sorries. Both private helpers
mono_component_of_mono_homology and residue_coefficient_ne_zero_of_mono are proved.
Added one sorry: AlgebraicGeometry.isIso_residue_stalk_homologyMap
(node lem-sc-residue-stalk-homology-map-comparison), in its own new module.
This is a decomposition: one upper hole closed, one lower hole added, net zero.
It separates the genuine missing geometric naturality from the now proved homology
and rank-one algebra; it is not an independent axiom-free proof of the whole theorem.

Edge cases checked: no point lies in the empty open. The residue field of the chosen
point is nontrivial, and the frames exclude zero degree-zero modules. The helper does
not require any condition on the target differential or negative terms. In higher
rank a nonzero single coefficient would not follow, and the frame hypotheses are
used explicitly in conjugating the map to multiplication on R. Arbitrary frames and
arbitrary derived conjugating isomorphisms preserve the argument.

## No longer needed

Removed direct proof imports Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback and
Sheaf.AlgebraicGeometry.DerivedPullbackComposition from the item's module, replacing
them with the new comparison import. Their nodes
lem-pc-flat-complex-derived-pullback and
lem-pc-ringed-spaces-derived-pullback-composition remain in the new comparison's proof
plan and are now imported there; this delivery does not claim they are globally unnecessary. No unit route is
bypassed. No other existing module or node is claimed pruned. The original target
negative-term hypothesis is retained but is unnecessary for the algebraic step.

## Where the brief, the DAG or earlier work was wrong

The parent's second step does not need the target H⁰ to embed in its degree-zero
term. Injectivity of the homology arrow, together with the single source, already
forces injectivity of its component; this is proved using cycle naturality. Thus
negative target terms need not vanish for this coefficient result. The existing
object-only residue cohomology equivalences cannot by themselves identify the
representing chain arrow. The new node states that missing naturality step rather
than substituting an arbitrary object isomorphism. No existing statement was changed.
The new node retains the original geometric route and adds the existing natural
residue-pullback/global-sections comparison as a needed tool.

## New nodes

lem-sc-residue-stalk-homology-map-comparison, in
lean/Sheaf/AlgebraicGeometry/ResidueStalkHomologyMapComparison.lean, isolates the
natural isomorphism on residue stalk H⁰ of α from the geometric comparisons of
Stacks Tags 0E62, 06YJ, 0D5S, and 0098. Its natural-language proof names the two
original dependencies and lem-sc-residue-pullback-global-sections. No change record
is needed because no existing definition, statement, or visibility changed.

## Second reading by K3

1. Compared the existing module with the repository using diff. The signature and
   visibility of residue_ne_zero_rankOne_stalk_coefficient are byte for byte
   unchanged; no existing definition changes. The only new public declaration is
   isIso_residue_stalk_homologyMap in its own module. Verdict: pass.
2. Compiled both modules in dependency order using lcompile.py, without errors or
   warnings. Scanned for forbidden declarations and sorry: the sole delivered
   sorry is the named comparison theorem. A scratch-copy #print axioms probe shows
   only propext, Classical.choice and Quot.sound for each private helper; the two
   public theorems additionally have sorryAx, as reported. No data definitions,
   arbitrary witnesses, or hidden proof holes are added. Verdict: pass as a
   decomposition, not an axiom-free proof of the item.
3. Read the comparison statement and its complete docstring proof against Stacks
   [0E62](https://stacks.math.columbia.edu/tag/0E62),
   [06YJ](https://stacks.math.columbia.edu/tag/06YJ),
   [0D5S](https://stacks.math.columbia.edu/tag/0D5S), and
   [0098](https://stacks.math.columbia.edu/tag/0098). Strict perfectness supplies
   bounded flat terms; restriction through the open immersion and residue-field
   transport give the same derived fibre. Natural counits and the natural stalk
   tensor comparison intertwine the arrow, including arbitrary choices of c and e.
   For S = Spec k and U = top this is ordinary tensor homology; for P = 0 the
   isomorphism hypothesis cannot hold. Negative target terms do not affect the
   comparison. Empty U admits no hs. The rank-one algebra is a separate, fully
   proved step, so the new theorem is not a renamed nonvanishing assertion.
   Repeated leanfinder search with "Naturality of derived tensor base change for
   morphisms of bounded complexes of flat modules at a scheme point", loogle with
   "HomologicalComplex.homologyMap, CategoryTheory.IsIso", and grep with
   "mapHomologyIso_hom_naturality|homologyπ_naturality|cyclesMap_i". Results give
   tensor and generic homology APIs, not this geometric morphism comparison.
   Read KFlatStalkResidueCohomology and StalkFreeResidueCohomologyComparison: their
   object equivalences do not imply naturality for the supplied arrow. Also searched
   the upstream WeilConjectures and current Sheaf sources. Verdict: true, needed,
   strictly one part of the argument, with matching node; no immediate closure.
4. Checked the top-down reduction: geometric homology invertibility, source cycle
   and quotient isomorphisms, then rank-one tensor balancing. The original two
   proof dependencies are both retained inside the comparison, rather than pruned
   from its import closure. Added its missing proof-only imports of
   FlatComplexDerivedPullback, DerivedPullbackComposition, and
   ResiduePullbackGlobalSections. Public imports of ChangeOfRings and
   Adjunction.Additive are needed by the new signature's scalar-extension functor
   and instance expressions. Read dag/units/sk-prop-av-cube.json: realized has empty
   statement and step lists already; this delivery does not modify them or replace
   the general-cube route. The comparison uses the existing pullback and stalk
   results as tools. No globally pruned module is claimed. Verdict: pass after
   restoring the dependency imports.
5. Checked the existing node diff: only stage-3-owned proof, proof_deps and
   proof_origin fields change. The three new proof steps match the Lean reduction.
   The new node has source, statement dependencies, proof plan, origin, searches,
   creation, blueprint, chapter, unit and verbatim Lean signature records.
   Its proof_deps are exactly the union of its proof-step uses, now reflected in
   its imports. Verdict: pass.

Second reading changed: restored the three missing proof-dependency imports in
ResidueStalkHomologyMapComparison, updated the parent's docstring to describe the
actual source-homology monomorphism and tensor-balancing proof, and recorded these
checks and fresh searches. No mathematical statement or proof body was changed.
