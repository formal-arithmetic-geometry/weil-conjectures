## What changed

Proved `CategoryTheory.sitePullback_abelian_exact` with its signature and existing
public imports unchanged. Added the proof-only import
`Sheaf.CategoryTheory.SitePullbackAbelianUnderlying` and Mathlib's
`CategoryTheory.Adjunction.Additive`. The proof constructs additivity using the
abelian pullback adjunction, finite colimit preservation from left adjointness,
and finite limit preservation by transporting the underlying-sets comparison
and reflecting limits through the forgetful functor. It then applies
`ShortComplex.ShortExact.map_of_exact` and `ShortComplex.Exact.map`.

The new module isolates only step 2 of the old plan, the natural isomorphism
between underlying abelian inverse image and set inverse image. It does not
assert additivity, preservation of limits or colimits, or preservation of exact
complexes. Those clauses are combined and proved in the original module.

Updated the original node's proof, proof dependencies and proof origin. No
existing statement, definition, unit or chapter was changed.

## Proved and sorry left

- `CategoryTheory.sitePullback_abelian_exact` has no `sorry` in its proof: one of
  the original module's one sorries is reduced.
- The only added sorry is `CategoryTheory.sitePullback_abelian_underlying`, in
  `Sheaf.CategoryTheory.SitePullbackAbelianUnderlying`, node
  `lem-weil-pbc-site-pullback-abelian-underlying`.
- Existing imported `CategoryTheory.sheavesAlgebraicStructuresAbelian` remains
  an external sorry dependency, node
  `lem-weil-pbc-sheaf-algebraic-structures-abelian-component`; it is not edited.

Both delivered modules compile together locally without warnings. The bridge's
edge cases were checked mathematically: for identity U it is the identity
comparison; for empty source the set-limit hypothesis forces the appropriate
terminal underlying object and the abelian image is the zero group sheaf;
arbitrary topologies and empty covering families cause no change to the
adjunction/group-object argument. The comparison is a natural isomorphism of
functors, including morphisms, not an equality of arbitrarily chosen models.
The existing site hypotheses hcover/hpullback are retained unchanged; the
explicit IsContinuous instance already supplies what this proof needs.

## No longer needed

The second reading also removed the redundant direct import
`Mathlib.CategoryTheory.Sites.Whiskering` from the new underlying-comparison
module; `Sites.Pullback` already supplies its declarations transitively.

Removed these proof-only imports from the original module:
`Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects`,
`Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects`, and
`Sheaf.CategoryTheory.SiteContinuousPushforwardSheaf`.

The underlying-comparison module needs only the abelian components:
`Sheaf.CategoryTheory.Adjunction.LiftedCommGrpBranch` and
`Sheaf.CategoryTheory.SheavesAlgebraicStructuresAbelian`. Thus the combined
ring-and-group statements and their ring branches are unnecessary on this
item's route: `lem-weil-pbc-adjunction-lifts-group-ring-objects`,
`lem-weil-pbc-sheaf-algebraic-structures-objects`,
`lem-weil-pbc-lifted-comm-ring-branch`,
`lem-weil-pbc-sheaf-algebraic-structures-ring-component`, and modules
`Sheaf.CategoryTheory.Adjunction.LiftedCommRingBranch`,
`Sheaf.CategoryTheory.SheavesAlgebraicStructuresRing` and its ring-core imports.
This is a pruning of this Lean import route; other targets may still need them.

`lem-weil-pbc-site-continuous-pushforward-sheaf` and its module are not used;
continuity is already an explicit instance in the unchanged statement.
`def-weil-pbc-sites-and-cohomology` stays a statement dependency, but is not a
separate proof step. The adjunction, uniqueness, sheafification and sectionwise
limit nodes remain used through Mathlib or the bridge; they are not pruned.
The old operation-formula proof of additivity is unnecessary: Mathlib's
adjunction additivity proves that clause directly. No blueprint unit statement
or realized step is bypassed: this item is below the realized unit level.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The plan omitted a Lean-ready
comparison between the lifted group-object left adjoint and Mathlib's abelian
sheaf pullback. The supplied algebraic-object and lifted-adjunction lemmas do
not themselves state that comparison. The new node makes precisely that step
available; the rest of the plan is implemented with Mathlib.

LeanFinder found finite-limit preservation of pullback only under representable
flatness and related sectionwise-limit facts. Loogle found
`Adjunction.left_adjoint_additive`. Source searches in Mathlib and
`lean/WeilConjectures` found no general underlying-pullback comparison.
LeanSearch was attempted but returned Internal Server Error; no negative
verdict is inferred from that failure. Blueprint searches for `underlying
sheaf` and `00YV` found no matching blueprint node. The local checkout lacks the
Stacks TeX files; the primary source pages for 04JC and 00YV were read online.

## New nodes

`lem-weil-pbc-site-pullback-abelian-underlying` isolates step 2 of the original
plan (Stacks 00YR/00YV(2), also the first paragraph of 04JC). It states only the
natural comparison of underlying sheaves. Its complete proof in words uses the
existing abelian-sheaf/group-object component, the existing lifted commutative
group adjunction, sectionwise identification of right adjoints, and uniqueness
of left adjoints. Its module is
`lean/Sheaf/CategoryTheory/SitePullbackAbelianUnderlying.lean`, with one public
named theorem whose proof is exactly `by sorry`. There are no change records,
since no existing statement or definition is modified.


## Second reading by K2

1. Compared the delivered exactness module with the repository using `diff -u`.
   Its sole existing declaration, including all universes, site axioms, hcover,
   hpullback, continuity, both set-preservation hypotheses and all five conclusion
   clauses, is byte-for-byte unchanged up to `:= by`. Existing docstrings and public
   imports are unchanged. Only its proof and private imports differ. The comparison
   module is new; no existing definition or statement is changed and no change
   record is needed. Verdict: pass.
2. Compiled both modules locally in dependency order, without errors or warnings.
   Inspected the complete proof: pushforward additivity is checked sectionwise;
   adjunction additivity and colimit preservation give the first and third clauses;
   the comparison transports finite-limit preservation and the conservative,
   limit-preserving forgetful functor reflects it; the two ShortComplex mapping
   theorems give both sequence clauses. Scratch copies with `#print axioms` for
   each delivered theorem show exactly propext, Classical.choice, Quot.sound and
   sorryAx. The last is expected from the named comparison, not an extra axiom.
   A source scan found precisely its one named theorem sorry and none of the
   forbidden constructs or hollow definitions. Verdict: pass as a partial proof.
3. Read the comparison statement, its full docstring argument, its new node, and
   the actual signatures of `sheavesAlgebraicStructuresAbelian` and
   `Adjunction.liftedCommGrpBranch`. The former supplies the two forgetful-compatible
   identifications and morphism criterion; the latter supplies the lifted
   adjunction and operation formulas. Continuous pushforward is sectionwise, so
   these formulas identify its group operations; uniqueness of left adjoints then
   supplies the comparison. Read primary source Stacks 00YV(2)
   (https://stacks.math.columbia.edu/tag/00YV) and the first paragraph of 04JC
   (https://stacks.math.columbia.edu/tag/04JC): they give precisely this argument.
   Finite limits, rather than finite colimits or flatness, suffice to lift group
   operations. Checked identity U, zero group sheaves, empty sites and topologies
   allowing empty coverings: all are covered by the adjunction argument; no
   nonempty covering or nonzero-object assumption enters it. The new theorem is
   strictly the underlying comparison, not the additive or exactness conclusion.
   Independently searched LeanFinder for "natural isomorphism sheaf inverse image
   forget abelian group structure" and used rg for sheafPullback, sheafCompose,
   forget and mapCommGrp in Mathlib Sites/Monoidal and both library roots. Hits for
   pushforward and module-sheaf forgetful comparisons do not prove this statement.
   No duplicate or short way to close this comparison was found. Verdict: pass.
4. Checked the shorter adjunction route before accepting the split. Mathlib
   already supplies additivity, colimits, sheaf inclusion limit preservation,
   objectwise forgetful limit preservation, limit reflection and exactness mapping;
   all are used directly. Removed the redundant direct Whiskering import from the
   new module after recompiling a scratch copy without it. Its remaining public
   imports supply the comparison signature and the concrete abelian sheafification
   instances; the two Sheaf imports are private proof-plan dependencies. Matched
   all ten old proof dependencies against the new argument: the sites definition
   remains in stmt_deps; continuous pushforward and the combined group/ring nodes
   are pruned; conjugate uniqueness is retained through the comparison; the five
   Mathlib-backed adjunction/limits/abelian dependencies remain. The report's
   pruning list names each removal. Read sk-thm-p1.json realized statement and all
   four realized step lists: this supporting node is below them, none is bypassed,
   and the unit record is untouched. Verdict: pass.
5. Compared both versions of the original JSON node: only proof, proof_deps and
   proof_origin differ. Each new step matches the compiled argument; its uses
   union is exactly proof_deps. Checked the new node's four steps against the
   imported component signatures and the Mathlib-backed adjunction and uniqueness
   nodes, and its verbatim Lean statement against the new module. It records source,
   searches (including the failed LeanSearch honestly), ancestry, chapter, unit,
   status split and worker creation metadata. Verdict: pass.

Second reading changed only the redundant direct Whiskering import and this report.
The theorem proof and split statement required no repair.
