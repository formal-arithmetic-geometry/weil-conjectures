## What changed

Wrote a complete reduction of
`AlgebraicGeometry.Etale.projectiveLine_strictLocal_stalkExchangeComparison`
by composing two comparisons through total strict-local projective-line cohomology.
Added proof-only imports of `ProjectiveLineOriginalStalkTotalCohomologyExchange`
and the existing `StrictLocalTotalCohomologyExchange`. The original statement and
all definitions are unchanged. The additive equivalences are `c₁.trans d₁.symm`
and `c₂.trans d₂.symm`; injectivity of `d₂` and the two comparison identities
prove the required equation.

## Proved and sorry left

The item's sole sorry is replaced by a combination proof. The algebraic
composition/cancellation proof compiles in `scratchpad/Glue.lean`, and the new
intermediate statement compiles. The complete item compiles cleanly in the sandbox, and the required delivery
dry run passes with `OK`.
The new declaration
`AlgebraicGeometry.Etale.projectiveLine_originalStalk_totalCohomologyExchange`
remains sorry (node `lem-weil-pbc-p1-original-stalk-total-cohomology-exchange`).
It isolates the original stalk formula and its compatibility with total-space
pullback. Its conclusion contains no local higher-direct-image stalks.
The existing imported declaration
`AlgebraicGeometry.Etale.exists_addEquiv_strictLocal_totalCohomology_exchange`
remains sorry upstream; this delivery neither changes it nor duplicates it.

## No longer needed

The item's six old proof-only imports are removed:
`Sheaf.AlgebraicGeometry.DerivedExchangeTermwise`,
`Sheaf.AlgebraicGeometry.EtalePullbackForgetModules`,
`Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic`,
`Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula`,
`Sheaf.Paper.InverseImageStalkGerm`, and
`Sheaf.Paper.StrictHenselizationFunctoriality`.
The corresponding old direct proof dependencies are
`lem-weil-pbc-derived-exchange-termwise`,
`lemma-weil-pbc-etale-pullback-forget-modules`,
`lem-weil-pbc-injective-module-abelian-acyclic`,
`prop-weil-pbc-strict-henselization-stalk-formula`,
`lem-weil-pbc-inverse-image-stalk-germ`, and
`lem-weil-pbc-strict-henselization-functoriality`.
They remain dependencies of the new original-stalk comparison, so none is
pruned globally. All three existing public imports support the unchanged
statement. The item's direct proof dependencies are now the new original-stalk
comparison and the existing total-space local comparison. Neither strict-local
closed-fibre exchange nor proper base change is used by this reduction.

## Where the brief, the DAG or earlier work was wrong

The plan already notes that its module-to-abelian coefficient comparison is at a
narrower universe than this statement. That bridge remains explicitly inside the
new original-stalk comparison; the proof does not assert that forgetting module
coefficients preserves injectives. The existing local total-space comparison
supplies the other half of the original plan and avoids duplicating that work.
The blueprint ancestor helper reports `None` for this recently split item; the
new node instead cites clause 2 of `lemma-weil-pbc-p1-exchange-geometric-stalk`,
which is the original geometric-stalk unit step. No unit realization is bypassed.

## New nodes

`lem-weil-pbc-p1-original-stalk-total-cohomology-exchange`, module
`Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange`,
is the original-geometric-stalk-to-total-space part of the argument, sourced to
Stacks 03Q9, 03FD and the map-on-stalks calculation in 095T. Its independent
local counterpart is already stated for arbitrary cartesian squares and does
not require properness or torsion. The combination cancels the common total-space
comparisons in Lean. Edge cases checked in the mathematical statement: q=0 gives
restriction of sections; zero coefficients give zero groups; separably closed
nonperfect fields are treated by extension of geometric points, without imposing
perfectness or integral residue factorizations. No change record is needed.


## Second reading by H1

1. Compared both delivered modules with the repository: the original module's
   existing theorem signature is byte for byte unchanged, as is its docstring;
   no definitions or target statements change. The other module is new. No
   change record is required. Verdict: pass.
2. Independently compiled both delivered modules in import order with lcompile;
   both compile without warnings. Compiled scratch copies with `#print axioms`
   for both declarations: only `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx` occur. The new named theorem is the only textual sorry delivered;
   the existing local comparison is still open upstream. No forbidden trust
   escape or hollow definition occurs. The composition and cancellation prove
   the exact compatibility equation. Verdict: valid conditional reduction,
   not an axiom-free completion.
3. Read the new theorem, its full proof docstring, its node, and the existing
   local comparison. Checked the higher-direct-image stalk formula and module
   acyclicity argument in the local Stacks sources (03Q9 and 03FD), and the
   stalk calculation in 095T. In degree zero the map is restriction of sections;
   zero coefficients give trivial groups; identity base change gives an
   identity comparison. Separably closed nonperfect fields require no
   perfectness assumption. The new conclusion omits local direct-image stalks:
   it is the original-stalk-to-total-space part, combined with a distinct
   existing local-stalk-to-total-space theorem. It is not a renaming of the
   item. Fresh leanfinder and grep searches using derived direct images,
   geometric fibers, and natural base change found no replacement; loogle
   confirms the additive-equivalence composition identity used in the proof.
   Repository searches likewise found only the stated component results and
   downstream projective-line comparisons. The larger coefficient universe
   and ModuleCat-to-abelian comparison remain work in the split theorem, not
   silently supplied by the narrower injective-module theorem. Verdict: pass;
   this remaining geometric comparison cannot be closed in a few minutes.
4. Read `dag/units/sk-thm-p1.json`, including every `realized` step. This is a
   reduction below its geometric-stalk step; the surrounding strict-local
   closed-fibre comparison and curve invariance route stays in place. The two
   proof imports in the item are used, and the new module's fourth public
   import supplies cohomologyMap in its statement. Corrected the inaccurate
   claim that no original import was removed, and explicitly listed all six
   removed imports and old direct dependencies. None is globally pruned because
   the new intermediate's plan still needs them. Verdict: pass after report fix.
5. Checked both node records against the Lean declarations. The item's two
   proof dependencies are precisely the two comparisons used; its elementary
   cancellation step agrees with the Lean proof. The new node has its source,
   complete proof plan, dependency union, searches, creation and blueprint
   provenance, chapter/unit, and verbatim Lean signature. Its plan explicitly
   records the coefficient-universe bridge still to prove. No unit records
   are changed. Verdict: pass.

Changes made in second reading: corrected and completed `## No longer needed`;
fixed the copied author credit in the new module to H1; removed one redundant
blank line in the item's proof ending. No mathematical statement or proof was
changed. Local compilation and explicit axiom checks passed; delivery preflight
and server compilation are checked by the dry run immediately before pushing.
