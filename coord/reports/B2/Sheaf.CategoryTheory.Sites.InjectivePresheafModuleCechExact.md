## What changed

Corrected the already disputed intermediate theorem
CategoryTheory.injective_presheaf_module_cech_cocycle_lift so homs, rings,
module values, and family indices share universe v. No target changes.
Implemented its proof from an actual free module chain complex. The private
freeCochainEquiv evaluates morphisms on (t,id), its inverse uses the free module
adjunction, and freeCochainEquiv_boundary proves compatibility with the exact
alternating restriction differential. ShortComplex.Exact.descToInjective extends
the cocycle morphism; comp_descToInjective proves the resulting primitive equation.
No object is chosen from an unproved existence theorem.

Added Sheaf.CategoryTheory.Sites.SiteCechFreeComplexExact. Its tuple presheaves,
index maps, simplicial object, and alternating free complex are fully constructed;
the simplicial laws follow from the chosen product universal properties. Only
positive-degree exactness is split off as a named theorem with its source, full
proof in words, and node. It has no coefficient module or injectivity hypothesis,
so it is strictly one part of the original argument, not a renamed cocycle theorem.

Changed only the proof body of the unclaimed direct user
Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic, preserving every signature
and visibility. The original body fails against the corrected interface; its named
theorem is reopened rather than hidden behind a nested hole. See Forced adaptations.
The change record is coord/changes/injective-presheaf-module-cech-universes.md.

## Proved and sorry left

Closed the item's one hole, after correcting its false universe signature:
CategoryTheory.injective_presheaf_module_cech_cocycle_lift
(node lem-weil-pbc-injective-presheaf-module-cech-cocycle-lift).
No sorry remains in the item's module or its private helpers.

Added one strictly smaller split-off hole:
CategoryTheory.SiteCechComplex.freeComplex_exactAt
(node lem-weil-pbc-site-cech-free-complex-exact).

Reopened one existing downstream theorem as a forced adaptation:
CategoryTheory.injective_module_cech_cohomology_isZero
(node lem-weil-pbc-ringed-site-injective-module-cech-acyclic).
Its existing signature, visibility, source, and proof docstring are preserved.
This is a corrected-statement decomposition plus an explicit downstream regression:
one upper hole closed, one split off, and one downstream hole reopened. It is not
net sorry progress and it is not an axiom-free proof of the corrected theorem.

Local lcompile.py --all compiled the three-module set without errors or warnings.
The original downstream module compiled against the baseline but failed against
the corrected dependency. The adapted module compiles against the delivered set.
The delivery dry run is the final validation step.

Edge cases checked mathematically: q=0 uses exactness at chain degree one,
never degree zero. Empty families give empty tuple bases and zero cochains.
An empty lift fibre contributes zero; nonempty fibres contract by insertion.
No global section of the family or covering hypothesis is added. Arbitrary product
choices and infinite families are covered by the same universal-property argument.
The common universe is the required size condition; no ring commutativity is used.

## No longer needed

Removed the item's direct proof import Sheaf.Paper.PowerSetComplexContractible.
Its node lem-weil-pbc-power-set-complex-contractible is no longer a direct
dependency of the cocycle theorem; it remains needed by the new freeComplex_exactAt
proof plan. Thus no global module pruning is claimed.

The coproduct/free-representable construction is implemented directly as the free
module presheaf on a disjoint union of representables, without categorical coproduct
comparison modules. The existing free Yoneda node remains in the proof plan;
Mathlib's freeHomEquiv and explicit naturality implement its coproduct form.
PresheafFreeNerveExact and PresheafFreeNerveComparison are not imported: they use
a different categorical nerve, and constructing a comparison to that nerve would
add another layer of glue. FreeCechComplexExactK1 is not imported: its interface
requires a ring sheaf and a covering. Those hypotheses are absent here.

The unit sk-prop-cd has empty realization lists for this item. No unit statement
or step is bypassed. No module is claimed globally unreachable. All three original
public imports remain; the new proof import is private to the module.

## Where the brief, the DAG or earlier work was wrong

The original theorem is false with independent universes, as the reviewed C1
report established. The original DAG omitted the size condition necessary to
apply injectivity to free representables. The downstream proof then used the
false unrestricted theorem; its original general signature cannot invoke the
corrected theorem. This delivery makes that dependency failure explicit.

The existing general ringed-site statement is not asserted false: HasSheafify,
WEqualsLocallyBijective, and covering hypotheses may support a different proof.
Its old free-presheaf proof does not justify its independent universes. The
unclaimed downstream module therefore needs a separate proof or coordinated repair.

The cited Stacks tex file is absent from this clone. Read the official Stacks
pages https://stacks.math.columbia.edu/tag/03FC,
https://stacks.math.columbia.edu/tag/03F5 and
https://stacks.math.columbia.edu/tag/03AT. Tag 03F5 explicitly applies to presheaves
of rings and arbitrary families with products, so it justifies the new exactness
lemma without a topology. LeanFinder, Loogle, launcher grep and local source
searches ran; LeanSearch returned Internal Server Error and is recorded unavailable.
The tool requires LeanSearch as a separate search kind even though the machine
brief listed LeanFinder, Loogle, and grep; all four were attempted.

Compilation briefly encountered a full shared disk. It subsequently recovered
without changing files outside the sandbox; affected local artifacts were rebuilt.

## New nodes

lem-weil-pbc-site-cech-free-complex-exact states exactness of the fully constructed
free chain complex in positive degrees. Its source is Stacks Tags 03F5 and 03AT.
Its proof is objectwise: partition generators by the map to U, identify each fibre
with tuples of lifts, apply the power-set contraction, take direct sums, and reflect
exactness through evaluation. It has no M or injectivity hypothesis, and provides
only the chain-complex step used by the proved Yoneda/extension argument.

The existing cocycle node's statement, Lean signature, proof, dependencies, and
proof origin are updated. Its statement_change names the only DAG citer and marks
its old use invalid. The original unit and chapter are unchanged. The existing
ringed-site theorem already has its node; no duplicate statement node was added.

## Forced adaptations

Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic is unclaimed.
The original compiler errors against the delivered dependency at line 77 were:

```
failed to synthesize instance of type class Category.{w, u} C
Application type mismatch: c has cochain carrier universe max s w,
but the corrected theorem expects cochain carrier universe w.
Application type mismatch: S has type SiteCechComplex.{u, v, w} f hom,
but the corrected theorem expects SiteCechComplex.{u, w, w} f hom.
```

Only the proof body following the unchanged signature is changed (original
lines 68–78). Replace the obsolete reduction with `by sorry`. Keeping only the
failed application as an inner hole would violate the rule requiring every hole
to be an entire named theorem. No import, signature, visibility, public helper,
universe command, or unrelated line changes. The original full source is saved
under scratchpad for comparison and compiled against the changed dependency.
The delivery tool independently repeats the baseline and counterfactual checks.

## Second reading by B2

1. Compared both existing delivered modules with the repository using diff.
   The sole signature change is the declared repair of the already disputed
   presheaf theorem, recorded in injective-presheaf-module-cech-universes.md.
   The downstream signature, visibility, imports and docstring are byte for byte
   unchanged. No target or existing definition changes. Verdict: pass as a
   recorded intermediate-statement correction, not a proof of the old statement.

2. Independently compiled the three modules in import order with lcompile.py.
   No errors or warnings. Inspected all proof bodies and definitions: the only
   holes are freeComplex_exactAt and the reopened
   injective_module_cech_cohomology_isZero, both entire named theorems listed
   above. No forbidden declarations or hollow data constructions. A scratch
   #print axioms check shows only propext, Classical.choice and Quot.sound for
   tuplePresheaf, tupleMap, tupleSimplicial and freeComplex; the exactness,
   lifting and reopened downstream theorems additionally use sorryAx.
   The delivery probe checks all declarations, including the private helpers.
   Verdict: valid reduction with explicitly open dependencies, not an
   axiom-free proof and not net hole progress.

3. Read the exactness statement, its actual constructed complex, the universal
   properties and the complete docstring proof. Independently read official
   Stacks Tags 03F5 and 03AT. Checked empty indices, empty/nonempty lift fibres,
   q=0, repeated indices, arbitrary product choices and infinite families.
   Positive-degree exactness needs neither a covering nor an injective module.
   The split is strictly the chain-exactness part; Yoneda comparison, differential
   compatibility and injective extension are proved in the item's module.
   Independent LeanFinder search for an extra-degeneracy contraction and Loogle
   search for alternatingFaceMapComplex exactness found no direct match.
   Local searches identified Mathlib ExtraDegeneracy.homotopyEquiv, the upstream
   abelian-presheaf/cofree Cech theorem, PresheafFreeNerveExact and
   FreeCechComplexExactK1. They require extra constructions, different complexes,
   abelian rather than module injectivity, or stronger size/site hypotheses;
   none directly closes this statement in a few minutes. Verdict: pass.

4. Checked the target-downward reduction, each import and the old proof_deps.
   The direct PowerSetComplexContractible import is the sole removed dependency;
   it remains in the smaller exactness theorem's plan and is not globally pruned.
   The free Yoneda Mathlib leaf is realized here by the explicit coproduct
   version built from freeHomEquiv, with inverse laws proved, so its mathematical
   step is retained. Public imports supply signature types, the constructed
   free complex, or abelian/homology instances; proof-only new imports are plain.
   sk-prop-cd has empty realized lists, and no unit step is bypassed.
   Verdict: pass; no globally pruned module is claimed.

5. Compared both new/updated node statements and signatures with Lean, checked
   proof-step dependency unions, source, creation, blueprint and unit fields.
   Found the downstream node still described its now-invalid application as a
   valid step. Added its node to the delivery, changing only proof/proof_origin:
   the universe-size step is explicitly unresolved and the named theorem is
   reopened. Its statement, dependencies and Lean interface remain unchanged.
   Verdict: pass after this metadata repair.

Second reading changed only the stale downstream DAG proof description and this
report. No Lean proof or signature was changed during the second reading.

## Forced adaptations

### Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic
Original against changed dependencies failed:
```
/tmp/forced-adaptation-6cdy40ww/lean/Sheaf/CategoryTheory/Sites/InjectiveModuleCechAcyclic.lean:77:76: error: Application type mismatch: The argument
  c
has type
  AddCommGrpCat.carrier.{max s w} (HomologicalComplex.sc' (S.complex I.val.presheaf) q (q + 1) (q + 2)).X₂
of sort `Type (max s w)` but is expected to have type
  AddCommGrpCat.carrier.{w} (SiteCechComplex.cochains ?m.256 (PresheafOfModules.presheaf ?m.250) (q + 1))
of sort `Type w` in the application
  injective_presheaf_module_cech_cocycle_lift ?m.245 ?m.250 f ?m.255 ?m.256 q c
/tmp/forced-adaptation-6cdy40ww/lean/Sheaf/CategoryTheory/Sites/InjectiveModuleCechAcyclic.lean:77:10: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Category.{w, u} C

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
/tmp/forced-adaptation-6cdy40ww/lean/Sheaf/CategoryTheory/Sites/InjectiveModuleCechAcyclic.lean:77:72: error: Application type mismatch: The argument
  S
has type
  SiteCechComplex.{u, v, w} f hom
of sort `Type (max (max u v) w)` but is expected to have type
  SiteCechComplex.{u, w, w} f ?m.255
of sort `Type (max u w)` in the application
  injective_presheaf_module_cech_cocycle_lift ?m.245 ?m.250 f ?m.255 S

(with the modules compiled into /tmp/forced-adaptation-6cdy40ww/.lbuild) [4.1 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
