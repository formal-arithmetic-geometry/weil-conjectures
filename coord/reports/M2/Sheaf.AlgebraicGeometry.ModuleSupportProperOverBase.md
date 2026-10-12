## What changed

Repair of return F1 (reviewer X-77b04): added the two requested direct-importer rows,
`Sheaf.Paper.FiniteStructureAlgebraLift` and `Sheaf.Paper.FiniteStructureProperSupport`,
after the former line 24 of `coord/changes/ModuleSupportProperOverBase-proof-import.md`.
The Lean proof, statements, imports, and node are unchanged by this repair.

Replaced the sole sorry in `AlgebraicGeometry.Scheme.Modules.module_support_proper_over_base`
with a complete Lean proof from existing declarations. The theorem signature and existing docstrings are unchanged. The second reading
made `ClosedImmersionPushforwardAnnihilated` a plain import because only the proof uses it. Closedness is the final clause of
`finite_type_module_support_closed`. `schemeTheoreticSupport` supplies the annihilator ideal,
its closed immersion, exact support image, and annihilation. The second clause of
`closedImmersion_pushforward_annihilated` supplies quasi-coherence, finite type, and an
invertible unit for the explicitly constructed tensor pullback, yielding the pushforward
isomorphism. The closed-subset properness properties prove both directions of properness.

For the converse characterization, use the isomorphism already present in the hypothesis:
`closedImmersion_pushforward_stalks` makes the pushforward stalk zero off the image, and
injectivity of the isomorphism on stalks transports this to F. Its closed support is therefore
a closed subset of the proper image. Added a private proof import of
`Sheaf.AlgebraicGeometry.ClosedPushforwardStalks` and updated the existing node's fourth
proof step, proof dependencies, and proof origin to describe this route. The import-direction
check permits the added import. No new data definition or choice of an arbitrary module
witness was introduced: G is the tensor pullback, and the adjunction unit used is the one
fixed by the existing canonical section formula.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.Modules.module_support_proper_over_base`
(node `lem-weil-pbc-module-support-proper-over-base`). There are no sorrys left in the
item and none added elsewhere; zero statements split off. This is a proof from existing
named dependencies, not an unconditional closure of their remaining holes:
`finite_type_module_support_closed`, `schemeTheoreticSupport`,
`closedImmersion_pushforward_annihilated` remain existing upstream obligations.
`closed_subset_proper_over_base_properties` and the added stalk theorem now have proofs
in the repository; their own imported obligations remain outside this delivery.

Local compilation passes without errors or warnings. The proof handles zero modules,
empty closed subschemes, and empty schemes: no support point or section is assumed to exist.
No target signature, intermediate statement, or definition changed. The second reading
removed the public re-export of the proof-only annihilation theorem module.

## No longer needed

The public re-export of `Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated`
is no longer needed; the proof retains it as a plain import.

Removed redundant direct proof imports of `Sheaf.AlgebraicGeometry.TensorPullback` and
`Sheaf.Topology.PresheafModuleStalkFunctor`. The former is already publicly available through
`ClosedImmersionPushforwardAnnihilated`; the latter's extra module-stalk definitions are
unused, since the proof uses Mathlib's abelian stalk functor. Their conceptual definition
nodes remain used where appropriate; this does not claim either module becomes unreachable
from every target. All original mathematical proof-dependency nodes remain needed. No
additional nodes or modules are claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original fourth step proves support inclusion directly
from ideal annihilation; the Lean statement also provides a pushforward isomorphism, allowing
the shorter existing closed-pushforward-stalk argument. This is a change below the unit level.
The `sk-thm-p1` realized statement and steps are untouched. The original docstring records
the original valid proof plan; the node and this report describe the implemented variant.

Source checked against Stacks Cohomology of Schemes Lemma 0CYS and Sheaves Lemma 00AE
in the locally available Stacks source copies. Searches used the prescribed msearch
LeanFinder, Loogle, and grep routes, plus source search; no complete existing theorem
matching all three conjuncts was found.

## Earlier second reading (a previous round; superseded)

1. Compared the sole delivered Lean module with the repository by `diff` and checked the
   existing theorem signature byte for byte: unchanged. There are no new declarations,
   data definitions, statement changes, or statement change records. The import visibility repair has the change record
   `coord/changes/ModuleSupportProperOverBase-proof-import.md`. Verdict: pass.
2. Compiled the module locally without errors or warnings. A scratch-copy `#print axioms`
   reports only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`, the last coming
   from existing upstream obligations listed above. No sorry or forbidden declaration
   occurs in the delivered module. The chosen adjunction has its unit fixed sectionwise;
   G is the explicit tensor pullback. The ideal supplied by schemeTheoreticSupport is
   determined on every affine open and is used within a proof of existence, not a new
   data definition. Verdict: pass relative to the named open dependencies.
3. No statements were split off, so no new truth, docstring, or node obligations arise.
   Read the used dependency signatures and checked zero modules, empty subschemes, and
   empty schemes: the proof never assumes a point or nonzero section exists. Fresh
   LeanFinder search with different wording and `rg` of both library roots found no
   shorter complete existing theorem. Verdict: pass.
4. The proof opens the original hole and combines the existing support, annihilation,
   and properness theorems. The converse uses the proved closed-pushforward-stalk theorem.
   The two removed direct imports are redundant; all old proof-dependency nodes remain
   conceptually used, and no globally unreachable module is claimed. Checked the
   `sk-thm-p1` realized fields: this item realizes no unit statement or step and the unit
   route is preserved. Found one pre-existing proof-only public import and made it plain.
   Verdict: pass after that import repair.
5. Checked the delivered node against Lean and its original record: only allowed proof
   fields differ, proof_deps is the union of the steps' uses, and there are no new nodes.
   Repaired step 5 to describe only the implemented tensor-pullback witness construction;
   its former converse-annihilation paragraph described an unused argument. Verdict: pass.

Second reading changed the proof-only import of
`Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated` from public to plain,
corrected node proof step 5, and updated this report. No Lean proof body changed.

The corrected dry run passes compilation and preflight with the import change record.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only the proof and proof-only import visibility differ. Verdict: pass.
2. Compiled the delivered module with `lcompile.py`; it succeeds without errors or warnings. The module contains no `sorry`, forbidden declarations, or hollow definitions. The proof uses the explicit tensor pullback and existing adjunction unit, and any remaining `sorryAx` can only arise from named upstream dependencies. Verdict: pass.
3. No statements were split off and no new nodes were added. The converse stalk argument is valid for zero modules and empty supports, and the forward witness is determined by the scheme-theoretic support construction. Searches and repository inspection found no duplicate theorem that subsumes this result. Verdict: pass.
4. The proof follows the existing unit route through finite-type support closedness, scheme-theoretic support, proper closed-subset properties, and pushforward annihilation. The converse uses the existing closed-pushforward-stalk theorem. The removed direct imports are unused, while the annihilation module remains a plain proof import. Verdict: pass.
5. The node proof, proof dependencies, and proof origin agree with the Lean proof, including the tensor-pullback witness and stalk argument. No unit statement or realized step was changed. Verdict: pass.

Changed during this reading: no final Lean proof changes; verified the existing proof-only import repair and metadata alignment. A temporary proof adjustment was reverted. An initial dry-run attempt reported `FAILED: nothing is proved`; the completed subsequent dry run accepted the item as a repair of a returned delivery and passed compilation and preflight. The scratch axiom check reports only `propext`, `Classical.choice`, `Quot.sound`, and upstream `sorryAx`.


## Second reading by M2

1. Compared the sole delivered module with the read-only repository using `diff` and
   programmatically compared the entire theorem header up to `:= by`: byte-for-byte
   identical. Existing docstrings and definitions are unchanged. The public-to-plain
   annihilation import is explicitly recorded in
   `coord/changes/ModuleSupportProperOverBase-proof-import.md`. Read the sole return,
   F1 from X-77b04, and verified both requested importer rows are present. Compiled
   scratch copies of the unchanged `Sheaf.Paper.FiniteStructureAlgebraLift` and
   `Sheaf.Paper.FiniteStructureProperSupport` against the delivered module; both pass
   without warnings. Verdict: pass.
2. Compiled the delivered module with `lcompile.py`: no errors or warnings. Compiled
   a scratch copy with `#print axioms` for
   `AlgebraicGeometry.Scheme.Modules.module_support_proper_over_base`: exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The last comes from
   existing imported obligations; the delivered module has no sorry, new definition,
   axiom, unsafe, opaque, implemented_by, or extern. Read the annihilation theorem and
   `exists_tensorPullbackAdjunction`: the witness G is the explicitly constructed
   tensor pullback, and the adjunction unit is specified sectionwise. The chosen ideal
   is fixed on every affine open by the annihilator equality; no arbitrary witness
   is installed in a data definition. Verdict: pass relative to imported obligations.
3. No statements split off and no holes added. Read Stacks source copies under
   `/home/ubuntu/work-bp/sheaf/literature/stacks-project/`: Cohomology of Schemes 0CYS,
   `lemma-module-support-proper-over-base`; Morphisms 01QY,
   `lemma-i-star-equivalence`; Sheaves 00AE, `lemma-stalks-closed-pushforward`.
   Checked their finite-type, quasi-coherence, local finite-type, and closed-image
   hypotheses against the used signatures. The zero module and empty schemes or
   subschemes require no nonempty witness or point. A fresh LeanFinder query
   "quasi coherent sheaf supported on a proper closed subscheme pushforward finite type"
   returned ideal-sheaf support and finite-type definitions, no complete replacement;
   repository searches for support/properness found no shorter duplicate. Verdict: pass.
4. Read the proof from its three target conjuncts downward. Closedness uses the last
   clause of `finite_type_module_support_closed`; `schemeTheoreticSupport` supplies
   hI, hker, hrange, and hkill. The annihilation theorem supplies the tensor pullback
   and invertible unit. Properness uses the existing closed-subset properties in both
   directions. In the converse, the closed-pushforward stalk theorem gives vanishing
   off the image, and injectivity of the mapped module isomorphism transports it to F;
   closed-subset inheritance concludes. The removed direct tensor and module-stalk
   imports are unnecessary; all old mathematical dependency nodes remain used.
   `## No longer needed` lists those imports and claims no globally pruned module.
   Read `dag/units/sk-thm-p1.json`: this node realizes no unit statement or step, and
   no realized field or unit route is changed. Verdict: pass.
5. Compared the delivered node with its original: only `proof`, `proof_deps`, and
   `proof_origin` differ. Checked each proof step against the Lean: steps 1–3 use
   the support construction and properness equivalence, step 4 describes exactly
   the implemented stalk argument, and step 5 constructs the tensor-pullback witness.
   Programmatically checked that proof_deps is precisely the union of step uses
   and that no old proof-dependency node was omitted. There are no new nodes.
   Verdict: pass.

Changed during this reading: corrected the report's stale assertion that
`closed_subset_proper_over_base_properties` still has an unproved body; its repository
version now has a proof. Appended this independent reading and rechecked the F1 repair.
The delivered Lean proof and DAG were already correct and were retained unchanged.
