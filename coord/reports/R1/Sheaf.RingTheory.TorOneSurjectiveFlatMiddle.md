## What changed

Repaired reviewer X-8ca5d C1 (returned head 8ca5de650), following the earlier
X-65165 point 4 interface repair, in
`Sheaf.RingTheory.TorOneSurjectiveFlatMiddle`. Replaced the arbitrary module-action
and scalar-tower binders on Tor with constructed canonical actions, and replaced
the existence of an unspecified R-linear epimorphism with surjectivity of the
constructed natural B-linear `CategoryTheory.torOneBaseChange`.

`torOneModule` sends a coefficient scalar to the Tor functor's image of its
multiplication endomorphism. Its module laws, additivity of coefficient maps,
R-linearity of coefficient maps, and restriction-of-scalars tower are proved.
`torOneCoefficientMap` is Tor applied to the R-linear algebra map A → B.
Its compatibility with coefficient multiplication is proved from functoriality.
The tensor-source B-action is transported through tensor symmetry from the
usual action on B ⊗[A] Tor; its pure-tensor scalar formula is proved.
`torOneBaseChange` is a balanced additive tensor lift, upgraded to a B-linear
map by tensor induction. `torOneBaseChange_tmul` proves exactly
`t ⊗ b ↦ b • torOneCoefficientMap(t)`. All constructed data is explicit;
no data or law is selected from an unproved existence theorem.

Updated the existing node's `lean.statement` and `lean.declarations`, and annotated
step 3 with the constructed interface and the fact that surjectivity remains
unproved. The mathematical `statement`, statement dependencies, unit route and
source origin are preserved. Proof dependencies now also record the two proved
coefficient-functor laws requested by reviewer X-8ca5d C1. All five Challenge targets
are untouched. The dispute marker is retained as requested until delivery.
No additional module or hole is created. Two DAG nodes are added for the
already proved additivity and R-linearity instances.

Change record: `coord/changes/torOne-surjective-flat-middle-canonical.md`.
It gives verbatim old and new signatures and lists every transitive importer
with its current holder and effect. `tools/downstream.py --uses` finds no
application outside the declaring module. An earlier preparation compiled the then-direct proof importer
`Sheaf.RingTheory.FlatOfLocalCriterionBaseChange` against the repair. At this
second reading the current repository has no import of this module and no
application of the changed declaration; no forced adaptation is necessary.

Validation: the repaired module compiles with `lcompile.py` without warnings.
The earlier importer compile predates its upstream replacement. The current
version no longer imports this item; its optional recompile during this reading
failed on the unavailable compiled module LocalizedBaseChangeQuotientFlat,
before checking its declaration. This is not validation of that newer importer. A scratch axiom check reports only propext, Classical.choice and
Quot.sound for the canonical action, scalar tower, coefficient map, base-change
map and pure-tensor formula; only the original surjectivity theorem uses sorryAx. No arbitrary-action instance is installed globally: the fixed actions
are selected explicitly by let-bindings in the repaired conclusion and map.

## Proved and sorry left

Holes closed: 0 of 1. Holes added: 0. Split off: 0.
This is the requested repair of a false interface, not a claim of proving
surjectivity or a decomposition of its argument.

The sole remaining hole is `CategoryTheory.torOne_surjective_flat_middle`
(node `lem-weil-pbc-tor-one-surjective-flat-middle`), now with the correct
canonical-action and specified-map signature. Its whole-body proof is `by sorry`.
The docstring gives the complete free-resolution, flat-quotient tensor
injectivity, cycle-surjection, and boundary-quotient argument from Stacks 00MM.

New proved laws, with no holes: `CategoryTheory.torOneSecondAdditive`,
`CategoryTheory.torHomology_map_smul`, `CategoryTheory.torOneSecondLinear`,
`CategoryTheory.torOneModule_smul`, `CategoryTheory.torOne_algebraMap_smul`,
`CategoryTheory.torOneScalarTower`, `CategoryTheory.torOneCoefficientMap_smul`,
`CategoryTheory.torOneTensorModule_smul_tmul`, and
`CategoryTheory.torOneBaseChange_tmul`. The module and map construction laws
inside `torOneModule`, `torOnePairing`, and `torOneBaseChange` are also complete.

## No longer needed

No original import, proof dependency, node or module is pruned. The remaining
surjectivity proof still requires the original source's cycle and quotient
argument. The second reader removed the redundant added public imports
`Mathlib.LinearAlgebra.TensorProduct.Tower` and
`Mathlib.Algebra.Module.TransferInstance`: their required declarations are
already available through the retained imports. Added proof-only imports are
Homology.ShortComplex.Linear and
CategoryTheory.Linear.FunctorCategory. No target-closure pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the superseded Lean signature allowed any compatible A-action
on the underlying Tor group. For ℤ → 𝔽₂ × 𝔽₂ → 𝔽₂ with the first projection
as algebra map and the second projection acting on Tor₁(𝔽₂,A), the source tensor
vanishes but the target is 𝔽₂. A scalar tower only fixes restriction to ℤ;
it does not impose the canonical A-action. This repair removes those binders.

The mathematical DAG statement and the source were correct: they specify the
natural map. Read [Stacks Tag 00MM](https://stacks.math.columbia.edu/tag/00MM)
and its free-resolution proof. The new action is the functorial multiplication
action of that proof, not an arbitrary action with an added hypothesis.
The new conclusion identifies the map rather than merely claiming some epi.
The prior delivery's dispute-only response did not satisfy reviewer point 4;
this delivery supplies the actual constructions and proved formulas requested.

Edge cases checked mathematically: when B=A with the identity algebra map,
functoriality makes the formula t ⊗ b ↦ b • t; when M is projective the Tor
objects vanish, consistently with Mathlib's projective Tor vanishing; when
B is the zero ring the target is zero and the pairing is zero. For the former
counterexample the canonical action is the regular action on 𝔽₂², so the
tensor source is 𝔽₂ and the specified map is the first projection after
base change. No nonzero-ring or faithful-action hypothesis was added.

Searches in `searches.jsonl`: LeanFinder for the canonical coefficient action
and flat-intermediate Tor surjection, Loogle for CategoryTheory.Tor', and
grep/direct rg in Mathlib and both project roots. No existing canonical Tor
module/map interface or ready surjectivity lemma was found. One Loogle query
had a quoting typo and was immediately rerun correctly; generic grep hits in
words containing “tor” were ignored. The construction uses Mathlib's existing
Tor, projective-resolution comparison, tensor universal property, and homology
scalar laws. No new mathematical notion duplicates the Tor definition:
`TorOne` is only an abbreviation of that existing object.

Reviewer X-8ca5d correctly noted that listing the two supporting instances in
`lean.declarations` did not state their mathematical results. This metadata
repair adds a separate node for each and records their actual uses. Both proved
implementations and the repaired surjectivity signature remain unchanged;
only their docstrings gain the corresponding blueprint identifiers. LeanSearch
was unavailable during the repair; its failures are recorded without claiming
a search verdict. Loogle, LeanFinder and targeted Mathlib grep were successful.
Blueprint searches for “Tor additive” and “Tor linear” found no matching node.

## New nodes

`lem-weil-pbc-tor-one-second-additive` states additivity of
N ↦ Tor'_1(M,N), and records the existing proved
`CategoryTheory.torOneSecondAdditive` instance in this item's module. Its
`lean.statement` is the verbatim instance signature. The adjacent
`lean_signature_context` records its universe, namespace and section variables, and
`lean_full_signature` expands all ring and module parameters explicitly. Its complete resolution-comparison proof,
source, search records and blueprint ancestry are recorded. No sorry is added.

`lem-weil-pbc-tor-one-second-linear` states R-linearity of the same functor and
records the existing proved `CategoryTheory.torOneSecondLinear` instance with
its verbatim signature, section context and expanded complete signature. Its proof records the additivity dependency,
the degreewise tensor scalar identity, the proved local homology scalar helper,
and scalar compatibility of the resolution-comparison morphisms. Both new
nodes are used in the parent node's canonical-action construction step and its
`proof_deps`. The unchanged change record remains
`coord/changes/torOne-surjective-flat-middle-canonical.md`.

The prior second reading predates these records and has been removed from this
report so it cannot certify this repair. The next independent second reader
must check both new mathematical statements against their complete Lean
signatures, their source/proof/search/blueprint fields, additivity as a linearity
dependency, and both new uses in the parent node. The reader should also confirm
that both implementations and the repaired surjectivity signature are unchanged.

## Second reading by R1

1. **Interfaces: pass with the declared repair.** Compared the whole module
   with the repository using diff. The sole existing declaration has the exact
   old and new signatures in the canonical-action change record. No existing
   definition or Challenge target is edited. The mathematical parent statement
   is unchanged. The replacement is the specified natural map of Stacks 00MM,
   not an arbitrary epi or an arbitrary compatible coefficient action.
2. **Kernel and data: pass.** Independently compiled the module cleanly with
   lcompile.py. A scratch copy printed axioms for all 19 declarations: only
   propext, Classical.choice and Quot.sound, except sorryAx for the original
   surjectivity theorem. There is exactly one whole-body named theorem hole,
   with its source and complete resolution/cycle/quotient proof. No forbidden
   declaration or data choice from an unproved existence theorem occurs. Read
   all constructions: multiplication endomorphisms give the coefficient action,
   Tor of the algebra map gives the coefficient map, and the balanced tensor
   lift gives the stated B-linear natural map.
3. **Supporting statements: pass.** No holed statement was split off. Both new
   nodes have verbatim Lean signatures, explicit section context and full
   signatures; their mathematical statements are exactly the additive and
   R-linear functor instances. Their resolution-comparison proofs match the
   implementations. Linearity requires the proved additivity instance, recorded
   in both statement and proof dependencies. Source, search, creation and
   blueprint fields are present. Checked zero maps/scalars, the zero module,
   B=A, projective M and B=0: no missing hypothesis or incompatible action.
   Independently searched with Loogle for leftDerived/Linear and LeanFinder
   for additivity of derived coefficient maps, plus targeted rg in Mathlib,
   both library roots and slopmaster2. No ready replacement for these laws or
   the surjection was found. The msearch grep returned unrelated word matches;
   it supplies no positive match. The new nodes are strictly supporting laws,
   not restatements of surjectivity.
4. **Route and pruning: pass after import cleanup.** Read Mathlib Tor and
   leftDerived_app_eq and checked Stacks https://stacks.math.columbia.edu/tag/00MM.
   The source's cycle-surjection and boundary-quotient argument stays as the
   unproved parent, honestly counted as zero holes closed and zero added. All
   original proof dependencies remain, and sk-thm-p1's realized statement and
   steps are untouched. Removed redundant proof-only Homology.Linear: Tor
   publicly reaches it through Projective.Resolution and HomotopyCategory.
   Independent removal probes show ShortComplex.Linear and Linear.FunctorCategory
   are needed only by proofs, so their plain imports are appropriate. No
   original node or target-closure module is claimed pruned.
5. **DAG: pass.** The existing node changes only lean, proof and proof_deps.
   Its new uses include both supporting laws; proof_deps is the union of uses.
   All old dependencies are retained for the remaining planned proof. New node
   proofs, origin and declarations agree with the Lean; neither depends on the
   unproved parent. The canonical map and action signatures remain those of
   the first worker's repaired implementation.

Second-reading changes: removed one redundant proof-only import and corrected
the report and change record's import count. Updated stale importer-validation
claims to distinguish the earlier successful compile from the current upstream
replacement, which no longer imports this module. No statement, definition,
proof body, node or hole was changed.
