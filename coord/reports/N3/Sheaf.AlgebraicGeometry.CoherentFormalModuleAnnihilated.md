## What changed

In `lean/Sheaf/AlgebraicGeometry/CoherentFormalModuleAnnihilated.lean`, replaced the proof
of `LinearMap.ker_coker_reduction_annihilated_double` with clause (c), namely the second
conjunct, of `LinearMap.ker_coker_annihilated_mod_ideal`, applied to `J`. The hypothesis,
quotient submodules, induced `mapQ`, and both annihilator conclusions coincide exactly.
Explicit universe arguments specialize the unused naturality and converse clauses too;
otherwise projecting out clause (c) leaves universe metavariables in the declaration.

This follows step 3 of `lem-weil-pbc-formal-systems-annihilated-by-power`. The first worker changed only
one proof. The second reading additionally corrects proof-only import visibility, with no
signature, definition, declaration visibility, or node change; see
`coord/changes/CoherentFormalModuleAnnihilated-imports.md`. The unit
`sk-thm-p1` and all its realized statements and steps are preserved.

The whole module compiles using `lcompile.py`. LeanFinder, Loogle, and the launcher grep
search were run; none returned a shorter matching Mathlib result. The existing dependency
already contains the exact result, including different universe levels for source and target.

## Proved and sorry left

Closed one of the item's three holes:

- `LinearMap.ker_coker_reduction_annihilated_double`
  (`lem-weil-pbc-formal-systems-annihilated-by-power`), proved from the existing declaration
  `LinearMap.ker_coker_annihilated_mod_ideal`
  (`lem-weil-pbc-kernel-cokernel-annihilated-mod-ideal`). That dependency remains admitted;
  this is a stage-3 proof from a stated dependency, not a claim of axiom-free completion.

The following two named theorem holes are unchanged, both belonging to
`lem-weil-pbc-formal-systems-annihilated-by-power`:

- `AlgebraicGeometry.coherentFormalModule_annihilated_iff`.
- `AlgebraicGeometry.coherentFormalModule_annihilated_double`.

No holes were added, no new intermediate statements were introduced, and no hole was moved.
This is a partial delivery. The geometric proofs still require the transport from the
Spec-level affine equivalence to evaluation on an arbitrary affine open, identification of
the limit projections with quotient maps, and the local zero criterion for sheaf ideal
products. For the fourth condition, formal kernels must be transported through exact
restriction and the affine equivalence; they cannot be treated as termwise kernels.
Their existing docstrings and DAG proof remain the proof plan.

## No longer needed

None. No imports, nodes, or modules were pruned. The public re-exports of
`CoherentFormalModulesAffine` and `CoherentFormalModulesAbelian` are replaced by plain
proof imports, and `CoherentFormalModule` is exposed directly for the signatures. The geometric dependency imports are
retained for the two untouched geometric statements. The algebra dependency is used by
the completed proof, so its module and node remain needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The second reader found two geometric proof-only
dependencies incorrectly exposed as public imports and corrected their visibility. The existing commutative-algebra dependency
is sufficient as stated. Its seven universe parameters require explicit specialization
when using only clause (c), because clauses (b) and (d) quantify over additional modules
whose universes are not determined by the selected conclusion.

## Earlier second reading (a previous round; superseded)

1. Compared the complete delivered module with the repository. All three existing
   theorem signatures are byte for byte identical, with no data or definition changes.
   Only the algebra proof and the documented import visibility correction differ. Pass.
2. Compiled the module and a scratch copy printing axioms for all three declarations.
   Only `propext`, `Classical.choice`, `Quot.sound` and `sorryAx` occur. The completed
   algebra proof inherits `sorryAx` from the existing admitted dependency, as reported.
   The only direct holes are the two unchanged named geometric theorems; no forbidden
   declaration, hollow definition, or new hole is present. Pass for partial delivery.
3. No new or split-off statements or nodes exist. Independently checked the projected
   clause and its quotient map against the dependency: exactly the same hypotheses and
   both conclusions, including different source/target universes. The zero ideal, unit
   ideal and zero modules introduce no extra restriction. Repeated LeanFinder, Loogle
   and launcher grep searches with different queries; no shorter matching result. Pass.
4. The one-line projection is the shortest stated-dependency route. The two remaining
   geometric holes require affine transport and local checking, not another projection;
   no new decomposition was introduced. No imports or dependency nodes can be pruned
   from their retained plan. `sk-thm-p1` and its realized route remain unchanged. Fixed
   two proof-only public imports; the defining module is now public directly. All seven
   direct importers compile unchanged against the delivered compiled overlay. Pass.
5. Read the item and algebra dependency nodes, their proof steps, `proof_deps`, and
   `proof_origin`, together with the unit record. Item step 3 already explicitly invokes
   clause (c), exactly as the new proof does. The other dependencies remain the plan
   of the two unchanged holes, so no node update is required. Pass.

Changed import visibility and added
`coord/changes/CoherentFormalModuleAnnihilated-imports.md`, with the downstream scan
and users table. Updated this report. The first worker's proof is unchanged.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered module with the repository. All three existing theorem
   signatures are byte-for-byte identical. The only changes are the algebra proof and
   the proof-only import visibility correction recorded in the change record. Pass.
2. Compiled the module with `lcompile.py` and checked all three declarations with
   `#print axioms`. There are no forbidden declarations, hollow definitions, or
   unnamed holes; the remaining `sorryAx` comes only from the two unchanged geometric
   theorems and their admitted dependencies. Pass for this partial delivery.
3. No statements were split off and no new nodes were added. The algebra projection is
   exactly clause (c) of `ker_coker_annihilated_mod_ideal`, including its hypotheses,
   quotient maps, and both conclusions; no shorter library result was found. Pass.
4. The algebra proof is the shortest route through the stated dependency. The remaining
   geometric holes are unchanged, and no imports or nodes can be pruned. The unit
   `sk-thm-p1` route and all realized steps remain intact. Pass.
5. Read the item node, its proof dependencies and proof origin, and the unit record.
   The node's step 3 explicitly invokes clause (c), matching the delivered proof; the
   unchanged geometric imports remain needed by the other two holes. Pass.

The second reading changed only proof import visibility and added the associated change
record; no signatures, definitions, declarations, target statements, or DAG statements
were changed.

## Second reading by N3

1. Compared the delivered module with the repository. Existing theorem signatures and
   declarations are byte-for-byte unchanged; only the algebra proof and import visibility
   differ. Pass.
2. Compiled the module and all sandbox modules with `lcompile.py`. The file has exactly the
   two documented theorem `sorry`s, no forbidden declarations, and the completed theorem's
   axioms are limited to permitted axioms plus the admitted dependency's `sorryAx`. Pass.
3. Checked the projected clause against `LinearMap.ker_coker_annihilated_mod_ideal`; its
   hypotheses, quotient submodules, map, universes, and two conclusions coincide exactly.
   No new statements or nodes were introduced, and searches found no shorter result. Pass.
4. The completed proof is the shortest route through the stated algebra dependency. The
   two geometric imports remain needed by the open theorems; proof-only imports were made
   private and the defining `CoherentFormalModule` import remains public. The unit route is
   preserved and no nodes are pruned. Pass.
5. Read the item node, its proof dependencies and proof origin, and the unit record. The
   node's algebra step explicitly calls clause (c), matching the Lean proof; all remaining
   dependencies and realized unit steps remain unchanged. Pass.

Changed only the algebra proof and import visibility, and recorded the latter in the change
record. No statement, definition, declaration visibility, or DAG node was changed.
