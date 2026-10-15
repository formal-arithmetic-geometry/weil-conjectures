## What changed

Proved all three holes in `Sheaf.RingTheory.ProEtale.ClosedLiftMap`, preserving every
existing signature, visibility, docstring and construction:

- `Algebra.ClosedLift.ι_toAlgHom`: express algebra-map composition as the underlying
  morphism of the categorical composition, apply `colimit.ι_desc` to `coconeC`,
  and unfold its component by reflexivity.
- `Algebra.ClosedLift.postcomp_compatible`: reassociate with `AlgHom.comp_assoc`
  and substitute the indexing morphism's `comp_toC` field.
- `Algebra.ClosedLift.ι_map`: apply `colimit.ι_desc` to the cocone whiskered by
  `postcomp`; its component is definitionally the desired coprojection.

Removed three unused public imports. The change record is
`coord/changes/closed-lift-map-import-pruning.md`. No consumer requires adaptation.
The target module compiles cleanly in about two seconds. All 25 transitive downstream
sources were checked individually against its sandbox replacement: 24 compiled and one
already fails on the unchanged baseline, as detailed below. The dry run additionally
checks the axioms of every declaration. No global library build was run.

Searches used `msearch.py` with LeanFinder for the colimit factorization identity, Loogle
for `CategoryTheory.Limits.colimit.ι_desc`, and grep for factorization/associativity.
LeanFinder and Loogle both returned `colimit.ι_desc`, whose exact type was checked
with Lean. Source-library and project searches found no duplicate closed-lift identities.

## Proved and sorry left

Closed 3 of 3 original holes, all attached to node `def-exc-ind-etale-closed-lift`:

- `Algebra.ClosedLift.ι_toAlgHom`.
- `Algebra.ClosedLift.postcomp_compatible`.
- `Algebra.ClosedLift.ι_map`.

No `sorry` remains in this module. No holes, intermediate statements or modules were added.
The final proofs use Mathlib and the existing definitions directly; no unproved project
theorem is used. Scoped instance disabling prevents an implicit dependence on the upstream
open filteredness theorem. The upstream filteredness and reduction theorems are untouched.

## No longer needed

Removed these unused import edges:

- `Sheaf.RingTheory.IndPrincipalZariski`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `Mathlib.RingTheory.FinitePresentation`.

The only retained import is `WeilConjectures.RingTheory.ProEtale.ClosedLift`, which provides
the indexing category, diagram, colimit and retained map used in the signatures.
The removed scheme-etale and finite-presentation imports supplied no additional definition
needed here; the principal-ind-Zariski notion is absent from these statements and proofs.
No DAG node or entire module is asserted to become globally unreachable: other consumers
still import the principal-ind-Zariski module explicitly. No unit-route node is bypassed.
The definition node retains its empty proof-dependency list. The second reading records
the three direct structural arguments in its proof and proof_origin fields.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or DAG step needed correction. Unlike the brief's generic
expectation of a long decomposition, this module consists of two colimit factorization
identities and one associativity identity; all are proved directly. Its three extra
public imports were unnecessary. The unit record's realized statement/step arrays contain
no node that this pruning would bypass. No definition, target, statement, or unit route changed.


Broader-check limitation: the untouched
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport`
fails with and without the sandbox overlay at lines 100, 106, 114 and 120. The error is
an application of `preservesFiniteColimits_tensorLeft_sheaf` passing a `Scheme` where the
current compiled declaration expects a `MonoidalCategory Ab` instance. The same module
was copied into a separate scratch root with no overlay and reproduced that error, so
this is not a forced adaptation caused by the import pruning. It is left untouched.
All four direct importers pass. `TargetsCheck` also compiles; its existing line 20
produces a long-line warning. These findings are reported rather than changing unrelated
modules. Scratch verification output is in `scratch/importer-results.json` and the baseline
check in `scratch/compact-support-baseline.log` within this sandbox.

## Second reading by E3

1. **Interfaces — pass.** Compared the complete module with the read-only repository
   version. All existing declaration signatures, visibility, docstrings and definition
   bodies are byte-for-byte unchanged. The three public-import removals are declared in
   `coord/changes/closed-lift-map-import-pruning.md`. No other module is delivered.
2. **Proof and axioms — repaired, pass.** Independently compiled the module and checked
   `#print axioms` for all five declarations in a scratch copy. The initial delivery's
   `ι_toAlgHom`, `map` and `ι_map` inherited `sorryAx`: typeclass search selected general
   colimits through the open `Algebra.ClosedLift.isFiltered_index` instance. Added
   command-scoped `attribute [-instance] isFiltered_index in` for exactly those three
   declarations. General commutative-algebra colimits now suffice. The final five
   declarations use only `propext`, `Classical.choice` and `Quot.sound`; there is no
   `sorry`, new axiom, unsafe code or hollow definition in the delivery. These scoped
   commands restore the instance immediately and do not change downstream attributes.
3. **Split statements — pass, none.** No statements, holes or modules were split off.
   Checked the indexing category and cocone constructions, including zero-ring inputs:
   the identities hold by the colimit universal property and composition alone, without
   ind-etaleness, filteredness or a nonzero hypothesis. Searched Mathlib's colimit API
   and the project ring-theory sources for factorization and postcomposition identities.
   The existing `colimit.ι_desc` and `AlgHom.comp_assoc` are already the direct route.
4. **Route and pruning — pass.** The proof uses the shortest structural identities and
   retains only the import needed by its statements and definitions. The removed imports
   and absence of globally pruned nodes/modules are fully listed above. Read the unit's
   `realized` arrays: no unit statement or step is bypassed. Independently recompiled all
   four direct importers against the final sandbox replacement. All passed unchanged.
   The first worker's broader 25-module checks and baseline limitation are retained as
   evidence from that earlier check, rather than represented as a new global build.
5. **DAG — repaired, pass.** Read the complete definition node and its unit. Updated only
   `proof` and `proof_origin` to record the three direct structural arguments; its
   `proof_deps` remains empty. No new node is needed. In particular, the repaired
   elaboration does not add a dependency on the filteredness node that already depends
   on this definition.

Second-reading changes: removed the implicit open filteredness dependency through three
command-scoped instance exclusions; synchronized the node's proof metadata; clarified
this report and the existing import-pruning change record. No mathematical statement,
construction, docstring, unit route or consumer source changed.
