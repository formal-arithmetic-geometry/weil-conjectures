## Worker report

The module `Sheaf.CategoryTheory.OperadicActiveColimitExtensionCriterion` states the
conditional active-slice free-extension criterion.  It defines the active base and active
part of an operad, the active comma slice over a target colour, the canonical operation
cylinder, the tensor-diagram predicate, the two-sided fixed-object tensor functor, and the
preserved-colimit hypothesis.  It then states
`operadic_active_colimit_extension_criterion` with proof `sorry`.

The Lean statement renders the node as follows.  `pO` and `pP` are maps to the opposite
simplex base, with `hO` and `hP` the ordinary nonsymmetric operad predicates and
`hsmallO`, `hsmallP` the stated smallness hypotheses.  `q` is an arbitrary monoidal
infinity category with `hq`; no presentability or ambient cocompleteness is assumed.
`f` and `hf` are the inert-preserving operad map.  `HasPreservedActiveColimits` quantifies
all algebras `A`, target colours `b`, canonical tensor-cylinder representatives `D,H`,
and requires a coherent colimit cocone.  For every fixed tensor operation and fixed
objects `L,R`, it requires the mapped cocone for `(L ⊗ -) ⊗ R` to remain colimiting;
unit-valued or one-sided tensors are included by the tensor unit.  The conclusion gives
restriction `R`, its coherent left adjoint `L`, the literal precomposition equation for
restriction, coherent adjunction data, and for every tensor-cylinder representative a
colimiting cocone normalized by `IsSubstitutionCocone`.  The latter records the identity
operation unit and operadic substitution by two coherent triangles with the same long edge.

The nullary case is included by `Fin 0` in `IsMonoidalTensorOperation` and by the unit
transport in `IsTensorDiagram`; no nonempty or positive-arity assumption is made.  Empty
active slices are allowed (their colimit requirement is explicit).  The source and target
of every cylinder are equations of whole coherent functors, so higher homotopies are
retained.  No presentability assumption on `q` appears.

Dependency declarations used:

* `Sheaf.CategoryTheory.CompleteAlgebroid`: `SSet.Enhanced.Algebroid.tensorWith`,
  `SSet.Enhanced.Algebroid.algebras`-level interfaces and `SSet.Enhanced.Algebroid`
  monoidal fibre constructions.
* `Sheaf.CategoryTheory.PresentableInfinityCategory`:
  `SSet.Presentability.IsSmall` and coherent colimit preservation conventions.
* `Sheaf.CategoryTheory.NonsymmetricOperadsPresentability`:
  `SSet.Enhanced.NonsymmetricOperad.presentable` and its ordinary operad object model.
* `Sheaf.CategoryTheory.InertOperadColorReconstruction`:
  `SSet.Enhanced.InertOperad.algebras`, `algebraFunctor`, `algebraInclusion`, and
  `SSet.Enhanced.InertOperad.vertexFunctor`.
* `Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction`:
  `HomotopicalAlgebra.ModelInfinity.CoherentAdjunction`.
* `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`:
  `SSet.Enhanced.coconeCategory` and `SSet.Enhanced.IsColimiting`.

Searches for an existing declaration found no exact result.  `msearch.py ... leanfinder`
for “Operadic left Kan extension at a color computed by colimit over active operations”
returned only ordinary Kan-extension declarations; `msearch.py ... loogle "operad"`
returned zero hits; `msearch.py ... grep 'operad|[Oo]peradic|operadicActive'`
found only an unrelated Mathlib comment.  `rg` over `lean/Sheaf` and
`WeilConjectures` found no active-slice criterion.  The recorded Mathlib search in the
node likewise contains only ordinary Kan-extension results.  The source PDF was checked
at Proposition A.2.10, Propositions A.4.3--A.4.4 and Corollary A.4.5 (pp.703,705--706).

The retained packet was submitted to `deliver2.py --no-push` before repair. Its first
compile stopped in the overlay dependency `SpaceValuedStraightening.Diagrams`, which
reported a missing noncomputable annotation. A later required-wrapper run passed
against its current overlay without any change to that dependency. Final verification
is recorded below.

## Second reading by NV

I reopened the node and module.  The hypotheses correspond one by one: small ordinary
operads, arbitrary monoidal infinity category, inert-preserving map, per-algebra/per-colour
active-slice colimits, and preservation by every fixed two-sided tensor.  The conclusion
contains restriction, a coherent left adjoint, the mapping-space adjunction data through
`CoherentAdjunction`, objectwise active-slice colimit cocones, the identity-operation unit,
and operadic substitution coherence.  The active slice is built from the full coherent
comma object and retains all higher simplices.  The `Fin 0` and tensor-unit clauses cover
nullary operations. The independent immutable-head review subsequently found H4:
the local activity predicates duplicated existing definitions. The repair below
removes those predicates and uses their existing declarations; rereading their
formulas shows identical endpoint and active-edge conditions. No mathematical
statement change is needed.


## Repair of the immutable-head return

H4 is preserved: the returned module duplicated endpoint activity and active edges
already defined as `SSet.Enhanced.Nonsymmetric.IsActiveBase` and
`SSet.Enhanced.Nonsymmetric.IsActiveEdge` in
`Sheaf.CategoryTheory.OperadicWeakApproximation` (lines 39–49). The duplicate
`OperadicActiveExtension.IsActive` and `OperadicActiveExtension.IsActiveEdge`
definitions were removed, the existing module is imported, and `activeBase` and
`sliceSubcomplex` now use those existing predicates explicitly. The Lean declaration
list and note were updated. Their formulas are identical, including zero arity;
no mathematical statement correction is necessary.

The source and report at returned head `7c95da5a96cd` were compared with the retained
packet; they contained the same duplicate predicates, so the repair applies the H4
change rather than repushing the old packet. Current shared sources were searched
with `rg` for `IsActive`, `IsActiveBase` and `IsActiveEdge`, locating the exact
reusable definitions above. The theorem signature, hypotheses, and conclusion
remain as in the returned head.

The activity predicates are helper definitions in the existing weak-approximation
module, not uses of its weak-approximation theorem or predicate. The first dry run
rejected adding the whole weak-approximation node as a statement dependency because
that node reaches this criterion. That unnecessary node dependency was removed;
`stmt_deps` remains unchanged, while the actual Lean import reuses only the two
endpoint/active-edge definitions already spelled out in this item. The repaired
module compiled without a Lean import cycle.

## Final compile verification

The final replacement file was compiled with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py NV lem-coef-operadic-active-colimit-extension-criterion lean/Sheaf/CategoryTheory/OperadicActiveColimitExtensionCriterion.lean`.
The wrapper exited 0 and recorded successful separate sandbox and library checks:
`Sheaf/Stage2/Sandbox0.lean` (7.1 s) and
`Sheaf/CategoryTheory/OperadicActiveColimitExtensionCriterion.lean` (3.2 s).
Both compiler message sections were empty: no errors or additional warnings.
The only postponed proof remains the named criterion theorem.

## Maintainer review fix (cc reviewer, 2026-10-17)

The H4 repair imported `Sheaf.CategoryTheory.OperadicWeakApproximation` for
`Nonsymmetric.IsActiveBase`/`IsActiveEdge`. That module publicly imports
`Sheaf.CategoryTheory.OperadicAlgebraPresentability`, and the node
lem-coef-operadic-algebra-presentability lists this item as a proof dependency;
stages/2-statements.md §3.7 then adds this module's import there, which would close the
cycle AlgebraPresentability → this module → WeakApproximation → AlgebraPresentability
and block the stage-3 proof plan of that node. The identical predicates
`SSet.Enhanced.Operadic.IsActiveArrow` and `IsActiveEdge` of
`Sheaf.CategoryTheory.OperadicCorrespondence` (node def-coef-operadic-correspondence,
upstream of this item through lem-coef-generalized-active-extension-criterion) are used
instead: endpoint preservation `a.unop 0 = 0`, `a.unop (last m) = last n`, and an edge
lying over such a base arrow, with no cocartesian condition. The import closure of the
fixed module no longer contains OperadicAlgebraPresentability. Theorem signature,
hypotheses and conclusion are unchanged. Per-file compile through
`tools/nt_compile.py`: exit 0, no error and no warning.
