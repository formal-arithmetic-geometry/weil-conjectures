## What changed

Proved `AlgebraicGeometry.Etale.finiteEtale_lifts_scheme_torsor` with its signature unchanged.
The assigned module contains the complete proof and private helpers only; there are no new modules.
The representation constructions follow the sorry-free part of
`WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent` (lines 57–478), with private
names under `Scheme.EtaleTorsor.SchemeLiftRepresentation`. This avoids importing that module's
`HenselianFiniteEtale` dependency, which already reaches the assigned module. The private finite-local-constancy helper states the two underlying conditions directly rather than using
`Scheme.IsFiniteLocallyConstantSheafOfTypes`, whose definition is in that cyclic module.
The lower `finiteLocallyConstant_sets_representable` theorem supplies the representing scheme.
No definition chooses data from an unproved mere-existence theorem.

Fullness lifts every action endomorphism and faithfulness proves the action equations.
Private helpers explicitly establish coproduct and product universal properties in the finite
étale category. Preservation by the equivalence and uniqueness of limit and colimit objects
identify the simple-transitivity morphism downstairs; an equivariant scheme isomorphism
conjugates it to the torsor morphism of t₀. Reflection then proves invertibility upstairs.
The clopen image argument proves surjectivity, also without a nonempty-base assumption.

Added proof-only imports for geometric points, finite coproducts of finite morphisms,
and the closedness of a clopen open immersion. The second reading removed seven redundant
proof-only imports; their declarations are already available through the retained imports. The image argument still uses properness and universal openness through retained imports.
Updated the item's DAG proof to the actual argument. No statement or public definition changed.
The preflight command-scope over-approximation is documented in
`coord/changes/finite-etale-scheme-torsor-lift-private-proof-scope.md`; no user needs adaptation.

Validation: the module was repeatedly compiled with lcompile.py. The empty-base case is
included in all constructions (empty covers and stalk conditions are vacuous). The trivial
group case is included. The equivalence, rather than a surjectivity assumption on i, reflects
the clopen image inclusion. No helper contains sorry.

Repair validation: removed the four declarations named in the landing return:
`reprE_inv_hom`, `reprE_inv_map`, `reprVadd_add`, and
`toSheafTorsorContinuousMap_ofRepresentable_equiv` under the private representation namespace.
Cancellation now uses Mathlib's concrete `Iso.hom_inv_id_apply` and `Iso.inv_hom_id_apply`
through the section functor; both directions apply to arbitrary sheaf isomorphisms.
Naturality uses the existing `NatTrans.naturality_apply`. The action-addition field and
sheaf-torsor equivariance are checked in their constructions, with no duplicate standalone
lemmas. No source-library module is adapted.

The current landing check also identified additional copied signatures. Generalized
`exists_fiberOpens_comp_sigmaι` to varying scheme summands, generalized
`isConstant_over_of_section` to arbitrary constant group sheaves, and replaced
`finite_sheafFiber` with `exists_surjective_sheafFiber`, which does not assume `Finite M`.
The stalk surjection implies the required finite stalks by `Finite.of_surjective`.
The representative lemma also records that its total scheme is the given representative.
The private-action lemmas now spell out all binders: their `reprAct` and `reprVadd` refer to
this module's private constructions, not the declarations in the cyclic source module.
These private changes preserve the assigned theorem's exact signature.

Ran the same `import_prune_check.py` landing guard against the original module: exit 0.
The repaired module compiles locally without errors or warnings. The delivery dry run rebased its generated commit on current `origin/sheaf-dag` and
printed OK. Server compilation also passed with `WEIL_SERVER_COMPILE=1`; nothing was pushed.
The repaired version awaits its independent second reading.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.finiteEtale_lifts_scheme_torsor`
(node `lem-weil-pbc-finite-etale-scheme-torsor-lift`).

No sorry remains in the assigned module. No holes were added or split off.
This proves the theorem from the existing representability interface, which still depends on
its previously stated descent obligations; it does not assert that every imported declaration
is now axiom-free. The delivery's net change is one hole closed and zero holes added.

## No longer needed

No DAG dependency or module was pruned from the import closure: all five original proof
dependencies are used. Seven direct proof imports are redundant because the retained imports
already supply their declarations and instances. Removed:

- `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products`
- `Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts`
- `WeilConjectures.CategoryTheory.ConcreteCategory.FinitelyGenerated`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`

`EtaleTorsorDescent` was never imported by the assigned module and is still
excluded because it would create a cycle. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing high-level representation theorem cannot be imported: import_direction.py reports
that EtaleTorsorDescent already reaches this module. Its lower sorry-free proof can be reused
as generalized private constructions together with the acyclic representability interface, as the existing DAG
suggested. No mathematical statement was found false.

For simple transitivity it is enough to use preservation of products and coproducts by the
assumed equivalence, after explicitly identifying these objects in the finite étale category.
A separate theorem that arbitrary scheme base change preserves coproducts is unnecessary.
No extra DAG node is required for these fully proved private constructions.

The earlier delivery's successful preflight did not catch the landing guard's duplicate
statement rejection. This repair checks that guard explicitly; the obsolete second-reading
section was removed so that the next reader assesses the repaired version.

## Second reading by X2

1. **Statements unchanged.** I diffed the delivered module and DAG node against the repository versions. The public theorem `AlgebraicGeometry.Etale.finiteEtale_lifts_scheme_torsor` has the identical signature; no public definition or target statement changed. The DAG proof text records the route implemented by the module.

2. **Proof validity.** The module compiles with `lcompile.py` without errors or warnings. It contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`; all helpers are private and definitions contain no postponed data. The proof uses only the existing imported interfaces and the permitted concrete isomorphism laws.

3. **Split statements and dependencies.** No statements were split off and no new nodes were added. The existing proof dependencies are used. The private helper generalizations are strictly internal proof constructions and introduce no public theorem or DAG obligation. Edge cases, including an empty base and trivial group, are covered by the constructions and do not add hypotheses.

4. **Pruning and route.** I checked the retained imports with the import-prune guard and confirmed exit 0. The seven listed proof-only imports are redundant and are removed; no target-reachable module or DAG dependency is pruned. The unit route is preserved: representation, action lifting, simple transitivity, and surjectivity follow the node's realized steps.

5. **DAG agreement.** The node's `proof`, `proof_deps`, and `proof_origin` match the actual private representation argument and the final lifting proof. No statement-change record is needed. The existing private-proof-scope change record documents the command-scope classification; no adaptation of another module is present.

I changed only the review report by adding this second-reading record. The delivered Lean module and node already passed local compilation and the import-prune check; no proof repair was necessary in this reading.
