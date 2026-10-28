## What changed

Decomposed `CategoryTheory.RingedSiteGlobalRHom.preserves_derived_limits` into two
independent component statements, and proved their assembly without changing its signature.
The item constructs the comparison as β(lim I) inverse followed by Q(limit.post).
A generic private categorical calculation proves naturality and the exact projection formula.
The item also proves Grothendieck abelianness of the tower category, uses the canonical
functorial K-injective resolution with injective terms, and proves that evaluation and
ordinary inverse limit preserve the required K-injectivity. The inverse-limit proof uses
the exact constant-tower adjunction and an explicit comparison with the degreewise limit.

The existing ten definitions and instances were moved verbatim to
`Sheaf.Algebra.Homology.RingedSiteGlobalRHomModel`, publicly re-exported by the item.
The model retains every old public import; all names, universes, types and bodies are unchanged.
The independent statement modules import this model, avoiding an import cycle.
Change record: `coord/changes/D4-global-rhom-model-extraction.md`.
There are no existing direct or indirect Lean importers, as checked by tools/downstream.py.

The four delivered modules compile individually, in dependency order. The completed item
compiled in 34.1 seconds before the final warning-only option cleanup, within the 60-second
limit. The delivery tool performs the final compile and axiom checks. Profiling options
were removed. The heartbeat budget is scoped to the one large assembly theorem; no compile
time limit or transparency-respect setting was changed.

## Proved and sorry left

Closed the original textual hole in
`CategoryTheory.RingedSiteGlobalRHom.preserves_derived_limits` by a complete proof from the
two statements below. This is a decomposition of one hole into two, not a sorry-free proof
or a net reduction of holes: one hole closed, two added, net minus one.

The new, strictly smaller statements left with exactly `:= by sorry` are:

- `CategoryTheory.RingedSiteGlobalRHom.coefficient_model`
  (`lem-sfb-global-rhom-coefficient-model`): the A-linear representative comparison,
  its naturality, and all-degree natural A-linear cohomology equivalences. It has no towers
  or limit comparison.
- `CategoryTheory.RingedSiteGlobalRHom.resolved_tower_models`
  (`lem-sfb-global-rhom-resolved-tower-models`): invertibility of ordinary limit.post and
  the two Roos triangles with actual projections. It has no global-RHom comparison,
  no β or α, and no cohomology equivalences. Resolution existence and K-injectivity
  are proved in the item and are not postponed to this statement.

There are zero sorries in the item and zero in the extracted definitions. All private
helpers are proved. No definitions choose unspecified objects from an unproved existence
statement: comparisonIso is an explicit construction from its parameters, and the tower
resolution is the existing canonical functorial resolution.

## No longer needed

No existing module is withdrawn. The unit statement and its steps are unchanged.
The proof no longer directly needs these four original nodes, and their direct approvals
were pruned from the item's tool_uses list:

- `lem-sf-ringed-derived-tensor-hom-adjunction` and
  `lem-sf-ringed-derived-native-tensor`: the coefficient comparison uses the existing
  internal-Hom sections model, so its tensor-adjoint characterization need not be reconstructed.
- `lem-weil-pbc-ringed-strict-tower-homotopy-limit` and
  `lem-weil-strict-roos-comparison`: the stated result asks for actual-projection Roos
  triangles. The injective-tower triangle and the kernel-to-cone argument give those
  directly; no separate total-derived-limit functor or descent comparison is needed.

The following former direct proof imports are absent from the item:
`Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel`,
`Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction`,
`Sheaf.Algebra.Homology.RingedDerivedTensorNative`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.Algebra.Homology.KInjectiveHomComplex`,
`Sheaf.CategoryTheory.InjectiveTowerRoosShifts`,
`Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`,
`WeilConjectures.Algebra.Homology.KernelShiftedMappingCone`,
`Sheaf.CategoryTheory.StrictRoosComparison`,
`Mathlib.Algebra.Homology.DerivedCategory.KInjective`, and
`Mathlib.Algebra.Homology.DerivedCategory.Plus`.
The sections-model, K-flat, Hom-K-injective, injective-tower and kernel-cone dependencies
remain in the appropriate child node's proof plan; they have not been declared globally
unnecessary. The narrow Hom-K-injective lemma has an existing independent-universe companion.
All former public imports are retained through the extracted model. No claim is made that
these modules leave the targets' transitive closure: the ledger decides that.

## Where the brief, the DAG or earlier work was wrong

The existing sections-model theorem is an additive-group-valued comparison. Its cohomology
clause provides pointwise Nonempty equivalences, without the explicit naturality and scalar
identities this item's signature asks for. Therefore it does not directly close the
coefficient-valued comparison, which is isolated in coefficient_model with the full
K-flat replacement and scalar-compatibility argument in its docstring and node.

No mathematical counterexample was found and no statement was weakened. Checked edge cases
are E=0, L=0, the zero tower, identity transitions, zero transitions, all q including negative
q, the zero coefficient ring and the empty site. Limit.post is determined by its projections;
the target Roos kernel inclusion has coordinates (0,z), so there is no boundary-sign change.
The new proof stays below the existing unit and follows its homological-algebra route.
The inherited blueprint ancestor is null in the live node; this delivery preserves that
record and extends its documented provenance instead of inventing an ancestor.

## New nodes

`def-sfb-global-rhom-resolved-model` records the unchanged definitions in their shared module.
It is a relocation of the existing model, not another construction of derived Hom.

`lem-sfb-global-rhom-coefficient-model` records the original argument's representative and
cohomology steps with their full A-action and naturality requirements. Its source is
sites-cohomology.tex Tags 0B6E, 08JA and 0A96.

`lem-sfb-global-rhom-resolved-tower-models` records only the ordinary-Hom limit comparison
and the two normalized Roos triangles, using Tag 0941 and the existing injective-tower and
kernel-cone inputs. It deliberately leaves the proved resolution and K-injectivity step
in the item. Each child has a complete proof in words and three kinds of Mathlib searches.

Change record: `coord/changes/D4-global-rhom-model-extraction.md`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Algebra.Homology.RingedSiteGlobalRHomCoefficientModel": "738f9c6d3c3719ba33d0da38180f4a285f257bda", "Sheaf.Algebra.Homology.RingedSiteGlobalRHomDerivedLimits": "b0cece311c55089c0472b7de7a36f156415f61b2", "Sheaf.Algebra.Homology.RingedSiteGlobalRHomModel": "db15c77d2c85deb41799e449802201e447a65d39", "Sheaf.Algebra.Homology.RingedSiteGlobalRHomResolvedTowerModels": "92465720cd3da3bdb1a96df102ace1d101204126"}, "results": {}, "time": "2026-10-28T10:02:28+0800", "transitive": 0, "version": 1}
```

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
