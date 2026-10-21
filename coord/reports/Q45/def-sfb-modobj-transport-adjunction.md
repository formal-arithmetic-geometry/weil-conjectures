## Worker report

This is an `existing: true` attachment, with no new Lean module. The exact construction is
`CategoryTheory.Adjunction.mapModAdjunction` in
`WeilConjectures.CategoryTheory.ModuleObjects.MapMod`, lines 201–286 of the live source.
The node and its statement, dependencies and proof are unchanged; only `lean` is set.

Source read: the full statement and proof of
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-sfb-transport/def-sfb-modobj-transport-adjunction.md`
and its `.proof.md` companion. Read both dependency nodes, their full Lean signatures and
docstrings, the implementation of `MapMod.lean`, and Mathlib's `Adjunction.IsMonoidal`.
There is no repair note for this item. The prescribed CompactObject example is withdrawn;
its node now attaches the upstream definition, which also illustrates the existing-record case.

Hypothesis and clause comparison:

- Arbitrary monoidal categories C and D are `{C : Type u₁} [Category.{v₁} C]
  [MonoidalCategory C]` and `{D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]`.
  All four universes are independent; the construction has no size equality assumption.
- The functors and underlying adjunction are `{F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)`.
- Strong monoidality of F is `[F.Monoidal]`, lax monoidality of G is `[G.LaxMonoidal]`,
  and the mate compatibility is precisely `[adj.IsMonoidal]`. Mathlib's two fields give
  G's unit and tensor structure maps as the mates of F's oplax maps; F is strong here.
- The arbitrary monoid object is `(R : C) [MonObj R]`. No commutativity is required.
- `unitAlgHom adj R` is an abbreviation for `adj.unit.app R`, not an arbitrary scalar map.
  `isMonHom_unitAlgHom` proves it is a monoid morphism with the target structure transported
  first by F and then by G. Its implementation uses `Functor.monObjObj_id` and
  `Functor.monObjObj_comp` to transport the monoidal-natural-transformation instance to
  exactly those structures, rather than relying on a potentially different composite instance.
- The required adjunction is literally
  `F.mapMod R ⊣ G.mapMod (F.obj R) ⋙ Mod.comap (adj.unitAlgHom R)`.
  Functor composition `⋙` applies G's module transport first and restriction second,
  exactly the mathematical expression Res composed with mapMod(G).
- The underlying forward map in `mapModAdjunction`'s `homEquiv` is
  `adj.homEquiv M.X N.X φ.hom`; the inverse is
  `(adj.homEquiv M.X N.X).symm ψ.hom`. They are bundled with `Mod.Hom.mk'` using
  `mapMod_homEquiv_smul_hom` and `mapMod_homEquiv_symm_smul_hom` respectively.
  Thus this is the original adjunction bijection restricted to linear maps in both directions.
  Its two naturality fields are the underlying adjunction's naturality equations, lifted by
  `Mod.hom_ext`. It is not a bare existence assertion or an adjunction with unspecified bijection.
- The action on GN is precisely restriction along the unit: expansion of `mapMod` and
  `Mod.comap` gives `adj.unit.app R ▷ G.obj N.X ≫
  Functor.LaxMonoidal.μ G (F.obj R) N.X ≫ G.map γ[F.obj R,N.X]`.
  This is the formula in the node and its proof.

Dependency declarations used:

- `def-sfb-modobj-transport`: its recorded closed-audit declarations
  `CategoryTheory.Functor.mapMod`, `CategoryTheory.Functor.modObjObj`, and
  `CategoryTheory.Functor.act_mapMod_obj`, all in
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod`. Read their full definitions:
  the transported action is the lax tensor map followed by the image of the old action;
  maps have underlying map F(f).
- `def-sfb-modobj-restriction`: its Mathlib match `CategoryTheory.Mod.comap` in
  `Mathlib.CategoryTheory.Monoidal.Mod`, lines 351–410, specialized to the self action.
  Read `scalarRestriction`, `scalarRestriction_hom` and `comap`: the restricted action
  is f tensor identity followed by the old action, and objects/maps remain unchanged.
- `MapMod.lean` imports the actual transport module, and its `Mod.comap` is the Mathlib
  construction above. No dependency copy or repair is needed.

Edge cases checked by reading the full binders and formulas: F and G need not be an equivalence;
G need not be strong monoidal; R need not be commutative; C and D need not be braided, additive,
abelian, closed or have limits/colimits. Although the module imports broader infrastructure,
none of those assumptions enter the declarations attached here. The identity adjunction is
included and gives the usual identity Hom bijection. Unit monoids and zero monoids in pointed
examples are included; no nonzero or nontrivial assumption is present. There is no family index,
scheme or characteristic restriction. Empty ambient categories have no R to instantiate, as in
the source, and do not require a spurious nonemptiness hypothesis.

Searches actually run through msearch.py (Q45, this item):

- LeanFinder: `monoidal adjunction module objects mapMod restriction adjunction` returned
  representation and ordinary-module restriction adjunctions plus historical `Mod_.comap`
  results; none gives this general ambient-category statement.
- Loogle: `CategoryTheory.Adjunction.mapModAdjunction, CategoryTheory.Adjunction.mapMon`
  reported unknown identifier `CategoryTheory.Adjunction.mapModAdjunction` (the upstream
  declaration is outside Mathlib's index). This is a query error, not evidence of absence.
- Grep: `mapModAdjunction|mapMod|Monoidal` in `CategoryTheory/Monoidal` returned generic
  monoidal infrastructure; the narrower repeated query
  `mapModAdjunction|def mapMod|def comap` in the same directory found `Mod.comap:403`.
- LeanSearch: `A monoidal adjunction lifts to module objects by restriction along its unit`
  returned `Mod_.scalarRestriction`, `Adjunction.mapMon`, monoidal-unit coherence and mates;
  no exact Mathlib module-object lift.
- Project `rg` for `mapModAdjunction|def-sfb-modobj-transport-adjunction|modAdjunction` in
  `lean/WeilConjectures` and `lean/Sheaf` found the exact existing upstream module
  `CategoryTheory/ModuleObjects/MapMod.lean`, including its main definition at line 276,
  and numerous consumers. The broader `modAdjunction` in the Mathlib-extension module
  was read too; it is not needed because the exact unit-specialized construction exists.
- The node-id grep of `lean/WeilConjectures` had no hits. DAG/name-index searches found
  only blueprint references to `CategoryTheory.Adjunction.mapModAdjunction`, not another
  node's Lean attachment. The function's source and implementation establish the match.

No statement fault or disputed mathematical claim was found. No new definitions, postponed
proofs, modules or nodes are introduced.

Validation: the sandbox's scratch `ExistingProbe.lean` is checked only with scompile.py;
it instantiates the exact adjunction signature with independent universes, checks the unit
monoid-morphism instance and both linearity lemmas, and prints axioms of the main definition
and the unit instance. It is not a delivered library module. The required deliver2.py dry run
also checks all attached names against the live server and runs the maintainer's preflight.

The dispatcher brief assigns independent second reading to the maintainer and forbids starting
other agents. This worker report does not claim an independent review by its author.

The explicit scompile.py probe passed cleanly in both sandbox and library checks (1.1 seconds
each). The exact adjunction and unit-instance signatures elaborate with independent object and
morphism universes. Both `#print axioms` results contain exactly `propext`, `Classical.choice`
and `Quot.sound`; neither uses `sorryAx`.

## Repair of returned delivery

The return for immutable head `fb0a10157ad7` reports one format failure in the
maintainer's `--apply-fixes` input: `def-sfb-modobj-transport-adjunction.json`
is a whole existing node, which that interface does not accept as an override.
The ordinary delivery still requires that node at its prescribed `dag/nodes/` path.
The source statement and construction need no mathematical change.

Read `tools/merge_delivery.py` and `tools/stage2_delivery.py`: for an existing
attachment the review override must be named
`def-sfb-modobj-transport-adjunction.lean-record.json` and contain the `lean`
record itself, without a surrounding node or `lean` key. Repaired the review
handoff by creating `review-fixes/` in the sandbox with exactly that record and
`def-sfb-modobj-transport-adjunction.report.md`; neither is a whole-node fix.
The fix directory contains no unrecognized files. The node's `lean.note` now
records this repair, so the pushed delivery differs from the returned head.
No maintainer tools or source files were modified or invoked.

For review from the delivered report, materialize the following object as
`DIR/def-sfb-modobj-transport-adjunction.lean-record.json` (never as
`DIR/def-sfb-modobj-transport-adjunction.json`):

```json
{
 "module": "WeilConjectures.CategoryTheory.ModuleObjects.MapMod",
 "declaration": "CategoryTheory.Adjunction.mapModAdjunction",
 "declarations": [
  "CategoryTheory.Adjunction.unitAlgHom",
  "CategoryTheory.Adjunction.isMonHom_unitAlgHom",
  "CategoryTheory.Adjunction.mapMod_homEquiv_smul_hom",
  "CategoryTheory.Adjunction.mapMod_homEquiv_symm_smul_hom",
  "CategoryTheory.Adjunction.mapModAdjunction"
 ],
 "statement": "noncomputable def mapModAdjunction :\n    F.mapMod R ⊣ G.mapMod (F.obj R) ⋙ Mod.comap (adj.unitAlgHom R)",
 "branch": "slopmaster2",
 "by": "Q45",
 "date": "2026-10-21",
 "existing": true,
 "note": "Exact existing construction in the live upstream source, MapMod.lean:201-286. The only hypotheses are two arbitrary monoidal categories, F strong monoidal, G lax monoidal, adj : F ⊣ G with adj.IsMonoidal, and R a monoid object. unitAlgHom is literally adj.unit.app R; isMonHom_unitAlgHom uses the twice-transported monoid structure. mapModAdjunction has the exact functors in the node and its toFun/invFun use adj.homEquiv and its inverse on underlying maps. No module or duplicate definition is introduced. Repair of returned head fb0a10157ad7: the review override is a lean-record JSON object, not a whole existing-node JSON. The report includes the accepted override filename and payload; the sandbox review-fixes directory contains only accepted fix artifacts."
}
```

Compared the retained attachment against the current shared node: only `lean`
differs, and the statement, statement dependencies and proof are unchanged.
Also reread the current live server `MapMod` source with `scompile.py --source`:
the recorded definition signature, its unrestricted ambient-category binders,
the unit monoid morphism and both restricted Hom-equivalence formulas agree
with this attachment. The dependency transport node is now attached upstream;
its closed-audit declarations remain exactly those used here.

## Second reading by Q45

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
