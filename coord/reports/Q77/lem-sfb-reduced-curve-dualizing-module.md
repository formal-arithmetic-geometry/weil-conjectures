## Worker report

The new module `Sheaf.AlgebraicGeometry.ReducedCurveDualizingModule` states
`AlgebraicGeometry.exists_reducedCurveDualizingPair`. Its only theorem has proof
`sorry`. Two transparent supporting declarations package exactly this item's
representing pair: `Scheme.Modules.moduleCohomologyOverField` composes the recorded
module-cohomology functor with restriction of scalars along the actual structure
map, and `ReducedCurveDualizingPair` stores a coherent module with the natural
linear duality. There is no choice of a module or of a scalar action in either
definition. No mathematical statement or proof dependency of the item was changed.

Sources read: Stacks Project `curves.tex`, `lemma-duality-dim-1`, lines 579–644
(Tag 0BS2), `lemma-duality-dim-1-CM`, lines 647–675 (0BS3), `lemma-euler`,
lines 957–987 (0BS5), and the generic-support argument beginning at line 5480
in `lemma-vanishing-on-gorenstein` (0E3E). These justify the reduced pure-dimensional
specialization without imposing connectedness or triviality of the constants.
The module docstring contains all nine accepted proof steps, including the
field homothety computation and the explicit representing-pair uniqueness argument.

The statement matches hypothesis by hypothesis and clause by clause:

- `k : Type u`, `[Field k]`: the arbitrary base field.
- `C : Scheme.{u}`, `[C.Over (Spec (.of k))]`: the scheme with its structure map.
- `[IsProper (C ↘ Spec (.of k))]`: properness of that map, including finite type.
- `[IsReduced C]`: reducedness, without geometric reducedness.
- `[Nonempty C]`: the explicitly required nonempty scheme.
- `hPure : C.IsPureDimension 1`: every irreducible component has dimension one.
- `∃ D : ReducedCurveDualizingPair k C`: existence of the representing pair.
  `D.omega : C.Modules` is its module and `D.coherent` is the exact finite-type
  plus finite-type-kernels predicate `RingedSpace.IsCoherent C.toRingedSpace`.
- `D.duality F hF`: for each coherent test module, a `≃ₗ[k]` from `(F ⟶ D.omega)`
  to `Module.Dual k ((moduleCohomologyOverField k C 1).obj F)`.
  The source scalar action is the existing `homModuleOfOver`; the target uses
  `RingedSpace.moduleCohomology` followed by `ModuleCat.restrictScalars` along
  `Scheme.globalSectionsRingHom`. This cohomology is computed in module sheaves.
- `D.naturality`: for every morphism `a : F ⟶ G` of coherent modules and
  `b : G ⟶ D.omega`, duality of `a ≫ b` equals duality of `b` precomposed with
  the actual cohomology map of `a`. It quantifies over all maps and both coherent
  tests, with no independent comparison maps or weakened naturality.
- The first conjunct quantifies over every other representing pair `D'` and
  asserts `∃! e : D.omega ≅ D'.omega` satisfying equality of the duality maps
  on every coherent test and map into the first module. Thus uniqueness is of
  the isomorphism respecting the representing data, not mere existence of an
  unstructured isomorphism.
- The generic-stalk conjunct quantifies over every `Z ∈ irreducibleComponents C`
  and every `η` with `IsGenericPoint η Z`. It asserts `IsField (C.presheaf.stalk η)`
  and a linear equivalence of the omega stalk with that ring. Over this field
  this is exactly dimension one. The linear-equivalence formulation avoids
  manufacturing a separate field structure and keeps the actual stalk module.
- The submodule conjunct quantifies over each coherent `N` and every monomorphism
  `i : N ⟶ D.omega`. If every component-generic stalk is `Subsingleton`, then
  `IsZero N`. A categorical mono represents precisely a submodule up to its
  canonical image identification; no pointwise injectivity hypothesis is added.
- The morphism conjunct states `a = 0 ↔` all component-generic stalk maps of `a`
  are zero for each coherent source `F`, so both directions of the stated
  equivalent criterion are retained.
- The last conjunct uses the recorded `Scheme.Modules.eulerChar` of both
  `D.omega` and the actual structure module `SheafOfModules.unit C.ringCatSheaf`
  and says that they are negatives.
- No connectedness, smoothness, perfectness of the field, geometric reducedness,
  or identification `H^0(C,O_C)=k` is assumed. All binders and universes are
  explicit. The uniform scheme/field universe follows the project conventions;
  finite type objects may be represented in that universe.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (line 180).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`
  (line 42), with the recorded proper-morphism definition.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`
  (line 69), including its stalk comparison.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`, the
  componentwise topological dimension definition, including the empty case.
- `WeilConjectures.AlgebraicGeometry.Coherent`: `RingedSpace.IsCoherent`, with
  `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType`. The item
  `lean.note` identifies clause 3. Its full signature and kernel condition were read.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  is transparently `SheafOfModules`; `C.Modules` is its scheme specialization.
- `WeilConjectures.Topology.RingedSpaceModuleCohomology`:
  `RingedSpace.moduleCohomology`, the right derived global-sections functor
  with target the modules over global sections, not underlying abelian-sheaf Ext.
- `Mathlib.Topology.Sober`: `IsGenericPoint` (closure of the singleton).
- `Mathlib.Topology.Irreducible`: `irreducibleComponents` (maximal irreducible sets).
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor`. The actual sheaf specialization used
  is `RingedSpace.moduleStalkFunctor` from
  `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`; both were read and use
  Mathlib's same presheaf stalk carriers, scalar action, and induced maps.
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`:
  `Scheme.Modules.eulerChar`, its `finsum` of signed finite dimensions, and
  `Scheme.globalSectionsRingHom`, the structure-morphism map on sections.
- `WeilConjectures.AlgebraicGeometry.Modules.Linear`:
  `Scheme.Modules.homModuleOfOver`, the existing canonical k-action on module maps.

All proof-dependency modules with recorded Lean declarations are plain imports;
statement dependencies are public imports. The proof in the docstring names the
remaining accepted DAG prerequisites; this stage does not state or prove those
proof prerequisites.

Edge cases checked before writing: the empty scheme is excluded exactly by the
node; a zero-dimensional component is excluded exactly by pure dimension one.
The zero coherent test module is admitted by the duality and naturality fields.
A zero coherent submodule satisfies the conclusion, and all zero morphisms are
covered by the reverse direction of the stalk criterion. Disconnected curves,
reducible curves, singular reduced curves, and arbitrary characteristic remain
admitted. For P¹ the expected omega is O(-2), of rank one with Euler characteristic
-1. For a disjoint union of two P¹'s the characteristic is -2, and the statement
still allows the two-dimensional algebra of constants. The generic field may be
an extension of k; generic rank is taken over the local ring, not over k.

Searches actually run through `batch2/msearch.py` (2026-10-24):

- leansearch: `proper reduced curve coherent dualizing module natural duality first cohomology`:
  eight hits, on cotangent H1, group cohomology, and `Module.Dual`; none states this theorem.
- leanfinder: `proper reduced curve dualizing sheaf Hom dual first cohomology Euler characteristic`:
  eight hits about elliptic-curve ideal classes and function-field class numbers; no match.
- loogle: `Dualizing`: zero hits, unknown identifier `Dualizing`.
- grep of Mathlib AlgebraicGeometry: `dualizing|dualising`: zero hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for dualizing/dualising/Dualizing
  found relative/derived duality and nodal dualizing-line interfaces, but no coherent
  dualizing module for an arbitrary reduced curve with this representing property.
- Exact item-id search over both Lean trees found no declaration. Exact new-name
  search (`moduleCohomologyOverField|ReducedCurveDualizingPair|exists_reducedCurveDualizingPair`)
  over both trees and `dag/lean_names_upstream.json` found no existing names.
- Coherence searches and source reading found the exact existing
  `RingedSpace.IsCoherent` definition, used rather than duplicated.

No statement dispute, source error, or correction is needed.

## Repair of H13

The returned head `0d82eaeedfa3` attempted to rebind the landed
`pqf-def-coherent` record. The saved packet retained that attempted rebinding;
its initial dry run passed as `626d7c87972`, but the independent return still
requires the semantic repair below.

Removed `dag/nodes/sec-abelian-varieties/pqf-def-coherent.json` from the packet.
The live Q25 `CoherentFiniteType` / `IsQuasiCoherentFiniteType` record is preserved
byte for byte by delivering no change to it. The item Lean module is unchanged:
its direct public import of `WeilConjectures.AlgebraicGeometry.Coherent` supplies
`AlgebraicGeometry.RingedSpace.IsCoherent`. Added item `lean.note` citing clause 3
of the dependency statement and Stacks Tag 01BV: finite type with finite-type
kernels of all finite-free maps on every open. This is exactly the notion used
for the representing module, test modules and submodules. Removed the former
§1(B) dependency-repair paragraph. No dependency module or node is delivered.

## Validation

The saved module had already passed the server compile and module-mode check.
For this repair it is retained byte for byte, as requested by the independent
review. The initial saved-packet dry run passed as `626d7c87972`; that result
included the rejected dependency rebinding and is not the repaired validation.
The repaired module passed `scompile.py` on 2026-10-24 in both modes:
sandbox 4.1 seconds, library 8.5 seconds, with no diagnostics. The repaired
packet is submitted to `deliver2.py --no-push` before delivery.

The local self-check confirms that the item differs from current live data only
in `lean`, its primary signature matches the module verbatim, the module has
explicit binders with `autoImplicit false`, its sole postponed theorem is named
and has the full proof docstring, and all Lean lines have at most 100 characters.
No dependency node or module is delivered.

## Second reading by Q77

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
