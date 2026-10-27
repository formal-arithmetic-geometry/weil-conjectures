## Worker report

The module `Sheaf.AlgebraicGeometry.FlatAssociationStalkDictionary` states
`AlgebraicGeometry.Scheme.Modules.flatAssociation_stalk_dictionary`, with its whole
proof `sorry`. There are no definitions, helper theorems, new nodes, dependency
repairs, or changes to the mathematical statement. The node copy changes only `lean`.

Hypotheses and objects, matched to the node:

- Schemes `Y`, `Z` and the morphism `h : Y ⟶ Z` are bound explicitly in universe `u`.
  The point is the explicit binder `y : Y`, and `z` is written directly as `h y`.
- Flatness is `[Flat h]`; local Noetherianity of the target is
  `[IsLocallyNoetherian Z]`. There is no local Noetherianity assumption on `Y`.
- The module is `G : Z.Modules`, and its sole module finiteness condition is
  `[SheafOfModules.IsQuasicoherent.{u} G]`. In particular, the conjunction
  `IsQuasiCoherentFiniteType` is not imposed: its module exposes the recorded
  quasi-coherence predicate as required by pqf-def-coherent.
- `A` and `B` are `Z.presheaf.stalk (h y)` and `Y.presheaf.stalk y`.
  `M` is `(RingedSpace.moduleStalkFunctor Z.toRingedSpace (h y)).obj G`.
  The stalk homomorphism is `(h.stalkMap y).hom` throughout.
- Both maximal ideals are `IsLocalRing.maximalIdeal` of their respective rings.
  `I` is the ideal image of the maximal ideal of `A` under that stalk homomorphism.
  `C` is the literal quotient of `B` by that image, without any chosen replacement.
- The fibre is `h.fiber (h y)`, its projection is `h.fiberι (h y)`, and its unique
  point over `y` is `h.asFiber y`. The canonical transported stalk map is the
  already recorded `h.fiberStalkMap y`.

Conclusions, in the order of the conjunction:

1. `(h.stalkMap y).hom.Flat` states the flat ring map; `IsLocalHom` states locality.
   The displayed `Ideal.comap` equality is exactly the specified inverse-image
   equality of maximal ideals. `IsNoetherianRing (Z.presheaf.stalk (h y))` is the
   final assertion of clause (1), not an added hypothesis.
2. `Nonempty` of the displayed isomorphism in `ModuleCat B` states the B-linear
   isomorphism of the pullback stalk with extension of scalars of `M` along
   `A → B`. Mathlib's `ModuleCat.extendScalars` writes this tensor as `B ⊗[A] M`,
   with its B-action bundled. This is canonically symmetric to the node's
   `M ⊗[A] B`, exactly the convention documented by the recorded
   lem-weil-pbc-module-stalk-pullback interface; it adds no module structure choice.
   The next equivalence is membership of `y` in `associatedPoints` of the actual
   tensor pullback iff `m_B` belongs to `RingTheory.annihilatorAssociatedPrimes`
   of that extension of scalars. The following equivalence is membership of `h y`
   in `associatedPoints G` iff `m_A` belongs to the same exact-annihilator prime
   set of `M`. No weakly associated primes or radical-annihilator predicate is used.
3. The existential `e : C ≃+* O_(Y_z,y_z)` states the fibre ring isomorphism.
   The equation on every `b : B` says it is induced by the actual fibre stalk map.
   Mapping the quotient ideal `m_B.map (Ideal.Quotient.mk I)` through `e.toRingHom`
   gives exactly the maximal ideal of the fibre stalk.
   For every `v : C`, the two `Submodule.colon {v}` terms are respectively
   `Ann_B(v)` and `Ann_C(v)`: the first uses the canonical quotient B-module
   structure, the second the regular C-module. The equivalence equates them to
   `m_B` and its quotient image respectively. The final equivalence identifies
   association of `h.asFiber y` in the actual fibre structure sheaf
   `SheafOfModules.unit (h.fiber (h y)).ringCatSheaf` with exact association of
   `m_B` in `C` regarded as a B-module.

Dependency declarations used, with their recorded modules:

- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, with
  `Flat.stalkMap` and `Flat.iff_flat_stalkMap` read for the stalk interpretation.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: exposes the recorded
  `SheafOfModules.IsQuasicoherent`; its other predicates are not hypotheses.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor` and its stalk carrier. On module sheaves,
  the statement uses the prescribed `AlgebraicGeometry.RingedSpace.moduleStalkFunctor`
  from `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`, publicly imported by
  the recorded `RelativeAssassin` interface. These use the same Mathlib stalks.
- `WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes`:
  `RingTheory.annihilatorAssociatedPrimes`.
- `Sheaf.AlgebraicGeometry.RelativeAssassin`:
  `AlgebraicGeometry.Scheme.Modules.associatedPoints` (the absolute-points clause
  of the relative-assassin definition node).
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`, `asFiber`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: exposes the actual
  `AlgebraicGeometry.Scheme.Modules.tensorPullback` constructed in the publicly
  imported upstream `WeilConjectures.AlgebraicGeometry.TensorPullback` module.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, used in the
  extension-of-scalars model `ModuleCat.extendScalars` from Mathlib's
  `Algebra.Category.ModuleCat.ChangeOfRings` (available through the pullback API).
- `Sheaf.AlgebraicGeometry.FibreStalkQuotient`: `Scheme.Hom.fiberStalkMap` and
  `fiberStalkMap_surjective_ker_quotientEquiv`. Public because its canonical map
  occurs in the statement, although the DAG originally names this node as a
  proof dependency. No new notion or mathematical assumption is introduced.

The other stated proof dependencies are imported without `public`:
`Mathlib.Geometry.RingedSpace.LocallyRingedSpace` (`LocallyRingedSpace.Hom`),
`Mathlib.AlgebraicGeometry.AffineScheme` (`IsAffineOpen.fromSpec_app_self`,
`IsAffineOpen.isLocalization_stalk`),
`Mathlib.RingTheory.Localization.Submodule` (`IsLocalization.isNoetherianRing`),
and `WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk`
(`Scheme.Modules.exists_tensorPullback_stalk_iso`). Their recorded signatures and
source docstrings were read. Other proof dependencies coincide with statement
imports. There is no import cycle and no omitted stated proof dependency.

Sources read directly: literature/stacks-project/divisors.tex, lemma-bourbaki,
including its stalk paragraph (Tag 05DB); schemes.tex, lemma-local-ring-fibre
(Tag 0HA1); algebra.tex, lemma-ass-quotient-ring (Tag 05BY). The theorem docstring
carries all five proof steps and the dependency names, without proving anything.

Edge cases checked before writing and on rereading:

- Empty `Y`: no `y` can be supplied, so the pointwise theorem has the right scope.
- `G = 0`: the tensor stalk is zero and both associated-prime sets are empty;
  the fibre assertion is independent of `G`, as required.
- Identity morphism: `A = B`, the fibre quotient is the residue field, and the
  tensor-stalk assertion reduces to scalar extension along identity.
- `A` a field: its maximal ideal and its extension are zero, so `C = B`; the
  quotient and annihilator clauses reduce to the identity comparison.
- `v = 0`: both annihilators are top, whereas both relevant maximal ideals are
  proper; the annihilator equivalence holds with both sides false.
- No finite generation of `M`, Noetherianity of `B`, nonzero-module hypothesis,
  characteristic restriction, finite-type assumption on `h`, or universe equality
  beyond the standard common scheme universe is added.

Searches on 2026-10-24:

- `msearch.py ... leanfinder` query: "Flat pullback associated points stalk tensor
  product and fibre quotient maximal annihilator dictionary". Eight results,
  including `Flat.stalkMap`, `Flat.iff_flat_stalkMap`, and rank-at-stalk lemmas;
  none supplies this three-clause dictionary.
- `msearch.py ... loogle` query: `AlgebraicGeometry.Flat.stalkMap`. One result,
  the individual flatness assertion, not the whole statement.
- `msearch.py ... grep` query: `associatedPoints|annihilatorAssociatedPrimes`.
  Zero Mathlib search hits. The explicit upstream and project searches below
  identified the relevant project definitions.
- `msearch.py ... leansearch` query: "Associated points of a pullback module are
  detected by maximal annihilators in its tensor product stalk, and fibre stalks
  are quotient local rings". Eight results: localization of associated primes,
  local-ring stalk instances, `restrictStalkNatIso`, stalk pullback, and tensor
  rank facts. None states this dictionary; `restrictStalkNatIso` specifically
  requires an open immersion and does not give general flat pullback.
- `rg -n 'flatAssociation|flat_association|associatedPoints|lem-trf-flat-association-stalk-dictionary'`
  over both `lean/WeilConjectures` and `lean/Sheaf`: found the recorded
  `RelativeAssassin` definitions, the parent `FlatPullbackAssociatedPoints`
  theorem, and other associated-point consumers. No declaration states this
  conjunction, and there was no existing declaration for this node id.
- Read `RingTheory.annihilatorAssociatedPrimes` and `Scheme.Modules.associatedPoints`
  in full, and searched the declaration name before introducing it: no collision.

Validation: scompile.py Q94 lem-trf-flat-association-stalk-dictionary compiled
both its private sandbox probe and the actual module successfully (15.0 s and
6.2 s respectively), with no errors or unexpected warnings. Only the expected
stage-2 theorem proof is postponed. No STATEMENT-DISPUTED issue was found.

## Second reading by Q94

A separate rereading of the node text, proof steps, and finished Lean file checked
all binders and every conjunct against clauses (1), (2), and (3), using the mapping
above. This rereading was performed by this worker: the dispatch brief explicitly
forbids starting another agent; the maintainer's independent delivery review is
still required. No claim of a second worker's independent review is made.

Particular checks were the lack of a finite-type condition on `G`, the exact
annihilator definition (rather than weak association), the canonical fibre map
rather than an arbitrary ring equivalence, the quotient B-action in `Ann_B(v)`,
the quotient image ideal in `Ann_C(v)`, and the actual unit structure sheaf on the
fibre. `extendScalars` reverses the displayed tensor factor order only by the
standard canonical symmetry documented by the recorded dependency. Neither a
statement change nor an interface repair is needed. No mismatch was found and
no change followed this rereading.
