## Worker report

The theorem is `CategoryTheory.CondensedBar.condensed_derived_invariant_bar` in
`Sheaf.CategoryTheory.CondensedDerivedInvariantBar`. Its only postponed proof is `sorry`.
Its conclusion `Assertion G` is a fully expanded specification in the new definition
module `Sheaf.CategoryTheory.CondensedEquivariantBarData`. No statement correction.

Hypotheses and clauses:

* A commutative condensed ring is `Ring = CommMon (Sheaf (coherentTopology Profinite)
  AddCommGrpCat.{u+1})`; its underlying `A.toMon` is the recorded
  `Profinite.CondensedRing`. `Modules` abbreviates the landed internal module category.
  `Assertion` quantifies over ALL these rings and all their ring morphisms.
* The profinite group is `G : Type u` with `Group`, `TopologicalSpace`,
  `IsTopologicalGroup`, `CompactSpace`, `T2Space`, `TotallyDisconnectedSpace`.
  Compact Hausdorff totally disconnected groups are the profinite groups in the node.
  The coherent site has objects of universe u+1, morphisms of universe u; coefficients
  are in u+1, and the standard derived localizations have morphisms in u+2.
* `Equivariant` is an abbreviation of the LANDED
  `Profinite.CondensedAction.ActionModule A.toMon G`, with sectionwise internal linear
  action by ALL continuous generalized elements, natural under every base change.
  The landed category and addition of equivariant maps are retained. `forgetAction`
  and `Invariants` are also abbreviations of the existing declarations, not copies.
* `Invariants.functor`, its inclusion, injectivity, image and normalized adjunction are
  the landed invariant-submodule specification. `Assertion` existentially provides
  abelian/Grothendieck structures and models; these are conclusions, not hypotheses.
  `resolutionComparison` uses the EXISTING ordinary unbounded
  `Functor.rightDerivedFunctor` and its K-injective unit, never a per-degree proxy.
* `freeParameter A P` applies `Profinite.CondensedAction.InternalBar.free A.toMon`
  to `GrothendieckTopology.uliftYoneda.obj P`. That landed free functor is literally
  free abelian sheaf followed by `Mod.free`, with its free-forgetful adjunction.
* `InternalFunctions.internalHom` identifies each functor with the EXISTING
  `Mod.ihom (freeParameter A P)`, the internal relative tensor right adjoint.
  `evaluate` identifies its sections at S with natural functions on all pairs
  T→S and T→P; `add`, `smul`, `map`, `restriction` fix that identification.
* `power G n = Profinite.of (Fin n → G)`. `BarDiagram.term` gives the internal-Hom
  terms; `face` gives the action first face, adjacent-product interior face and
  last-deletion face. `degeneracy` inserts 1 using `Fin.insertNth`; `maps` fixes
  postcomposition by equivariant maps. This is an ACTUAL cosimplicial object.
* `cochains` uses the existing alternating coface complex. `doubleComplex` applies it
  to ONE nonnegative resolution and flips the two complex indices. `totalCochains`
  uses the existing finite-diagonal total functor on up ℕ in both directions,
  so the outer/bar sign convention is d_bar + (-1)^p d_resolution.
* `Computation.forgetInjectives`, `forgetLimits`, `forgetColimits` and `columns`
  ensure the resolution computes DERIVED second-variable internal Hom, rather than
  replacing it with underived continuous functions. `columns` asserts invertibility
  of the existing derived unit on every underlying resolution and every parameter P.
* `Augmentation.degreeZero` evaluates the zero-column augmentation as the actual
  invariant inclusion restricted to T. `TotalAugmentation.components` fixes its
  component in resolution degree n by the (0,n) total coprojection.
* `Computation.augmentation_quasiIso` and `iso` give the asserted DERIVED-OBJECT
  isomorphism for EVERY equivariant injective resolution. `normalization` equates
  its hom with `resolutionComparison.hom` followed by localization of precisely
  this augmentation. `naturality` quantifies over every coefficient map and every
  augmentation-preserving lift, hence includes resolution independence (identity
  coefficient maps) and independence of the lift.
* `ScalarAction` specifies internal scalar restriction up to its underlying
  `Mod.comap a.hom.hom` isomorphism, intertwining every group-valued section.
  `ScalarModel.invariants` is fixed by the invariant inclusion square;
  `bar` and `evaluation` specify each internal-Hom comparison with no scalar twist.
  It is a cochain isomorphism, hence respects the nerve differential. `total` and
  `summands` specify the induced map on every (p,q) summand.
* `scalarInvariantChain` and `scalarTotalChain` are real constructions using the SAME
  beta from the restricted A'-resolution to the A-resolution. `ScalarComputation.lifts`
  supplies these beta, without assuming restriction preserves injectives. `columns`
  asserts the induced map in every internal-Hom column is a quasi-isomorphism;
  `invariantQI` and `totalQI` give the two vertical isomorphisms after localization.
  `square` explicitly equates the two composites of the localized augmentations
  with the INVERSES of these maps. Thus it states scalar compatibility in the derived
  category, with every lift quantified. Compose it with `Computation.naturality`
  for any N→Res N' to obtain exactly the node's general scalar/coefficients clause.
* No discrete representation category, topological-module cohomology, arbitrary
  comparison map, or arbitrary Nonempty-selected data defines any object here.
  The source records this formal bar input as an agent expansion with a reference
  wanted; the Lean docstrings retain that attribution honestly.

Dependencies used (recorded declarations read in full):

* `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`;
  `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`.
* `Sheaf.CategoryTheory.CondensedActionModule`: `ActionModule`, `actionPreadditive`,
  `forgetAction`, `Invariants` (landed while this work was in progress; initial
  duplicate draft constructions were removed).
* `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `InternalAbelianSheafModule.sectionModuleFunctor`, `sectionRingSheaf`.
* `Sheaf.CategoryTheory.CondensedInternalBarResolution`:
  `Profinite.CondensedAction.InternalBar.free`, `freeAdjunction`; their underlying
  `Sheaf.composeAndSheafify`, `AddCommGrpCat.free`, `Mod.free` constructions are reused.
* `WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor`: `Mod.ihom`;
  `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`: `Mod.comap`
  exactness; `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`: the ℕ total shape;
  Mathlib's `HomologicalComplex₂.totalFunctor`, `flipFunctor`, `ιTotal`.
* `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`: `InjectiveResolution`;
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs` and
  `.KInjective`: `rightDerivedFunctor`, `rightDerivedFunctorUnit`,
  `rightDerivedFunctorObjQIso`.

All recorded proof-dependency modules are imported (plain imports), including the landed
product-action inflation, internal-bar resolution through the public data import,
Grothendieck enough injectives, flat extension-by-zero, tensor closedness, derived
injective naturality, double-complex total and first-quadrant comparison, resolution
lifts and uniqueness, scalar internal-Hom adjunction, K-flatness, derived change of
rings, and the bounded-below injective lifting model category. The theorem docstring
includes all nine proof steps, including signs and the noninjective Res J comparison.

Edge cases checked: zero ring and zero module impose no Nontrivial assumption; G=1
and finite G retain the same internal action and no topology-to-discrete comparison;
Fin 0 gives the terminal zero power and first differential gm-m; for empty test objects
all generalized-element conditions still make sense. The internal-functions definition
also includes empty profinite parameters. Total degree n has only n+1 summands. Scalar
maps include identity, nonflat and zero-ring maps; no injective-preservation hypothesis
is imposed on scalar restriction. Identity coefficient maps between different resolutions
are included in naturality. Explicit localization universes repair the elaborator's
otherwise distinct implicit localizations without imposing any universe equality on sites.

Searches: `msearch.py` LeanFinder query "Derived internal Hom bar construction computes
invariants of modules over a condensed ring with a profinite group action" returned
LightCondensed internal-Hom and Condensed.profiniteFree, no exact result. Loogle
"Condensed, barComplex, invariants" returned no hit (unknown barComplex). LeanSearch
"Sheaves of modules with internal profinite group action and derived invariant bar complex"
returned ordinary `Rep.barComplex` and sheaf-module declarations, no internal theorem.
Mathlib grep `invariants|barComplex` in CategoryTheory and
`InternalFunctions|FunctionFamily|CondensedBar|Equivariant` in Condensed gave zero hits.
Direct rg in WeilConjectures and Sheaf initially found only unrelated discrete material;
the refreshed read found the newly landed action and free-module interfaces, which are
now used. DAG grep and blueprint_refs found no compatible derived bar-data definition;
ancestor reports None for the item's inherited chain. Exact search outputs are in the
new node's mathlib_searches, and the original local log is searches.jsonl.

Validation: scompile.py compiled BOTH delivered modules separately in dependency order,
including the normal library module names, with no warnings or errors. The only postponed
statement is the item's theorem. Final dry-run and delivery results are recorded below.

## New nodes

`def-sfb-condensed-equivariant-bar-data` defines the compatible cosimplicial, total,
derived-unit, augmentation, naturality and scalar-normalized specifications used by
`Assertion`. It reuses, rather than replaces, the landed action module, invariants,
free internal module, tensor-Hom, resolutions and totals. Its source is exactly the
item's formal expansion of paragraph (3); it is a definition of data, not another
postponed theorem. Its statement cites all eight interfaces it builds on. The three
search kinds above found no existing compatible data interface. Its blueprint ancestry
retains the item's null ancestor and explicit via chain.

## Second reading by NU

Self-review against the node after compilation: checked every hypothesis and clause
above, the landed interface replacements, all face indices, the first-quadrant signs,
and the scalar augmentation square. The important corrections during this reading were
removing duplicate action/free definitions after refreshed dependencies landed and fixing
all derived localizations explicitly to u+2. No independent agent was started: the dispatch
brief forbids delegation and assigns independent review to the maintainer. This section
records self-review only; it does not claim an independent second reader.
