## Worker report

Module `Sheaf.Paper.AmbientQcqsExchangeCanonicalShifts` states the complete node in
three named theorems, all with `sorry` proofs. No definition or map is replaced.
The natural-language statement is unchanged. The item cites the new definition node
`def-sfb-module-derived-functor-shifts` for its specified shift instances. The
compositor theorem node remains a proof dependency, with a plain proof import.

Hypothesis and clause correspondence:

- A commutative condensed ring is `Λ : Sheaf (coherentTopology Profinite.{u})
  Ab.{u + 1}` with `[MonObj Λ] [IsCommMonObj Λ]`. This is the unbundled form of the
  recorded `Profinite.CondensedRing` ring-object abbreviation; it includes arbitrary
  condensed rings, without requiring a topological presentation.
- The four arbitrary schemes are `{X' X C Y : Scheme.{u}}`, with the four named
  arrows and `sq : ChosenCartesianSquare a f' f c`. The chosen Cartesian
  identification, projection equations and commutativity are exactly those of
  the recorded square structure.
- `DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  (condensedRingObj Λ X))` is the ordinary unbounded D_X. All universes are explicit;
  the published module-object framework supplies the small-site size convention.
  No finite type, Noetherian, properness, boundedness or constructibility binder occurs.
- Phi is `moduleObjectDerivedPushforward Λ f ⋙ moduleObjectDerivedPullback Λ c`;
  Psi is `moduleObjectDerivedPullback Λ a ⋙ moduleObjectDerivedPushforward Λ f'`.
  Functor composition is written in application order, so these are c* Rf* and Rf'* a*.
  The first two conjuncts of `ambient_qcqs_exchange_canonical_shifts` are their
  `IsTriangulated` assertions with the existing composite shift structures.
- The final conjunct quantifies over every `(n : ℤ)` and every `L : D_X`, and states
  `Ex.app (L⟦n⟧) ≫ zeta = xi ≫ (Ex.app L)⟦n⟧'`. This is exactly the displayed
  equation in Lean's left-to-right composition order. `Ex` is the actual recorded
  `condensedAmbientExchange Λ sq`.
- The prescribed shift normalization is the existing
  `modulePullbackDerivedCommShift` (transport through the canonical exact comparison)
  and `modulePushforwardDerivedCommShift` (the published K-injective structure).
  No shift instance is installed using `rightAdjointCommShift` here.
- `ambient_qcqs_exchange_canonical_normalization` asserts `NatTrans.CommShift` for
  the unit and counit of each specified derived adjunction (f and f'), and for
  `(condensedAmbientPullbackComparison Λ sq).hom`. Its source and target functors
  are explicitly written with the named module functors, ensuring the same fixed
  shifts are used. The square is defined by the actual two canonical compositors
  and the equality in `sq`, already normalized to the localized termwise square
  by the compositor dependency; no arbitrary square comparison is supplied.
- `ambient_qcqs_exchange_distinguished_triangle` takes a triangle `T` and its
  distinguishedness proof. Both image triangles are asserted distinguished.
  It gives a triangle morphism `t` whose `hom₁`, `hom₂`, `hom₃` are precisely the
  three exchange components. `TriangleMorphism.comm₃` is the connecting-arrow
  square, with the shift comparisons already present in `mapTriangle.obj`.
  Thus the final square is part of the assertion, not omitted as naturality alone.

Dependency declarations read and used:

- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward` and
  `moduleObjectDerivedPullback`, transparent names for the full composite total
  derived functors, publicly imported through the shift dependency.
- `Sheaf.Paper.CondensedAmbientExchange`: `condensedAmbientExchange` and
  `condensedAmbientPullbackComparison`; the exchange is the unit/square/counit mate.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`:
  `derivedUpperStarLowerStarAdjunction`, `leftDerivedUpperStarComp`, and the
  `upperStar`/`lowerStar` functors reexported by it. The adjunction is the specified
  K-flat/K-injective derived adjunction of the full underived composites.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`, publicly available through exchange.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, publicly
  imported by the shift module; its exact unbundled ring-object data is used above.
- `Sheaf.Paper.ModuleDerivedFunctorShifts`:
  `modulePullbackExactComparison`, `modulePullbackDerivedCommShift`, and
  `modulePushforwardDerivedCommShift`, owned by the new definition node.
- `Sheaf.Paper.ModuleDerivedFunctorCompositorShifts` (proof import):
  `module_derived_functors_exact_and_comparison_shifts`,
  `module_pullback_compositor_exact_normalization` and `module_pullback_square_shift`.
  These supply precisely the canonical shift and localization normalization.
- Mathlib `CategoryTheory.Pretriangulated`, `Functor.IsTriangulated`,
  `Functor.mapTriangle`, `NatTrans.CommShift` and the commutation/whiskering lemmas
  in `CategoryTheory.Shift.CommShift`; composite exactness is
  `Functor.IsTriangulated.instComp`. Signatures and definitions were read.
- Proof-only imports retain the recorded `def-weil-pbc-proetale-operations` module
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` and the recorded
  `lem-weil-pbc-proetale-derived-pullback-composition` module
  `Sheaf.Paper.IntegralFinitePullbackComposition`.
- `def-weil-size-convention` is a metatheoretic convention, without an import.
  `lem-sfb-kflat-derived-adjunction-transport-shifts` currently has no Lean record
  or Mathlib match; it is a proof dependency only and no declaration is needed to
  state this item. Its future proof import is left for the maintainer when stated.

Edge cases checked before writing: n=0 and n negative remain quantified; n=1 gives
exactly the connecting-arrow comparison. Empty schemes and the zero coefficient ring
are admitted with the same signatures. Identity squares specialize to their canonical
unit/compositor/counit maps. The exchange need not be invertible. No boundedness,
properness or qcqs assumption is introduced despite the historical item name.

Searches for existing statements:

- `msearch.py`, leanfinder: "The canonical derived base change exchange transformation
  for condensed module sheaves commutes with all integer shifts and gives morphisms
  of distinguished triangles". Eight results: condensed-module category instances,
  exact-derived-functor shift instances and sheaf pullback composition; no full match.
- `msearch.py`, loogle: `CategoryTheory.NatTrans.CommShift,
  CategoryTheory.Functor.IsTriangulated`. Eight results on transporting triangulatedness
  and derived functors, with no statement for the specified ambient exchange.
- `msearch.py`, grep: `condensedAmbientExchange|ambient.*[Cc]ommShift|
  exchange.*[Cc]ommShift` in Mathlib CategoryTheory: zero hits.
- `rg` of the same patterns and the item id in `lean/WeilConjectures` and
  `lean/Sheaf` finds the actual exchange definition and consumers. Read the private
  iso-locus theorem in `Sheaf.Paper.UnboundedBaseChangeExtension`: it installs new
  right-adjoint shifts rather than retaining the fixed K-injective shifts, and
  asserts closure of the iso locus rather than this item's normalization and
  triangle-morphism clauses. It is not an existing match.
- `rg` of the proposed declaration names in upstream names, source and Sheaf has
  no hit. The delivered file introduces only the three item theorem names.

Sources read: local Stacks derived.tex, labels lemma-derived-shift (05SU),
lemma-right-derived-exact-functor (015F), lemma-pre-derived-adjoint-functors (0DVC),
and the current blueprint's det-sf-comp-coherence-refinement proof (2).
Every theorem docstring contains its corresponding full natural-language proof route.
No disputed statement or statement correction is needed. The ownership repair, new
definition node and dependency module are detailed below.

## Second reading by Q14

No second worker was started, as required by the dispatch. The maintainer's independent
review reads this delivery. I checked the three signatures against every clause above:
the square orientation is a then f = f' then c; the shift equation has Ex then zeta;
the final theorem uses a triangle morphism with the specified components, whose third
square includes the connecting map. The first compile found a lexer ambiguity at a
shifted parenthesized component; inserting a space fixed that notation.


## Return repair

The immutable returned head was `0bfbf3530b66`; the retained delivery log records
`0bfbf3530b6`. The saved packet was inspected before editing and its required first
fresh dry run passed at `fe8224fb0ae`. That packet still had the ownership defect,
so it was not re-pushed. Current server source of
`Sheaf.Paper.ModuleDerivedFunctorCompositorShifts` was read with `scompile.py --source`
and agrees with the local source from which the extraction is made.

The return has one required repair. The three plain definitions/instances
`modulePullbackExactComparison`, `modulePullbackDerivedCommShift` and
`modulePushforwardDerivedCommShift` now belong to the new definition node below.
They are removed from the compositor module and its `lean.declarations`; that
module publicly imports the new module. The item replaces its former extra theorem
statement-dependency by the definition node, and publicly imports the definition
module. It keeps a plain import of the compositor module for the proof dependency.
Every declaration name, parameter, type, body and instance priority is retained.
Only the moved docstrings' blueprint ownership changes. No theorem signature or
mathematical statement changes, and every postponed proof remains `sorry`.

## New nodes

`def-sfb-module-derived-functor-shifts`, module
`Sheaf.Paper.ModuleDerivedFunctorShifts`, owns precisely the three extracted
constructions. Its source is Stacks derived.tex Tags 014X
(`lemma-additive-exact-homotopy-category`), 015F
(`lemma-right-derived-exact-functor`, with the dual left-derived comparison) and
05SE (`proposition-derived-functor`), together with the published K-injective
implementation. It serves refinement (2) of the compactification coherence proof,
under the item's blueprint ancestor `det-sf-comp-coherence-cocycle`.

Hypothesis and clause correspondence for the new definition node:

- Arbitrary commutative condensed coefficients and arbitrary scheme arrows are
  the explicit section variables `Λ`, `[MonObj Λ]`, `[IsCommMonObj Λ]`,
  `{X Y : Scheme.{u}}`, `(f : X ⟶ Y)`. There is no extra geometric hypothesis.
- The categories and the specified full derived functors are the existing
  `moduleObjectDerivedPullback` and `moduleObjectDerivedPushforward`. Their module
  `Sheaf.Paper.CondensedModuleDerivedPushpull` is publicly imported; their definitions
  are exactly `(upperStar Λ f).leftDerivedFunctor` and
  `(lowerStar Λ f).rightDerivedFunctor`. The coefficient object is the existing
  `condensedRingObj`, the module category is Mathlib `Mod`, and the ordinary
  unbounded category is Mathlib `DerivedCategory` with the framework's universes.
- The canonical `c_f` is `modulePullbackExactComparison`, using the recorded
  `CategoryTheory.Functor.leftDerivedExactComparison` with the actual
  `leftDerivedFunctor` and `leftDerivedFunctorCounit`. This uses the universal
  comparison, not a choice of an arbitrary natural isomorphism.
- The termwise shifts are the existing `mapDerivedCategory.CommShift` structure.
  `modulePullbackDerivedCommShift` is exactly
  `Functor.CommShift.ofIso (modulePullbackExactComparison Λ f).symm ℤ`.
  Reading Mathlib's `CommShift.ofIso` shows its component is
  `c_(K[n]) ≫ s_D(K) ≫ c_K.inv[n]`, which is precisely the node's displayed
  right-to-left composition formula.
- `modulePushforwardDerivedCommShift` is
  `inferInstanceAs ((lowerStar Λ f).rightDerivedFunctor.CommShift ℤ)`.
  The source of `RightDerivedFunctor.Triangulated` defines this structure by
  transport from `rightDerivedFunctorIsoKInjectives.symm`, built using the inverse
  K-injective equivalence, termwise pushforward, and `DerivedCategory.Qh`.
  No new adjunction-derived shift structure or existence choice is introduced.

Searches actually performed for this node:

- `msearch.py leansearch`: “Transport integer shifts on exact derived module pullback
  along the canonical comparison and use fixed K-injective shifts on derived module
  pushforward”: eight hits, including termwise `mapDerivedCategory` shifts,
  their factorization comparison and K-injective shift stability. These are reused;
  none owns the three specified module specializations.
- `msearch.py loogle`: `CategoryTheory.Functor.CommShift.ofIso`: four hits,
  `ofIso`, `ofIso_compatibility`, `ofIso_commShiftIso_hom_app` and
  `ofIso_commShiftIso_inv_app`. The transport construction is reused exactly.
- `msearch.py grep`: `modulePullbackExactComparison|modulePullbackDerivedCommShift|
  modulePushforwardDerivedCommShift`: zero Mathlib hits. `rg` with the same pattern
  in `dag/nodes`, `lean/WeilConjectures` and `lean/Sheaf` finds only the compositor
  theorem module and its theorem-node record. Thus these existing bodies are moved,
  not copied, into the new owner. `rg` for transported shifts and K-injective shifts
  in the DAG and `blueprint_refs.py search` for `shift` and `transported` found no
  definition node owning this specialization. The search records retain the actual
  queries/results; generic matches are not reported as absent.

Edge cases: negative shifts and zero shifts are all part of `CommShift ℤ`, with
its zero/addition laws supplied by Mathlib's real transport structure. For an
identity scheme map the same canonical comparison is used; no identity-only branch
or normalization is assumed. The zero condensed ring and the empty schemes remain
admitted. There is no invertibility assumption on the exchange, nor a restriction
on the boundedness of a derived object.

## Dependency modules

`lem-sfb-module-derived-functor-compositor-shifts` receives a lean-only §1(B) repair.
Its old record owned three plain shift constructions under a theorem node. That
ownership could not justify using them as statement notions of the item. The repaired
`Sheaf.Paper.ModuleDerivedFunctorCompositorShifts` publicly imports their definition
module and retains all the other declarations, with their original types and bodies.
Its `lean.declarations` drops exactly the three moved names; its `lean.note` explains
this interface repair. No non-lean field of this dependency node changes.

The six retained theorem clauses were re-read against the node: exactness of both
functors and shift compatibility of both comparisons are the four conjuncts of
`module_derived_functors_exact_and_comparison_shifts`; the K-flat resolution counit
normalization and its shift equation are the two conjuncts of
`module_pullback_resolution_shift_normalization`; localization of the ordinary
compositor is `module_pullback_compositor_exact_normalization`; its degree `r+n`
representative is `module_pullback_compositor_shift_degree`; hom and inverse shift
compatibility are `module_pullback_compositor_commShift`; the arbitrary commutative
square identity is `module_pullback_square_shift`. The remaining helper definitions
still construct the termwise comparison, resolution counit, specified compositor
and specified square. Their source/proof docstrings and all six `sorry` bodies are
unchanged. In particular no cartesian hypothesis is added to its last theorem.

## Second reading by Q14 (repair)

No other agent was started, as the dispatched brief requires. This is a self-check
for the maintainer's independent review. I read both new/repaired node records and
all three modules. The three extracted constructions have unchanged names, section
parameters, signatures and bodies; their docstrings now cite the definition node.
The compositor module publicly reexports them and lists only its own remaining
declarations. The item imports that definition publicly and the theorem privately.
The item's only extra statement-dependency over current main is the definition node;
the compositor theorem remains among its original proof dependencies. Its three
original theorem statements and the natural-language node statement remain unchanged,
so the earlier clause-by-clause mathematical check still applies. The new node's
transport formula was checked directly against Mathlib `CommShift.ofIso`, including
its inverse direction. All universes are explicit and `autoImplicit false` remains
in every module. Compilation and delivery checks follow below.


Validation: `scompile.py Q14 lem-sfb-ambient-qcqs-exchange-canonical-shifts`
compiled all three delivered modules separately in dependency order, including their
actual library paths, with no errors or unexpected warnings. Library checks took
9.0 s for `ModuleDerivedFunctorShifts`, 11.6 s for the repaired compositor module,
and 17.2 s for the item. A structural comparison confirms that the dependency
node changes only in `lean`, the item only in `lean` and `stmt_deps`, all six
compositor theorem declarations are unchanged, and every Lean line is at most
100 characters. The first repaired dry run accepted the module/node ownership
shape and found two bracket-citation errors in the new definition's prose:
a combined `[sk-def-sfb-module-objects, def-weil-abstract-derived-category]`
was split into the two exact separate node citations required by the preflight.
No Lean code changed for that correction.

## Reviewer fix (maintainer review of 735d3bd09435)

The PASSed head 2472d1bb0dce (byte-identical content) was refused at landing by the import-prune
check: `ModuleDerivedFunctorShifts` declared the three names that the delivery itself removed from
`ModuleDerivedFunctorCompositorShifts` (the landing index does not drop names a delivered module
removes). The fix therefore moves nothing:

- `Sheaf.Paper.ModuleDerivedFunctorCompositorShifts` is restored to its published text (unchanged);
  it keeps declaring `modulePullbackExactComparison`, `modulePullbackDerivedCommShift` and
  `modulePushforwardDerivedCommShift`.
- `Sheaf.Paper.ModuleDerivedFunctorShifts`, the module of `def-sfb-module-derived-functor-shifts`,
  publicly imports it and reexports the three declarations, which the node's `lean.declarations`
  list; its primary declaration is the transparent abbrev `modulePullbackCanonicalExactComparison`
  (`rfl`-equal to `modulePullbackExactComparison`). `existing: true` on the compositor module was
  not used: the non-module `#check` probe of that module fails on the
  `AcyclicKFlatTensor` Sheaf/WeilConjectures import clash.
- The item module and its record are unchanged; its public import of `ModuleDerivedFunctorShifts`
  still provides the specified shift instances.
