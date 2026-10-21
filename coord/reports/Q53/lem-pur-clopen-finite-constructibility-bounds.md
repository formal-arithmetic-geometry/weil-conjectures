## Worker report

The module `lean/Sheaf/Paper/FiniteClopenConstructibilityBounds.lean` states
`WeilConjectures.PurityFiniteSetting.finite_clopen_constructibility_bounds`.
Its only postponed proof is that theorem's `sorry`; its docstring gives all eight
steps of the DAG proof. The helper `finiteClopenCoefficientFinite` exposes the
existing finiteness theorem on the existing coefficient quotient. It constructs
no new coefficient object and introduces no postponed theorem.

Hypotheses and coefficient conventions:

- `P : PurityFiniteSetting.{u}` is the recorded global finite-field datum, the
  prime different from its characteristic, the fixed coefficient closure and
  finite intermediate extension, and the positive level. `P.Ring` unfolds to
  `Padic.coefficientExtensionRing P.coefficients.l P.extension P.level`, the
  specified valuation-ring quotient by the chosen uniformizer power.
  `P.level_pos` includes every positive level; there is no divisibility or
  ramification assumption.
- `X : Scheme.{u}` and `[X.Over (Spec (CommRingCat.of P.field.k))]` give the
  scheme over the fixed algebraic closure. `LocallyOfFiniteType` and
  `QuasiCompact` on its structure morphism are exactly finite type.
- `{I : Type w} [Finite I]`, `Xi`, and `j` are the finite family of actual
  component schemes and immersions. Both immersion classes are explicit.
  `hdisjoint` makes distinct images disjoint and `hcover` makes their union all
  of X. No nonemptiness, nonempty component, separatedness or base compatibility
  datum beyond the canonical composite to the base is imposed.
- Every sheaf category is `proEtaleRingModules` over `proEtaleConstantRing` on
  the original small `Scheme.ProEt` site. Every derived category is the same
  standard localization `proEtaleDerivedCategory`. The site has object universe
  u+1 and morphism universe u; the finite index universe w is independent.

Conclusions, in their Lean conjunction order:

1. For each `S : Stratification X` and component i, the witness `T` has strata
   indexed by `e : Fin T.n ≃ Fin S.n`. The isomorphism
   `T.domain t ≅ pullback (S.immersion (e t)) (j i)` and its equation with the
   actual `pullback.snd` give precisely the intersected subschemes, with the
   original scheme structures. `Stratification` includes constructibility,
   locally closed immersions, disjointness and covering.
2. For any component stratifications `S`, the witness T is indexed by
   `Σ i, Fin (S i).n`, and the displayed isomorphisms identify each domain and
   its immersion with the original domain followed by `j`. These are the
   component strata viewed as subschemes of X. This retains the same finite
   locally constant models: restricting an isomorphism to a constant module
   along the first comparison restricts its trivializing cover, and the second
   comparison leaves the stratum and its sheaf unchanged. No arbitrary point
   subsets or changed reduced scheme structures replace the strata.
3. The `∀ F` equivalence uses exactly `IsConstructibleProEtaleModuleSheaf` and
   the canonical `proEtaleConstantRingPullback`. Its underlying object is the
   inverse image followed by extension along the constant-section comparison,
   namely the pullback in the recorded constructibility definition.
4. The `∀ K` equivalence with `∀ m : ℤ` detects constructibility of *every*
   cohomology sheaf, including complexes with infinitely many nonzero degrees.
   No boundedness premise replaces this assertion.
5. The next clause quantifies over any ordered integers a,b and identifies
   `proEtaleCohomologicalSupport K ⊆ Set.Icc a b` with the same containment for
   all actual derived restrictions. Support is exactly the set of degrees
   with nonzero cohomology sheaf, so these are the stated fixed bounds.
6. The next clause uses the retained recorded `HasProEtaleTorAmplitude`, with
   exactly the same a,b on each side. That predicate tests **every** module
   sheaf placed in degree zero and every K-flat resolution of each
   representative. It imposes no globally extendable-test restriction;
   component zero insertions are among those tests (proof steps 5--6).
7. The first existential equivalence has source the full subcategory of
   `intrinsicFiniteTorsionConstructible` and target the product of the same
   component full subcategories, exactly D^b_c.
8. The second uses `finiteTorConstructible`, exactly D^b_ctf. In both clauses
   the natural isomorphism after `Functor.pi` of the inclusion functors
   identifies the equivalence with `Functor.pi'` of the **canonical** derived
   restrictions, on objects and morphisms. This does not assert an unrelated
   abstract equivalence. The fixed-interval iff clauses apply to every inverse
   image of a tuple under these equivalences, proving the assertion about
   any preassigned common cohomological and Tor bounds for the glued object.
9. The last clause explicitly includes zero objects and every ordered interval,
   with both zero cohomology outside that interval and the Tor condition.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `Ring`, `ringCommRing`, its coefficient extension and positive-level fields.
- Mathlib `AlgebraicGeometry.Morphisms.FiniteType`, `...QuasiCompact`,
  `AlgebraicGeometry.OpenImmersion`, and `...Morphisms.ClosedImmersion`:
  `LocallyOfFiniteType`, `QuasiCompact`, `IsOpenImmersion`, `IsClosedImmersion`.
- Mathlib `AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `ProEt.topology`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`; its imported
  `Sheaf.Paper.ProEtaleConstructibleSheaf` supplies the recorded
  `Scheme.IsConstructibleProEtaleModuleSheaf`.
- `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude` publicly retains
  `Scheme.HasProEtaleTorAmplitude` and `HasFiniteProEtaleTorAmplitude` from
  `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`. The original intrinsic
  interface fits the category here; no universe equality or transport is needed.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: the retained primary declaration
  `WeilConjectures.finiteTorConstructibleEtale` and its added public exports
  `WeilConjectures.finiteTorConstructible` and `finiteTorConstructibleCategory`
  from the unchanged `Sheaf.Paper.FiniteTorAmplitude`.
- Mathlib `Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; its homology interface supplies `homologyFunctor`.
- The retained intrinsic Tor predicate supplies its own tensor construction.
  The item does not use `def-weil-derived-tensor` directly. Its NE record for
  `AlgebraicGeometry.ProEtale.derivedTensor` is byte-identical to live; no
  tensor node repair or direct tensor-module import is delivered.
- Added already-landed statement dependencies `def-weil-pbc-proetale-operations`,
  `def-weil-proetale-constructible-sheaf`, `def-weil-cohomological-support`:
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` provides
  `proEtaleConstantRingPullback`, `proEtaleConstantRingDerivedPullback`;
  the constructible-sheaf record retains the original intrinsic predicate;
  `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport` supplies
  `proEtaleCohomologicalSupport`. No new node or new notion is needed.
- Proof-only Mathlib declarations: stability of open and closed immersions
  under base change and `Topology.IsConstructible.preimage_of_isOpenEmbedding`
  (005J), `image_of_isOpenEmbedding` (09YD). Their modules are imported.
  `lem-pur-clopen-ringed-module-gluing` and
  `lem-pur-finite-product-derived-tensor-calculus` have no recorded module in
  this read clone, so there is no import for them; their uses are explicit in
  the proof docstring. They are proof prerequisites, not extra hypotheses.

Edge cases checked before writing:

- I empty forces X empty through `hcover`; neither I nor any stratum domain
  is required nonempty. The empty Sigma of component strata gives T.n = 0.
- The constructible-sheaf interface requires a positive number of strata;
  on the empty scheme one empty stratum realizes it. Empty strata are allowed
  by `Stratification`; this convention is equivalent to allowing the empty
  stratification. The proof docstring records this explicitly.
- Empty components, a singleton identity cover, and a two-point clopen cover
  all satisfy the formulas. Ordered singleton intervals a=b and arbitrarily
  shifted component complexes retain the exact specified endpoints.
- For A=O_E/(varpi^2), a residue module may be bounded constructible without
  finite Tor amplitude; the two subcategories remain distinct.
- The zero complex satisfies every ordered interval. For the empty cover the
  same universal Tor tests still include the unique zero sheaf; no vacuous
  restriction to a smaller coefficient universe or nonzero tests is imposed.

Searches for duplicates (2026-10-21):

- `msearch.py Q53 lem-pur-clopen-finite-constructibility-bounds leanfinder
  "Constructibility and fixed cohomological and Tor bounds are detected on a
  finite disjoint clopen scheme cover"`: 8 hits, including
  `IsLocallyConstructible.iff_isConstructible_of_isOpenCover`, scheme open
  covers and locality of locally Artinian/Noetherian schemes. None states
  constructibility of these module sheaves or either fixed derived bound.
- `msearch.py ... loogle "IsConstructible, IsOpenImmersion"`: zero hits,
  unknown identifier `IsConstructible` (the topology declaration is namespaced).
- `msearch.py ... grep
  "clopen.*(constructib|[Tt]or)|([Cc]onstructib|[Tt]or).*clopen"`: 24 hits,
  indicator functions, clopen boxes and topological clopen sets; no exact theorem.
- `rg` on the node id and clopen/constructibility/Tor patterns in
  `lean/WeilConjectures` and `lean/Sheaf`, and the upstream name index:
  no declaration for this node. The published
  `Sheaf.Paper.FiniteClopenDerivedDecomposition` contains
  `finiteClopen_finite_bounds`, `finiteClopen_finiteTor_iff` and
  `finiteClopen_finite_equivalences`. Their full signatures were read.
  They cover several derived clauses, but omit sheaf constructibility,
  unbounded constructible cohomology, and the explicit scheme strata
  assertions, so an `existing:true` binding would omit parts of this node.
  This module does not import that downstream module or duplicate its notions.
- Exact proposed declaration names were searched in Mathlib, WeilConjectures
  and Sheaf with `rg`; no collision was found.

Sources read: the item's complete eight-step DAG proof, all statement-dependency
statements/records and their recorded declarations/docstrings, the current blueprint
`main-20261015/.../def-pur-section-invariant.md`, and the Stacks topology.tex
lemmas named by Tags 005J and 09YD. No statement correction or disputed claim.

Validation after H13 repair: server `scompile.py` compiled both
`FiniteTorAmplitudeSites` and `FiniteClopenConstructibilityBounds` under their
sandbox and real library module names, using the repaired dependency as a private
overlay. All passes were clean, with no errors or warnings. A structural self-check
verified the derived-tensor node's byte identity, preservation of NW's primary
module/declaration/statement and complete declaration-list prefix, and exact
identity of every prior source byte after removing the one added public import.
The item still has exactly one `sorry`, in its theorem proof; the dependency
module has none. All Lean lines satisfy the 100-character convention.

## Dependency modules

`def-weil-finite-tor-amplitude`: additive Section 1(B) repair of
`Sheaf.Paper.FiniteTorAmplitudeSites`. The existing ordinary-etale predicate cannot
be applied to the pro-etale category of this item. The module now publicly imports
`Sheaf.Paper.FiniteTorAmplitude`, exposing the already defined pro-etale
`WeilConjectures.finiteTorConstructible` and `finiteTorConstructibleCategory`.
The node retains NW's module, primary `finiteTorConstructibleEtale` declaration,
statement and all prior declarations; the two pro-etale names augment the list.
The ordinary-etale definition and its docstring are byte-identical to live.
No new definition, theorem, stronger hypothesis or coefficient transport is added.
Only this dependency's `lean` field changes, with the additive repair in `lean.note`.

## Returned delivery H13 repair

The independent review of head `5f1d0861b0ab` accepted the item statement but
returned two destructive dependency-record replacements. Both are repaired:

1. `def-weil-derived-tensor.json` is restored byte-for-byte from live, retaining
   NE's `AlgebraicGeometry.ProEtale.derivedTensor` binding. It contributes no
   change to the delivery. The item uses tensor only through the unchanged
   `HasProEtaleTorAmplitude`, so its direct intrinsic tensor import was removed.
2. `def-weil-finite-tor-amplitude` retains NW's recorded ordinary-etale interface.
   Its original declarations list is a prefix of the new list; only the two
   already published pro-etale names are appended. The existing module gains
   one public import, with every prior source byte retained. This preserves
   `EtaleGeometricBiduality`, `EtaleLocallyClosedShriek`, `SupportedClassGeometry`,
   `InternalAdjunctionPairingChange` and `BoundaryAlphaNormalization`, whose
   `finiteTorConstructibleEtale` name and body remain available unchanged.

The initial saved-packet dry run passed as commit `d19d9541190`; that mechanical
pass did not resolve H13. This repair changes the actual module and records and
is compiled and dry-run again before delivery. The item theorem's signature,
proof docstring and single `sorry` are unchanged from the accepted statement.

## Second reading by Q53

Final in-session rereading, with the node and the complete Lean signature open;
no separate agent was started, as the dispatcher explicitly prohibits it.
The two strata clauses retain actual immersed schemes by isomorphisms commuting
with their immersions. The sheaf and unbounded-cohomology clauses are separate;
the latter was not replaced by bounded constructibility. Cohomological and Tor
intervals have identical a,b in all components, and the Tor definition permits
all degree-zero module sheaves. The two full-subcategory equivalences commute
with the actual ambient restriction, avoiding arbitrary equivalences. All global
and finite-cover hypotheses are present; no nonempty or separation hypothesis
was introduced. The empty-stratum convention and the zero-object clause were
checked against the exact existing predicates. The only formatting mismatch
found by compilation was the five long lines, now wrapped. The dependency repair now preserves NW's ordinary-etale binding and adds the
pro-etale exports; NE's tensor record is restored byte-identically, as detailed
in the H13 repair section. All definitions have real data;
there is exactly one postponed theorem, matching the item's DAG node.

Repair self-check: reread the two full module files and the finite-Tor node record.
The only dependency source change is `public import Sheaf.Paper.FiniteTorAmplitude`;
the item's import now uses the recorded `FiniteTorAmplitudeSites` module. All
nine conclusion clauses still use the same intrinsic pro-etale objects and
canonical restrictions. The saved-record statement equals the theorem signature
verbatim. The preserved ordinary-etale definition still serves the five consumers
named by the reviewer, including `Sheaf.SixFunctors.BoundaryAlphaNormalization`.
No new statement correction or node is introduced by this repair.
