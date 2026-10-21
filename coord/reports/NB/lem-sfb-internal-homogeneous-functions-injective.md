## Worker report

This delivery states `Profinite.CondensedAction.homogeneous_functions_injective` in
`Sheaf.CategoryTheory.CondensedHomogeneousFunctionsInjective`. Its only theorem has
proof `sorry`. The other declarations are transparent abbreviations, an evaluation
construction, and a normalized specification, all with real data. The repair adds
one definition node binding existing canonical generators,
uses the existing bar-data freeParameter directly, and makes no dependency-module
or statement correction.

The previous worker's stale-assignment diagnosis was mistaken: the NW report is headed
"Stage-1 worker report", and the merge recorded at coord/ledger.md:23389 landed the
proof split only. The assigned node has no Lean record on the base. This delivery is
its first stage-2 formalization, not another stage-1 split.

Clause-by-clause correspondence:

- The arbitrary commutative condensed ring is `R : Profinite.CondensedRing.{u}` with
  `[IsCommMonObj R.X]`. No topological presentation of R is assumed.
- The coherent profinite site is `coherentTopology Profinite.{u}`; coefficients and
  section modules have universe u+1, and the site has object universe u+1 and morphism
  universe u. This is the recorded size convention, with explicit universe u and
  `set_option autoImplicit false`; no equality of site and coefficient sizes is added.
- The profinite group is `G : Type u` with `Group`, `TopologicalSpace`,
  `IsTopologicalGroup`, `CompactSpace`, `T2Space`, and `TotallyDisconnectedSpace`.
  The action sections are the recorded `C(S,G)` for every profinite S.
- The internal equivariant coefficient module is `J : ActionModule R G`, with exactly
  the dependency's action, linearity, naturality, and morphisms. Its underlying
  internal module is `J.module`, and the sole injectivity assumption is
  `[CategoryTheory.Injective J.module]`, never injectivity of J(S).
- Every integer n >= 0 is covered by `(n : ℕ)`, including n=0.
- The free module is the existing `CondensedBar.freeParameter ⟨R.X⟩
  (CondensedBar.power G (n+1))` from def-sfb-condensed-equivariant-bar-data. Here
  `⟨R.X⟩` bundles the given commutativity instance; it changes no ring data or
  universe. The module is definitionally the existing `InternalBar.freePower`.
  Its unit generators are the existing `InternalBar.generator`, now bound by
  def-sfb-condensed-free-module-generators. No free object or generator is copied.
- `homogeneousHom R G J n` is the existing `SheafOfModules.homObj` applied to that
  free module and UJ under the recorded section-module equivalence. This equivalence
  retains sections and restrictions; the Hom is the tensor right adjoint by the
  recorded closed tensor theorem. The internal Hom has the coefficient universe u+1;
  its four universe parameters are supplied explicitly to avoid elaborator defaults.
- `HomogeneousFunctions.internalHom` identifies the underlying module sheaf of the
  equivariant object with exactly that Hom. `homogeneousEvaluate` applies an actual
  slice-linear map at `Over.mk f` to a canonical free generator.
- `HomogeneousFunctions.action` quantifies S, g in C(S,G), a section c, every T, every
  f:T→S, and every continuous tuple x of length n+1 over T. Its left side evaluates
  g acting on c. Its right side applies `J.act T (g.comp f.hom.hom)` to c evaluated
  at `fun i ↦ (g.comp f.hom.hom)⁻¹ * x i`. Thus it is precisely the node's displayed
  diagonal formula, after every profinite base change, with the correct inverse and
  multiplication order.
- `∃ H : HomogeneousFunctions R G J n, Injective H.object` states existence of the
  specified action and injectivity in the actual existing action category. A displayed
  underlying isomorphism is used so existence need not choose a module from a theorem.
  All such normalized models are equivariantly isomorphic: use their two internal-Hom
  identifications, full faithfulness of the recorded equivalence, and the action formula
  on all local generators. Hence this is injectivity of the stated object, with no
  additional arbitrary action parameter and no weaker alternative construction.
- There is no projectivity, discreteness, finite-group, enough-injectives, resolution,
  sectionwise-injectivity, or flat-coefficient hypothesis. The proof uses flatness of
  the free representable module, as the node's proof does.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` (publicly reexported
  by the action module).
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`, `Mod.Hom`,
  regular module and forgetful functor; the module category is used via
  `Profinite.CondensedAction.Modules`.
- `Sheaf.CategoryTheory.CondensedActionModule`: `Modules`, `sectionModule`,
  `ActionModule`, `Equivariant`, `actionCategory`. The entire recorded module was read.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `CategoryTheory.Injective`,
  whose `factors` field is exactly the extension property in both categories.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`:
  `SheafOfModules.tensorClosed`, the recorded closedness/naturality statement.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `CategoryTheory.InternalAbelianSheafModule.sectionModuleFunctor` and
  `sectionModuleEquivalence`; the actual sections of its output are used.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`, whose sections are slice module morphisms, and its
  underlying `PresheafOfModules.restrictOver` and `homObj` source were read.
- `Sheaf.CategoryTheory.CondensedEquivariantBarData`: `CondensedBar.freeParameter`
  and `CondensedBar.power`, used directly for the free internal module. Its
  `InternalFunctions` was read: it specifies function functors and evaluations but
  supplies no canonical free-adjunction unit generator.
- `Sheaf.CategoryTheory.CondensedInternalBarResolution`: existing `InternalBar.free`,
  `freeAdjunction`, `tuples`, `freePower`, `generator`, recorded by the new definition
  node def-sfb-condensed-free-module-generators. The consumer directly uses `generator`;
  the other four implement that generator. The resolution theorem is not used.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat`:
  `SheafOfModules.isFlat_extensionByZero_unit`, imported for the proof plan.
- `def-weil-size-convention` is metatheoretic, with no declaration to import.

The added statement dependencies are the bar-data definition, the new definition
node owning the existing generator helpers, the section-module equivalence, and
slice sheaf Hom. The latter two were already proof dependencies. The worker-added
bar-resolution theorem dependency is removed; it was absent from the base node.
No base statement dependency or existing dependency record is changed. Imports cover
all original statement and recorded proof dependencies; there is no import cycle.

Edge cases checked before writing: n=0 still has one homogeneous group coordinate and
an empty relative tuple in the proof. G=1 gives the ordinary extension property into
UJ, and all powers and generators remain defined. J=0, a zero coefficient ring, and
empty profinite test objects are allowed. Infinite profinite groups use continuous
maps and entire slices, with no finite or locally constant replacement. The statement
requires no sectionwise splitting or sectionwise injectivity. No statement dispute
was found.

Searches (prescribed msearch.py unless specified):

1. LeanFinder: "Internal homogeneous functions on a profinite group with injective
   internal module coefficients form an injective equivariant module". Eight hits,
   including `Rep.instInjective`, `FDRep.instInjectiveOfNeZeroCastCard`, profinite
   limit-map injectivity and representation intertwining maps. None states this
   arbitrary-ring internal assertion.
2. Loogle: "CategoryTheory.Injective, SheafOfModules.homObj". Zero hits; service
   reported unknown identifier SheafOfModules.homObj (it is a project declaration).
3. Mathlib grep: "homogeneous|coinduc" in CategoryTheory. Two unrelated hits:
   Galois/Topology.lean coinduced topology and Abelian/Injective/Resolution.lean
   Homotopy.mkCoinductive.
4. Direct rg in Mathlib for internal.homogeneous, homogeneous.functions and
   homogeneous.*injective: no matching statement. Direct rg and the required
   item-id grep in lean/WeilConjectures: no item declaration. Direct rg across
   lean/Sheaf, lean/WeilConjectures and the DAG found existing bar/free constructions
   and the existing internal-function specification; those were read. Neither states
   homogeneous-function injectivity. New fully qualified declaration names were
   searched in both project source roots; no collision.

Sources read: the item's complete statement and eight-step proof, every stmt_dep
statement and record, their source declarations and docstrings, the current blueprint
paragraph (3), the existing internal-bar and bar-data modules and node statements,
Stacks homology.tex lemma-adjoint-preserve-injectives (015Z), sites-modules.tex
lemma-j-shriek-flat (03EV) and lemma-internal-hom-adjoint-tensor (03EO). The theorem's
proof docstring follows the node's eight steps, with the explicit slice construction
of the action included in step 6. This is the agent-formulated helper recorded by
the node, not a claim that the short blueprint paragraph itself states this lemma.

Validation: the retained packet was inspected first and its prescribed initial dry run
passed (249e57a1ca0). This did not repair the immutable-head review, so the concrete
H2/H4 dependency repair below was made. scompile.py compiled the repaired module
separately as a sandbox (8.3 seconds) and library module (6.8 seconds), exit 0 with
no errors or warnings. The unchanged theorem signature, action formula and eight-step
proof docstring are retained. All binders remain explicit under autoImplicit false.

## New nodes

`def-sfb-condensed-free-module-generators` records the existing plain definitions
`InternalBar.free`, `freeAdjunction`, `tuples`, `freePower`, and `generator` in the
unchanged module Sheaf.CategoryTheory.CondensedInternalBarResolution. The primary
binding is `generator` with `existing: true`; no new Lean module or definition is
written. Its statement gives the free-forgetful composite adjunction and unit
inclusion on local continuous tuples, including arity zero. The source is the
agent-formulated free-module construction supporting the same blueprint paragraph
(3), as already implemented in the existing module at lines 53-90.

H12/non-duplication: def-sfb-condensed-equivariant-bar-data was checked FIRST and is
usable. Its `freeParameter` has literally the same composeAndSheafify/free module
body as `InternalBar.freePower`, and is now used directly in `homogeneousHom`.
That definition node is cited both by the consumer and by the new definition node.
Its `InternalFunctions` is a normalized specification; it supplies no canonical unit
generator or free adjunction. The new node fills that missing definition ownership
by attaching existing declarations, rather than constructing the same notion again.
The supporting `free` and `freePower` names are the already-landed implementation of
the generator; no alternate free object is introduced. This is the existing:true
helper-ownership pattern, as in def-per-log-characteristic-generator-image.

The new node's clauses map as follows: A and commutativity are R and IsCommMonObj R.X;
the site and universe are coherentTopology Profinite.{u} and coefficient u+1;
its modules and sections are Modules R and sectionModule R; F_A is InternalBar.free,
its adjunction is InternalBar.freeAdjunction, P_n is InternalBar.tuples G n,
A[G^n] is InternalBar.freePower R G n (definitionally the cited freeParameter), and
[x] is exactly InternalBar.generator R G n S x. The latter applies the adjunction
unit at op S to the ULift of the continuous tuple map. No theorem or `.choose`
is involved in any of these bodies. All topology/group binders are those of the
existing module, in the same single universe u. Edge cases: n=0 gives the singleton
power and its empty tuple generator; empty S admits its unique continuous tuple;
trivial or infinite G, zero ring and zero coefficient modules require no changes.

New-node searches, all before writing the node:

- msearch leansearch: "Generators from the unit of the free abelian sheaf and internal
  module adjunction". Eight hits, including PresheafOfModules.freeAdjunction,
  freeAdjunctionUnit, SheafOfModules.free/freeSection and AddCommGrpCat.adj.
  These give generic components or free modules on constant indices, not this
  internal condensed-ring tuple-generator interface.
- msearch leanfinder: "Canonical generators of the free internal module on a profinite
  representable over a condensed ring". Eight hits, notably Condensed.profiniteFree
  and Condensed.free, which concern ordinary constant coefficient rings.
- msearch loogle: "Sheaf.adjunction, Mod.freeForgetAdjunction". No hits; the service
  reported unknown identifier Sheaf.adjunction. The actual source declarations were read.
- msearch grep: "freeParameter|freeAdjunction|generator" in Condensed. No hits.
- Direct rg in lean/WeilConjectures and lean/Sheaf found the existing bar-resolution
  helpers and the bar-data freeParameter. Direct rg over definition-node records
  found no InternalBar generator owner. The bar-data record and full signatures and
  docstrings were read; its prior review explicitly distinguishes these plain defs
  from the theorem. blueprint_refs.py search "free internal module" returned zero.

The raw prescribed search results are retained in the new node's mathlib_searches.

## Repair of immutable head 7f48924c142b

H2/H4: the previous worker-added stmt_dep lem-sfb-condensed-internal-bar-resolution
is replaced by the definition node above, and the existing bar-data definition is
cited and used directly. The initial report's claim that using plain defs justified
the theorem dependency was wrong. The theorem dependency is gone; the actual
existing generator has a definition owner. No second copy, no statement correction,
no changed proof, no change to any accepted hypothesis or conclusion.
The advisory base tensor-closed dependency is retained: it belongs to the original
node and supplies the closedness used in the proof plan.

## Second reading by NB

Worker self-check after repair (the independent review is the maintainer's): read
the item node, new node, their records and both relevant existing source modules
again. The new node owns precisely the five existing definitions before the
resolution theorem, and none of their bodies refers to that theorem. `freeParameter`
is directly used for the Hom source and is definitionally the generator's source;
compilation checks this without an extra equality or transport assumption. The
original arbitrary commutative R, coherent site, profinite G, sole [Injective J.module],
every n : Nat, whole-slice internal Hom and homogeneous action on every T-to-S are
unchanged. Rechecked the inverse and multiplication order, n=0, trivial G, zero R/J,
empty tests and infinite G. The only postponed theorem remains
homogeneous_functions_injective with its original eight-step proof docstring.
The difference against the current read-only main node is confined to lean and
added definition/interface stmt_deps; no base field or dependency is removed.

Dry-run correction: the new definition node originally grouped two dependency ids
in one bracket. Preflight requires individual [id] citations; both citations are
now separate. No mathematical content or Lean source changed for that repair.
