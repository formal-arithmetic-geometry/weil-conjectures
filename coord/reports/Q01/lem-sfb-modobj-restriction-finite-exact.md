## Worker report

The module `Sheaf.CategoryTheory.Monoidal.ModuleRestrictionFiniteExact` states
`CategoryTheory.Mod.finite_limits_colimits_exact_comap`. Its only theorem has proof `sorry`;
it introduces no definitions. The node's mathematical statement and dependency lists are
unchanged. No statement dispute, missing notion, or unusable dependency interface was found.

Hypothesis and conclusion correspondence:

- A monoidal category C: `{C : Type u} [Category.{v} C] [MonoidalCategory C]`.
  The object and morphism universes are independently bound as `u` and `v`.
- C has finite limits and finite colimits: `[HasFiniteLimits C] [HasFiniteColimits C]`.
- R and S are arbitrary monoid objects: `{R S : C} [MonObj R] [MonObj S]`.
- A morphism of monoid objects: `(φ : R ⟶ S) [IsMonHom φ]`, meaning preservation of the
  unit and multiplication, without an isomorphism assumption.
- R tensor - and S tensor - preserve finite colimits:
  `[PreservesFiniteColimits (tensorLeft R)]` and
  `[PreservesFiniteColimits (tensorLeft S)]`.
- Mod_R(C) has finite limits and colimits: the first two conclusion conjuncts,
  `HasFiniteLimits (Mod C R)` and `HasFiniteColimits (Mod C R)`.
- Mod_S(C) has finite limits and colimits: the next two conclusion conjuncts,
  `HasFiniteLimits (Mod C S)` and `HasFiniteColimits (Mod C S)`.
- Scalar restriction preserves finite limits and finite colimits, hence is exact:
  `exactFunctor (Mod C S) (Mod C R) (comap (D := C) φ)`.
  Reading Mathlib's definition and `exactFunctor_iff` shows this is definitionally
  `PreservesFiniteLimits (comap (D := C) φ) ∧
   PreservesFiniteColimits (comap (D := C) φ)`.
  Thus the last conjunct includes both preservation clauses and the exactness assertion.
- The final exclusion of extra structures is respected: there is no braiding, closedness,
  additivity, commutativity, or invertibility binder. The self-left-action instance is the
  canonical tensor action, rather than additional chosen action data.

Dependency declarations read and used:

- `def-galois-finite-limits-colimits`: Mathlib module
  `Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits`, declarations
  `CategoryTheory.Limits.HasFiniteLimits` and `HasFiniteColimits`. Both are Props
  quantifying over all finite index categories, including the empty one. The subsequent
  size-transfer instances cover finite shapes in larger universes.
- `sk-def-sfb-ring-object`: its recorded module
  `WeilConjectures.CategoryTheory.RingObjects.RingPresheaf` is publicly imported.
  The part of its recorded declaration list needed here is Mathlib's `CategoryTheory.MonObj`
  and `CategoryTheory.IsMonHom` from `Mathlib.CategoryTheory.Monoidal.Mon`.
  Their full signatures, documentation and axioms were read. No sheaf specialization is
  needed for this generic node; the recorded ring-presheaf construction was also inspected.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.Mod`, `ModObj`, `Mod.Hom`, and `Mod.forget`. The ambient action is the
  tensor action `CategoryTheory.selfLeftAction` in
  `Mathlib.CategoryTheory.Monoidal.Action.Basic`.
- `def-sfb-modobj-restriction`: its Mathlib match `CategoryTheory.Mod.comap` in
  `Mathlib.CategoryTheory.Monoidal.Mod` is used directly. Its complete definition,
  `scalarRestriction`, and `scalarRestriction_hom` were read: its object is M.X,
  its morphism is g.hom, and its action is the monoid map tensored with the identity,
  followed by the old action. Thus no replacement restriction functor is defined.
- `def-galois-exact-functor`: the Mathlib match
  `CategoryTheory.exactFunctor` in `Mathlib.CategoryTheory.Limits.ExactFunctor`, together
  with `Limits.PreservesFiniteLimits` and `Limits.PreservesFiniteColimits` in
  `Mathlib.CategoryTheory.Limits.Preserves.Finite`. Full definitions and docstrings read.
- Proof dependency `lem-sfb-modobj-forget-creates` has no recorded Lean module yet.
  The supporting existing source module
  `WeilConjectures.CategoryTheory.Monoidal.Mod.Limits` is imported without `public`.
  Its full limit and colimit constructions and `Mod.createsLimit` / `Mod.createsColimit`
  were read. The docstring gives all five proof steps in the item, including transfer from
  a chosen lifted cone/cocone to an arbitrary limiting/colimiting cone/cocone. No new
  declaration is needed from this dependency to type the statement.

The source first sentence was read in blueprint main-20261015,
`sec-six-functors-basics/sk-def-sfb-module-lower-shriek/`
`def-sfb-module-open-lower-shriek.proof.md`: scalar restriction retains the underlying
sheaf and is exact. This node extracts the finite universal-property argument, supported
by the explicitly constructed internal-module limits and colimits above.

Edge cases checked before writing:

- Empty index category: finite limits include a terminal object, and finite colimits an
  initial object. No `Nonempty J` restriction is introduced. The colimit action uses
  exactly the stated preservation of finite colimits by left tensor, including the
  initial object; the limit action requires no tensor-limit preservation.
- Identity monoid map and noninvertible monoid maps are included by `IsMonHom φ`.
  The former gives identity restriction; the latter uses exactly the same action formula.
- Ordinary noncommutative rings in Ab give the usual exact scalar restriction; no
  commutativity of either monoid enters. Cartesian Set gives monoid actions, which also
  satisfy the stated construction. Neither example is imposed as a restriction on C.
- A zero object, when present, is covered; no nonzero assumption on a monoid or module
  occurs. Separate `u` and `v` avoid a smallness/equal-universe restriction.

Searches made with the prescribed `msearch.py Q01 lem-sfb-modobj-restriction-finite-exact`:

- LeanFinder query: "Restriction of scalars along a morphism of internal monoid objects
  preserves finite limits and finite colimits when tensoring with both monoids preserves
  finite colimits". Eight hits: internal `Mod_.scalarRestriction`, `Mod_.comap`, their
  action/linearity declarations, ordinary `ModuleCat.preservesLimit_restrictScalars` and
  `preservesColimit_restrictScalars`, closed tensor preservation, and monoidal linearity.
  None states the generic finite-exactness result here. Deprecated search-result names
  were resolved against the actual Mathlib source, using the current `Mod` namespace.
- Loogle query: `"Mod.comap", "PreservesFiniteLimits"`. Zero hits.
- Mathlib grep query:
  `PreservesFinite.*comap|PreservesLimits.*comap|PreservesColimits.*comap`
  under `CategoryTheory`. Zero hits.
- LeanSearch query: "Restriction of scalars for internal monoid objects preserves finite
  limits and finite colimits". Eight hits: ordinary ring/module restriction and its
  preservation declarations, internal scalarRestriction and its linearity lemma, and
  presheaf restriction. No exact match in an arbitrary monoidal category.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for restriction/comap and preservation
  found `Mod.preservesFiniteLimits_comap` and `preservesFiniteColimits_comap` in
  `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`. Their full signatures
  were read: they additionally require `[Abelian C] [MonoidalPreadditive C]`, so they cannot
  supply this node's general statement. Other hits specialize to Ab or sheaves.
- Search for the item's id in `lean/WeilConjectures` found no existing declaration.
  The upstream declaration index was searched, as were the candidate theorem name and
  nearby declarations. No existing theorem has this signature.

Validation: the prescribed `scompile.py` checked the delivered module both in its sandbox
namespace and at its library module path, cleanly, approximately 2.3 seconds per check,
with no errors or warnings. All variables and universes are explicitly bound. The sole
postponed theorem is the declaration matched by this DAG node, with a complete proof plan.

## Second reading by Q01

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
