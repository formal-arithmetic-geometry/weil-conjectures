## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcValuativeDescent` states
`AlgebraicGeometry.AlgebraicSpace.closedDiagonal_and_fullValuativeLifting_of_fpqc_cover`
with `sorry`. It also supplies two real Prop definitions spelling out the two properties
explicitly defined by this very node; they belong to this node, carry its blueprint marker,
and are listed in `lean.declarations`. They introduce no independent auxiliary mathematical
notion and contain no postponed proof or chosen data. The node statement is unchanged.

The prior worker's stale-assignment diagnosis was incorrect. The NH merge recorded at
`coord/ledger.md:37952` delivered the stage-1 split (its `split_report.worker` is `stage1`),
including the two new proof prerequisites. It did not provide a Lean statement for this
item. The current node has no `lean` record before this delivery. This is its stage-2 statement,
not another split or a duplicate of a landed statement.

Clause-by-clause correspondence:

- The scheme X is `{X : Scheme.{u}}`.
- The algebraic space with morphism q:E → X is `(E : AlgebraicSpace X)`. The recorded
  definition is the category of algebraic spaces over X, so q is its structure morphism,
  already encoded by the functor on `Over X`. Every morphism from an algebraic space to
  X has this relative functor of points; no separate chosen presentation is assumed.
- The family is `{I : Type u} (U : I → Scheme.{u}) (f : ∀ i : I, U i ⟶ X)`.
- Its fpqc condition is exactly
  `hcover : Presieve.ofArrows U f ∈ Scheme.fpqcPrecoverage X`, the recorded declaration
  of `def-weil-pbc-fpqc-covering`.
- For each i, the actual base change E_i over U_i has functor of points
  `(Over.map (f i)).op ⋙ E.obj.obj`. On a U_i-scheme `t:T → U_i` this is
  E(T, t ≫ f i). Such a section is precisely a map T → E over X together with the
  already specified map T → U_i, which is precisely a map to E ×_X U_i over U_i.
  On morphisms it is the same pullback of sections. Thus this expression uses the
  universal fibre product, without an arbitrary comparison, a representability assumption
  on E, or a transported choice of atlas. A separate bundled base change is unnecessary.
- Separatedness is `HasClosedDiagonal`. Its definition uses the recorded
  `AlgebraicSpace.IsRepresentableWith` with property
  `fun _ _ p ↦ IsClosedImmersion p.left` on the diagonal `prod.lift (𝟙 F) (𝟙 F)`.
  The product of relative functors on `Over S` is the relative fibre product over S.
  Expanding the recorded predicate quantifies over every S-scheme T and every map from
  its represented functor into this product, and asks for a representing scheme with a
  closed-immersion projection to T. This is exactly the node's scheme-test meaning of a
  closed diagonal. Any other representing scheme is uniquely isomorphic over T and has
  the same property; no choice of a better scheme test weakens the condition.
- Full valuative lifting is `HasFullValuativeLifting`. Its binders quantify over every
  `R : Type u` with `[CommRing R] [IsDomain R] [ValuationRing R]`, every fraction field
  `K : Type u` with `[Field K] [Algebra R K] [IsFractionRing R K]`, and every map
  `b : Spec (CommRingCat.of R) ⟶ S`.
- The generic map a over b is the section
  `a : F.obj (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b)))`.
  Its type imposes exactly the compatibility over S; it is not an arbitrary element or
  a map whose base is unconstrained.
- `∃! e : F.obj (op (Over.mk b)), ... = a` is existence and uniqueness of a lift over b.
  The equality uses the presheaf restriction along the actual fraction-field spectrum
  morphism `Spec.map (CommRingCat.ofHom (algebraMap R K))`, as an `Over S` morphism.
  `Eq.refl _` is the defining commuting-triangle equality, not a new assumption.
- `hlocal : ∀ i, HasClosedDiagonal ... ∧ HasFullValuativeLifting ...` requires both
  properties of every q_i, and the conclusion requires both properties of q.
- There are no quasi-compactness, quasi-separatedness, finite-type, Noetherian, rank-one,
  discreteness, etaleness, or nonemptiness hypotheses on q or the valuation rings.
  All universes and variables are bound explicitly. Tests live in the same u as the
  schemes, exactly as Mathlib's `ValuativeCommSq` and the recorded size convention;
  there is no independent smaller test universe making the assertion vacuous.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`,
  `Spec.map` (the last two also recorded by the existing proof dependency
  `def-weil-affine-spectrum`).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicSpace.IsRepresentableWith`; the full definition and docstrings were read.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fpqcPrecoverage`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`,
  `pullback.snd`, `pullback.lift`; the universal-property interpretation above explains
  why the restricted relative functor is the same fibre product. The theorem does not
  need to choose a representative of that fibre product.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.RingTheory.Valuation.ValuationRing`: `ValuationRing` and its domain/fraction-field
  interpretation, through the dependency's `mathlib_match` (which needs no `lean` record).
- `Mathlib.RingTheory.Localization.FractionRing`: `IsFractionRing`.
- `Mathlib.CategoryTheory.Comma.Over.Basic`: `Over.map`, `Over.mk`, `Over.homMk`.

All already-stated proof dependencies have imports, including
`Sheaf.AlgebraicGeometry.FpqcClosedImmersionDescent` and the Mathlib flatness, tensor-product,
affine/quasi-separated, and faithfully-flat modules. The two new stage-1 proof dependencies
`lem-a1-flat-valuation-lifting` and `lem-a1-algebraic-space-fpqc-sheaf` currently have no
recorded declarations or Mathlib matches; they occur in the theorem's complete seven-step
natural-language proof docstring but are not needed to type its statement. No theorem is
invented for them in this delivery.

Edge cases checked before writing:

- An empty covering index is allowed; the fpqc assumption forces the base to be empty.
  Tests still quantify over all valuation rings; there are no maps from their nonempty
  spectra to that base. Empty algebraic spaces are allowed as well.
- A field is a valuation ring; choosing R=K, including the identity fraction-field map,
  still requires the unique extension along the identity. There is no positive-rank or
  nontrivial-valuation restriction.
- The generic map a need not exist; when its section set is empty the dependent universal
  quantification is exactly the absence of a valuative diagram. For any given a both
  existence and uniqueness are present.
- Arbitrary fraction fields, arbitrary base maps, and arbitrary covering members are
  retained. No preferred fraction field, finite family, or nonempty I is imposed.
- The diagonal is tested on every map from a represented scheme to the product, including
  empty schemes. The algebraic space itself is not assumed to be a scheme.

Searches for a pre-existing statement:

- `msearch.py ... leanfinder` query: "Fpqc descent of separatedness and the full valuative
  existence and uniqueness property for morphisms from algebraic spaces to schemes".
  Eight hits: `IsSeparated.valuativeCriterion`, `IsSeparated.of_valuativeCriterion`,
  `ValuativeCriterion.iff`, `ValuativeCriterion`, `ValuativeCriterion.eq`,
  `ValuativeCriterion.existence`, `IsProper.of_valuativeCriterion`,
  `ValuativeCriterion.Existence`. All are scheme-level criteria, not this descent theorem.
- `msearch.py ... loogle` query: `"AlgebraicSpace", "ValuativeCriterion"`: zero hits.
- `msearch.py ... grep` query: `AlgebraicSpace|valuative.*descent|descent.*valuative`,
  subdirectory `AlgebraicGeometry`: zero hits.
- Direct `rg` of the upstream `WeilConjectures` for the same concept and for this item's
  exact id: zero hits. Direct `rg` of `lean/Sheaf` found the recorded algebraic-space
  framework, products, etale maps, modules and open gluings, but no fpqc valuative descent
  theorem or definitions of these two conditions. Exact searches for `HasClosedDiagonal`
  and `HasFullValuativeLifting` in Mathlib algebraic geometry, upstream and `lean/Sheaf`
  returned zero hits before this sandbox was compiled.
- Read Mathlib's full `ValuativeCommSq`, `ValuativeCriterion` and constituent signatures:
  they require a morphism of schemes, so cannot be used for a general algebraic space.

Sources checked: the local Bhatt–Scholze PDF, Lemma 7.3.9, p.67, says to apply descent
in the forward inclusion. The detailed auxiliary argument is the unchanged node's split.
Read Stacks `spaces-descent.tex`, `lemma-descending-property-separated` (0421) for the
relative diagonal descent and `lemma-fpqc-universal-effective-epimorphisms` (04P2) for the
fpqc morphism equalizer. There is no statement dispute or correction.

Validation: `scompile.py NE lem-a1-space-fpqc-separated-valuative-descent` compiled the
sandbox file and its library-path form cleanly. An initial misspelling of `Eq.refl` was
corrected before the clean compile. The sole postponed theorem is the named item, with
its source and full natural-language proof; definitions have real data.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Reviewer fix (maintainer review of cc52fc2fac02)

H4 (second definition of a notion): the delivered `HasClosedDiagonal F :=
IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) (prod.lift (𝟙 F) (𝟙 F))`
restated the project's landed separatedness predicate
`AlgebraicGeometry.AlgebraicSpace.IsSeparatedPresheafMap`
(`Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`, lem-trf-space-qc-separated-etale-local,
already used by two landed citers): `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
(diagonalPresheafMap g)`. The fix deletes `HasClosedDiagonal` and states both separatedness
clauses as `IsSeparatedPresheafMap (terminal.from F)`. The terminal presheaf on `Over X` is
represented by `Over.mk (𝟙 X)`, so `terminal.from E.obj.obj` is `q : E → X` and the presheaf
pullback over it is `E ×_X E`; for the base change it is `q_i : E_i → U_i` over `U_i`. The
meaning (every scheme test of the diagonal is a closed immersion) is unchanged. The now unused
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` import is removed (it comes with the new
public import). `HasFullValuativeLifting`, the theorem name, its binders, the docstrings and
the node are unchanged. The fixed file compiles clean with `nt_compile.py`.
