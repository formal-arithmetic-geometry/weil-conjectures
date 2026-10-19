## Worker report

The module `Sheaf.AlgebraicGeometry.FieldExtensionExchange` states
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_fieldExtension`, with `sorry`
as the whole proof. Its docstring contains the node's seven-step proof plan.
The only declaration is the theorem; no definitions or helper theorems are added.

Source: Stacks Project, Tag 0F1C, `lemma-base-change-field-extension`, in
`scratchpad/etale-cohomology.tex`. The section introduction assumes nothing further.
The field-extension, qcqs, bounded-below, stalkwise torsion, and scalar-extension
clauses agree with the node and the source. The conclusion uses the canonical
exchange of the recorded derived-exchange node.

Each hypothesis and clause is rendered as follows:

- The field extension L/K is `(K L : Type u) [Field K] [Field L] [Algebra K L]`.
  Its embedding is `algebraMap K L`, and the corresponding spectrum morphism is
  `Spec.map (CommRingCat.ofHom (algebraMap K L))`. No algebraicity, separability,
  finiteness, perfectness, or characteristic assumption is imposed.
- The K-schemes are `(T S : Over (Spec (.of K)))`; `(g : T ⟶ S)` supplies their
  morphism over K. Its scheme map is `g.left`, and its compatibility with the
  two structure morphisms is part of the Over morphism data.
- The two geometric hypotheses are `[QuasiCompact g.left] [QuasiSeparated g.left]`.
  There is no absolute qcqs assumption on T or S.
- Scalar extension W_L is the actual chosen pullback of `W.hom` along the spectrum
  morphism. The projection to W is `pullback.fst`; g_L is the underlying map of
  `(Over.pullback ...).map g`. The displayed `CommSq` uses those exact maps.
  Its inline equality proof is construction data, using `Over.pullback_map_left`.
- `E : _root_.DerivedCategory.Plus (Sheaf T.left.smallEtaleTopology
  AddCommGrpCat.{u + 1})` means a bounded below derived object of abelian sheaves
  on the small etale site, with underlying unbounded derived object `E.obj`.
- `hE : HasTorsionCohomologyOfInvertibleOrder K T E.obj` is the current recorded
  interface of `def-kun-torsion-invertible`. Expanding its real definition gives
  every integer q, every separably closed geometric point, and every element x
  of the geometric stalk of the q-th cohomology sheaf, followed by a positive
  integer n with `(n : K) ≠ 0` and `n • x = 0`. Nonzero in a field means a unit.
  The integer can depend on the degree, point, and element. This stalk condition
  already implies local torsion, so no separate local-torsion conjunct is needed.
  The local/stalk equivalence is also recorded by
  `Scheme.isTorsionAbelianSheaf_characterizations`. Separably closed points give
  the same etale stalk test as algebraically closed points.
- The derived pullback E_L is the inverse image along the T projection in the
  target of `derivedBaseChangeMapPlus`. Its source is inverse image along the S
  projection of Rg_* E, and its target is Rg_L,* E_L. The conclusion
  `IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} ...).app E)` asserts
  invertibility of precisely this canonical exchange.

Dependency declarations read and used:

- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap`.
- `Sheaf.AlgebraicGeometry.BaseChangeConventions`: the convention uses
  `CategoryTheory.Over.pullback`, `Limits.pullback.fst`, and its induced maps.
  Its module-valued `Scheme.Modules.moduleBaseChange` is not the abelian inverse image.
- Scheme conventions: Mathlib `AlgebraicGeometry.QuasiCompact` and
  `AlgebraicGeometry.QuasiSeparated`, including the quasi-compact diagonal clause.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: D(T_et) is the derived category of
  `Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`, D+ is `DerivedCategory.Plus`,
  and cohomology is `DerivedCategory.homologyFunctor`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategoryPlus`, the exact inverse image on D+.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.lowerStar` and
  `Etale.rightDerivedLowerStarPlus`, giving direct and derived direct image.
- `Sheaf.AlgebraicGeometry.InvertibleTorsionOrders`:
  `Etale.HasTorsionCohomologyOfInvertibleOrder`, `Etale.IsTorsionOfInvertibleOrder`,
  `Etale.invertibleTorsionOrders`. The full current server source was read with
  `scompile.py --source`; it quantifies directly over positive annihilators.
- `WeilConjectures.SixFunctors.BaseChange.Derived`:
  `Etale.derivedBaseChangeMapPlus`, with the exact source and target above.

The proof imports retain the recorded separable-colimit, smooth-base-change,
perfect-closure, separating-basis, homeomorphism-invariance, inverse-image-exactness,
stalk, resolution, termwise-exchange and pasting interfaces. In particular the now
published `Sheaf.AlgebraicGeometry.SmoothBaseChangeLimit` is imported for `lem-kun-0f09`.

Edge cases checked: identity, transcendental and inseparable field extensions are
all allowed. Empty schemes and the zero derived object are allowed. All integer
cohomology degrees are tested, with an arbitrary lower bound and no upper bound.
The annihilator excludes zero, permits one, and need not be uniform. Characteristic
zero permits every positive integer; characteristic p permits precisely orders
prime to p. An arbitrary common universe u includes all these fields and schemes
by enlargement; abelian coefficient groups use the recorded u+1 convention.
Every variable and universe is explicitly bound.

Searches (repeated for this repair, 2026-10-16):

- `msearch.py`, LeanFinder: "Etale derived direct image commutes with base change
  along an arbitrary field extension for bounded below torsion cohomology of
  invertible orders". Eight results concerned etale algebras and Kahler
  differentials; none is the theorem.
- `msearch.py`, Loogle: `"derivedBaseChange"`. Zero results.
- `msearch.py`, Mathlib grep in AlgebraicGeometry:
  `HasTorsionCohomologyOfInvertibleOrder|HasFieldInvertibleTorsionEtaleCohomology|derived.*fieldExtension`.
  Zero results.
- Direct rg of WeilConjectures and lean/Sheaf for the two predicates and the theorem
  name found only the now published Q31 predicate in `InvertibleTorsionOrders`.
  Direct rg of WeilConjectures for `lem-kun-0f1c` found no theorem.
- Current server source requests for `FieldInvertibleTorsion` and
  `FieldExtensionExchange` both reported unavailable. The current recorded dependency
  instead names `InvertibleTorsionOrders`, whose source is available and was read in full.
  The synonymous `lem-kun-0f1c-exchange` has no published Lean record; the delivery
  retains its shared single theorem/module rather than inventing a second declaration.

No statement correction, new node, dependency repair, mathematical dispute, or
statement-dependency change is needed. The node's `lean.statement` is the exact
updated theorem signature. All other node fields are unchanged.

## Repair of return L

The return at immutable head `4c1d099dcd9c` reported an unknown
`AlgebraicGeometry.Scheme.HasFieldInvertibleTorsionEtaleCohomology` in the independently
compiled theorem. The repaired theorem imports the current published
`Sheaf.AlgebraicGeometry.InvertibleTorsionOrders` and uses its recorded
`Etale.HasTorsionCohomologyOfInvertibleOrder K T E.obj`. Its direct stalkwise condition
matches the source without a prime-factor reformulation. The obsolete pending N1
module `FieldInvertibleTorsion.lean` and its stale dependency-node copy have been
removed from this delivery. This avoids re-recording a dependency already landed by
Q31. The theorem name, geometric hypotheses, bounded-below object and canonical
exchange conclusion are retained.

The earlier second-reading section concerned the obsolete two-module delivery;
it has been removed so a fresh second reader can review this repair.

Validation of the repaired final file: the prescribed `scompile.py Q25 lem-kun-0f1c`
compiled `FieldExtensionExchange.lean` both as the independent sandbox module and
at its library module path, with no errors or warnings. The verbatim signature,
100-character line limit, and lean-only node change were checked. The required
`deliver2.py --no-push` dry run follows; no push is authorized for this worker.

## Second reading by Q25

I independently read the current node `lem-kun-0f1c`, the final Lean module, all
seven statement-dependency nodes and their recorded interfaces, and the definition
of the canonical derived exchange. I read Stacks `etale-cohomology.tex`, section
“Applications of smooth base change”, `lemma-base-change-field-extension`
(Tag 0F1C), including the section introduction and the proof. The source is present
in this sandbox's scratchpad; the shared literature checkout has only its citation
records. The section assumes no additional hypotheses. The node's mathematical
statement agrees with the source, so no statement correction or citer audit is
needed. There are no new nodes or dependency modules in this delivery.

The complete object/hypothesis/conclusion list and its Lean rendering is:

1. **Fields and specified extension L/K.** `(K L : Type u) [Field K] [Field L]
   [Algebra K L]`, with `algebraMap K L`. PASS. I read `Algebra` in
   `Mathlib.Algebra.Algebra.Defs`: it supplies the unital ring map required by
   `def-pc-field-extension`; a unital map between fields is injective. No finite,
   algebraic, separable, perfect, or characteristic hypothesis is introduced.
2. **Schemes T and S over K and a K-morphism g:T→S.**
   `(T S : Over (Spec (.of K))) (g : T ⟶ S)`. PASS. The structure maps are
   `T.hom`, `S.hom`, and `g.left` is the scheme morphism; the Over morphism stores
   its compatibility with K. This is the accepted scheme-over-base encoding,
   not an extra assumption on either structure map.
3. **g quasi-compact and quasi-separated.** `[QuasiCompact g.left]
   `[QuasiSeparated g.left]`. PASS. I read the Mathlib classes: preimages of
   compact opens are compact, and the diagonal is quasi-compact. They match
   `def-weil-pbc-scheme-conventions`. Neither T nor S is assumed absolutely qcqs,
   Noetherian, separated, of finite type, or nonempty.
4. **Scalar extensions and their induced morphism.** For W=T,S, the schemes are
   `pullback W.hom (Spec.map (CommRingCat.ofHom (algebraMap K L)))`, with
   projection `pullback.fst`. The map g_L is
   `((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map g).left`.
   PASS. I read `BaseChangeConventions` and its projection statement. These are
   the actual fibre products and the functorial base change of g. The inline
   `CommSq` proof uses `Over.pullback_map_left` to establish their projection
   equality. It is construction data, not an extra hypothesis or a postponed
   theorem. The square is the cartesian scalar-extension square, although the
   canonical exchange API only needs its commutativity.
5. **E in D+(T_et).** `E : _root_.DerivedCategory.Plus
   (Sheaf T.left.smallEtaleTopology AddCommGrpCat.{u + 1})`. PASS. I read the
   recorded `DerivedCategories` module: these are abelian sheaves and the full
   subcategory of cohomologically bounded below derived objects. `E.obj` is the
   same object's image in the unbounded derived category. It is not a complex
   of modules with an extra coefficient action, nor a bounded or degree-zero
   special case.
6. **Every cohomology stalk is torsion of orders invertible in K.**
   `hE : HasTorsionCohomologyOfInvertibleOrder K T E.obj`. PASS. I retrieved and
   read the current published `Sheaf.AlgebraicGeometry.InvertibleTorsionOrders`
   using `scompile.py --source`. Its real definition says, for every integer q,
   every separably closed geometric point s, and every element x of the fibre
   of H^q(E), there exists n with `0 < n`, `(n : K) ≠ 0`, and `n • x = 0`.
   The existential is inside all three universal quantifiers. Nonzero in K is
   equivalent to invertible in K. These points include the algebraically closed
   geometric points and give the same small-etale stalk test; algebraic closures
   of residue fields exist in the scheme's universe. The stalkwise condition
   implies local sheaf torsion, so dropping a separate local-torsion conjunct
   does not weaken the hypothesis. It does not require a uniform annihilator.
7. **E_L is the pullback of E.** In `derivedBaseChangeMapPlus`, the upper
   horizontal map is the T projection, so the target applies its exact derived
   inverse image to E before Rg_L,*. PASS. I read
   `Functor.mapDerivedCategoryPlus` in the recorded ExactFunctor module and
   `Etale.lowerStar` in the recorded UpperLowerStar.Defs module: inverse image
   is induced by the exact sheaf functor, and direct image evaluates on the
   scheme-theoretic base change of an etale object.
8. **The derived direct image after scalar extension is the pullback of Rg_*E.**
   `IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} ...).app E)`.
   PASS. I read the declaration in
   `WeilConjectures.SixFunctors.BaseChange.Derived`. Its source is inverse image
   along the S projection of Rg_*E, and its target is Rg_L,* of the T inverse
   image of E. Thus this asserts that precisely the canonical exchange is an
   isomorphism, rather than existence of an unrelated isomorphism. It supplies
   every clause of the source conclusion with the required quantifier order.

**Edge cases.** Identity, transcendental, and purely inseparable extensions are
covered. Empty T and empty S are allowed whenever the indicated Over objects and
morphism exist; no point or nonempty instance is requested. The zero derived object
is allowed. Every integer cohomological degree, including zero and negative
degrees, is tested; E has an arbitrary lower bound and need not have an upper
bound. The annihilator cannot be zero, may be one, and may vary with each element.
Characteristic zero allows every positive integer; characteristic p allows exactly
positive integers prime to p. No index set occurs in the signature, so there is no
empty-index exclusion. The common arbitrary universe u is the project's scheme
and field size convention, and includes fields and schemes of any fixed sizes by
choosing a common larger universe; abelian groups are in u+1 as required by the
recorded site API. Every variable and universe in the signature is explicitly
bound. No equality of distinct site universes has been imposed.

**Independent searches.** I ran the prescribed `msearch.py Q25 lem-kun-0f1c`
queries with vocabulary different from the worker's:

- LeanFinder: “Base extension of the ground field preserves higher direct images
  of etale torsion complexes under a quasi compact quasi separated map”. Eight
  results, all about etale algebra maps or Kahler differentials. None concerns
  this etale derived exchange theorem.
- Loogle: `"rightDerivedLowerStarPlus", "IsIso"`. No results.
- Mathlib grep, AlgebraicGeometry: `ground.field|field.extension|fieldExtension`.
  Five results concerning elliptic curve points, residue-field degrees, radical
  morphisms and global sections of proper schemes; none is this statement.
- LeanSearch: “Etale derived pushforward commutes with arbitrary field extension
  for bounded below complexes with prime to characteristic torsion cohomology”.
  The service returned Internal Server Error; the wrapper recorded it unavailable.
- Direct rg of the pinned WeilConjectures source, shared lean/Sheaf, and upstream
  name index for `derivedBaseChangeMapPlus_fieldExtension`, base-change/field
  combinations, and `0F1C|0f1c`. No existing declaration matches. The side library
  has other field-extension results for sections, dimensions and specific curves;
  those do not state this theorem. The synonymous node `lem-kun-0f1c-exchange`
  has no Lean record, so it supplies no existing declaration to reuse.

**Findings and changes.** No mathematical mismatch was found. The theorem, its
signature, the node statement and every non-Lean node field remain unchanged.
I added explicit imports for the recorded ExactFunctor and UpperLowerStar.Defs
statement interfaces and the Affine and BaseChange.Square proof interfaces. They
were available transitively before; the explicit imports record the dependency
plan required by stage 2. No definition, helper theorem, or proof was added. The
only theorem still has exactly `sorry` as its whole proof. The module and theorem
docstrings cite Tag 0F1C and `(blueprint: lem-kun-0f1c)`; the theorem docstring
contains each of the node's seven proof steps. There are no private notions,
file-local notation, hollow definitions, or tautological hypotheses. I checked
that `lean.statement` is verbatim the file's signature and that all lines are at
most 100 characters. The prescribed compile of the independently read signature
passed both sandbox and library-path checks without warnings; the final import
changes are compiled again before delivery.
