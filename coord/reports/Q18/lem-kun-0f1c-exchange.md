## Worker report

Repair of return L for immutable head 4142e4dd7fb3: the consumer named the obsolete
`AlgebraicGeometry.Scheme.HasFieldInvertibleTorsionEtaleCohomology`. The current
`def-kun-torsion-invertible` node records Q31's published
`Sheaf.AlgebraicGeometry.InvertibleTorsionOrders`. Read that complete module in the
shared checkout and confirmed its current server source with `scompile.py --source`.
The consumer now publicly imports that module and uses its
`AlgebraicGeometry.Etale.HasTorsionCohomologyOfInvertibleOrder K T E.obj`.
Removed the obsolete `FieldInvertibleTorsion.lean` sibling and the sandbox dependency
node copy, so this delivery cannot overwrite the current dependency's Lean record or
introduce a second definition. Only the item's Lean record changes. The recorded
signature is updated verbatim. The earlier second reading describes the obsolete
interface and is archived under scratchpad; this repaired delivery awaits its fresh
second reader. Nothing is delivered by this worker.

The module states
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_fieldExtension`, with proof
`sorry`. Its theorem docstring preserves the node's nine-step proof plan. Read the
full node and Stacks Lemma 59.90.1, Tag 0F1C, including its proof and preceding
section, in `scratchpad/etale-cohomology.tex`, lines 18024 onwards. The section has
no standing extra hypotheses. No statement correction or disputed assertion is needed.

Clause-by-clause correspondence:

- The extension L/K is `(K L : Type u) [Field K] [Field L] [Algebra K L]`.
  The structural field map is `algebraMap K L`, and its spectrum map is
  `Spec.map (CommRingCat.ofHom (algebraMap K L))`.
- The K-schemes are `(T S : Over (Spec (.of K)))`; their structure maps are
  `T.hom` and `S.hom`. The morphism `(g : T ⟶ S)` is a K-morphism by its bundled
  compatibility equation.
- Exactly `[QuasiCompact g.left] [QuasiSeparated g.left]` impose the two morphism
  hypotheses. No finiteness or absolute quasi-compactness of T or S is assumed.
- For W=T,S the scalar extension is the chosen
  `pullback W.hom (Spec.map (CommRingCat.ofHom (algebraMap K L)))` and r_W is its
  `pullback.fst`. The induced g_L is
  `((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map g).left`.
  Its first-projection equation is `Over.pullback_map_left`, giving the `CommSq`.
  Pullback cancellation makes this constructed square Cartesian. The recorded
  exchange takes only that square's commutative part; no arbitrary map is assumed.
- Bounded belowness and abelian coefficients are the type
  `E : _root_.DerivedCategory.Plus
  (Sheaf T.left.smallEtaleTopology AddCommGrpCat.{u + 1})`.
- The hypothesis is now `hE : HasTorsionCohomologyOfInvertibleOrder K T E.obj`.
  Unfolding the recorded definition tests every q in Z using
  `DerivedCategory.homologyFunctor`. Its `IsTorsionOfInvertibleOrder` tests each
  element of each geometric stalk through `Scheme.pointSmallEtale` and `sheafFiber`.
  It requires `∃ n : ℕ, 0 < n ∧ (n : K) ≠ 0` with `n • x = 0` (the conjunction
  is packaged as membership in `invertibleTorsionOrders K`). These are precisely
  positive annihilators invertible in K. The integer may depend on q, the point
  and x. Geometric stalk torsion implies local torsion by the recorded torsion
  characterizations. The predicate uses separably closed fields in `Type u`;
  these supply enough geometric points for a `Scheme.{u}`. Algebraic closures
  of residue fields lie in this universe, and passing between separably closed
  and algebraically closed geometric points preserves their etale stalks.
- E_L is the exact derived inverse image along r_T already built into the target
  of `derivedBaseChangeMapPlus`. Its source at E is r_S inverse image of Rg_*E;
  its target is Rg_L,* of that E_L. The derived-category inclusion uses `E.obj`.
- The conclusion is `IsIso` of exactly
  `(derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} canonicalCommSq).app E` in D+(S_L).
  This is the specified canonical exchange morphism, with no existential choice
  of an isomorphism replacing it.

Dependency declarations used (full signatures/docstrings inspected):

- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap` for the field extension.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiCompact`,
  `QuasiSeparated` (the finite-type dependency supplies the quasi-compact clause).
- `Mathlib.AlgebraicGeometry.Over`: `Scheme.Over`, `Scheme.Hom.IsOver`, with
  their bundled `CategoryTheory.Over` version used here.
- `Sheaf.AlgebraicGeometry.BaseChangeConventions`: the recorded convention uses
  `Over.pullback`, `pullback`, `pullback.fst` for scheme base change.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `ChosenCartesianSquare`, its
  chosen pullback convention and its underlying `CommSq`. Our square is constructed
  from pullbacks rather than provided as an extra parameter.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: the recorded ambient
  `DerivedCategory`, `DerivedCategory.Plus`, `DerivedCategory.homologyFunctor`.
- `Sheaf.AlgebraicGeometry.InvertibleTorsionOrders`:
  `Etale.HasTorsionCohomologyOfInvertibleOrder`, `Etale.IsTorsionOfInvertibleOrder`,
  `Etale.invertibleTorsionOrders`. These are the current recorded dependency interface.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryPlus`, giving the exact derived inverse images.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.lowerStar`,
  `Etale.rightDerivedLowerStarPlus`, used by the derived exchange.
- `WeilConjectures.SixFunctors.BaseChange.Derived`:
  `Etale.derivedBaseChangeMapPlus`, the canonical natural transformation.

Proof-only imports remain unchanged. The node's future proof inputs not yet
recorded as usable modules are 0F09, affine and qcqs permanence, compatible perfect
overfields, perfect-field separating bases and horizontal exchange pasting. They
are not needed for elaborating this statement; their route remains in the docstring.

Edge cases: L=K and identity g are included, as are arbitrary infinite,
transcendental and inseparable extensions. Empty schemes and E=0 are admitted.
Every integer cohomology degree is tested, including negative degrees. In
characteristic zero every positive annihilator is allowed; in characteristic p
exactly prime-to-p annihilators are allowed. The zero stalk element has annihilator
1. There is no common annihilator, constructibility or coefficient-ring finiteness
hypothesis. The common arbitrary universe u accommodates the fields and schemes;
coefficient groups have universe u+1 as required by the small etale site API.
Every variable and universe is bound explicitly.

Searches for existing notions/statements (earlier search outputs retained in
`searches.jsonl`, reread during repair):

- LeanFinder via msearch.py, “canonical derived base change for a field extension
  torsion etale abelian sheaves invertible orders”: eight hits on formally etale
  algebras and Kahler differentials; no exact exchange theorem.
- Loogle via msearch.py, `CategoryTheory.IsIso, "baseChange"`: six hits on
  Guitart-exact Kan-extension maps; no etale derived field-extension theorem.
- Mathlib grep via msearch.py, `derivedBaseChangeMapPlus|torsion.*invertible`:
  no hits. An earlier `IsIso, CategoryTheory.Sheaf` Loogle query reported an unknown
  identifier and was supplemented by the qualified query above.
- LeanSearch via msearch.py, “torsion etale abelian sheaf geometric stalk elements
  killed by positive integers invertible in a field”: unavailable, Internal Server
  Error; the other search kinds supplied the search evidence.
- rg in Mathlib, upstream WeilConjectures and shared lean/Sheaf for fieldExtension,
  field_extension, 0F1C, derivedBaseChangeMapPlus and invertible-torsion terms found
  no exact duplicate. Nearby single-sheaf field-extension isomorphisms assume an
  algebraically closed base and a uniform annihilator and assert Nonempty of an
  object isomorphism; neither states this canonical-arrow theorem for arbitrary g.
- Repair rg for `HasTorsionCohomologyOfInvertibleOrder`,
  `HasFieldInvertibleTorsionEtaleCohomology` and the theorem name in both source
  trees found only the current Q31 predicate in shared lean/Sheaf. The current
  DAG's dependency record and `scompile.py --source` agree on its module/signature.
  The old `FieldInvertibleTorsion` server source is unavailable. Reuse the published
  interface; no helper definitions or dependency modules are required.

Validation: `scompile.py Q18 lem-kun-0f1c-exchange` compiled the sole delivered
module both as `Sheaf.Stage2.Sandbox0` and as
`Sheaf.AlgebraicGeometry.FieldExtensionExchange` on 2026-10-16, with no errors or
warnings. The required `deliver2.py --no-push` check is the final validation step.

## Second reading by Q18

Read independently against the complete item node, its eleven statement-dependency
nodes and their recorded Lean interfaces, the delivered module, and Stacks
`etale-cohomology.tex`, section “Applications of smooth base change”, Lemma
`lemma-base-change-field-extension` (Tag 0F1C), lines 18024–18069 in the retained
source. The section introduces no additional standing hypotheses. The statement
is unchanged and agrees with the source. Its canonical-map formulation makes
explicit the comparison used in the source proof.

Object, hypothesis and conclusion checklist (H3):

1. An arbitrary field extension L/K: `(K L : Type u) [Field K] [Field L]
   [Algebra K L]`, with map `algebraMap K L`, is exactly the field-extension
   dependency's `Algebra` interface. Verdict: exact; neither algebraic,
   separable, perfect nor finite is assumed.
2. Schemes T and S over K and a K-morphism g: `(T S : Over (Spec (.of K)))
   (g : T ⟶ S)` bundles the two structure maps and the structural compatibility.
   Read `Scheme.Over`, `Scheme.Hom.IsOver` and the corresponding `Over` API;
   the bundled version is the same category of K-schemes. Verdict: exact.
3. Quasi-compactness of g: `[QuasiCompact g.left]` uses the dependency's actual
   quasi-compact clause, whose definition tests compact open preimages.
   It does not accidentally require `LocallyOfFiniteType`. Verdict: exact.
4. Quasi-separatedness of g: `[QuasiSeparated g.left]` is the recorded Mathlib
   class `QuasiCompact (pullback.diagonal g.left)`. Verdict: exact; neither
   separatedness nor absolute quasi-compactness of T or S is imposed.
5. Scalar extensions W_L and projections r_W for both W=T,S: the displayed
   `pullback W.hom (Spec.map (CommRingCat.ofHom (algebraMap K L)))` and
   `pullback.fst W.hom ...` are exactly the chosen fibre products and projections
   of `BaseChangeConventions`. Verdict: exact.
6. Induced g_L and its Cartesian square: the theorem uses
   `((Over.pullback ...).map g).left`. Read the construction and its projection
   equations; `Over.pullback_map_left` supplies the displayed `CommSq` equation.
   Pullback cancellation makes this square Cartesian; its identification with
   the pullback of g along r_S follows from the two pullback universal properties.
   The exchange dependency needs only this canonical square's commutativity.
   Verdict: exact; no arbitrary square or replacement map is assumed.
7. Bounded below derived object of abelian etale sheaves:
   `E : _root_.DerivedCategory.Plus
   (Sheaf T.left.smallEtaleTopology AddCommGrpCat.{u + 1})` is the exact abelian
   coefficient and bounded-below convention of `DerivedCategories`.
   `E.obj` is its underlying unbounded derived object. Verdict: exact.
8. Cohomology stalks torsion of orders invertible in K:
   `hE : HasTorsionCohomologyOfInvertibleOrder K T E.obj` uses the currently
   recorded `InvertibleTorsionOrders` declaration, not the removed private
   field-torsion interface. Opened all three relevant definitions: for every
   integer q, every separably closed geometric point, and every stalk element,
   it requires `∃ n : ℕ, 0 < n ∧ (n : K) ≠ 0` and `n • x = 0` (membership
   packages the first two conjuncts). In a field nonzero is equivalent to being
   a unit. These geometric points include residue-field algebraic closures and
   suffice to test local torsion, so no extra uniform bound or constructibility
   is hidden or lost. Verdict: exact.
9. E_L is derived inverse image along r_T, and the direct images are Rg_* and
   Rg_L,*: read `Functor.mapDerivedCategoryPlus`, `Etale.lowerStar`,
   `Etale.rightDerivedLowerStarPlus` and `Etale.derivedBaseChangeMapPlus`.
   The latter's source is `Rg_* ⋙ r_S⁻¹` and target is `r_T⁻¹ ⋙ Rg_L,*`.
   Thus its component at E uses precisely E_L and the two named direct images.
   Verdict: exact; no alternative module category or resolution choice.
10. The canonical exchange is an isomorphism in D+(S_L):
    `IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
    canonicalCommSq).app E)` states invertibility of this specified arrow,
    rather than existence of an unrelated object isomorphism. Read the derived
    exchange definition and its resolution formula. Verdict: exact, with the
    node's quantifier order.

Edge cases: the same formula admits L=K, identity g, empty T or S, and E=0.
Infinite, transcendental and inseparable extensions are not excluded;
arbitrary field characteristic is allowed, and a field embedding preserves it. Every cohomological integer, including zero and negative
integers, is tested; no n=0 annihilator is allowed or needed. Zero stalk elements
have the allowed annihilator 1. In characteristic zero every positive integer
is allowed; in characteristic p the condition is prime-to-p torsion. There is
no index set or nonemptiness hypothesis in the theorem. The arbitrary common
universe u can contain the fields and schemes after enlargement; coefficients
are in u+1 as required by the small etale-site API. Same-universe geometric
points give enough points and impose no additional size restriction. All
variables and universes are explicitly bound; there is no hidden instance
besides the displayed field, algebra and qcqs structures.

Independent duplicate searches (H4): ran `msearch.py` LeanFinder with “arbitrary
extension of base field commutes with derived pushforward of etale torsion
abelian sheaves” (8 hits on formally etale algebras and Kahler differentials;
none has the required statement), Loogle with `"derivedBaseChangeMapPlus"`
(0 hits), and grep with `fieldExtension|field_extension|base.change.field`
(0 Mathlib hits). Repeated `rg` across pinned Mathlib, upstream
WeilConjectures and shared `lean/Sheaf` for fieldExtension, field_extension,
scalar extension, ground/base field, derivedBaseChangeMapPlus and the new
full theorem name. Nearby geometric-stalk, module scalar-extension, failure
of base-change, and algebraic-field-extension declarations do not assert this
canonical exchange for arbitrary qcqs g and D+ abelian coefficients. The
previously reported LeanSearch service failure is retained in the worker's
search evidence; the new independent searches use the working prescribed
tools. No duplicate theorem, new definition node, dependency module, private
notion or hollow construction is delivered.

Mismatch found and repaired: the worker's proof-import inventory was stale.
`lem-kun-0f09` and `lem-kun-bc-base-change` now have recorded declarations in
`Sheaf.AlgebraicGeometry.SmoothBaseChangeLimit` and `Sheaf.Paper.KunBaseChange`.
Opened their statements and added both as proof-only imports (steps 3 and 9).
Also added direct public imports of the statement dependencies
`Sheaf.AlgebraicGeometry.DerivedCategories`,
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`. No declaration, theorem signature,
mathematical hypothesis, conclusion, DAG statement or dependency list changed.
The existing module and theorem docstrings name Tag 0F1C and the item blueprint;
the theorem docstring carries all nine proof steps, including coefficient
transport, separable smooth limits, compatible perfect closures, exact
invariance, canonical mates and cancellation by horizontal pasting. The sole
postponed theorem remains `sorry`; the inline simplification only supplies the
canonical square's commutativity. H5/H6/H8/H9 pass. `lean.statement` was checked
byte-for-byte against the theorem signature, and every Lean line is at most
100 characters.

Validation: the prescribed `scompile.py` checks the delivered module separately
in sandbox and library contexts under the default 60-second per-file limit.
The final `deliver2.py --no-push` and delivery both rerun that same wrapper on
the final module, including all five added dependency imports, and enforce the
warning and preflight checks. No global build, live file edit, tool change or
new mathematical assertion is part of this second reading.
