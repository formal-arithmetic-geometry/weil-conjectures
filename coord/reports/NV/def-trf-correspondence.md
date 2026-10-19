## Worker report

The module `Sheaf.Paper.TraceCohomologicalCorrespondence` defines
`WeilConjectures.TrfCohomologicalCorrespondence`, its map `toProduct`, and its
`IsAdmissible` predicate. The source is the current blueprint
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/def-trf-correspondence.md`,
order 2430. I opened that source and the node including `blueprint_update`;
the mathematical statement is unchanged. There is no repair note for this item.
No new nodes or dependency repairs are needed. No theorem is introduced, and
no definition contains `sorry`.

Clause-by-clause correspondence:

- The global finite-field datum is `F : FiniteFieldDatum.{u}`. Its fields
  record the prime `p`, positive exponent, `q = p^a`, the finite field and
  its fixed algebraic closure, with their structures. The base is literally
  `Spec (.of F.k)` throughout.
- The coefficient prime is `(l : ℕ) [Fact l.Prime]`, with the explicit
  `hl : l ≠ F.p` parameter on the correspondence. The coefficient extension
  is `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. The coefficient is the dependency's
  `Padic.coefficientExtensionRing l E (n + 1)`, not an arbitrary finite ring.
  As in `TraceExceptionalAdmissibility`, the natural index `n` denotes
  the positive exponent `n+1`; `n=0` is exactly level 1. Every positive
  level occurs. The finite extension's inclusion in the fixed coefficient
  algebraic closure plays no role in any operation at a single finite
  stage; this interface is the same general finite-extension interface
  as the recorded admissibility dependency. In the coefficient conventions
  it specializes to `T.datum`, `T.coefficients.l`,
  `T.coefficients.different`, `T.coefficientField`, and `T.level - 1`,
  where `T.level_pos` gives `(T.level - 1) + 1 = T.level`.
- The scheme `X` is `X : Over (Spec (.of F.k))`, with
  `[IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]`.
  Finite type is locally finite type plus quasi-compact, as recorded by
  the scheme-property convention. No properness, smoothness or descent
  of `X` to `k₀` is imposed.
- The input `K ∈ D^b_ctf(X,A)` is the binder
  `K : (trfFiniteTorFixed l E n X.left).FullSubcategory`. This is the
  dependency's inverse image of `finiteTorConstructible` under the
  canonical derived coefficient realization. It includes exactly bounded
  constructibility and finite Tor amplitude, with all ambient morphisms.
  In particular it is not an unbounded replacement for `D^b_ctf`.
- The support is the field `C : Over (Spec (.of F.k))`, with instance fields
  `separated`, `finiteType`, and `quasiCompact` asserting the corresponding
  three properties of `C.hom`. Thus it is a separated finite-type scheme
  over the same base.
- The geometric morphism is given by `c₁ c₂ : C ⟶ X`. In the over-category
  these are precisely two scheme morphisms commuting with structure maps.
  The actual map to `X ×_s X` is `toProduct`, defined by
  `pullback.lift c.c₁.left c.c₂.left (c.c₁.w.trans c.c₂.w.symm)`.
  Its first projection is leg 1 and its second projection is leg 2.
  The standard fibre-product universal property identifies this data
  with the displayed source map, without storing redundant compatibility data.
- The field `u` has source
  `((ProEtale.upperStar (ModuleCat (ULift A)) c₂.left).leftDerivedFunctor).obj K.obj`
  and target `(trfCorrespondenceExceptional F l E n C X c₁).obj K.obj`.
  The former is the ordinary derived inverse image, in the fixed-scalar
  presentation of the recorded finite derived pullback. The latter is
  literally `trfExceptional l E n c₁.left` with the dependency's
  compactification instance. The category of `u` is
  `DerivedCategory (Sheaf (ProEt.topology C.left) (ModuleCat.{u+1} (ULift A)))`,
  the canonical coefficient realization of `D(C_proet,A)` used by the
  admissibility dependency. There is no `[IsIso u]`, properness of leg 2,
  or exceptional-admissibility hypothesis on a plain correspondence.
- The final sentence is `TrfCohomologicalCorrespondence.IsAdmissible`.
  Its first conjunct is the recorded `IsExceptionallyAdmissibleAt` for
  `c₁`. Its second conjunct quantifies over Cartesian squares
  `IsPullback g'.left f'.left c.c₁.left g.left`, and requires the same
  fixed-stage predicate for `f'`. The base changes are within the source's
  separated finite-type `k`-scheme setting. Arbitrary presentations of
  these Cartesian squares are accepted, including identity squares;
  it is not restricted to a chosen pullback object. There is no
  all-coefficient-stage uniform-bounds requirement here, and no new
  ambient exceptional-adjoint datum. The phrase “occurring below” means
  the base changes in this finite-type correspondence setting, which
  the predicate permits without choosing any future diagram in advance.

The three helper declarations belong to this very notion and are listed
in `lean.declarations`. `trfCorrespondenceCompactifiable` applies the
existing compactifiability theorem. It first rewrites the source structure
map along `f.w`, then applies the existing `IsSeparated.of_comp`,
`locallyOfFiniteType_of_comp`, and `QuasiCompact.of_comp` to obtain the
leg's properties. `trfCorrespondenceExceptional` uses this instance with
`trfExceptional`. `trfCorrespondenceLegAdmissible` exposes the very same
geometric instance calculation for `IsExceptionallyAdmissibleAt`.
None is an independent new mathematical notion or a postponed theorem.

Dependency declarations read and used:

- `Sheaf.Paper.TraceExceptionalAdmissibility`:
  `WeilConjectures.trfFiniteTorFixed`, `WeilConjectures.trfExceptional`,
  `WeilConjectures.IsExceptionallyAdmissibleAt`; I read their definitions
  and the `TrfExceptionalStage` fields. The specified exceptional functor
  and finite-Tor presentation are reused, not reconstructed.
- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `WeilConjectures.TraceFormulaCoefficientConventions` and its coefficient
  field/ring and `derivedPullback` definitions were read. The module is
  imported for the recorded finite-coefficient conventions. The definition
  is parametrized on their finite-field, finite-extension and positive-stage
  ingredients, allowing arbitrary separated finite-type `X` as this node says.
- `Sheaf.Paper.DerivedPullbackTensorHom` (through the preceding import):
  `WeilConjectures.finiteDerivedPullback`, whose body is the canonical
  intrinsic finite pullback; its fixed-scalar input operation is
  `AlgebraicGeometry.ProEtale.upperStar` and its left derived functor,
  exactly as in `TrfOrdinaryStage.pullback`. Thus using fixed coefficients
  does not introduce a competing notion of derived pullback.
- `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt` (through admissibility):
  `AlgebraicGeometry.ProEtale.sfFiniteExceptionalAt`, read in full. Its
  formula is the ordinary etale right adjoint between the two comparison
  functors, and is the specified functor used by `trfExceptional`.
- `Sheaf.Paper.FiniteFieldFiber` (through admissibility):
  `WeilConjectures.FiniteFieldDatum`; I read its fields and the coefficient
  datum and positive finite coefficient conventions.
- `def-weil-scheme-morphism-properties` has an explicit convention-only
  record and no declaration. The actual classes used here are Mathlib's
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`. The auxiliary
  compactification is supplied by
  `Sheaf.AlgebraicGeometry.CompactifiableOverField`,
  `AlgebraicGeometry.hasCompactification_of_finiteType_over_field`.

Edge cases checked before the definition and against the resulting fields:
`K=0` is allowed; its coefficient map is not required to be invertible.
The empty support is allowed, and if `X` is empty any support admitting
both legs is empty. With `C=X=Spec k` and both legs the identity, the
coefficient map is an arbitrary endomorphism after the canonical ordinary
and exceptional identity identifications. Identity and nonidentity base
changes are both quantified. The lowest positive coefficient level is
`n=0`. All scheme and site universes follow the existing fixed-scalar
realization: the small site has object universe `u+1` and morphism universe
`u`; values are `ModuleCat.{u+1} (ULift.{u+1,u} A)`. No equality of site
object and morphism universes is added.

Searches for an existing definition:

- `msearch.py NV def-trf-correspondence leanfinder
  "cohomological correspondence derived pullback exceptional inverse image"`:
  8 hits, generic sheaf pullback and exact functor declarations;
  no cohomological correspondence.
- `msearch.py ... loogle "CohomologicalCorrespondence, ExceptionalInverseImage"`:
  0 hits, unknown identifier `CohomologicalCorrespondence`.
- `msearch.py ... grep "CohomologicalCorrespondence|cohomological.?correspondence"`:
  0 Mathlib hits. The exact JSON search results remain in sandbox `searches.jsonl`.
- `rg` of the project and upstream for `Correspondence`,
  `cohomological.?correspondence` and the item id found the upstream
  `AlgebraicGeometry.ProEtale.Correspondence` in
  `WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence`.
  I read its full signature and docstring and surrounding variables.
  It uses the strong `Etale.HasBoundedBelowUpperShrieks` ambient package
  and `rightDerivedUpperShriek`, rather than this node's specified
  finite constructible functor. Its support is not constrained to the
  separated finite-type setting and its coefficient inputs are arbitrary
  ambient objects. It therefore is not an exact existing attachment for
  this node. The current admissibility dependency explicitly excludes
  precisely that strong ambient assumption. The other project hits
  concern lisse representation correspondences and oriented points.
- `rg` of Mathlib, the source, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for all proposed full declaration basenames
  found no pre-existing declaration with one of these names.

Validation: the sole delivered Lean file passed `scompile.py NV
 def-trf-correspondence <module>` both as sandbox and as module, with no
errors and no warnings (8.4 s and 9.9 s in the successful run).
The first compile's ordinary class-instance elaboration and style diagnostics
were repaired using explicit structure-map instance terms and `let` in the
Prop-valued compactifiability abbreviation. There are no statement faults,
`STATEMENT-DISPUTED` flags, changed natural statements, or new DAG dependencies.

## Second reading by NV

Replaced by the maintainer's independent reading (cc review service, 2026-10-18). The
delivered section was the placeholder "No second reading by a worker", which is delivery error
H11. Nothing in the Lean module or in the node record changes.

Statement of the node (current blueprint main-20261015 order 2430, identical to main-20261017,
and to master order 2086 except order and note), with the Lean that renders each item:

1. The global finite-field datum: `F : FiniteFieldDatum.{u}`, the recorded declaration of
   def-weil-finite-field-fiber. Base `s = Spec k` is `Spec (.of F.k)`. Matches.
2. Coefficient conventions, `A = A_{E,n}`, l a prime with l different from p:
   `(l : ℕ) [Fact l.Prime]`, `hl : l ≠ F.p`, and `E` finite over `Padic l`, with
   `Padic.coefficientExtensionRing l E (n + 1)`. Level `n+1` covers every `n ≥ 1`, and
   `n = 0` gives `A_{E,1}`. This is the same interface as the recorded
   `TraceExceptionalAdmissibility`. Matches.
3. X separated of finite type over k: `X : Over (Spec (.of F.k))` with `IsSeparated`,
   `LocallyOfFiniteType`, `QuasiCompact` on `X.hom`. Nothing stronger is assumed. Matches.
4. C a separated finite-type scheme, with `c = (c₁,c₂) : C → X ×_s X`: the fields `C`,
   `separated`, `finiteType`, `quasiCompact`, `c₁ c₂ : C ⟶ X` in `Over`, and
   `toProduct = pullback.lift c₁.left c₂.left _ : C → pullback X.hom X.hom`, with `c₁` first.
   A map to `X ×_s X` gives C a k-structure for which both legs are k-maps, and conversely,
   so this is equivalent data. Matches.
5. For `K ∈ D^b_ctf(X,A)`: the binder `K : (trfFiniteTorFixed l E n X.left).FullSubcategory`.
   This is the recorded finite-Tor constructible predicate of the admissibility module,
   pulled back along the canonical `sfIntrinsicDerivedEquivalence`. It is not the unbounded
   category. Matches.
6. `u : Lc₂^*K → Rc₁^!K` in `D(C,A)`: the field `u`. Its source is the project's
   `leftDerivedFunctor` of `ProEtale.upperStar (ModuleCat (ULift A)) c₂.left`. This is the
   same expression as `TrfOrdinaryStage.pullback`, and it is canonically the
   fixed-scalar form of the recorded `finiteDerivedPullback` (= `sfIntrinsicDerivedPullback`,
   which is `mapDerivedCategory` of the transported `upperStar`; compare
   `leftDerivedFunctorIsoMapDerivedCategory`). Its target is `trfExceptional l E n c₁.left`,
   which is literally `sfFiniteExceptionalAt` (def-weil-exceptional-inverse-image) at the
   canonical compactification. `HasCompactification` is a `Prop` class, and the instance comes
   from the same `hasCompactification_of_finiteType_over_field` term as in
   `IsExceptionallyAdmissibleAt`. Leg roles: c₂ ordinary, c₁ exceptional. Matches.
7. Admissible if c₁ and every base change of c₁ occurring below are exceptionally
   admissible at A: `IsAdmissible`. Its first conjunct is the recorded
   `IsExceptionallyAdmissibleAt` for c₁. Its second conjunct ranges over every Cartesian square
   `IsPullback g'.left f'.left c₁.left g.left` of separated finite-type k-schemes and asks the
   same for `f'`. The square direction is `g' ≫ c₁ = f' ≫ g`, so `f'` is the base change of c₁
   along g. The predicate is at the fixed stage A, as the node says "at A". It assumes no
   uniform bounds, no FullCD and no invertibility of u. Matches.

Edge cases: K = 0; C empty; X empty (then C is empty); C = X = Spec k with identity legs (u is
then an arbitrary endomorphism after the canonical identifications); n = 0 (stage 1); identity
base changes are included in the quantifier. Universes are the dependency's: `Scheme.{u}`, a
site of object universe u+1, `ModuleCat.{u+1} (ULift A)`. No universe equality is added.

Searches. The upstream `AlgebraicGeometry.ProEtale.Correspondence`
(WeilConjectures/SixFunctors/ProEtale/TraceFormula/Correspondence.lean:139) has the same leg
convention. It needs the ambient `Etale.HasBoundedBelowUpperShrieks` and uses
`rightDerivedUpperShriek`, an ambient right adjoint that def-trf-admissibility explicitly
excludes for finite coefficients. Its support has no separated finite-type constraint, and its
K is not restricted to D^b_ctf. So it is not an exact attachment. The other `Correspondence`
hits in lean/Sheaf (operadic, lisse, oriented) are unrelated, and the DAG nodes
def-trf-graph-correspondence and def-trf-fixed-scheme cite this item. No duplicate was found.

Compile: `nt_compile.py --json` on the delivered module, 10.0 s, rc 0, no diagnostics.
No `sorry`, no line over 100 characters, all variables bound. `lean.statement` is verbatim
lines 90-93 of the file. The node differs from the base only in `lean`.
Changes made by this reading: this section only.
