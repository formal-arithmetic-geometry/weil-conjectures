## Worker report

Existing declaration: `AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_of_isProper`,
in `WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekBaseChange`, lines 105–145.
The complete docstring, signature, and proof were read from the side-project source, and
`scompile.py --source` confirmed the same published source. The older slopmaster2 source
checkout lacks this module; this is an existing published side-framework declaration,
so its availability is from the side overlay. Preflight requires the provenance label
`slopmaster2` for every `WeilConjectures.*` existing module; the record uses that
label while documenting the actual source location. No module, theorem, definition, or proof
is written in this delivery. The item's `lean` field and the source-based coefficient
clarification recorded under `statement_change` are delivered.

The match, hypothesis by hypothesis and clause by clause:

- The coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ]` from the enclosing section,
  and `[Finite Λ]` on the theorem. The ambient finite-discrete coefficient convention
  is implemented by sheaves valued in `ModuleCat.{u + 1} Λ`; it needs no choice of
  topology on Λ or finiteness condition on the module sheaves.
- The four corners are `{X' X Y' Y : Scheme.{u}}`, with arrows
  `{g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}`.
  `(sq : IsPullback g' f' f g)` supplies exactly the cartesian square and its
  commutativity. The base-change arrow g is arbitrary.
- Properness is `[IsProper f]`, the standard Mathlib convention. Its definition was
  read in `Mathlib.AlgebraicGeometry.Morphisms.Proper`, lines 39–43; universally
  closed includes quasi-compactness, so locally finite type gives finite type.
- The object is
  `K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))`.
  This is the small pro-etale site and ordinary constant-coefficient module-sheaf
  category. `Sheaf J (ModuleCat Λ)` is the usual fixed-ring presentation of modules
  over the constant ring sheaf; no constructibility, completion, local-system,
  finite-generation or finite-Tor-amplitude restriction is imposed.
- The input witness is used through
  `hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K`.
  Its definition in `WeilConjectures.SixFunctors.ProEtale.Derived.Comparison`,
  lines 79–86, is `DerivedCategory.TStructure.t.plus.map D(ν^*(X)[A])`.
  `ObjectProperty.map` in `Mathlib.CategoryTheory.ObjectProperty.Basic`, lines
  158–164, unfolds this to `∃ L, t.plus L ∧ Nonempty (D(ν^*).obj L ≅ K)`.
  Thus each actual pair `(L, α)` in the node gives exactly the needed hK; the theorem
  proof opens that witness as `⟨K', hK', ⟨eK⟩⟩`. Bounded-below K follows from exactness
  of comparison, as `DerivedCategory.plusEtaleOrigin.plus` states. Encoding D+ by
  this property inside D does not exclude any bounded-below object.
- The conclusion is
  `IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K)`.
  The map's full definition and docstring were read in
  `WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar`, lines 349–383:
  `leftDerivedUpperStarSquareIso` is inverse composition, commutativity transport,
  then forward composition; `derivedBaseChangeMap` is its `mateEquiv` under the
  two derived pullback/direct-image adjunctions. Its source is `Rf_* ⋙ Lg^*`
  and target `Lg'^* ⋙ Rf'_*`, precisely the displayed exchange with Lean's
  left-to-right functor composition. Exact inverse image for constant coefficients
  identifies Lg* and Lg'* with the node's inverse images. This is the constant-ring
  specialization of the ambient ringed exchange, not an arbitrary morphism.
- Witness independence is part of the same conclusion: the arrow just displayed
  depends only on Λ, the square, and K. It does not take L, α, or hK. For any two
  witnesses, even without assuming they are isomorphic, the resulting asserted
  arrow is literally this same arrow. No witness-dependent construction is chosen
  in the conclusion. This supplies the node's isomorphic-witness clause without
  adding a tautological equality conjunct or a duplicate theorem.

Dependency records were opened. `def-weil-pbc-etale-origin-witness` has neither a
`lean` record nor a `mathlib_match`; the scheme-conventions node is explicitly a
convention-only collection. At the earlier reading the ambient-exchange record was
also missing. At this repair it records
`AlgebraicGeometry.Scheme.proEtaleAmbientRingedExchange` in
`Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange`; I opened its complete
signature and docstring and its canonical pullback comparison construction.
It is the ringed unit/square/counit mate, whose constant-coefficient specialization
is the existing theorem's exchange. No private copies or dependency modules are
needed for an exact existing theorem attachment (brief §1 and §5).

The existing proof follows the DAG's single paragraph: finite Λ is additively torsion;
`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring` in
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` gives etale PBC;
`comparison_derivedBaseChangeMap`, `baseChangeSourceComparisonIso`, and
`baseChangeTargetComparisonIso` in
`WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` transport and identify
that very exchange. It then conjugates using the witness isomorphism. No proof is
modified. This attachment is not a claim that the dependency closure is sorry-free.

Source: the DAG statement and proof were read in full. The locally referenced
blueprint Markdown is not installed in this read-only checkout. The external source
[Stacks 09C8](https://stacks.math.columbia.edu/tag/09C8), Section 61.30, was opened:
the last finite-level reduction in its proof transports bounded-below etale objects
by comparison and applies etale PBC. Its completed-coefficient theorem is context,
not an additional completeness hypothesis on this finite-level node.

Edge cases checked in the signature and constructions: the zero coefficient ring
is allowed (`CommRing`, no `Nontrivial`); the zero complex, empty schemes, and
identity/base-change isomorphism squares are included; arbitrary lower bounds in ℤ
are allowed by `t.plus`; no bound above, constructibility, or invertibility of a
prime is imposed. Universes are explicit in the existing source: schemes have
universe u and coefficient modules use the standard common u+1 lift. There is no
independent too-small index universe. Disconnected and non-quasi-compact base-change
schemes are not excluded.

Searches actually run:

- msearch LeanFinder: "proper base change for finite coefficient pro-etale bounded
  below complexes with etale origin" — eight unrelated etale ring-map/base-change
  hits, no exact match.
- msearch Loogle: "IsIso, baseChange" — no hits; unknown identifier IsIso.
- msearch LeanSearch: "proper base change for finite coefficients on the pro etale
  site" — unavailable, Internal Server Error; not counted as a negative result.
- msearch grep: `pro.?[Ee]tale.*base.?[Cc]hange|isIso.*baseChange` in
  Mathlib/AlgebraicGeometry — zero hits.
- rg in the old project's WeilConjectures tree for the node id and the eventual
  theorem name — no hit. Broader pro-etale/plusEtaleOrigin searches found the
  comparison property, but not this theorem there.
- rg in the side-project WeilConjectures tree for
  `finite-level-proetale|etale-origin-witness|ambient-ringed-exchange` — found
  `Derived/LowerShriekBaseChange.lean`, including the exact theorem above.
- rg in `lean/Sheaf` for the witness/ambient names and pro-etale comparison notions
  — no duplicate exact theorem. `dag/lean_names_upstream.json` did not list these
  node ids. The exact published source was subsequently read with `--source`.

Validation: an isolated scompile probe imports the existing module and checks the
full theorem, the plusEtaleOrigin property, and the canonical exchange; it also
prints the theorem's axioms to avoid confusing attachment with proof completion.
The probe passed cleanly and printed `[propext, sorryAx, Classical.choice, Quot.sound]`;
therefore the existing theorem remains dependent on postponed proofs.
The required deliver2 dry run follows this report and checks the existing declaration
again. No disputed statement remains; the second reader's coefficient clarification
and complete correction record below are retained.

## Earlier second reading (a previous round; superseded)

I independently opened the item JSON, all three direct statement-dependency nodes,
the exact side-framework source of `Derived/LowerShriekBaseChange.lean`, and its
`Derived/UpperLowerStar.lean` exchange construction. I also opened
`Derived/Comparison.lean`, `ObjectProperty.map`, and Mathlib's `IsProper` definition.
The existing attachment is retained; no module or dependency module is delivered.
There are no new definition nodes and no copied helper notions to review.

Source reading came before the final Lean verdict. The archived blueprint item and
its unit and chapter are available in the launcher's literature mirror, even though
not installed under this shared clone's literature directory. I read all three.
I read `proetale.tex`, `section-proper-base-change` and
`theorem-proper-base-change` (Tags 09C8/09C9), including the complete last reduction
to bounded-below etale complexes; also `conventions.tex`, `section-algebra`.
The source assumes commutative rings with identity, including the zero ring.
Finite coefficients are the finite-level specialization of the source's torsion
quotients. No completeness, perfectness over a different ring, constructibility,
Noetherian scheme, or prime-invertibility condition is needed in this extracted
finite-level assertion. Finite commutative rings are already Noetherian and torsion;
the theorem is not claiming the completed-coefficient assertion for arbitrary K.

The independent object/hypothesis/conclusion list and signature match are:

1. **Coefficient ring Lambda, finite and discrete.** The inherited binder is
   `(Λ : Type (u + 1)) [CommRing Λ]`, and the theorem adds `[Finite Λ]`.
   Verdict: the first worker missed that the node's `Lambda finite` was ambiguous
   after the witness's module dependency was explicitly extended to noncommutative
   finite rings. I corrected only the node's opening coefficient phrase to
   `a finite discrete commutative ring with identity`, following the source's
   standing ring convention, with a full §1(C) record. Thus `[CommRing Λ]` is now
   accounted for explicitly, rather than an unrecorded narrowing. Discreteness is
   represented by ordinary ModuleCat-valued sheaves with the fixed abstract ring;
   no additional topological ring input or condensed coefficient object is used.
2. **Four schemes and their four arrows, with an arbitrary base-change map.**
   The inherited variables are `{X' X Y' Y : Scheme.{u}}`,
   `{g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}`.
   `(sq : IsPullback g' f' f g)` is precisely the cartesian square used in the
   ambient-exchange dependency and the source. Its `toCommSq` supplies the
   commutativity used in the canonical mate. Verdict: exact; g has no extra
   quasi-compactness, finite-type, smoothness, or surjectivity assumption.
3. **Proper f.** `[IsProper f]` is the Mathlib class extending separated,
   universally closed, and locally finite type. Universally closed includes
   quasi-compactness, giving exactly the finite-type proper convention of the
   dependency. Verdict: exact; no restriction to schemes over a field is present.
4. **K in the bounded-below pro-etale derived category with constant Lambda
   coefficients.** K has type
   `DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))`.
   The site is the small pro-etale site. The coefficient sheaf of the module
   dependency is sheafified locally constant Lambda-valued functions, equivalently
   the constant ring sheaf: continuous functions on the quotient pi_0(U) correspond
   to locally constant functions on U, which locally are constant sections.
   ModuleCat-valued sheaves give its usual fixed-ring module presentation.
   `hK.plus` supplies boundedness below, with an arbitrary integer lower bound.
   Verdict: exact representation of D+ inside the unbounded D, with no bound above
   or finite-generation requirement on sheaves.
5. **Etale-origin pair (L, alpha).**
   `hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K` unfolds by
   `ObjectProperty.map` to an etale derived object L, `t.plus L`, and
   `Nonempty (D(ν^*).obj L ≅ K)`. Every specified pair from the dependency supplies
   this hypothesis with that very L and alpha. Conversely, it asserts precisely
   existence of such a pair. The node is an isomorphism proposition for the
   canonical, witness-independent map, so erasing the input data into this Prop
   is equivalent to universally asserting it for each specified pair. The theorem
   does not manufacture a witness-dependent transported map by arbitrary choice.
   Verdict: adequate for this theorem; it is not an attachment of the separate
   data-retaining witness-definition node to an existence predicate.
6. **The displayed exchange is an isomorphism.** The conclusion is
   `IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
   sq.toCommSq).app K)`.
   `derivedBaseChangeMap` is `mateEquiv` of the pullback composition square under
   the two specified derived adjunctions. Its functor source is
   `R(f_*) ⋙ L(g^*)`, and its target `L(g'^*) ⋙ R(f'_*)`, hence it runs in exactly
   the displayed direction. `leftDerivedUpperStarIsoMapDerivedCategory` identifies
   the derived pullbacks with degreewise exact inverse image for these constant
   coefficients. The formula is the same unit/square/counit construction read in
   `def-weil-pbc-ambient-ringed-exchange`, specialized to its constant coefficients.
   Verdict: the canonical map, not an arbitrary isomorphism between its endpoints.
7. **Independence under isomorphic replacement of the witness.** Neither the
   exchange construction nor its component has a witness argument. All witnesses
   prove invertibility of this one fixed map. In the upstream proof, naturality
   transports the assertion along alpha; it does not choose a new exchange arrow.
   Verdict: the independence clause holds directly by how the asserted arrow is
   specified. An extra tautological equality conjunct is unnecessary.
8. **Quantifiers and universes.** Schemes and arrows precede the coefficient ring,
   square, K and hK in the elaborated theorem. No conclusion depends on any hidden
   witness choice. The theorem's coefficient and module lift is u+1 for schemes
   of universe u, the established size convention of this project. A finite ring
   has a representative at that size; no arbitrary smaller test universe, equality
   of small-site object and morphism universes, or smallness hypothesis is added.
   Verdict: all inherited variables are explicitly bound, confirmed by `#check @`.

Edge cases: zero ring and zero complexes are included (no Nontrivial);
empty schemes and empty-site objects are allowed; arbitrary disconnected and
non-quasi-compact base-change schemes are allowed; identity and isomorphism
squares are included; the lower bound can be any integer; no characteristic or
prime invertibility restriction occurs. There is no index-set or n parameter in
this theorem, so an empty index set and n=0 impose no further hypothesis. In
particular this is not silently restricted to constructible or bounded complexes.

Independent searches used different terminology from the first worker:

- msearch LeanFinder, `proper pushforward commutes with arbitrary inverse image
  on bounded below torsion sheaves via pro etale comparison`: eight hits about
  underived sheaf/module pushforward composition, no additional exact theorem.
- msearch LeanSearch, `inverse image of proper derived pushforward for finite ring
  coefficients on pro etale sheaves of etale origin`: Internal Server Error,
  recorded unavailable, not negative evidence.
- msearch grep, `IsProper.*IsIso|isIso.*[Pp]roper`: generic category and scheme hits,
  no exact Mathlib statement.
- Direct rg of Mathlib/AlgebraicGeometry, the older WeilConjectures pro-etale tree,
  the side-framework pro-etale tree, and lean/Sheaf/Paper, with
  `isIso.*[Pp]roper|[Pp]roper.*[Bb]ase[Cc]hange|torsion.*[Bb]ase[Cc]hange`:
  the side framework contains exactly the attached finite-level theorem, while
  its condensed bounded-constructible proper-base-change theorems concern other
  categories. The older tree lacks this theorem. No duplicate Sheaf theorem found.
  Broader direct searches for plusEtaleOrigin and derivedBaseChangeMap located
  and led me to read their actual definitions rather than rely on names.

I verified H4/H5/H6 by retaining the published declaration without copying it or
proving anything. Its existing proof is not delivered as a new stage-2 proof.
There are no new declarations requiring docstrings; the upstream docstring states
this blueprint and the transport proof, and the full proof was independently read:
finite Lambda gives additive torsion; etale proper base change applies to L;
source and target comparison isomorphisms and comparison_derivedBaseChangeMap
identify that exchange; naturality conjugates along alpha. The source imports and
its open sorry dependencies remain as published. This is a statement attachment,
not a claim of comparator acceptance or a sorry-free proof.

Mismatch repaired: explicit source commutativity was missing from the node/first
report's matching. No Lean signature was changed. The five-citer audit below
supersedes the worker's final sentence that no statement correction was needed.
No other mismatch was found. `lean.statement` was compared byte-for-byte with the
source substring from `theorem` through the conclusion before `:=` and matches.

Validation: I reran the existing-declaration scratch probe through scompile.py.
Both its sandbox compile and library confirmation passed, with no warnings.
`#check @` showed all section parameters and instances, and `#print axioms` still
reports `sorryAx` alongside the three standard axioms, as already disclosed.
The dry-run preflight and real delivery below separately recheck the attachment.

## Statement corrected

Old statement (verbatim):

```tex
Let $\Lambda$ be finite, let $f$ be proper, and let
$K\in\Dplus(X_{\Proet},\Lambda)$ carry an etale-origin witness
[def-weil-pbc-etale-origin-witness] $(L,\alpha)$. Then the pro-etale exchange
map

$$
 g^{-1}Rf_*K\xrightarrow{\sim}Rf'_*g'^{-1}K
$$

is an isomorphism. It is independent of replacing the witness by an
isomorphic witness.
```

Correction: only the opening `Let $\Lambda$ be finite` becomes
`Let $\Lambda$ be a finite discrete commutative ring with identity`.

The phrase Lambda finite left its ring structure implicit, while def-weil-pbc-proetale-modules explicitly admits noncommutative finite rings. The cited source works with commutative unital rings (Stacks conventions.tex, section-algebra); make this inherited source convention and the finite discrete topology explicit. No claim that noncommutative proper base change is false is made. This repairs an ambiguity against the source rather than adding a proof convenience, and does not change the unit sk-thm-properbasechange statement.

Source: Stacks Project, proetale.tex and conventions.tex, Tag 09C8 / Tag 09C9, theorem-proper-base-change, final finite-level reduction in the proof; conventions.tex, section-algebra (rings are commutative with 1).

I enumerated exactly the nodes whose stmt_deps or proof_deps contain this
item and opened every one, including both the four-arrows and complete-proetale
applications, the two six-functor uses and the fixed target. I also read the
adic coefficient datum, compact-support direct-image definition and six-functor
datum to check their inherited coefficient rings. All five uses survive:

- `def-weil-pbc-four-arrows`: holds: true. Its P_n=A/I^n is commutative because the adic coefficient datum explicitly assumes A commutative; the canonical finite-level exchange and witness use are unchanged.
- `nt-target-proetale-qbar`: holds: true. Its fixed condensed algebraic-closure coefficient ring and finite-extension/commutative integral reduction route are unchanged; this clarification of the finite-level prerequisite changes no target statement or operation.
- `thm-sf-comp-composition`: holds: true. Its compact-support direct image is the finite-level construction of def-compact-support-direct-image-detailed with A_{E,n}=O_E/varpi_E^n, a commutative finite ring; proper base change on etale-origin objects still applies.
- `thm-sf-dual-base-change`: holds: true. The concrete finite-coefficient stage of def-sf-datum is A_{E,n}=O_E/varpi_E^n, a commutative finite ring; the formal right-adjoint argument and other coefficient stages are unchanged.
- `thm-weil-pbc-complete-proetale`: holds: true. Its finite-level application uses P_n=A/I^n from the adic coefficient datum with A commutative, so every required application still holds.

No citer is edited, and the unit statement and every target statement stay verbatim.

## Repair validation

The previous attempt's dry run passed, but subsequent submission attempts encountered
`FileNotFoundError` for the wrapper-created `ExistingChecks.lean`. This worker is
authorized only to prepare the attachment and run `deliver2.py --no-push`; the next
second reader submits it.

I reopened the exact published theorem with `scompile.py --source`, its inherited
binders, the comparison property, both exchange constructions, the archived blueprint
node and unit, and Stacks' complete finite-level reduction and ring conventions.
The signature in `lean.statement` is unchanged and matches the source verbatim.
The current citer enumeration still contains exactly the five audited nodes above.
The coefficient clarification and its audit remain valid.

Repeated searches: LeanFinder, "proper base change for bounded below pro etale
complexes of finite coefficients from the etale site", returned eight unrelated
etale/base-change facts; Loogle, "AlgebraicGeometry.IsProper, CategoryTheory.IsIso",
returned zero hits. Direct rg of the old upstream tree, Mathlib/AlgebraicGeometry,
lean/Sheaf and the side framework found the exact theorem only in the side framework.
No new notion or theorem is introduced.

The repeated `scompile.py` probe passed both its sandbox and library checks cleanly
(40.2 s and 37.6 s). Its full `#check @` output confirms the inherited binders;
the axiom output still includes `sorryAx`, as expected for this statement attachment.

## Second reading by Q14

Independent final reading, 2026-10-16. I read the corrected natural statement
against its source before matching the Lean. The archived blueprint node, its
unit and chapter were read from the launcher's literature mirror, together with
Stacks `proetale.tex`, `section-proper-base-change` and the complete proof of
`theorem-proper-base-change` (09C8/09C9), and `conventions.tex`, `section-algebra`.
The source's final reduction uses bounded-below etale complexes with torsion
coefficients; finite commutative coefficients are a specialization of that
reduction. The completeness and perfectness hypotheses of the surrounding
completed-coefficient theorem are not hypotheses of the extracted finite-level
assertion. Stacks' standing ring convention is commutative with identity and
explicitly includes the zero ring. This validates the existing coefficient
clarification rather than silently restricting the Lean to convenient rings.

I opened the actual published module
`WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekBaseChange`, including its
section parameters, theorem docstring, signature and proof. `scompile.py --source`
also resolved that published module. The independent inventory and match are:

1. **Finite discrete commutative unital ring Lambda.** The enclosing section has
   `(Λ : Type (u + 1)) [CommRing Λ]`; the theorem has `[Finite Λ]`. Ordinary
   `ModuleCat.{u + 1} Λ` supplies discrete fixed-ring coefficients. Verdict: exact
   for the source-corrected statement, including the zero ring.
2. **Four schemes, four arrows, a cartesian square and arbitrary g.** The section
   binds `{X' X Y' Y : Scheme.{u}}`, `{g' : X' ⟶ X}`, `{f' : X' ⟶ Y'}`,
   `{f : X ⟶ Y}`, `{g : Y' ⟶ Y}`. `(sq : IsPullback g' f' f g)` is the cartesian
   condition, and `sq.toCommSq` is its commutativity. Verdict: exact; g has no
   finiteness, smoothness, separatedness or surjectivity condition.
3. **Proper f.** `[IsProper f]` uses the Mathlib class extending `IsSeparated f`,
   `UniversallyClosed f`, `LocallyOfFiniteType f`. I opened its definition in
   `Mathlib.AlgebraicGeometry.Morphisms.Proper`. Universal closedness includes
   quasi-compactness, so this is precisely properness in the conventions node.
   Verdict: exact, without a Noetherian scheme or ground field assumption.
4. **K in D+ of constant-coefficient pro-etale modules.** The K binder is
   `DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))`.
   The site is small pro-etale. `hK.plus` gives its boundedness below. I opened
   the now-recorded `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules` dependency:
   `finiteCoefficientRingSheaf` sheafifies continuous functions on connected
   components, and `finiteCoefficientRealization` is associated-module
   sheafification along constant scalars. Such functions into a discrete ring
   are locally constant, so this is the constant ring sheaf and its fixed-ring
   module presentation. Its etale realization and derived comparison signatures
   were also read. Verdict: the same mathematical coefficient modules and
   comparison, with no constructibility or finite-generation condition on K.
5. **Specified etale-origin pair (L, alpha).** The theorem takes
   `hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K`.
   I read its definition in `Derived.Comparison` and `ObjectProperty.map` in
   Mathlib: it is exactly `∃ L, t.plus L ∧ Nonempty (D(ν^*).obj L ≅ K)`.
   Every specified pair gives this hypothesis, and conversely it asserts
   existence of such a pair. For a proposition about a fixed map that has no
   witness argument, quantifying over those pairs is equivalent to this
   existential-image hypothesis. Verdict: exact for this theorem. The separate
   witness node remains a data-retaining definition; it is not being attached
   to an existence predicate or replaced by a classical choice.
6. **The specified exchange map is an isomorphism.** The conclusion is
   `IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
   sq.toCommSq).app K)`. I read the whole `derivedBaseChangeMap` and
   `leftDerivedUpperStarSquareIso` definitions in `Derived.UpperLowerStar`:
   inverse composition, square commutativity and forward composition give
   theta; `mateEquiv` under the two derived adjunctions gives the exchange.
   Its source is `Rf_* ⋙ Lg^*` and target `Lg'^* ⋙ Rf'_*`, exactly the displayed
   direction. `leftDerivedUpperStarIsoMapDerivedCategory` identifies these
   derived inverse images with exact inverse image. I also read the recorded
   ambient ringed exchange and its normalized canonical comparison, whose
   constant-ring specialization has this unit/comparison/counit construction.
   Verdict: the canonical exchange, not an arbitrary arrow or isomorphism.
7. **Independence under isomorphic witness replacement.** The conclusion's
   natural transformation and component depend only on Lambda, the square and
   K, not L, alpha or hK. Its proof conjugates this very component along alpha,
   using naturality. Verdict: all witnesses assert invertibility of the same
   map, which supplies the independence clause without an extra tautology.
8. **Quantifiers and size.** All section variables are bound, as confirmed by
   `#check @`. The coefficient/module universe is the project's common u+1
   lift for schemes in universe u. No equality between small-site object and
   morphism universes is imposed. Finite coefficient rings admit representatives
   at this size. Verdict: no excluded size case or vacuous test universe.

I read all three immediate dependency node records. The conventions collection
introduces no declaration of its own. The ambient exchange has its recorded
module, which I opened in full. The witness node has no recorded Lean yet, but
this existing theorem uses the already published `plusEtaleOrigin` predicate;
no missing object is needed to attach this exact theorem. No new definition
node, dependency module, private copy, hollow definition or new proof is
introduced by the delivery. The published theorem's proof follows the node:
finite coefficients give additive torsion, etale proper base change applies to
L, the source and target comparison isomorphisms transport it, the equation
`comparison_derivedBaseChangeMap` identifies the canonical exchange, and
naturality along alpha transfers the result to K. I opened that comparison
equation and both comparison-isomorphism signatures. Their qcqs assumptions
follow from properness of f and its base change; none is added to this theorem.

Edge cases: the zero ring and zero complex are allowed; schemes may be empty,
disconnected or non-quasi-compact; identity and isomorphism squares are allowed;
the cohomological lower bound is any integer, with no upper bound. There is no
index-set or n parameter, no positive-degree restriction, and no restriction
on characteristic or prime invertibility. Arbitrary base-change g is retained.

Independent searches used terminology different from the first worker:

- LeanFinder: `proper direct image inverse image exchange torsion module sheaves
  pro etale site essential image` returned eight results, including module
  pushforward sections and condensed essential-image characterizations; none
  states this theorem.
- Loogle: `CategoryTheory.Functor.essImage` returned the standard existence
  predicate, chosen witness/getIso and related facts; no replacement theorem.
- LeanSearch: `finite ring torsion coefficients proper morphism base change
  derived pro etale comparison` was unavailable (Internal Server Error),
  recorded as unavailable rather than evidence of absence.
- Direct rg on Mathlib/AlgebraicGeometry, the old WeilConjectures pro-etale tree,
  the published side framework and lean/Sheaf used `plusEtaleOrigin`,
  `isIso_derivedBaseChangeMap_app_of_isProper`, `proper.*base.change`, and
  `properBaseChange`. The exact theorem is in the published side framework;
  no duplicate is needed. The old checkout's comparison predicate is available
  but that checkout does not contain this theorem.

I independently enumerated the correction's citers and confirmed the list is
exactly the five entries in `statement_change`. I read the four-arrows and
complete-proetale applications in full: both use P_n=A/I^n from the explicitly
commutative adic datum, so their `holds: true` verdicts are correct. The two
six-functor citers use O_E/varpi_E^n, also commutative; the qbar target's fixed
coefficient and finite-extension route are unaffected. No unit or target
statement changes. The old statement in the correction record equals the
current base node verbatim.

Mismatches found in this reading: none requiring a further Lean or node change.
I retained the earlier source-based coefficient clarification and added this
independent audit. The recorded `lean.statement` equals the published source
substring from `theorem` to before `:=` byte-for-byte. The scratch import/check
probe passed through scompile.py with no warnings; `#check @` confirmed the
full inherited binders. `#print axioms` includes `sorryAx` as well as the three
standard axioms, so attachment does not assert completed proof closure.
