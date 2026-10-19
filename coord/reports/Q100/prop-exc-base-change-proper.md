## Worker report

Item: `prop-exc-base-change-proper`; group Q100; 2026-10-17.
Module: `Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange`.
The node's reviewed statement has two independent assertions. They are stated as
`AlgebraicGeometry.Scheme.sfProperExceptionalOpenBaseChange` and
`AlgebraicGeometry.ProEtale.sfProperFiniteExceptionalOpenBaseChange`. Both proofs
are `sorry`; every auxiliary definition has actual data. No statement correction,
new node, or dependency-record change is made.

### Hypotheses and clauses: optional ambient assertion

- The finite coefficient is `Padic.coefficientExtensionRing l E (n + 1)`, with
  `[Fact l.Prime]`, `[Field E]`, `[Algebra (Padic l) E]`, and
  `[FiniteDimensional (Padic l) E]`. Indexing by `n + 1` ranges over every positive
  coefficient exponent, as in the recorded ambient datum. The published positive
  coefficient finiteness instance is used; no finite-ring instance is invented.
- The scheme-base data are `S X Y : Scheme.{u}`, `[X.Over S]`, `[Y.Over S]`,
  `_hS : ∀ x : S, IsUnit (l : S.presheaf.stalk x)`, and the two
  `LocallyOfFiniteType` plus `QuasiCompact` instances for the structure morphisms.
  `[f.IsOver S]` makes the named morphism a morphism over that base.
- Properness is `[IsProper f]`. The chosen compactification is `c`; the assumed
  datum is exactly `D : SfAmbientExceptionalRightAdjointDatum A f c`.
- An arbitrary open is `g : Y' ⟶ Y` with `[IsOpenImmersion g]`. There is no
  quasi-compactness or finite-type assumption on this open or its source.
- The square is Mathlib's actual `pullback f g`, with `pullback.fst f g` as g'
  and `pullback.snd f g` as f'. `IsPullback.of_hasPullback` (flipped when the
  helper's coordinate order requires it) fixes the Cartesian identification.
- The ordinary unbounded categories are the recorded `proEtaleDerivedCategory`.
  `sfProperSupportNormalization` identifies the ambient compact-support functor
  at `Compactification.ofIsProper f` with the actual derived direct image.
  `sfProperAmbientAdjunction` transports the given adjunction along this
  identity-open normalization; its right functor is precisely
  `D.rightAdjoint (Compactification.ofIsProper f)`.
- `sfProperOpenPullbackRestriction` uses the recorded sectionwise restriction
  isomorphism and the canonical identification of open inverse image with open
  restriction. `sfProperOpenDerivedRestriction` derives this actual map using
  K-injective-preserving right adjoints and exact open pullback.
- `sfProperOpenDerivedComparison` is Γ. It uses the open unit, inverse derived
  restriction, and the open adjunction counit. Thus its open transpose is the
  inverse sectionwise restriction, fixing the same normalization as the node's
  K-injective representative. It is defined without an ambient datum; its
  invertibility on all unbounded objects is a conclusion, not assumed data.
- The first conjunct is `IsIso` of this natural transformation Γ. The next
  clause is `∃ H, ∃ adj : Rf'_* ⊣ H`, so a right adjoint for the restricted
  proper direct image is supplied by the theorem. It does not assume or assert
  a full ambient datum for f'.
- The final `∀ K` ranges over every object of the unbounded derived category
  on Y. `sfProperExceptionalOpenComparison ... D H adj K` is precisely the
  `adj.homEquiv` image of the open `homEquiv` image of Γ, followed by
  `Rf_*` of the g' counit and then the normalized f counit. Its type is
  `g'^* Rf× K ⟶ H (g^* K)`, and the conclusion is `IsIso` of this map.
- The actual pullback functors are `sfIntrinsicDerivedPullback`. Their
  construction uses the exact open inverse-image functors, so these are the
  node's Lg* = g* and Lg'* = g'* without an added exactness hypothesis.

### Hypotheses and clauses: independent finite-field assertion

- `Dk : WeilConjectures.FiniteFieldDatum.{u}` supplies k = algebraic closure of
  the finite field, and `_hl : l ≠ Dk.p` is the invertible-coefficient condition.
  The l-adic field and positive finite coefficient parameters are the same as
  above. The sources and targets are schemes over `Spec (CommRingCat.of Dk.k)`
  with `LocallyOfFiniteType` and `QuasiCompact` structure morphisms.
- The named f is over k and proper. Again g is any open immersion and the
  square is the actual chosen pullback. No optional ambient datum occurs in
  this theorem's binders or conclusion.
- `K : EtaleOriginDerivedCategory Y (ULift A)` is exactly the recorded witnessed
  full category: an underlying bounded-below pro-etale complex with an etale
  bounded-below origin and its comparison isomorphism. There is no restriction
  to degree-zero objects, bounded objects, or constructible cohomology.
- That recorded category uses the continuous-function ring realization, while
  `sfFiniteExceptionalOpenComparison` uses fixed scalars. The helper
  `sfProperEtaleOriginFixedForgetful` first uses `etaleOriginForgetful` and
  then the inverse of the derived equivalence of the published
  `finiteCoefficientRealization`. This transports the very same witnessed
  object; it chooses neither a new origin nor an arbitrary map. `ULift` is
  exactly the recorded module-category size convention. The local bottom
  topology and its `DiscreteTopology` instance give the specified discrete
  topology on this finite ring without a universe equation.
- The conclusion is `IsIso (sfFiniteExceptionalOpenComparison A sq c₀ Kfixed)`
  with `c₀ = Compactification.ofIsProper f`. This is the existing canonical
  comparison-site paste of the etale exceptional mate, with type
  `g'^* Rf! Kfixed ⟶ Rf'! g^* Kfixed`, and the restricted compactification is
  the canonical base change of c₀. No freely supplied isomorphism is used.
- The theorem docstring gives all eight proof steps across the two assertions,
  including the finite-dimensional/Noetherian reduction, five-arrow etale
  comparison, its mate normalization, the bounded-below endpoint check, and
  Yoneda in the full origin category. The relative adjunction and its
  independent discharge are proof inputs, not additional hypotheses.

### Recorded declarations used

- `Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint`:
  `Scheme.sfAmbientCompactSupportCandidate`,
  `Scheme.SfAmbientExceptionalRightAdjointDatum` and its adjunction fields.
- Mathlib's proper/open morphism APIs: `AlgebraicGeometry.IsProper` and
  `AlgebraicGeometry.IsOpenImmersion`; Mathlib's `Limits.pullback`, projections
  and `IsPullback.of_hasPullback`. No duplicate geometric predicates are defined.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` and its published
  finite-coefficient interfaces: `proEtaleConstantDerivedDirectImage`,
  `sfIntrinsicDerivedPullback`, `sfIntrinsicPullback`, and the intrinsic
  constant-module adjunction. The recorded full-CD used class has the Mathlib
  match `Functor.essImage`; it is not replaced by a new predicate.
- `Sheaf.AlgebraicGeometry.ProEtaleProperOpenSheafComparison`:
  `sfProperOpenDirectImageCoordinates`, `sfProperOpenFixedRestrictionIso`, and
  the normalization of `sfProperOpenSheafComparison`.
- `Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction` and its import
  closure: `exceptionalOpenAdjunction`, `sfIntrinsicOpenAdjunction`,
  `sfIntrinsicDerivedOpen`, and `sfIntrinsicDerivedOpenId`.
- `Sheaf.Paper.EtaleOriginDerivedCategory`: `ProEtale.EtaleOriginDerivedCategory`
  and `ProEtale.etaleOriginForgetful`; its canonical coefficient realization is
  `ProEtale.finiteCoefficientRealization` from the finite-module framework.
- `Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage`:
  `sfFiniteExceptionalFixed`, `sfFiniteExceptional`,
  `sfFiniteExceptionalOpenComparison`, and `sfPositiveCoefficient_finite`.
- `Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge`:
  `sfConstructibleExceptionalAdjointDischarge`, giving the relative bounded-below
  adjunction independently of an unrestricted ambient datum. The node
  `thm-sf-ambient-adjoint-class` records `ComparisonClassAdjunction` and
  `exists_comparisonClassAdjunction` in `EtaleOriginAdjointClass`; these were
  read as the relative proof interface, not redefined.

Proof-only imports include the K-injective-resolution, Cartesian injective
acyclicity, finite-CD acyclic-complex, finite-type dimension, exact comparison,
etale proper/open interchange, derived comparison, direct-image mate,
pullback coherence, and comparison-sections modules. Other required APIs are
already in the imports' closure. Three legacy proof-only modules
(`EtaleOriginAdjointClass`, `ProEtaleExtensionZeroComparison`, and
`CanonicalCompactSupportSiteComparison`) were tested but not imported together
with the current finite-coefficient closure: the old
`WeilConjectures.SixFunctors.ProEtale.Derived.Comparison` and current
`...ProEtale.FiniteCoefficient.Derived.Comparison` both declare
`AlgebraicGeometry.ProEtale.derivedComparisonAdjunctionPlus`. In accordance with
the duplicate-import repair rule, the statement imports the current interfaces
and the compatible smaller proof modules. This requires no different object,
map, mathematical assumption, or dependency statement.

### Edge cases and statement audit

Checked before finalizing: identity open; empty open and empty source;
non-quasi-compact open in the ambient clause; arbitrary unbounded K in that
clause; every bounded-below origin complex (including shifts of degree-zero
sheaves) in the independent clause; every positive exponent (including 1);
and arbitrary distinguished compactification c. The helpers fix the identity
normalization by actual adjunction transport. No zero-dimensional or nonempty
scheme assumption is imposed. There is no constructibility, two-sided
boundedness, new ambient datum for f', or assumed comparison isomorphism.
All universes and variables are explicitly bound (`autoImplicit false`).
No `STATEMENT-DISPUTED` issue was found. The node already contains the reviewed
stage-1 repair and the module follows that statement and its eight proof steps.

### Searches and reuse decision

Searches used the prescribed `msearch.py Q100 prop-exc-base-change-proper`:

- LeanFinder: “Exceptional right adjoint of proper direct image commutes with
  restriction to an arbitrary open immersion”: eight general scheme-module
  restriction/adjunction results; no exact pro-etale statement.
- Loogle: `CategoryTheory.Adjunction, CategoryTheory.IsIso`: twelve general
  adjunction/equivalence results; no geometric assertion matching this node.
- Mathlib grep: `exceptional.*base.?change|base.?change.*exceptional`: no hits.
- LeanSearch: “Exceptional inverse image of a proper morphism commutes with
  open restriction”: eight generic scheme restriction results; no exact match.
- `rg` in upstream `WeilConjectures/`, Mathlib, and published `lean/Sheaf/`
  checked the node id, exceptional/open-base-change names, the coefficient
  realization, the identity-open normalization, and the helper declaration
  names. The upstream project has no declaration for this exact node. The
  identity-open derived isomorphism already exists and is reused.
- The nearby published `SfOpenExceptionalBaseChange` was read. Its ambient
  theorem additionally asserts a full restricted ambient datum, and its
  independent theorem covers only degree-zero origins or bounded constructible
  objects. Neither is exactly the current node's statement; the latter does
  not cover arbitrary D+ origin complexes. It is a downstream theorem and is
  not imported to define the canonical map here.

No new mathematical notion needed a definition node: the helpers are explicit
normalization, canonical-map, and coefficient-transport declarations belonging
to this item's interface, as allowed by the human isolation update. All nine
public definitions/theorems are listed in `lean.declarations`.

### Validation

The prescribed `scompile.py` successfully compiled this module against the
current side-project overlay and published live library. Final delivery
preflight and per-file compilation are run with `deliver2.py --no-push`.
No proof is claimed at stage 2; the independent second reading remains for
the next worker.

## Statement corrected

The node copy contains the stage-1 statement correction recorded in its
`split_report.statement_change`. The old source-level sentence claimed that
the finite-field coefficient class discharged the unrestricted ambient datum;
the current discharge theorem explicitly does not make that claim. The
corrected statement therefore has two clauses: the optional ambient assertion
on the full unbounded pro-etale category, with an explicitly constructed
restricted right adjoint and canonical mate, and the independent relative
assertion for every bounded-below retained etale-origin object. I read this
corrected text against the current blueprint source and the source tags for
open extension and open restriction (Tags 09AE and 09BN). The sole citer,
`cor-exc-base-change-open-immersion-general`, still holds: it uses the first
conditional clause and the bounded-below relative clause exactly as retained.

## Second reading by Q100

I read `dag/nodes/sec-smooth-purity/prop-exc-base-change-proper.json`, its
corrected source place
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-existence/prop-exc-base-change-proper.md`,
the ten recorded `stmt_deps` modules, the `Functor.essImage` Mathlib match
for the eleventh dependency, and the sole citer. The item-by-item
statement list and verdict are:

1. The coefficient is the positive finite ring
   `A = Padic.coefficientExtensionRing l E (n + 1)`, rendered in both theorem
   clauses, with `[Fact l.Prime]`, a field `E`, its `Padic l` algebra structure,
   and finite dimension. `n + 1` covers every positive level, including level
   one. Verdict: exact.
2. The optional ambient scheme data are `S X Y : Scheme.{u}`, `[X.Over S]`,
   `[Y.Over S]`, stalkwise invertibility of `l`, locally-finite-type and
   quasi-compact structure morphisms, and a named `f : X ⟶ Y` over `S`.
   Properness is `[IsProper f]`; `c : Compactification f` and
   `D : SfAmbientExceptionalRightAdjointDatum A f c` carry the specified
   compactification and full ambient datum. Verdict: exact; properness
   supplies the finite-type/separated structure required by the proper node,
   and no stronger independent hypothesis is added.
3. The open is an arbitrary `g : Y' ⟶ Y` with `[IsOpenImmersion g]`. The
   Cartesian square is the actual Mathlib pullback, with
   `pullback.fst f g : pullback f g ⟶ X` as `g'` and
   `pullback.snd f g : pullback f g ⟶ Y'` as `f'`, identified by
   `(IsPullback.of_hasPullback f g).flip`. Verdict: exact, including empty and
   non-quasi-compact opens.
4. The ordinary unbounded pro-etale derived categories are rendered by
   `proEtaleDerivedCategory`. `sfProperSupportNormalization` transports the
   ambient candidate at `Compactification.ofIsProper f` to the actual proper
   direct image, and `sfProperAmbientAdjunction` transports its adjunction;
   this is the node's normalization of `Rf^×`. Verdict: exact; no arbitrary
   right adjoint or comparison is introduced.
5. The canonical derived proper/open arrow `Γ` is rendered by
   `sfProperOpenDerivedComparison`, and the theorem asserts its `IsIso`. The
   restricted direct image right adjoint is the existential `H` together with
   `adj : proEtaleConstantDerivedDirectImage (pullback.snd f g) A ⊣ H`.
   Verdict: exact; this is the isomorphism implicit in the node's
   `Γ : g_! Rf'_* ≅ Rf_* g'_!` and the separately supplied restricted
   adjunction.
6. For every unbounded `K : proEtaleDerivedCategory Y A`, the comparison is
   rendered by `sfProperExceptionalOpenComparison ... D H adj K`, and its
   `IsIso` is asserted. Its definition is the two adjunction transposes of
   `Γ`, the open counit, and the normalized proper counit, in the node's stated
   order. Verdict: exact; the quantifier is over all unbounded objects.
7. The independent clause uses `Dk : FiniteFieldDatum`, `l ≠ Dk.p`, the same
   positive finite coefficient, finite-type schemes over `Spec Dk.k`, their
   locally-finite-type and quasi-compact structure maps, proper `f` over the
   base, and arbitrary open `g`. Verdict: exact; no ambient datum for `f` or
   `f'` is assumed in this clause.
8. Its input is the retained witness object
   `K : EtaleOriginDerivedCategory Y (ULift A)`, which is precisely the
   bounded-below etale-origin category of the dependency node. The helper
   `sfProperEtaleOriginFixedForgetful` forgets only the witness and applies the
   inverse of the published `finiteCoefficientRealization`; it does not choose
   a new origin or map. The conclusion is
   `IsIso (sfFiniteExceptionalOpenComparison ... Kfixed)`, using the canonical
   compactification `Compactification.ofIsProper f` and the canonical pullback
   compactification. Verdict: exact, including shifts of degree-zero objects
   and all bounded-below origins.

The edge cases were checked explicitly: identity, empty, and non-quasi-compact
opens; empty schemes and zero complexes; arbitrary unbounded `K` in the
ambient clause; bounded-below shifts and degree-zero objects in the relative
clause; `n = 0` represented by the positive level `n + 1 = 1`; arbitrary
characteristic prime distinct from the finite-field characteristic in the
independent clause; and the full declared universe `Scheme.{u}`. None is
excluded by the Lean binders.

The prescribed searches were repeated with `msearch.py` (LeanFinder, Loogle,
LeanSearch, and Mathlib grep), plus `rg` over upstream `WeilConjectures/`,
Mathlib, and published `lean/Sheaf`. They found no existing declaration of
this statement or notion. The nearby `SfOpenExceptionalBaseChange` was read
and rejected as non-equivalent because its ambient clause and its independent
object class differ. All recorded dependency declarations were opened and
matched to the signatures used here; no new definition node or dependency
repair is needed.

I found one contract mismatch in the worker module: the statement file used
file-local topology instances for the finite coefficient. I removed those
instances and made the topology and discrete-topology arguments explicit in
the `@EtaleOriginDerivedCategory`, `finiteCoefficientRealization`, and
`etaleOriginForgetful` applications. This leaves the mathematical statement
unchanged while making the declaration readable outside the file. No other
hypothesis, object, conclusion, universe, or import was changed. The module
now has no file-local notation, abbreviation, or instance.

Validation after the repair:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q100 prop-exc-base-change-proper lean/Sheaf/AlgebraicGeometry/ProperExceptionalOpenBaseChange.lean`

completed successfully, including the overlay and library compilation, with
only the permitted `sorry` declarations.

The required dry run returned `OK (dry run): commit 93c7d74468 passes the
preflight and compiles; nothing pushed`. The final report corrects a prose
transposition of the projection codomains; the Lean projections were correct.
The primary `lean.statement` is copied verbatim, including its line breaks,
from the compiled file. No Lean source changed after the successful compile.
