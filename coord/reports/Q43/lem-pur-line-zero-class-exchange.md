## Worker report

The delivery states `AlgebraicGeometry.LineZeroClass.line_zero_class_exchange`
in `Sheaf.Paper.LineZeroClassExchange`. Its sole postponed proof is `sorry`.
All helper definitions have real data. The H2 repair adds two definition-owner DAG nodes with existing:true records; no
Lean declaration or natural-language theorem statement changes. The resolved
stage-1 repair note was read: the current node already has the reviewed
three-step assembly and the two extracted lemmas, which are preserved verbatim.

Source read: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/thm-pur-rank-one-thom.proof.md`, Step 3 and Step 2 first paragraph. The present
node's more explicit statement distinguishes the supported Kummer arrow from
its compact image; this distinction is retained in the file.

Hypothesis and clause matching:

* The fixed algebraic closure of a finite field, the prime different from its
  characteristic, the finite coefficient subextension with its valuation ring
  and uniformizer, and the positive quotient exponent are precisely the fields
  of `P : WeilConjectures.PurityFiniteSetting`. The positive exponent is written
  `n+1` to use the already published `LineKummerField` interface, with
  `_hn : P.level = n+1`. This is an index presentation, not an extra restriction:
  every `P.level ≥ 1` is uniquely `n+1`. In particular `n=0` includes level one.
  `finiteTateCoefficient P.coefficients.l P.extension n` is the usual universe
  lift of the very same quotient at exponent `n+1`. No ramification divisibility
  or flatness of the coefficient quotient is assumed.
* A separated finite-type base is `B`, its structure map `hB`, and instances
  `IsSeparated hB`, `LocallyOfFiniteType hB`, `QuasiCompact hB`.
  `V : PurityVectorBundle P B hB 1` includes the given total space `V.E`, the
  projection `V.p`, the rank-one locally free module, and its chosen relative-Spec
  isomorphism. The section is exactly the existing `V.zeroSection`, not an
  arbitrary closed section. `zeroClosed` is the existing proof
  `V.zeroSection_spec.2.1`; the section equality is `V.zeroSection_spec.1`.
* The effective Cartier divisor and invertibility of the coefficient prime on
  the total space are concluded as `∃ hI : V.zeroSection.ker.IsInvertible` and
  `hX : IsUnit (... : Γ(V.E, ⊤))`. Neither is added as a hypothesis. The auxiliary
  `hA` witnesses that the chosen root exponent kills the prescribed quotient;
  this is the coefficient representative already used by the dependency.
* The stipulated supported Kummer arrow is exactly
  `LineKummerField.proClass`, constructed there from the unique normalized
  `Etale.cartier_kummer_map` family. The degree-zero object is the existing
  `proLine`, built from the prescribed `finiteTateProSheaf ... 1`, and is shifted
  by `(2 : ℤ)`. The compact image `tau_E` is the existing
  `LineKummerField.proTau ... c V.zeroSection V.zeroSection_spec.1 hI hX`.
  Its source is `SectionCompactSource.proSource`, whose composition normalization
  is the dependency's `composition_normalization`; its invertibility is asserted
  by the first conjunct for every `c : Compactification V.p`.
* An arbitrary base change is `g : B' ⟶ B`, with no class or finiteness assumption
  on `g`, `B'`, or `X'`. Every such morphism has its induced k-scheme structure;
  no extra structure is selected in the signature. `v`, `π'`, and
  `sq : IsPullback v π' V.p g` are any presentation of the pullback. Likewise
  `sqZ : ChosenCartesianSquare g z' V.zeroSection v` says exactly that `z'`
  is the pulled-back zero section. Its closed-immersion instance and the section
  equality `hz'` are the intrinsic structures of that presentation, not a
  flatness or regularity requirement. Both follow by pulling back the original
  section. Cartier regularity on this arbitrary base and prime invertibility
  are conclusions `∃ hI', hX'`, so non-Noetherian bases are retained.
* The compact functor after this base change is always the compactification
  formula for `c.ofIsPullback sq`; no finite-type-over-k compactification API is
  applied to `B'`. `SectionCompactSource.proExchange` is the published canonical
  exchange written in D+ by the fully faithful inclusion. It is constructed
  from the actual unbounded proper/open mate and the exact inverse-image
  comparisons, not an arbitrary invertible arrow. `IsIso` of its target component
  appears in `Exchange`.
* The supported-constant comparison is exactly
  `SectionCompactSource.proBeta ... sqZ`. The first equality in `Exchange` is
  `g*(a_E); C(M); Rπ'_!(beta) = constantPull(g); a_E'`, with the scalar-preserving
  `proConstantPull`. This is the node's identity source exchange under the stated
  identifications.
* The target pullback is an isomorphism `p` satisfying the published
  `IsFiniteTateProPullback ... v 1 p` root-projection normalization. `twistPull`
  is just its degree-zero derived and shifted image. The last equality of
  `Exchange` is, in Lean's left-to-right composition order,
  `g*(tau_E); C(K); Rπ'_!(twistPull) = constantPull(g); tau_E'`.
  Thus the actual arrow equality includes both endpoints explicitly.
* A geometric point is `Ω : Type u`, `[Field Ω]`, `[IsAlgClosed Ω]`, and
  `b : Spec (.of Ω) ⟶ B`. A chosen fibre basis is expressed equivalently by
  `v : AffineSpace (ULift (Fin 1)) (Spec Ω) ⟶ V.E`, the Cartesian projection
  square `sq`, and the Cartesian zero-section square `sqZ`. The resulting map
  from the literal fibre to this affine line is the isomorphism induced by that
  basis. Conversely every such Cartesian pair presentation is a fibre
  trivialization, and for a line over a field its origin-preserving
  trivializations are exactly changes of basis. The theorem quantifies over
  every presentation, so it retains arbitrary choices of basis.
* In the geometric clause the two canonical comparisons `p` and `q` satisfy
  `IsFiniteTateProPullback` and `IsFiniteTateSiteComparison`, respectively.
  The latter is the projection-normalized comparison from the ordinary root
  line to the prescribed pro-etale twist. `FibreFormula` explicitly composes
  `b*(tau_E)` with compact-fibre exchange, the shifted `p`, and
  `LineKummerField.compactTarget ... q`. Its right side is the constant source
  comparison followed by `compareConstant.inv` and
  `ν*.map (LineKummerField.etaleTau ... zeroSection ...)`.
  This is equality of the actual morphisms and their targets in the fully
  faithful D+ presentation. It is not merely a statement about cohomology groups
  or existence of an isomorphism. On `Spec Ω` this is the geometric-stalk
  presentation used in `lem-pur-cfiber-stalk`.
* `etaleTau` has the actual ordinary etale root-line representative
  `finiteEtaleTateLine ... (l^(n+1)) ... hA`, in degree zero then shifted by two.
  `LineKummerField.CoefficientRealization` identifies it with the derived scalar
  extension of the root sheaf, with its specified scalar-unit map. The geometric
  clause applies the dependency anew over Ω, not over k. It therefore requires
  no finite-type hypothesis on Ω over k. No supported-cohomology object or
  group is equated with compact cohomology anywhere in this module.

Dependency declarations read and used (modules are the exact recorded ones):

* `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  its `Ring` and `Coefficient` quotient conventions.
* `Sheaf.Paper.PurityVectorBundleZeroSection`:
  `AlgebraicGeometry.PurityVectorBundle`, `.zeroSection`, `.zeroSection_spec`.
* `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`:
  `WeilConjectures.sfIntegralTwistingFunctor` and its reexported finite twists;
  the actual finite line used here is the existing `Scheme.finiteTateProSheaf`.
* `Sheaf.AlgebraicGeometry.CartierKummerMap`:
  `AlgebraicGeometry.Etale.cartier_kummer_map`, `.cartierKummerMap`.
* `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`:
  `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport`; the statement uses its
  existing fixed-scalar D+ compactification presentation.
* `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`,
  `.rightDerivedLowerShriekOfCompactificationPlus` and their compatibility.
* `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `AlgebraicGeometry.Scheme.FixedEtaleOriginWitness`; the concrete antecedents
  are fixed by `LineKummerField` rather than existentially replaced.
* `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  `AlgebraicGeometry.ProEtale.siteComparisonDerivedPullbackPlus`, definitionally
  the `comparisonUpperStar.mapDerivedCategoryPlus` used in the formula.
* `Sheaf.Paper.CanonicalOriginCompactSupportComposition`:
  `AlgebraicGeometry.ProEtale.originComposition`, its identity normalization.
* `Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange`:
  `AlgebraicGeometry.ProEtale.isIso_csAuxiliaryExchange`; the canonical arrow
  is restricted to D+ in the existing `SectionCompactSource.proExchange`.
* `Sheaf.Paper.CompactFiberStalk`:
  `WeilConjectures.PurityFiniteSetting.compactFiberFiniteMap`, `.compactFiber_finite`.
  Its fixed-scalar pullback to `Spec Ω` is precisely the canonical exchange
  appearing in `FibreFormula`, before the specified twist/site endpoint maps.
* `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `AlgebraicGeometry.ProEtale.compactSupportSiteComparisonPlus` and its ambient
  counterpart, used by the existing `LineKummerField.compactTarget`.
* `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer`:
  `AlgebraicGeometry.Etale.ordinary_supported_kummer` and
  `.ordinary_supported_kummer_uniqueBoundary`.
* `Sheaf.Paper.FiniteTorAmplitudeSites`:
  `WeilConjectures.finiteTorConstructible`, `.finiteTorConstructibleCategory`;
  the field-realization dependency supplies this property for the shifted line.
* `Sheaf.Paper.LineKummerFieldRealization`:
  `AlgebraicGeometry.LineKummerField.proLine`, `.proTau`, `.etaleTau`,
  `.compactTarget`, `.line_kummer_field_realization`, and its root-normalization
  predicates reexported from `FiniteTateSiteDescent`.
* `Sheaf.Paper.SectionCompactSourceExchange`:
  `AlgebraicGeometry.SectionCompactSource.proSource`, `.proConstantPull`,
  `.proSupported`, `.proBeta`, `.proExchange`, `.compareConstant`,
  `.composition_normalization`, `.section_compact_source_exchange`.
* Proof-only `Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion`:
  `AlgebraicGeometry.Etale.compactSupportFiniteTorsion`, providing exchange
  invertibility and naturality/coherence in the ordinary etale model.

The two theorem nodes `lem-pur-line-kummer-field-realization` and
`lem-pur-section-compact-source-exchange` remain in `proof_deps` only. Their plain
definitions are cited through the new existing-definition owners
`def-pur-line-kummer-compact-images` and `def-pur-section-compact-source-maps`.
The existing owners `def-pur-finite-tate-site-comparison` and
`def-asd-finite-etale-tate-twist` are also added to `stmt_deps`.
No base theorem statement, proof step, or proof dependency is changed.

Edge cases checked before and after writing: empty B and its empty total space
(the statement and all comparisons remain meaningful); identity base change
(the normalized source and target equations specialize correctly); nonflat and
non-Noetherian B' (no flatness, Noetherian, finite-type or qcqs assumptions on it);
level one (`n=0` in the published successor index); arbitrarily ramified coefficient
extensions (no divisibility assumption); arbitrary algebraically closed geometric
fibre fields, including transcendental extensions of k; every fibre basis
(the Cartesian pair is universally quantified). Small sites retain object universe
u+1, morphism universe u, and the usual lifted coefficient universe u+1.

Searches actually run through `batch2/msearch.py`:

* LeanFinder: "Compactly supported Kummer zero section class of a line bundle
  commutes with arbitrary base change and its geometric stalk is the ordinary
  etale origin class". Eight hits about scheme-section localization and
  structure-sheaf stalk maps; none about this statement.
* Loogle: `"baseChange", "compact"`. Eight hits: quasi-compact morphism stability
  and compact-subset neighbourhood constructions. None states the result.
* Mathlib grep: `Kummer|zeroSection.*baseChange|compactSupport.*baseChange`,
  subdirectory `AlgebraicGeometry`. Zero hits.
* Direct `rg` on `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `zero_class_exchange`, `zeroClassExchange`, line/Kummer and `proTau`, then for
  `line_zero_class_exchange` and namespace `AlgebraicGeometry.LineZeroClass`:
  no exact statement or name clash. The existing `LineKummerFieldRealization`
  and `SectionCompactSourceExchange` supply the separate ingredients.
  `ClosedSectionCompactOrigin.closed_section_compact_origin` was read: it
  compares etale/pro-etale compact images on a single base, and does not state
  arbitrary-base-change compatibility or this geometric-fibre origin formula.
  Upstream Kummer affine-line orientation and Kummer-base-change results concern
  other morphisms and do not already state the delivered lemma.

No STATEMENT-DISPUTED flag or statement correction is warranted.

Validation: prescribed `scompile.py Q43 lem-pur-line-zero-class-exchange` on the
complete module succeeded in sandbox mode (47.2 seconds) and under its actual
library module name (9.1 seconds), with no errors or non-sorry warnings.

## Second reading by Q43

The dispatcher explicitly forbids spawning other agents and assigns the
maintainer the independent review. This section records the worker's second
reading, not a claim of independent authorship.

I reopened the node and the delivered file and checked the composition order:
Lean's `a ≫ b` is b after a, so `Exchange` first pulls tau, then applies the
exchange, then the root-normalized target pullback. Its source equation uses the
same `proBeta`, pulled compactification, and `proSource`. On the geometric side,
`FibreFormula` ends at the comparison pullback of the ordinary etale compact
origin target, and its right side is the realization of the actual `etaleTau`.
The base constant comparison is included on both sides; no equality between
nonmatching source objects is hidden. The geometric point is universally
quantified without a finite-type hypothesis, and its square includes the origin.

I checked the only additional index parameter `_hn`: every positive P.level
admits it, including one, and the coefficient ring is exactly the fixed quotient.
I also checked the distinction between the given total space and the canonical
relative spectrum: the statement uses `PurityVectorBundle` and its chosen phi,
so it covers all the total spaces in the node rather than only the canonical
model. No mathematical mismatch was found in this second reading. The
independent mathematical review is the maintainer's next step.


## Repair of returned head 1368a514b839

H2 is repaired by definition ownership. The unchanged consumer is
`lean/Sheaf/Paper/LineZeroClassExchange.lean`, SHA256
`9d895ed56cc7e680d658123ba505dc0f11d7007d097927299d87d6ed83d24abb`.
The current main node still has no Lean record and its mathematical statement,
accepted split, and proof dependencies agree with the retained delivery. The
normal delivery wrapper rebases the repaired files on current main.

The mistaken two theorem-node additions to `stmt_deps` have been removed. Both
remain in `proof_deps`, exactly as the return asks. In their place the item cites
two new definition nodes, each with `existing: true`, no `lean.file`, and the exact
published module/declarations/signature. The item additionally cites the landed
`def-pur-finite-tate-site-comparison` for `finiteTateCoefficient`,
`finiteTateProSheaf`, `IsFiniteTateProPullback`, `IsFiniteTateSiteComparison`, and
`def-asd-finite-etale-tate-twist` for `finiteEtaleTateLine`. Thus every plain
helper singled out in the return has a definition-node owner. The corresponding
public imports already occur, directly or by the same public owner modules, in
the unchanged compiling consumer. No theorem or helper is redefined.

The new definition nodes make no claim of the exchange equalities proved by the
two theorem nodes. Their canonical source and target arrows are precisely the
published formulas. Their signature fields were extracted verbatim from the
current owning source, and all listed declarations were reread with their full
signatures and bodies. Only the item `lean`/`stmt_deps`, the two new node files,
and this report change relative to main, in addition to the retained Lean module.

## New nodes

`def-pur-section-compact-source-maps` owns eighteen existing plain definitions in
`Sheaf.Paper.SectionCompactSourceExchange`: etale/pro-etale constants and supported
constants, constant pullback, exact closed degree-zero identification, normalized
proper/open interchange, direct-image compositor and identity, etaleSource,
compareConstant, compareSupported, sourceComparison, proSource, proConstantPull,
etaleBeta, proBeta and proExchange. Its source is current blueprint rank-one Thom
proof Step 3. The definition states the actual normalized inverse proper/open
source and its site transport, including on arbitrary bases. The canonical
exchange is the fully faithful D+ preimage of the actual ambient mate. It asserts
no invertibility or base-change equation for these maps. Underlying sheaf maps,
site comparison construction and Cartesian squares are cited through their
existing definition nodes. Representative-normalized proper/open interchange
and normalized derived direct-image compositors are cited as the actual
canonical comparison data used in the definition, not as owners of unrelated
plain definitions.

`def-pur-line-kummer-compact-images` owns ten existing plain definitions in
`Sheaf.Paper.LineKummerFieldRealization`: singleShiftInclusion, extPlusMap,
etaleLine, proLine, etaleClass, proClass, shiftedComparison, etaleTau, proTau and
compactTarget. Its source is current blueprint rank-one Thom proof Step 2 first
paragraph and Step 3. It defines degree-zero existing Tate lines, the uniquely
normalized supported Kummer class in D+, the actual compact images composed with
the above source maps, and the target comparison formed from the inverse shifted
root comparison and the inverse compact site comparison. The Kummer family is
selected from the uniquely normalized family in `lem-amb-cartier-kummer-map`;
that theorem is a genuine input to the construction, not a citation for an
unowned plain helper. No base-change or realization equality is part of the
new definition node. The section-source owner is its direct prerequisite;
there is no dependency on either extracted theorem or on the item itself.

For EACH new node the three searches were actually run via msearch and copied
from searches.jsonl into mathlib_searches: LeanSearch and LeanFinder used its
natural-language title description (see exact query in the node); grep used
`proSource|proExchange|proBeta|compareConstant` for the section source and
`proLine|proTau|etaleTau|compactTarget` for the compact Kummer images. Each semantic
search returned eight unrelated compact topology, scheme localization, affine
transition or standard-etale-presentation results; both Mathlib greps returned
zero hits. Direct rg on `dag/nodes` found the two existing theorem owners but
no definition owner for these declarations. Direct rg on upstream
`lean/WeilConjectures` returned zero matching names; the exact definitions are
in the two existing `lean/Sheaf/Paper` modules. `tools/blueprint_refs.py search`
for `compact section source` and `Kummer compact image` returned zero matches.
The ancestor command returned `thm-pur-rank-one-thom`, and both via lists are
`[lem-pur-line-zero-class-exchange]`. Existing supported-constant and Tate
notions are cited rather than duplicated. The new-node JSON uses indent 1,
Unicode, a final newline, and the required import_flags metadata.

Second reading of the repair: the two new mathematical definition statements
were checked against the listed existing bodies, not against the theorem
conclusions. I corrected the prose composite notation to the explicit
`h ∘ s`, `π ∘ z`, `j ∘ s` and `p ∘ j ∘ s` directions while retaining the
existing Lean definitions. Their generic A (section maps) and positive n+1
coefficient quotient (Kummer maps) universes and domains match the source.
Empty schemes, level one, arbitrary pullback bases and arbitrary specified
comparison q remain permitted. None of the source normalization, root
normalization, actual-arrow equalities, geometric-field generality or basis
quantification in the consumer has changed. The maintainer's independent
mathematical acceptance of these clauses in the return therefore still applies.

Repair validation: scompile.py was rerun on the unchanged complete consumer and
returned exit code 0, with both sandbox and library checks clean. The new
section-source owner cites the definition `pur713-def-shriek-exchange` for the
ambient finite-quotient mate, rather than borrowing a plain map from a theorem
node; its generic finite-A formula is stated explicitly. The two returned
theorem-node citations remain only in the consumer proof dependencies.
