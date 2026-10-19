## Worker report

The item is stated by `AlgebraicGeometry.Etale.isIso_supportedExteriorProduct` in
`Sheaf.AlgebraicGeometry.KunnethSupported`. It asserts invertibility of the actual
supported pairing on the etale site and of the actual pro-etale pairing for every
specified realization. The theorem proof is `sorry`; its docstring contains the
complete double-localization argument of the node, including the arbitrary-witness
naturality argument. The original item statement and proof are unchanged.

Hypotheses and clauses are rendered as follows.

- The algebraically closed field is `D.k` for
  `D : WeilConjectures.FiniteFieldDatum`. The prime is `l`, with `[Fact l.Prime]`
  and `_hl : l ≠ D.p`, as required by the coefficient convention.
- A finite extension of Q_l is `E` with `[Field E]`, `[Algebra (Padic l) E]`, and
  `[FiniteDimensional (Padic l) E]`. Positive level is `n` with `[Fact (1 ≤ n)]`.
  Every coefficient occurrence is the existing `Padic.coefficientExtensionRing l E n`,
  the quotient of the extension's valuation ring by the indicated uniformizer power.
  Its existing finiteness theorem supplies `Finite`; its finite-coefficient topology
  is the discrete topology, as required by origin witnesses.
- `X` and `Y` are schemes over `Spec (CommRingCat.of D.k)`. `LocallyOfFiniteType`
  and `QuasiCompact` on each structure morphism express finite type;
  `IsSeparated` on those same morphisms expresses separatedness. No properness or
  smoothness assumption is added. `i : Z ⟶ X` and `j : W ⟶ Y` carry
  `IsClosedImmersion`, with no smoothness requirement on the supports.
- `K` and `L` are `DerivedCategory.Bounded` of etale module sheaves. Their `.obj`
  fields are the ambient derived objects. Only `L` has the additional assumption
  `_hL : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A Y a b L.obj`.
  No constructibility or flatness assumption is made on `K`.
- The first conclusion is `IsIso (Etale.supportedExteriorProduct A f g i j K.obj L.obj)`.
  This arrow has source `RΓ_Z K ⊗ RΓ_W L` in the existing monoidal derived module
  category and target `RΓ_(Z×W) (Etale.externalProduct A f g K.obj L.obj)`.
  The support morphism is the actual pullback-product closed immersion.
- The second conclusion universally quantifies over `Kp`, `Lp` in the existing
  `FiniteCoefficientDerivedCategoryPlus`, and over their actual `EtaleOriginWitness`
  structures `wx`, `wy`. The isomorphisms `_hx : wx.L.obj ≅ K.obj` and
  `_hy : wy.L.obj ≅ L.obj` say that these witnesses realize the given complexes.
  It asserts `IsIso` of the independently constructed pro-etale supported arrow
  after the canonical inverse coefficient-presentation functors on `Kp.obj`, `Lp.obj`.
  It covers arbitrary witnesses and arbitrary identifications, including identities.
  The witness alpha maps are part of the witness structures, not omitted hypotheses.

Dependency declarations used (including the presentations underlying the statement):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.coefficientExtensionRing`, `Padic.finite_coefficientExtensionRing`.
- `Sheaf.AlgebraicGeometry.DerivedCategories` and its upstream imports:
  `Etale.DerivedCategoryModule`, `DerivedCategory.Bounded`, `DerivedCategory.Plus`.
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`:
  `Etale.DerivedCategory.hasTorAmplitudeIn`.
- `Sheaf.Paper.EtaleOriginWitness`: `ProEtale.EtaleOriginWitness`;
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `finiteCoefficientRealization`,
  `FiniteCoefficientDerivedCategory`, `FiniteCoefficientDerivedCategoryPlus`.
- `Sheaf.AlgebraicGeometry.SupportCohomology`: published kernel support construction
  and its derived functors. `Sheaf.AlgebraicGeometry.EtaleSupportedSections`:
  `supportedEtaleSections`, `supportedEtaleSectionsι`, its additive instance.
  The latter is the module-valued kernel functor required by the etale pairing;
  its owning landed node is added to the item's statement dependencies.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor` and
  `WeilConjectures.SixFunctors.ProEtale.Derived.Tensor`: the existing `derivedTensor`
  bifunctors. Their `externalProduct` declarations are imported from the corresponding
  etale Kunneth Defs and pro-etale ExternalProduct modules.
- Mathlib: `Scheme.Over`, `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`,
  `IsClosedImmersion`, and categorical `pullback` implement the scheme conventions,
  finite-type/separated/closed-immersion/base-change dependencies. No separate private
  definitions of these notions are introduced.
- Proof dependencies with published Lean interfaces are imported:
  `Sheaf.AlgebraicGeometry.SupportRestrictionTriangle`,
  `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`, and
  `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`.

Edge cases checked: empty schemes; empty support (zero support functor and pairing);
full support (the ordinary section pairing); the zero complex; level `n=1`; distinct
Tor endpoints and the zero complex's empty Tor interval; arbitrary, nonconstructible
bounded complexes; no finite Tor hypothesis on the first factor; both identity and
arbitrary origin witnesses. Locally Noetherian hypotheses used internally on the
pro-etale side follow from finite type over the field and are installed by the
existing theorem, so they are not additional hypotheses of the item. The small-site
object/morphism universes are retained. Coefficients use the existing one-universe
lift for module-valued small-site sheaves.

Searches: the exact tool outputs are saved in `searches.jsonl` and in the new node's
`mathlib_searches`. LeanFinder for “Kunneth formula for derived etale cohomology with
closed supports” returned eight unrelated etale-algebra/differential hits. Loogle
`"Kunneth"` and Mathlib grep `supportedExterior|supported.*[Kk]unneth|cohomologyWithSupport`
returned none. LeanFinder for the pro-etale supported product returned eight unrelated
cotangent/continuous-cohomology hits; LeanSearch for the canonical pro-etale pairing
and inverse realization was unavailable with Internal Server Error, recorded as
unavailable rather than no match. Mathlib grep for the prospective map names returned
none. `rg` in upstream WeilConjectures and side `lean/Sheaf`, plus the DAG/blueprint
search, found ordinary external products and the finite-coefficient realization but
no pro-etale supported product. The server source and delivery branches were checked:
NZ's support-cohomology module has since landed and is reused; N4's supported-product
branch contained a stage-1 definition, with no Lean implementation to reuse.

No statement dispute or source correction is needed. All new definitions have real
data. The only choices are normalized unique maps/adjunctions, or the inverse of the
fixed coefficient equivalence. An inverse equivalence is determined up to natural
isomorphism, exactly the equality notion used by the derived presentation and IsIso
assertion. No arbitrary map or arbitrary natural isomorphism replaces a canonical map.
Every postponed helper theorem has its source and a proof in its docstring and is
listed in its owning node's `lean.declarations`.

## Dependency modules

`def-pur-supported-exterior-product` had no recorded declaration. Its module constructs
closed supported constant coefficients, the canonical quotient, the uniquely normalized
ordinary adjunction with the support kernel, and its derived adjunction. It then defines
the coefficient tensor map by its quotient normalization, its signed total-complex map
by every bidegree inclusion, and the derived map by naturality plus localization
normalization. The supported product is the adjoint of that map followed by the pulled
back support evaluation counits. These are helpers of the same supported-product
notion, all listed in the lean record. The construction is available unbounded and
restricts to the source's bounded-below situation. Its node changes only in `lean`.

`def-weil-derived-tensor` now has Q11's landed lean-only repair recording the exact
existing upstream `AlgebraicGeometry.ProEtale.derivedTensor`, the K-flat total derived
bifunctor on fixed-ring module sheaves. The second reader found this concurrent repair
and removed this delivery's stale replacement record. The published Q11 record is used
unchanged; this delivery supplies no module or record for that dependency.

The initially missing support-cohomology dependency has landed during the work. The
published NZ module and record are used unchanged; its temporary sandbox copy is not
part of the delivery.

## New nodes

`def-pur-proetale-supported-exterior-product` makes precise the actual pro-etale arrow
required by the item's final clause and proof step 5. It uses the same normalized
adjunction construction on the small pro-etale site, with finite coefficients and
locally Noetherian ambients, and explicitly supplies the exact inverse coefficient
presentation needed to interpret the existing origin witnesses. Its field wrapper
derives the locally Noetherian hypotheses from the given structure morphisms. Its
statement includes all adjunction, ordinary/complex/derived normalization and exact
presentation obligations implemented in its module. The source is the item's final
clause and its complete witness-comparison proof. The searches above find no existing
node or declaration of this pro-etale supported pairing; the existing etale product,
ordinary pro-etale external product, and finiteCoefficientRealization are reused.

## Completion checks

The inherited diagnostic modules were removed from the delivery. The two large
comparison characterizations now use named morphism types and predicates, keeping
all ordinary quotient, signed bidegree, naturality and localization equations
unchanged while avoiding repeated expansion of their types during compilation.
A named equality also identifies the explicit pro-etale tensor-bifunctor value
with the existing upstream external product, avoiding repeated unfolding of its
large monoidal-instance term. It does not change the map or the external product.
All helper declarations are recorded in their owning node's `lean.declarations`.
The module records are regenerated from the actual signatures, with UTC dates.

The server source lookup for the supported-product module returned “Module source
unavailable”. A read-only branch inspection confirmed the existing supported-product
delivery has no Lean record to reuse. The lead-only `merge_delivery.py list` command
refused listing at its role gate; no merge was requested or attempted. The branch
check used read-only ref and object inspection instead.

The pro-etale construction reuses `ProEtale.supportSections i A` from the landed
support-cohomology node directly. Its inclusion into all sections uses the existing
kernel inclusion and `Sheaf.ΓNatIsoSheafSections` at the terminal pro-etale object.
No second pro-etale supported-section functor is defined.


## Second reading by N4

I independently read the item's node and all three delivered Lean modules, and opened
all recorded statement-dependency signatures. I read the blueprint source files for
orders 1938 and 1939 on the project server because literature is not installed in this
machine's shared clone. The source's implicit coefficient convention is the one in
`def-weil-finite-field-fiber`: prime l distinct from p, finite extension E/Q_l, and
positive level n. The DAG's previously reviewed explicit E and n binders agree with
that convention. This delivery does not correct the item's statement.

The source statement, matched clause by clause:

1. Global algebraically closed field k: `D : WeilConjectures.FiniteFieldDatum.{u}`
   and `D.k`. I opened `FiniteFieldFiber`: the datum includes the finite base field,
   the algebra over it, and `IsAlgClosure`; this is precisely the stipulated global
   field, rather than an extra restriction on a newly arbitrary field. Verdict: exact.
2. Coefficients: `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`, a field `E` with
   `Algebra (Padic l) E` and `FiniteDimensional (Padic l) E`, and `(n : ℕ)` with
   `Fact (1 ≤ n)`. Every coefficient is the existing
   `Padic.coefficientExtensionRing l E n`. I read its existing finiteness interface;
   the new instances only expose that theorem and the discrete topology required by
   the finite-coefficient witness interface. No extra valuation data is assumed.
   Verdict: exact.
3. Separated finite-type k-schemes X,Y: `Scheme.{u}`, `X.Over (Spec … D.k)` and
   `Y.Over (Spec … D.k)`, and `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`
   on each structure map. I read the dependency records and Mathlib class signatures:
   finite type is locally finite type plus quasi-compact; separated means the diagonal
   is a closed immersion. Properness, smoothness and constructibility are absent.
   Verdict: exact.
4. Closed subschemes Z,W: `(i : Z ⟶ X) (j : W ⟶ Y)` with `IsClosedImmersion`.
   Mathlib's class requires the closed embedding and stalk surjectivity. The support
   product is `supportedProductImmersion f g i j`, a real `pullback.map` from
   `pullback (i ≫ f) (j ≫ g)` to `pullback f g`. It is the scheme-theoretic product,
   including nonreduced supports. Verdict: exact.
5. Bounded coefficient complexes K,L: both are `DerivedCategory.Bounded` of
   `Sheaf …smallEtaleTopology (ModuleCat.{u+1} A)`; `.obj` is their ambient derived
   object. I opened `DerivedCategories` and the upstream coefficient definitions;
   these are the dependency's module-sheaf categories and bounded subcategories.
   Verdict: exact.
6. Finite Tor amplitude only for L: `_hL : ∃ a b : ℤ,
   DerivedCategory.hasTorAmplitudeIn A Y a b L.obj`. The upstream predicate tests
   every module sheaf in degree zero and vanishes outside the interval. There is no
   flatness, finite generation or constructibility on K, and no requirement a ≤ b
   excluding the zero case. Verdict: exact.
7. Étale conclusion: `IsIso (Etale.supportedExteriorProduct A f g i j K.obj L.obj)`.
   I followed its definition through `supportedSectionsDerived`, the closed constant
   coefficient functor, the uniquely normalized ordinary adjunction, the signed
   total-complex normalization and the derived normalization. Its source is precisely
   `RΓ_Z K ⊗ RΓ_W L` in the existing derived module monoidal category; its target is
   supported cohomology of the existing projection-pullback external product on the
   actual fibre product. Verdict: exact canonical arrow, not existence of an iso.
8. Pro-etale conclusion: the second conjunct universally binds Kp,Lp, their specified
   `EtaleOriginWitness` structures wx,wy, and identifications `wx.L.obj ≅ K.obj`,
   `wy.L.obj ≅ L.obj`. I opened `EtaleOriginWitness`: its alpha is the actual
   specified comparison isomorphism. `fixedRingDerivedTransport` is the derived
   inverse of `finiteCoefficientRealization`, not an arbitrary transport. After this
   presentation change the conclusion is `IsIso` of the independently defined
   `ProEtale.supportedExteriorProductOverField`. Its ordinary adjunction and both
   tensor normalizations mirror the supported-section construction, and the field
   wrapper derives local Noetherianness from locally finite type over k. It adds no
   hypothesis to the main statement. Verdict: exact, including arbitrary witnesses.

Edge cases: the binders allow empty ambient schemes, empty/full supports, arbitrary
closed scheme structures and zero K or L. Empty supports give the zero support
functor; full supports recover global sections. There is no index-set assumption.
Level n=1 is included; n=0 is excluded by the source, not by a new restriction.
The source's l≠p condition is explicit. Empty Tor intervals are allowed for zero L.
There is no bound on cohomology-group sizes or finite generation. The site object and
morphism universes remain those of the small sites; coefficient modules use the
existing u+1 convention, and no equality of distinct site universes is imposed.
Identity witnesses and arbitrary witness isomorphisms are both quantified over.

Independent searches used different words from the first worker. LeanFinder query
“Cup pairing of local sections supported on closed subsets induces a Kunneth
isomorphism on product schemes” returned coproduct/sheaf-on-union lemmas, no match.
LeanSearch query “Cohomology with supports exterior cup product on etale and proetale
sites” was unavailable (HTTP Internal Server Error), recorded as unavailable.
The valid Loogle query `"localCohomology"` found the ideal-power Ext-colimit functor;
I opened Mathlib/Algebra/Homology/LocalCohomology.lean and it is not the site-supported
pairing. Grep `localCohomology|cup.*[Ss]upport|[Ss]upport.*[Pp]roduct` found that same
functor and unrelated finite-support products. Direct rg over WeilConjectures,
lean/Sheaf and the upstream-name inventory found no supported exterior arrow or
fixedRingDerivedTransport. I also opened the upstream `Etale.supportedProduct` and
`cupWithSupports` in SixFunctors/Etale/Derived/Supports: these are sheaf-valued
products of exceptional-support objects on one scheme, with extra adjunction
instances, not this module-valued global exterior pairing. They therefore do not
replace the delivery. The DAG's existing etale supported-product node is reused;
there is no duplicate pro-etale supported-exterior definition node.

Dependency and new-node reading:

- `def-pur-supported-exterior-product`: the dependency had no usable recorded arrow.
  Its delivered module builds the pairing by the same pullback-and-tensor recipe as
  source order 1938. The more general unbounded construction restricts to the
  specified bounded-below case; it assumes no extra property there. The constant
  quotient equation fixes the ordinary map, bidegree equations fix the signed
  complex map, and naturality plus tensor-localization compatibility fix the derived
  family. All choices used for data have uniqueness in exactly the equality used
  later; there is no choice from a bare unconstrained existence theorem.
- `def-pur-proetale-supported-exterior-product`: I checked the new node against the
  final clause and comparison proof of source order 1939, and the etale recipe of
  order 1938. This is the missing pro-etale analogue needed to state that clause.
  Its module uses the landed `ProEtale.supportSections` kernel directly. I read
  Stacks cohomology.tex, section-cohomology-support-bis (0G6Y), for the unbounded
  support functor and its exact-left/derived-right adjunction; and proetale.tex,
  lemma-closed-immersion-complement-retrocompact-exact (09BM), for the pro-etale
  closed direct-image hypothesis. Local Noetherianness supplies retrocompactness.
  The new node has the correct definition-only fields, ancestry, source, searches,
  chapter/unit, empty proof arrays and a complete Lean record. I rendered its
  previously undelimited mathematical expressions as self-contained TeX, explicitly
  introduced every scheme and module variable, and cited the existing coefficient
  realization node in its statement and stmt_deps. This changes presentation only.
- The proposed `def-weil-derived-tensor` record was stale: Q11 has concurrently
  landed the same exact upstream `ProEtale.derivedTensor` interface. I opened it,
  checked its K-flat total-left-derived bifunctor and universe parameters, and
  removed this delivery's replacement JSON. The published record is used unchanged.
  This avoids overwriting another group's usable repair.

Repairs made: added the missing ordinary proof import
`Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution` for lem-kun-0f1m; imported the
recorded coefficient-realization owning module in the pro-etale construction;
corrected the pro-etale exactness proof docstring's globally quasi-compact complement
claim to retrocompactness and supplied its explicit Stacks 09BM reduction; formatted
the new definition node as TeX with its coefficient dependency; removed the stale
already-landed tensor record. The item's natural statement and Lean signature are
unchanged. No statement_change or citer audit is needed.

I checked all theorem bodies are `sorry`, definitions contain actual data, and every
postponed helper has a source/blueprint/proof docstring and is listed in its owning
node's declarations. The node lean.statement strings are verbatim equal to the
signatures parsed from all three modules. No file-local notation, private copy,
unbound variable or over-100-character Lean line was found.


Validation: all three sibling modules compiled separately through scompile.py with
no errors or warnings. After the repairs, deliver2.py --no-push compiled the final
versions and returned OK: the delivery passed the current server preflight. The
accepted dry-run commit was 3e0dad3ae9. No global build or direct Git mutation was run.
