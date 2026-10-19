## Worker report

The module states Stacks Project Tag 095K (1), read in
literature/stacks-project/etale-cohomology.tex, lemma-decompose-quasi-finite-morphism.
Its sole theorem is
AlgebraicGeometry.exists_affine_surjective_finite_etale_thickening_of_isQuasiFinite;
its proof is `by sorry`. No definitions or proofs are added. The node changes only in `lean`.
The theorem docstring carries all seven proof steps and their dependency identifiers.

Clause-by-clause correspondence:

- The affine schemes V and U are `{V U : Scheme.{u}} [IsAffine V] [IsAffine U]`.
- The given morphism is `(h : V ⟶ U)`.
- Quasi-finiteness is `(hqf : Scheme.Hom.IsQuasiFinite h)`, using the recorded
  Stacks finite-type-and-isolated-fibres predicate, not Mathlib's weaker pointwise predicate.
- Finite presentation is `(hfp : LocallyOfFinitePresentation h ∧ QuasiCompact h ∧
  QuasiSeparated h)`, exactly the three clauses specified in the node. This packages
  the full condition into one hypothesis rather than adding separate automatically
  derivable quasi-compact/quasi-separated instance hypotheses on an affine map.
- The affine U prime is `∃ (U' : Scheme.{u}) (_ : IsAffine U')`.
- Its map to U is `(a : U' ⟶ U)` with `Surjective a`.
- V prime is the chosen fibre product `pullback h a`, in the node's order V ×_U U prime.
- The closed subscheme is expressed by `∃ (Z : Scheme.{u}) (i : Z ⟶ pullback h a)`.
  The predicate `IsThickening i` unfolds to precisely `IsClosedImmersion i ∧ Surjective i`,
  giving both the closed immersion and surjectivity on underlying points. No square-zero
  or nilpotence bound is imposed: the source asks for a general thickening.
- The structure morphism to U prime is the actual composite `i ≫ pullback.snd h a`.
  `IsFinite` and `Etale` are asserted of this same composite. The finite-etale-category
  dependency's object condition is exactly this conjunction; no category or base-change
  functor needs to be constructed to express this clause.

Dependency declarations read and used:

- Sheaf.AlgebraicGeometry.QuasiFiniteMorphism:
  AlgebraicGeometry.Scheme.Hom.IsQuasiFinite (pqf-def-quasifinite).
- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom;
  Mathlib.AlgebraicGeometry.AffineScheme: AlgebraicGeometry.IsAffine (def-pc-scheme).
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  AlgebraicGeometry.LocallyOfFinitePresentation (def-sbc-locally-finite-presentation).
- Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact and Morphisms.QuasiSeparated:
  AlgebraicGeometry.QuasiCompact and QuasiSeparated (def-weil-pbc-scheme-conventions,
  which fixes no independent notion and has no module).
- Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap: AlgebraicGeometry.Surjective
  (def-weil-surjective-morphism).
- Sheaf.AlgebraicGeometry.Thickening: AlgebraicGeometry.IsThickening
  (def-sbc-first-order-thickening).
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: AlgebraicGeometry.IsClosedImmersion,
  used through IsThickening (def-weil-closed-immersion).
- Mathlib.AlgebraicGeometry.Morphisms.Finite and Morphisms.Etale:
  AlgebraicGeometry.IsFinite and Etale. The mathlib_match of
  def-weil-pbc-finite-etale-category specializes MorphismProperty.Over to their
  intersection; the theorem uses its stated finite-etale object condition directly.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback:
  CategoryTheory.Limits.pullback and pullback.snd (def-pc-fibre-product), with scheme
  pullback existence from Mathlib.AlgebraicGeometry.Pullbacks.

The recorded, already stated proof-dependency modules are imported without `public`
when they are not also needed in the signature: SeparatedLqfBaseChange,
QuasiFiniteLocallyQuasiFinite, QuasiFiniteIffFiniteFibres, NoetherNormalization,
Noetherian, IdealSheaf.Subscheme, ReducedIdealsZeroIntersection,
Ideal.Quotient.Operations, AlgebraicGeometry.Limits and PullbackCarrier.
Dependencies with neither a Lean record nor a Mathlib match are not invented:
lem-kun-fp-algebra-descent, lem-weil-pbc-descend-quasifinite-affine,
lem-weil-pbc-generic-finite-morphism-open-neighborhood and
lem-weil-pbc-finite-affine-section-cover will be available for stage 3 later.

Edge cases checked mathematically: U empty forces V empty, and all existential schemes
may be empty. V empty over nonempty U permits U prime = U and Z empty; the empty morphism
is finite etale and its empty inclusion is a thickening. No nonempty or nontrivial-ring
assumption appears. The finite-copy stage of the source proof allows zero copies.
No characteristic restriction, Noetherian hypothesis or finite-degree restriction was
added. All schemes use the original arbitrary universe u; no independent test universe
or index universe narrows the assertion. The base change a is only required surjective,
not flat, etale, finite or of finite presentation.

Searches for an existing statement:

- msearch.py leanfinder: “A quasi-finite finitely presented morphism of affine schemes
  admits a surjective affine base change with a finite etale thickening”: eight hits,
  concerning etale locality, affine space, finite presentation and descent; none states
  the closed thickening decomposition.
- msearch.py loogle: “AlgebraicGeometry.IsFinite, AlgebraicGeometry.Etale”: one hit,
  exists_etale_isCompl_of_quasiFiniteAt, which gives a different etale neighborhood
  splitting and not this surjective affine base change and thickening.
- msearch.py grep: “thicken.*[Ee]tale|[Ee]tale.*thicken|decompose.*[Qq]uasi”: zero hits.
- msearch.py leansearch: “A quasi finite finitely presented affine morphism admits a
  finite etale thickening after surjective base change”: service unavailable,
  Internal Server Error; no conclusion drawn from that unavailable search.
- rg of the same patterns and the exact item identifier in the upstream WeilConjectures
  tree, lean/Sheaf and dag/lean_names_upstream.json found only other thickening and
  etale-site/lifting results, plus a constructibility proof mentioning 095K. None
  is the required statement. The exact new declaration name has no prior occurrence.

No statement dispute, statement correction, new node or dependency module is needed.

Validation: scompile.py compiled the delivered module on the server cleanly in 1.4 seconds,
with nice 19, two threads and the unchanged 60-second per-file limit. No local Lean or Lake
invocation was used. The dry-run result is recorded below after preflight.

Dry run: deliver2.py --no-push printed OK: the commit compiles and passes preflight
except for the independent second-reading section, which the second reader will write.
Nothing was pushed.

## Second reading by NX

I independently opened the delivered node and Lean module, all nine statement-dependency
nodes, the recorded QuasiFiniteMorphism and Thickening modules, and the Mathlib
scheme, affine-scheme, morphism-property and pullback declarations. I read
literature/stacks-project/etale-cohomology.tex, lemma-decompose-quasi-finite-morphism
(Tag 095K), both its statement and proof and the preceding context. Part (1) assumes
only a quasi-finite finitely presented morphism of affine schemes. No Noetherian
hypothesis is inherited: Noetherianity occurs after the proof's descent reduction.

My object/hypothesis/conclusion checklist, matched against the file:

- Objects V and U are arbitrary schemes, both affine: `{V U : Scheme.{u}}`
  and `[IsAffine V] [IsAffine U]`. Mathlib IsAffine means that the canonical map
  to Spec of global sections is an isomorphism. Verdict: exact.
- The given scheme morphism h:V -> U is `(h : V ⟶ U)`. Scheme.Hom is the
  locally-ringed-space morphism recorded by def-pc-scheme. Verdict: exact.
- Quasi-finiteness is `(hqf : Scheme.Hom.IsQuasiFinite h)`. I read that
  dependency's actual definition: LocallyOfFiniteType, QuasiCompact, and each
  singleton `{h.asFiber x}` open in its scheme-theoretic fibre. This is the
  node's finite-type plus isolated-fibre-points definition, rather than just
  Mathlib's pointwise quasi-finite predicate. Verdict: exact.
- Finite presentation is `(hfp : LocallyOfFinitePresentation h ∧ QuasiCompact h ∧
  QuasiSeparated h)`. The Mathlib declarations impose finite presentation on
  affine-open ring maps, compact inverse images of compact opens, and a
  quasi-compact diagonal, respectively. This is precisely the convention in
  def-sbc-locally-finite-presentation and def-weil-pbc-scheme-conventions.
  There is no extra structure instance on h. Verdict: exact.
- The new affine base is `∃ (U' : Scheme.{u}) (_ : IsAffine U')`; its morphism
  is `(a : U' ⟶ U)` and its required property is `Surjective a`. I read
  Surjective.surj, which is surjectivity of the underlying point map. No flat,
  etale, finite, or finite-presentation condition is imposed on a. Verdict: exact.
- The new source V' is `pullback h a`, with second projection
  `pullback.snd h a : pullback h a ⟶ U'`. This is exactly the node's
  V ×_U U'. Stacks writes the factors in the reverse order; their canonical
  symmetry preserves both projections and the assertion. Scheme pullbacks
  exist without additional hypotheses. Verdict: exact.
- The closed subscheme is `∃ (Z : Scheme.{u}) (i : Z ⟶ pullback h a)`
  with `IsThickening i`. I unfolded the recorded dependency, which is exactly
  `IsClosedImmersion i ∧ Surjective i`. Closed immersion uses a closed
  embedding and surjectivity on stalks. Thus both the closed-immersion clause
  and surjectivity on all underlying points are present. There is no first-order
  or finite-order nilpotence condition. Verdict: exact.
- The final composite is `i ≫ pullback.snd h a`, and both
  `IsFinite (i ≫ pullback.snd h a)` and `Etale (i ≫ pullback.snd h a)`
  concern that same composite. I read IsFinite (affine with finite affine
  ring maps), Etale (etale affine-open ring maps), and the finite-etale-category
  match MorphismProperty.Over with property `@IsFinite ⊓ @Etale`.
  The node asserts this object property, not an equivalence of categories.
  Verdict: exact, with all existential choices after the given hypotheses.

Edge cases: if U is empty, V must be empty, and empty U' and Z are allowed.
If V is empty and U is nonempty, choose a = identity and Z empty. The empty
inclusion is a thickening of the empty base-changed source and the empty map
is finite etale. Zero coordinate rings and zero copies in the source proof
are allowed. No cardinal, degree, nonemptiness, characteristic, field,
Noetherianity, or reducedness assumption appears. The arbitrary universe u is
bound explicitly and contains every scheme used; no test-object quantifier
or independently smaller universe occurs. No n or index set is quantified in
the theorem, so there is no hidden exclusion of n = 0 or an empty family.

Independent duplicate searches (different queries from the first reader):

- msearch leanfinder: "quasi finite affine morphism becomes finite etale after
  surjective base change and reduction" returned eight hits, concerning etale
  postcomposition/base change, quasi-finite ring maps, etale-algebra descent,
  and locallyQuasiFinite_iff. None is this decomposition theorem.
- msearch loogle: "AlgebraicGeometry.Surjective, AlgebraicGeometry.Etale"
  returned instDescendsAlongSchemeEtaleMinMorphismPropertySurjectiveFlatQuasiCompact.
  It descends etaleness along a flat cover; it does not construct our cover or Z.
- msearch leansearch: "A quasi-finite finitely presented morphism between affine
  schemes has a finite etale closed thickening after surjective base change"
  returned service unavailable (Internal Server Error); no verdict from it.
- Direct rg of upstream WeilConjectures, the project's lean/Sheaf, Mathlib,
  and dag/lean_names_upstream.json used `095K`, `finite.etale.*thicken`,
  `thicken.*finite.etale`, `decompos.*[Qq]uasi`, and the proposed declaration
  name. The proposed name is absent from the read-only trees. I opened the
  potentially relevant GenericFiniteNoetherianSchemeSplitting,
  FinitePushforwardModuleLocallyConstantStrata, FiniteEtaleThickeningLift and
  upstream RelativeLineStep declarations. They concern generic-open splitting
  under Noetherianity, sheaf local constancy on curves, lifting an already
  given finite-etale object across a thickening, or weight bounds; none states
  this theorem. Existing recorded definitions are reused throughout.

I checked all seven docstring proof steps against the node: affine descent,
Noetherian finite stratification, section cover, Boolean-atom refinement,
Chinese-remainder union of disjoint sections, finite affine disjoint union,
and pullback to the original base. The source places and blueprint identifier
are in both docstrings. The sole theorem has `by sorry`; there are no new
or hollow definitions, auxiliary proofs, local notation, private declarations,
or unbound variables. All lines fit 100 characters. Already stated proof
modules are imported; the four still-unstated proof dependencies are explicitly
identified in the worker report. There are no new nodes, dependency modules,
or statement corrections to review under H12/H13 or section 4c.

No mathematical or Lean mismatch was found. I left the correct module and node
unchanged and added this independent second-reading record. A direct comparison
verified lean.statement equals the file's theorem signature verbatim.
Independent scompile.py validation of the only delivered module succeeded on the
server in 1.3 seconds, nice 19, two threads, 60 seconds per file, with no warnings
or errors. No local compiler or Lake build was used.
