## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry` states
`AlgebraicGeometry.Scheme.ProEt.qcqs_finite_family_geometry`, with proof `sorry`.
No definitions, dependency modules, new nodes, or statement corrections are introduced.
The node is an aggregate statement; none of the existing declarations states the whole
conjunction. The three component facts remain the recorded proof dependencies.

Hypotheses and clauses, in order:

- The base scheme is `(X : Scheme.{u})`; the small pro-etale category and topology are
  `X.ProEt` and `topology X`. The existing definitions `Qcqs X`, `qcqsInclusion X`,
  and `qcqsPrecoverage X` give precisely the full subcategory on qcqs schemes and
  its finite pro-etale covers. They are reused through the limits dependency.
- The universe convention is expressed by explicit `universe u v w`;
  finite families range over `I : Type v` with `[Finite I]` and sheaves have values
  in `Type (max (u + 1) w)`, allowing arbitrarily large coefficient sets and the
  universe-raised representable sheaves, just as the coproduct dependency does.
- Every affine object is qcqs: `∀ V : X.ProEt, IsAffine V.left →
  CompactSpace V.left ∧ QuasiSeparatedSpace V.left`.
- The site and fibre products are `∃ h : HasPullbacks (Qcqs X),
  ∃ J : @Pretopology (Qcqs X) inferInstance h, J.toPrecoverage = qcqsPrecoverage X`.
  Thus the pretopology has exactly the specified covers. Its axioms include pullback
  existence, isomorphism covers, composition and base change.
- Scheme fibre products and preservation by inclusion are the two
  `PreservesLimitsOfShape WalkingCospan` clauses, for `qcqsInclusion X` and its
  composite with `ProEt.forget X ⋙ Over.forget X`.
- Sending covers to covers is the implication from `R ∈ qcqsPrecoverage X T`
  to `R.map (qcqsInclusion X) ∈ precoverage X ((qcqsInclusion X).obj T)`.
- Each slice has finite limits: `∀ T : Qcqs X, HasFiniteLimits (Over T)`.
  Agreement with the full pro-etale slice is
  `PreservesFiniteLimits (Over.post (X := T) (qcqsInclusion X))`.
  Computation in schemes over T is `PreservesFiniteLimits` of the composite of
  `Over.post` with `Over.iteratedSliceForward` as displayed in the signature.
  No qcqs assumption on X or terminal object of the unsliced qcqs category is imposed.
- Adjoining any finite family to a cover is the final presieve clause of the
  existential: `S ∈ Precoverage.finite (Qcqs X) T` implies
  `R ⊔ S ∈ qcqsPrecoverage X T` when R is covering. Finite presieves encode finite
  families after forgetting repetitions, which do not affect covering.
- Subcanonicality is `(topology X).Subcanonical`. By Mathlib's definition and
  `GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable`, this says exactly
  that every `Hom_X(-,V)` is a sheaf. `uliftYoneda` is its universe-raised version.
- For every finite family `V : I → X.ProEt`, the hypotheses `hqc` and `hqs` say
  that every source is qcqs. The existential W and coprojections ι give a qcqs
  pro-etale object, a scheme isomorphism `e : (∐ fun i ↦ (V i).left) ≅ W.left`,
  and compatibility with every scheme coprojection. This identifies W with the
  scheme disjoint union, whose universal property restricts to the full qcqs
  subcategory; thus the disjoint union exists there. The following implication
  gives affineness when all summands are affine.
- `Nonempty (IsColimit (Cofan.mk ...))` asserts the coproduct property of the
  representable sheaves with these coprojections. The next clause states that
  the canonical `hc.desc` from any chosen coproduct is an isomorphism.
- `Function.Bijective (fun s ↦ fun i ↦ F.obj.map (ι i).op s)` identifies sections
  over W with the product of sections over the summands. The following equality,
  for every sheaf morphism η, is naturality in F for those same restriction maps.
- `IsEmpty I → IsEmpty W.left ∧ ∀ F, Nonempty (Unique ...)` explicitly includes
  the empty scheme and singleton sections. No nonemptiness assumption occurs.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: its recorded declaration
  `Scheme.proEtaleDerivedCategory` explains and imports the existing `Scheme.ProEt`
  and `Scheme.ProEt.topology`; the derived category itself is irrelevant here.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.forget`,
  `ProEt.precoverage`, `ProEt.topology`, and `ProEt.instSubcanonicalTopology`.
  The last declaration is the subcanonical dependency's `mathlib_match`.
- `Sheaf.AlgebraicGeometry.ProEtaleQcqsSiteLimits`: `Scheme.ProEt.qcqs_site_limits`;
  its public dependency `Sheaf.AlgebraicGeometry.ProEtaleQcqsSubsite` supplies
  `qcqsObjects`, `Qcqs`, `qcqsInclusion`, and `qcqsPrecoverage`.
- `Sheaf.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation`:
  `Scheme.ProEt.finite_coproduct_evaluation`. The quantified finite-family part
  uses its signature verbatim with an outer universal quantifier.
- `def-weil-size-convention` and `def-weil-pbc-scheme-conventions` have convention
  records, not declarations. The standard Mathlib notions named above implement them.
- `def-weil-pbc-sites-and-cohomology` records existing `Precoverage`, `Sheaf` and
  topology constructors; only site/sheaf language is relevant, not `Sheaf.H'`.
  Mathlib's `Pretopology` supplies the same finite-family site axioms.

Edge cases checked: X may be empty or non-qcqs; the unsliced category is only
asserted to have pullbacks. Slice terminal objects are T, always qcqs. Affines
include the empty affine scheme. A finite empty family is allowed, and its
section product is a singleton. Empty finite presieves may be adjoined to covers.
No finiteness of X, affine hypothesis on the summands, or nonempty index set is added.
No `STATEMENT-DISPUTED` or node fault was found.

Searches on 2026-10-15:

- `msearch.py ... leanfinder "The qcqs finite-cover pro-etale subsite has fibre
  products, slice finite limits and finite coproduct evaluation for sheaves"`:
  eight hits concerning etale sites, coherent sites, and points; no aggregate match.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.ProEt, HasPullbacks, Subcanonical"`:
  zero hits; the service reported unknown identifier `HasPullbacks`.
- `msearch.py ... grep "qcqs|finite_coproduct_evaluation|instSubcanonicalTopology"
  AlgebraicGeometry/Sites`: zero hits. Direct reading of the pinned Proetale
  module confirms the subcanonical instance and the full-site finite limits.
- `rg` in the upstream `WeilConjectures` and side `lean/Sheaf` for `qcqs` and for
  `finite_coproduct_evaluation|qcqs_site_limits`: the two recorded dependency
  declarations exist; no matching combined statement. A precise-name search for
  `qcqs_finite_family_geometry` in Mathlib, upstream name index, and side framework
  returns no declaration. Grep for this item's blueprint id in upstream
  `WeilConjectures` returns no hit.

Source checks: read the qcqs paragraph in Stacks proetale.tex's
`lemma-w-contractible-hypercovering` (09A1), fibre products (098M),
subcanonicality (098Z), and disjoint-union paragraph (0F4P), together with the
recorded finite-coproduct dependency's use of Hypercoverings 0DB1.

Validation: server `scompile.py NL` compiled the delivered module cleanly (1.6 s),
with nice 19, two threads and the unchanged 60-second per-file limit. Its three
side-only dependency modules were also compiled into the private overlay.

## Earlier second reading (a previous round; superseded)

Independent reading of the node JSON, the delivered module, all eight statement
 dependency records, and the source passages. Verdict: the Lean says what the node
says. No mismatch requiring a change to the statement, module, or DAG was found.
Only this second-reading report was added.

Objects, hypotheses, and conclusions matched individually:

1. An arbitrary scheme X: `(X : Scheme.{u})`, with no base finiteness,
   Noetherian, separatedness, or characteristic assumption. Correct.
2. Its small pro-etale site C: `X.ProEt` and `topology X`. Read Mathlib's
   `Scheme.ProEt` definition (`MorphismProperty.Over @WeaklyEtale ⊤ X`),
   `ProEt.forget`, `precoverage`, and `topology`, and the recorded
   `proEtaleDerivedCategory` dependency. Objects are weakly etale maps and
   arrows are X-morphisms, exactly as required. Correct.
3. The full qcqs subcategory D with finite covers: `Qcqs X`,
   `qcqsInclusion X`, and `qcqsPrecoverage X`. Read the definitions in
   `ProEtaleQcqsSubsite`: `qcqsObjects` is precisely compactness and
   quasi-separatedness of the source scheme; the precoverage is the comap
   of the full pro-etale precoverage intersected with `Precoverage.finite`.
   The latter means finitely many arrows, with repetitions forgotten. Correct.
4. Every affine object is qcqs: the first universal implication, with
   `IsAffine V.left`, `CompactSpace V.left`, `QuasiSeparatedSpace V.left`.
   The implication imposes no affine assumption on the rest of the theorem.
   Correct.
5. D is a site with fibre products: existential `h : HasPullbacks (Qcqs X)`
   and `J : @Pretopology ... h`, with `J.toPrecoverage = qcqsPrecoverage X`.
   Read `Pretopology`: its isomorphism, composition, and pullback axioms are
   the required site axioms. Correct, with exactly the specified covers.
6. Fibre products computed in schemes and preserved by inclusion: the two
   `PreservesLimitsOfShape WalkingCospan` clauses, for `qcqsInclusion X`
   and its composite through `ProEt.forget X` and `Over.forget X`. Correct.
7. Inclusion sends coverings to coverings: the universal implication on
   `R.map (qcqsInclusion X)` belonging to `precoverage X`. Correct.
8. Every slice D/T has finite limits: `∀ T : Qcqs X, HasFiniteLimits (Over T)`.
   Computation as scheme limits over T is preservation by the displayed
   `Over.post ... ⋙ Over.iteratedSliceForward ...`; agreement with C/T is
   `PreservesFiniteLimits (Over.post (X := T) (qcqsInclusion X))`. Correct.
   Read the recorded `qcqs_site_limits` signature: it supplies the scheme
   slice assertion; agreement with C/T follows from the same universal
   properties and the fully faithful inclusion. No extra global terminal
   object of D is being asserted.
9. Adjoining any finite family to a cover: the `R S : Presieve T` clause,
   with R covering, S finite, and `R ⊔ S` covering. Correct, including repeated
   arrows and the empty added family.
10. Finite scheme disjoint unions exist in D: `∀ I : Type v, [Finite I]`,
    `V : I → X.ProEt`, `hqc`, and `hqs`, followed by W, coprojections ι,
    and `e : (∐ fun i ↦ (V i).left) ≅ W.left`. Compatibility with every
    `Sigma.ι` identifies exactly the scheme coprojections. W is qcqs.
    These data give the coproduct universal property over X, and hence
    in the full subcategory D. Correct; no alternative union notion.
11. Affineness for affine summands: `(∀ i, IsAffine (V i).left) → IsAffine W.left`.
    Correct, only conditional on affineness of every summand.
12. Subcanonicality of C: `(topology X).Subcanonical`. Read Mathlib's
    `ProEt.instSubcanonicalTopology` and
    `GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable`:
    precisely every represented Hom_X(-,V) is a sheaf. Correct.
13. Canonical sheaf coproduct comparison is an isomorphism: the `IsColimit`
    witness for the cofan with maps `uliftYoneda.map (ι i)` asserts its
    coproduct universal property; the following `∀ c hc, IsIso (hc.desc ...)`
    identifies the canonical map from any chosen coproduct. These clauses
    express the same comparison with the same coprojections. Correct.
14. Sections over the union are the product of sections: `∀ F, Function.Bijective`
    for `s ↦ fun i ↦ F.obj.map (ι i).op s`. Naturality is the following
    equation for every `η : F ⟶ G`, s, and i. Correct, with W and ι chosen
    before F, so the union is independent of the sheaf.
15. Empty family: `IsEmpty I → IsEmpty W.left ∧ ∀ F, Nonempty (Unique ...)`.
    Correct: the scheme is empty and the section set a singleton.
16. Size convention: explicit `universe u v w`, `Scheme.{u}`, finite
    `I : Type v`, and coefficient sets `Type (max (u + 1) w)`.
    Finite indices are small in every required universe, so the independent
    index universe introduces no infinite-limit size problem. Read
    `uliftYoneda`: it is the representable sheaf followed by universe lifting,
    not a different representable. All universes and variables are bound.

Source reading: Stacks proetale.tex, lines 2332ff (098M), 2748ff (098Z),
2925ff (0F4P), and 2998ff (09A1), especially the full qcqs finite-cover
subcategory paragraph in the proof of (2); hypercovering.tex, lines 2947ff
and 2982ff (the two take-unions remarks). The base is only a scheme; no
ambient Noetherian or characteristic assumptions occur. The disjoint-union
paragraph obtains the product formula for every pro-etale sheaf. The finite
case keeps scheme disjoint unions qcqs and affine for affine summands.
The dependency signatures `qcqs_site_limits` and `finite_coproduct_evaluation`
were read in their actual side-library modules, not inferred from their names.
The 51-module framework provenance and isolation instructions were read in
`coord/pefw-upstream-framework.md`; no replacement framework objects are used.

Edge cases: empty X is allowed; X need not be qcqs; the slice terminal object
is T, not X. Empty I is allowed (no `Nonempty I` binder), including the empty
affine scheme and singleton sections. Zero rings are permitted by `Scheme`
and `IsAffine`. There is no integer n or characteristic parameter to restrict.
All finite cardinalities and all permitted coefficient universes are covered.

Independent searches (2026-10-15):

- LeanFinder via msearch: "Finite disjoint unions of quasi compact quasi
  separated weakly etale schemes and sheaf sections": eight hits on finite
  morphisms and affine transition limits, none the aggregate statement.
- Loogle via msearch: `"ProEt"`: twelve hits, including the full-site finite
  limits and topology definitions; none the qcqs aggregate theorem.
- LeanSearch via msearch: "The finite cover site of quasi compact quasi
  separated pro etale schemes has pullbacks and finite disjoint unions":
  unavailable (Internal Server Error); no verdict drawn from that service.
- Direct rg in Mathlib, upstream WeilConjectures, the exact side framework,
  lean/Sheaf, and the upstream declaration index for
  `qcqs_finite_family_geometry|qcqs_site_limits|finite_coproduct_evaluation|qcqsObjects`:
  only the existing side dependencies match; no aggregate declaration.
- Broader rg for `coproduct|coprod|disjoint|QuasiSeparated|CompactSpace` in
  Mathlib AlgebraicGeometry/Sites and Limits, upstream geometric extensions,
  and the side pro-etale module-object framework finds the scheme coproduct
  ingredients and framework operations, not this aggregate statement.

No new definition nodes or dependency modules were delivered, and there is
no statement correction requiring a citer audit. The module contains one
named theorem with a sorry proof, no hollow definitions, local notation,
private copies, or proofs. Its source and blueprint docstrings carry all
four node proof steps. The recorded lean.statement was checked verbatim
against the source signature. Validation and delivery follow below.

Second-reader validation: scompile.py compiled the delivered module in 1.6 s
and its three side-only dependencies separately in 1.4, 1.4, and 1.5 s,
with nice 19, two threads, and a 60-second per-file limit, with no errors or
warnings. An initial SSH connection closed before compilation; the retry passed.


## Second reading by NL

Fresh independent review against the node JSON, sandbox theorem, recorded dependency
signatures, and Stacks proetale.tex 098M, 098Z, 0F4P, 09A1 and hypercovering.tex
0DB1. The source assumes only a scheme, with no ambient finiteness hypothesis.
No mathematical mismatch found; no Lean or node change needed. The earlier second
reading remains historical; this section records this delivery's fresh review.

Object/hypothesis/conclusion checklist (each verdict: correct):

1. Arbitrary base scheme: `(X : Scheme.{u})`. No Noetherian, characteristic,
   compactness or nonempty assumption.
2. Small pro-etale site: `X.ProEt`, `topology X`; read `Scheme.ProEt`,
   `ProEt.forget`, `precoverage`, and subcanonical instance in pinned Mathlib,
   and `proEtaleDerivedCategory` in its recorded module. Objects are weakly
   etale maps and arrows are maps over X.
3. Full qcqs category and finite covers: `Qcqs X`, `qcqsInclusion X`,
   `qcqsPrecoverage X`. Opened their actual Subsite module: compact and
   quasi-separated source schemes, full inclusion, comapped covers intersected
   with finite presieves. No private substitute.
4. Every affine object qcqs: first universal implication, `IsAffine V.left`
   implies `CompactSpace V.left ∧ QuasiSeparatedSpace V.left`.
5. Site and fibre products: existential `HasPullbacks`, `Pretopology`, and
   equality `J.toPrecoverage = qcqsPrecoverage X`. Precisely those covers.
6. Fibre products computed in schemes and preserved in the full site: both
   `PreservesLimitsOfShape WalkingCospan` clauses, the second for the composite
   to schemes. Covers are sent to covers by the explicit `R.map` implication.
7. Every slice has finite limits: `∀ T, HasFiniteLimits (Over T)`; agreement
   with the full slice is `PreservesFiniteLimits (Over.post ... qcqsInclusion)`.
   The further composite through `Over.iteratedSliceForward` computes these
   as limits of schemes over T. Opened `qcqs_site_limits`: its actual signature
   supplies the latter; full-slice agreement is justified by the same universal
   properties, as the docstring explicitly explains.
8. Adjoining a finite family: `R` covering and `S ∈ Precoverage.finite` imply
   `R ⊔ S` covering. Repetitions do not change the presieve or cover property.
9. Finite disjoint unions: `∀ I : Type v, [Finite I]`, `V : I → X.ProEt`,
   `hqc`, `hqs`; W and coprojections precede all sheaves. The scheme coproduct
   isomorphism e and its compatibility with `Sigma.ι` give the scheme union,
   also a coproduct over X and in the full qcqs subcategory. Compactness and
   quasi-separatedness of W are explicit.
10. Affine union for affine summands: the conditional `∀ i, IsAffine ...` clause.
11. Subcanonical topology: `(topology X).Subcanonical`, exactly representable
    sheaves; `uliftYoneda` uses the same representables at the coefficient size.
12. Canonical coproduct comparison: `Nonempty (IsColimit (Cofan.mk ...))` for
    those coprojections, and `IsIso (hc.desc ...)` from any chosen coproduct.
13. Sections are the product: `Function.Bijective` of restriction along ι;
    naturality in every sheaf morphism η is the next displayed equation.
14. Empty family: `IsEmpty I → IsEmpty W.left` and `Nonempty (Unique ...)`.
15. Universes: explicit u,v,w; finite I is small regardless of v, while
    coefficients live in `Type (max (u + 1) w)`, covering arbitrary large sets
    and the raised representables. No object/morphism universe equality imposed.

Edge cases: empty X, non-qcqs X, empty affine scheme (zero ring), empty I,
empty additional family and every finite cardinality are included. The terminal
object asserted is in the slice over T, not the unsliced category over X.
There is no degree n or characteristic restriction. All binders are explicit.

Independent searches this round: LeanFinder via msearch with “Finite disjoint
union of weakly etale quasi compact quasi separated schemes represents a
coproduct of sheaves” returned eight scheme coproduct/extensivity ingredients,
not the aggregate statement. Loogle `"ProEt"` returned twelve site declarations,
not this statement. Direct rg for `qcqs_finite_family_geometry|qcqs_site_limits|
finite_coproduct_evaluation|qcqsObjects` in pinned Mathlib, slopmaster2
WeilConjectures, the exact side WeilConjectures framework and side Sheaf found
only the recorded component dependencies, no aggregate theorem. Read framework
provenance in coord/pefw-upstream-framework.md. No additional definition or
unusable dependency interface needs repair. No new nodes, dependency modules,
or statement_change occur, so no correction/citer audit is required.

The module has one named theorem, proof sorry, no definitions, hidden assumptions
or proved helper. Source/blueprint docstrings contain all four proof steps.
The node's lean.statement equals the file signature verbatim (checked directly).
Fresh server scompile passed the module in 1.5 seconds and the three side-only
imports separately in 1.3, 1.4 and 1.5 seconds: nice 19, two threads, limit 60
seconds per file, no errors or unexpected warnings. Second reading changed only
this report.
