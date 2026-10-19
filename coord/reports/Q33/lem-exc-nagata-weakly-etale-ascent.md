## Worker report

The module `Sheaf.RingTheory.NagataOfWeaklyEtale` states
`RingHom.isNagataRing_of_weaklyEtale`, with its entire proof postponed by one `sorry`.
The node is unchanged except for its `lean` record. No definitions or additional
DAG statements are introduced.

The source was opened and read: Greco, *Two theorems on excellent rings*,
Nagoya Math. J. 60 (1976), Remark 5.7(ii), printed p. 148,
https://scispace.com/pdf/two-theorems-on-excellent-rings-2lc74dyy3w.pdf.
It states Nagata preservation for absolutely flat homomorphisms. Remark 5.2,
printed p. 146, identifies this with base flatness and flatness of tensor
multiplication in the Noetherian setting. The foreword assumes commutative
Noetherian rings; Noetherianity of A follows from `hA`, and that of B is explicit.

Every hypothesis and clause is rendered as follows:

- The commutative rings A and B are `{A : Type u} {B : Type v}` with
  `[CommRing A] [CommRing B]`. The two universes are explicitly declared and
  independent, so the statement includes differently sized rings.
- A is Nagata is precisely `(hA : IsNagataRing A)`. This definition includes
  Noetherianity and the Japanese condition for every prime quotient.
- B is Noetherian is precisely `[IsNoetherianRing B]`.
- The given ring map is explicitly `(f : A →+* B)`, rather than a chosen
  auxiliary map. Its induced algebra structure is the actual `f.toAlgebra`.
- Weak etaleness is `(hf : @Algebra.WeaklyEtale A B _ _ f.toAlgebra)`.
  The explicit instance argument ties the hypothesis to exactly f; it means
  flatness over A and flatness of multiplication on B tensor_A B. No algebra
  structure independent of f is assumed.
- The conclusion is exactly `IsNagataRing B`.
- The final exclusion of universal catenarity and J-2 assumptions is respected:
  neither appears among the binders. No finite presentation, finite type,
  finite degree, injectivity, surjectivity, locality or domain condition is added.

Statement dependencies were read, including the full declaration signatures
and docstrings:

- `def-weil-pbc-nagata-ring`: `Sheaf.RingTheory.NagataRing`,
  `IsNagataRing`. Its body is `IsNoetherianRing R` conjoined with N-2 for every
  prime quotient. The module uses the recorded declaration directly.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`; its defining abbreviation is `IsNoetherian R R`, and
  `isNoetherianRing_iff_ideal_fg` confirms the ideal formulation.
- `def-weil-pbc-ind-etale-algebra`: public import of the recorded module
  `Sheaf.RingTheory.IndPrincipalZariski`. This mixed record expressly reuses
  `Algebra.WeaklyEtale` from `Mathlib.RingTheory.Etale.Weakly`. I read its
  two flatness fields and the recorded spectrum equivalence
  `AlgebraicGeometry.weaklyEtale_SpecMap_algebraMap_iff` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`.
  The dependency's principal ind-Zariski, ind-etale and pro-affine-etale
  clauses are not hypotheses of this theorem; none is substituted for
  weak etaleness.

The theorem docstring reproduces all eight proof steps of the node, including
the finite normalization model, normality of the base-changed finite algebra,
minimality of its kernel in L, the normal product factor, and identification
with the integral closure. All recorded proof dependencies that have statements
are imported without `public`: JapaneseDomain, AffineChartBaseChangeIso,
NormalOfFlatNormalFibers, ReducedNormalIffIntegrallyClosedTotalFractions,
WeaklyEtaleField and the Mathlib integral-closure, Noetherian, localization,
minimal-prime, jointly-injective-localization and weakly-etale base-change
modules. Public imports are exactly the three statement dependency modules.

Edge cases checked before writing:

- B may be the zero ring: it has no prime ideals, so the prime-quotient
  Japanese condition is vacuous and B is Noetherian; the statement includes it.
- A may be zero: a unital f then forces B to be zero, also included.
- Neither ring is required to be a domain or local. Products and disconnected
  spectra are allowed, as is the identity map.
- The given f need not be faithfully flat: a localization or projection with
  empty fibres is included, and no spectrum surjectivity is assumed.
- No characteristic or separability condition on finite extensions tested in
  the Nagata definition is imposed. The proof considers arbitrary finite
  extensions, including inseparable ones; residue extensions may be infinite
  algebraic extensions.
- Independent ring universes introduce no vacuous test-algebra hypothesis.
  The weakly etale class itself accepts both universes, and the conclusion
  uses B's own recorded Nagata predicate.

Searches for an existing statement (all performed before writing):

- `msearch.py ... leanfinder "A weakly etale homomorphism from a Nagata ring
  to a Noetherian ring makes the target Nagata"`: eight hits, concerning
  finite type Noetherian algebras, etale maps, composition and smooth flatness;
  no Nagata ascent theorem.
- `msearch.py ... loogle "IsNagataRing, Algebra.WeaklyEtale"`: zero hits;
  unknown identifier IsNagataRing in the Mathlib search index.
- `msearch.py ... grep "Nagata|Japanese|WeaklyEtale" RingTheory`: six hits,
  the five weakly etale class/flatness/ULift occurrences and a historical
  credit for Nagata in NoetherNormalization; no Nagata predicate or ascent.
- `rg` over Mathlib/RingTheory, upstream WeilConjectures and project lean/Sheaf
  for `IsNagataRing`, Nagata/weak-etale combinations and the proposed theorem
  name: no exact theorem. The project's
  `RingHom.isNagataRing_and_jTwo_of_weaklyEtale` in
  `Sheaf.RingTheory.NagataJTwoOfWeaklyEtale` requires an extra J-2 hypothesis
  and has a conjunctive conclusion, so does not state this node.
  `LocallyNagataCatenaryOfWeaklyEtale` concerns a different local assertion.
- `grep -rn "lem-exc-nagata-weakly-etale-ascent"` over upstream
  WeilConjectures: no hits. Search of `dag/lean_names_upstream.json` for the
  proposed declaration and Nagata/weak-etale combinations: no hits.

No statement dispute, correction, new node, or dependency repair was needed.

Validation: `scompile.py Q33 lem-exc-nagata-weakly-etale-ascent` compiled the
delivered file cleanly, including both wrapper probes (2.1 s and 2.5 s). No
errors or warnings were emitted. The required `deliver2.py --no-push` dry run
is the final check. The independent second reader will write their own reading
section.


## Second reading by Q33

I independently read the shared node, the sandbox node and Lean module, all three
statement-dependency records, and the declarations those records expose. I also
read through `IsN2`, which occurs inside the Nagata definition. No mismatch was
found; I left the Lean module and node record unchanged and added this review.
There are no new nodes, dependency modules or statement corrections to audit.

The source for this item is Greco rather than a Stacks lemma. I opened the
linked PDF and checked the Foreword (printed p. 139), Definition 5.1 and
Remark 5.2 (p. 146), Theorem 5.3 and its proof (pp. 146–147), and Remark
5.7(ii) (p. 148). The Foreword supplies commutativity and Noetherianity for
both rings. Remark 5.7(ii) asserts Nagata ascent for AF homomorphisms;
Remark 5.2 identifies AF with flatness of the base map and tensor
multiplication. In particular, this item does not inherit the additional
J-2 hypothesis in Theorem 5.3(ii) or the catenarity hypothesis in 5.3(iii).
Source: [Greco PDF](https://scispace.com/pdf/two-theorems-on-excellent-rings-2lc74dyy3w.pdf).

For the definitions I independently opened the upstream Stacks `.tex`:
`algebra.tex`, labels `definition-nagata` (Tag 032R) and `definition-N`
(Tag 032F); `more-algebra.tex`, label `definition-weakly-etale` (Tag 092B)
and `lemma-absolutely-flat-over-field` (Tag 092Q). The latter is also the
source of the first proof step. The shared checkout does not contain the
Stacks source directory, so these were read from the Stacks project's
upstream repository:
[algebra.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex),
[more-algebra.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex).

My object/hypothesis/conclusion checklist, with verdicts:

1. Objects: arbitrary commutative rings A and B. Lean has `{A : Type u}`,
   `{B : Type v}`, `[CommRing A]`, `[CommRing B]`, with explicitly declared
   independent universes `u v`. PASS: neither ring is specialized to a field,
   domain, local ring or fixed universe.
2. Hypothesis: A is Nagata. Lean has `(hA : IsNagataRing A)`. I opened
   `Sheaf.RingTheory.NagataRing`: this is `IsNoetherianRing A` conjoined
   with `IsN2 (A ⧸ p) (FractionRing (A ⧸ p))` for every prime ideal p.
   I opened `Sheaf.RingTheory.JapaneseDomain`: `IsN2` requires finiteness
   of the integral closure for every finite field extension, with the
   composite A-algebra structure enforced by `IsScalarTower`. PASS: this
   is exactly the node's Nagata condition and supplies source
   Noetherianity of A without an additional instance binder.
3. Hypothesis: B is Noetherian. Lean has `[IsNoetherianRing B]`. In
   `Mathlib.RingTheory.Noetherian.Defs`, the abbreviation is
   `IsNoetherian B B`; `isNoetherianRing_iff_ideal_fg` equates it with
   finite generation of every ideal. PASS: exactly the recorded notion.
4. Object: the specified ring homomorphism f from A to B. Lean has
   `(f : A →+* B)`. PASS: this is a unital homomorphism between the
   two previously introduced rings, with no injectivity, locality or
   spectrum-surjectivity requirement.
5. Hypothesis: that f is weakly etale. Lean has
   `(hf : @Algebra.WeaklyEtale A B _ _ f.toAlgebra)`. I opened
   `Sheaf.RingTheory.IndPrincipalZariski` and its public upstream
   spectrum-comparison import, then Mathlib's `Algebra.WeaklyEtale`.
   Its fields are precisely `Module.Flat A B` and flatness of
   `Algebra.TensorProduct.lmul' A` for the given algebra structure.
   The explicit `f.toAlgebra` fixes that structure to f. PASS: neither
   an arbitrary independent algebra structure nor ind-etaleness replaces
   weak etaleness. The principal ind-Zariski predicate in the mixed
   dependency record is not used. The spectrum equivalence is read in
   `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`.
6. Conclusion: B is Nagata. Lean concludes `IsNagataRing B`. PASS: the
   entire global prime-quotient condition is asserted, not merely its
   localization at each prime.
7. Scope clause: no universal catenarity or J-2 assumption on A. There
   are no such binders, and no hidden extra typeclass instances on A or
   B beyond their ring structures and Noetherianity of B. PASS.
8. Quantifiers: for every A, B and f satisfying these hypotheses, the
   conclusion holds. All binders are universal, followed by precisely
   this conclusion. The placement of the proof arguments `hf` and `hA`
   introduces no dependency or existential choice. PASS.

Edge cases checked: B may be zero, whose spectrum is empty; its Nagata
prime-quotient clause is vacuous. If A is zero, unital f forces B to be
zero. No `Nontrivial`, `IsDomain`, local-ring or faithful-flatness binder
excludes these cases, products, disconnected spectra, localization maps,
identity maps or maps with empty fibres. The statement imposes no
characteristic, separability or finite-degree condition. In particular,
`IsN2` includes finite inseparable extensions, and `hf` does not assert
finite presentation or finite type. There is no index set or integer n
in this statement, so the empty-index and n = 0 checks introduce no
additional cases. Independent u and v cover differently sized rings;
there is no test-algebra quantification in an unrelated smaller
universe. Within `IsN2`, finite extensions are tested in the fraction
field's universe, which suffices since a finite-dimensional extension
has a model in that universe. No new universe equality is imposed by
the statement, and every variable and universe is explicitly bound.

Independent searches, using different conceptual queries from the worker:

- LeanFinder: `Noetherian universally Japanese rings remain universally
  Japanese under absolutely flat algebra homomorphisms`. Eight hits,
  concerning flatness, going down, finite type and smooth algebras;
  none is Nagata ascent.
- Loogle: `"Nagata"`. Zero hits.
- Mathlib grep through `msearch.py`: `universallyJapanese|IsN2|absolutelyFlat|Nagata`
  in RingTheory. The only hit is the historical attribution in
  NoetherNormalization; it does not state the result.
- LeanSearch: `If a ring homomorphism is weakly etale and its source is
  a Nagata ring and target is Noetherian then the target is Nagata`.
  Eight hits including RingHom.Etale and Noetherian range results;
  none has the requested hypotheses and conclusion.
- Direct `rg` in Mathlib, upstream WeilConjectures and project
  `lean/Sheaf`, for Nagata, Japanese, universally-Japanese,
  absolutely-flat variants, `IsNagataRing` and the proposed declaration
  name. I also checked `dag/lean_names_upstream.json`. No exact
  existing statement was found. I opened the tempting project
  `RingHom.isNagataRing_and_jTwo_of_weaklyEtale`: it assumes J-2 and
  concludes a conjunction, so does not replace this item. I also
  opened `LocallyNagataCatenaryOfWeaklyEtale`, which concerns local
  Nagata conditions and catenarity rather than this global assertion.

I checked the module/docstring conventions and all eight proof-plan
paragraphs against the DAG proof: field fibres; weakly-etale base
change and residue extensions; the finite field model; normalization
of A/p; normality of the finite base change; minimality of the map's
kernel; the normal product factor and its fraction field; and equality
with the finite integral closure. The module imports the recorded
statement dependencies publicly and the available proof dependencies
without `public`. There is one named theorem and one whole-proof
`sorry`, no data definition, axiom, private copy, local notation or
proved helper. Both docstrings carry the source and blueprint id;
all Lean lines meet the 100-character limit.

Validation: I independently ran the prescribed `scompile.py` on the
sole delivered module. Both wrapper checks passed cleanly (2.8 s
sandbox probe, 3.0 s library module), with no warnings or errors.
A separate textual check confirmed that `lean.statement` is verbatim
the theorem signature, that the file contains exactly one `sorry`,
and that no `statement_change` is present. The prescribed delivery
wrapper performs the final current-base preflight and compile.
