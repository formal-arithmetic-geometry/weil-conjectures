## Worker report

The module `Sheaf.Paper.FiniteCtfTriangulated` states
`AlgebraicGeometry.Scheme.finite_ctf_isTriangulated` with a single `sorry` proof.
No definition is introduced, no dependency record is changed, and the node's statement
is unchanged. Source read: `literature/stacks-project/sites-cohomology.tex`, lines
12565–12589, label `lemma-cone-tor-amplitude`, Tag 08G2, especially clause (2) and its
long-exact-sequence proof hint. The theorem docstring transcribes all six DAG proof steps.

Hypothesis and clause correspondence:

- The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`.
- The valuation ring and chosen uniformizer are precisely the recorded
  `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionUniformizer` used
  inside `Padic.coefficientExtensionRing l E n`. No alternative quotient or ring is used.
- The positive integer level is `(n : ℕ) (hn : 1 ≤ n)`; the arbitrary scheme is
  `(Y : Scheme.{u})`. No base field, finite-type, separation, or characteristic hypothesis
  is added. In particular no global finite-field datum is required.
- The ambient category in every clause is
  `proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n)`, on the small
  pro-etale site, with the recorded module sheaf encoding.
- The property P is the infimum of `intrinsicFiniteTorsionConstructible l E n hn Y`
  and `fun K ↦ HasFiniteProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) K`.
  ObjectProperty infimum is pointwise conjunction. The first factor is exactly finitely
  many nonzero cohomologies with every cohomology constructible; the second is existence
  of one ordered Tor interval for all degree-zero test sheaves.
- Isomorphism closure is the first conjunct `ObjectProperty.IsClosedUnderIsomorphisms`.
- Full triangulated closure is the second conjunct `ObjectProperty.IsTriangulated`.
  Its fields are `ContainsZero`, `IsStableUnderShift ℤ`, and `IsTriangulatedClosed₂`.
  Thus it includes the zero clause and all shifts. Together with isomorphism closure,
  shifting back by `-m` yields the stated iff, and the middle-term field gives literal
  membership for a distinguished triangle. Mathlib supplies the full subcategory,
  inherited triangulated structure, and exact inclusion from these classes.
- The third conjunct explicitly states the fixed-interval implication for every K and
  all `(a b m : ℤ)`: amplitude `[a,b]` implies amplitude `[a-m,b-m]` of `K⟦m⟧`.
  The amplitude predicate itself includes `a ≤ b`, so no ordering is lost.
- The fourth conjunct quantifies over every triangle T and `(a b : ℤ)` with
  `T ∈ distTriang _`, assumes amplitude `[a,b]` for `T.obj₁` and `T.obj₃`, and concludes
  that same interval for `T.obj₂`. This retains the node's parenthetical bound as well
  as its finite-amplitude extension clause.

Dependency declarations read and reused:

- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`,
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`: exact intrinsic
  bounded-constructibility predicate without the unused global datum.
- `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`,
  `AlgebraicGeometry.Scheme.proEtale_bounded_constructible_isTriangulated`:
  isomorphism and triangulated closure for finite coefficients (proof import).
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`,
  `AlgebraicGeometry.Scheme.HasProEtaleTorAmplitude` and
  `AlgebraicGeometry.Scheme.HasFiniteProEtaleTorAmplitude`: universal K-flat
  representative test and existential ordered interval; both used directly.
- `Mathlib.CategoryTheory.Triangulated.Subcategory`,
  `CategoryTheory.ObjectProperty.IsTriangulated`, read at lines 180–184 and its
  neighboring middle-term/infimum interfaces; the ambient derived category is triangulated.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, and its imported
  `Sheaf.NumberTheory.Padics.CoefficientExtension`,
  `Padic.coefficientExtensionRing`: positive-level finiteness and the actual quotient.
  The coefficient construction's full definitions and docstrings were read.

Stated proof-dependency modules are imported, including the valued quotient Mathlib
module and derived homology sequence module. The exact derived tensor/projection-mate
node has no recorded Lean declaration, so no nonexistent proof import is added; it is
only needed to prove this theorem in stage 3, not to type its statement.

Edge cases checked: zero satisfies both predicates (Tor interval `[0,0]`); the empty
scheme is allowed; level `n=1` is allowed and `n=0` excluded exactly as in the node;
zero, positive, and negative shifts are all quantified over ℤ, with the cohomological
minus sign; degenerate ordered intervals `a=b` are allowed; reversed intervals make
`HasProEtaleTorAmplitude` false by its ordering conjunct. Distinguished triangles are
arbitrary, including zero vertices. The coefficient field and scheme share the recorded
size universe, which can be chosen large enough for both, without identifying the small
site's object universe `u+1` and morphism universe `u`.

Searches actually run:

- msearch leanfinder: "Bounded constructible pro-etale sheaf complexes with finite Tor
  amplitude form a triangulated subcategory". Eight results, including derived
  t-structure bounds and acyclic homotopy subcategory; no matching pro-etale theorem.
- msearch loogle: `ObjectProperty.IsTriangulated`. Zero results, unknown identifier.
- msearch grep: `HasFiniteProEtaleTorAmplitude|HasProEtaleTorAmplitude`. Zero Mathlib hits.
- msearch leansearch: "Finite Tor amplitude bounded constructible complexes form a
  triangulated subcategory". UNAVAILABLE, Internal Server Error; not a negative result.
- rg of `finiteCTF|FiniteCTF|finiteCtf|finite_ctf|TorAmplitude|torAmplitude|` followed
  by the item id in upstream WeilConjectures and project lean/Sheaf: found the recorded
  pro-etale Tor predicates and unrelated ring/etale Tor results; no exact theorem.
  The upstream etale statements use a different site and cannot be attached here.

No STATEMENT-DISPUTED issue or node fault was found. No independent second reading
has been claimed; the dispatcher supplies that reader after this worker returns.

Validation: `scompile.py NB lem-weil-finite-ctf-triangulated` passed both sandbox and
library-path compilation cleanly (2.4 s and 2.5 s). The first attempt exposed the missing
`CategoryTheory.Pretriangulated` namespace opening for `Triangle`; this was repaired.
The upstream name inventory was also searched for the item, its chosen theorem name,
and `HasFiniteProEtaleTorAmplitude`, with no matching existing theorem.

## Second reading by NB

I independently read the node, its five statement-dependency nodes and recorded Lean
interfaces, the delivered module, and Stacks sites-cohomology.tex at
`definition-tor-amplitude` (12377 onward) and `lemma-cone-tor-amplitude`
(12566 onward). The source assumes only a ringed site, arbitrary distinguished
triangles, and ordered integer intervals. It adds no geometric or characteristic
hypothesis. No statement correction, new node, or dependency module is present.

Object/hypothesis/conclusion list extracted from the node and matched with Lean:

1. Prime ell: `(l : ℕ) [Fact l.Prime]`. Exact.
2. Finite extension E/Q_ell: `(E : Type u) [Field E] [Algebra (Padic l) E]
   [FiniteDimensional (Padic l) E]`. Exact, with no extra valuation/topology datum.
3. Valuation ring, chosen uniformizer, and quotient A: every occurrence uses
   `Padic.coefficientExtensionRing l E n`. I opened CoefficientExtension.lean:
   it is the spectral valuation integer ring modulo the nth power of the ideal
   generated by the recorded chosen uniformizer. CoefficientExtensionFinite.lean
   supplies positive-level finiteness. Exact recorded construction.
4. Positive integer n: `(n : ℕ) (hn : 1 ≤ n)`. Exact.
5. Arbitrary scheme Y: `(Y : Scheme.{u})`. No Noetherian, finite-type, separation,
   base field, or invertibility instance is assumed. Exact.
6. Ambient category: `proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n)`.
   I opened the abbreviation: the standard derived category of SheafOfModules over
   the constant commutative ring sheaf, forgotten to rings, with ULift of A.
   Its small site's object universe u+1 and morphism universe u remain distinct.
   It is neither the etale nor the condensed coefficient category. Exact.
7. D^b_c membership: `intrinsicFiniteTorsionConstructible l E n hn Y`. I opened
   the definition: finite support of nonzero homology, with every homology sheaf
   constructible. The intrinsic interface removes only unused global-datum
   parameters. IsConstructibleProEtaleModuleSheaf uses finite locally closed
   constructible strata, locally constant restrictions, and finite geometric stalks.
   I followed LocallyClosedStratification to upstream Topology.Stratification:
   `isConstructible_stratum` is inherited, despite the scheme wrapper's obsolete
   docstring saying no constructibility is imposed. Exact.
8. Finite Tor amplitude: `fun K ↦ HasFiniteProEtaleTorAmplitude Y ... K`.
   I opened both Tor predicates and derivedTensor: one ordered interval works for
   all degree-zero module sheaves, on every K-flat resolution of representatives
   isomorphic to K. The tensor is the actual total tensor complex. Exact recorded
   dependency, with no private replacement.
9. P is the conjunction of 7 and 8: pointwise infimum `⊓`. Exact.
10. Isomorphism closure: first conjunct `ObjectProperty.IsClosedUnderIsomorphisms`.
    Exact.
11. Full triangulated subcategory, including zero and extension closure: second
    conjunct `ObjectProperty.IsTriangulated`. I read Mathlib's class, extending
    ContainsZero, IsStableUnderShift ℤ, IsTriangulatedClosed₂. Zero and middle
    terms initially belong up to isomorphism; conjunct 1 makes membership literal.
    The full subcategory inherits its shifts, distinguished triangles, and exact
    inclusion from this API. Exact.
12. P(K) iff P(K[m]) for every integer m: shift stability gives the forward
    implication; shift by -m and isomorphism closure give the converse. Exact.
13. Interval [a,b] shifts to [a-m,b-m]: third conjunct quantifies all K and all
    `(a b m : ℤ)` and states exactly that implication. The minus sign agrees
    with H^i(K[m]) = H^(i+m)(K). Exact.
14. Every distinguished K -> L -> M -> K[1] with P(K), P(M) has P(L): the
    IsTriangulatedClosed₂ field above, plus isomorphism closure. Exact.
15. Common interval [a,b] is retained for L: fourth conjunct quantifies every
    triangle T and a,b, assumes `T ∈ distTriang _` and amplitude for T.obj₁ and
    T.obj₃, and concludes that same interval for T.obj₂. This is source clause (2).

Edge cases: n=0 is excluded exactly by hn; n=1 is included. All primes, including
2, and all scheme characteristics are allowed; no ell-invertibility is assumed.
Zero has interval [0,0]; arbitrary triangles with zero vertices are allowed.
The empty scheme is allowed (a one-stratum empty partition meets the positive
stratum-count convention). There is no index-set binder. All integer shifts,
including zero and negative shifts, and intervals a=b occur. Reversed intervals
have false amplitude premise. The shared scheme/coefficient size follows the
recorded API; finite E/Q_ell is small up to algebra equivalence, so no mathematical
extension is lost. No small-site universe equality is added. Every variable and
universe u is explicitly bound.

Independent duplicate searches, using different wording from the worker:

- msearch leanfinder: "Finite Tor dimension closed under suspension and distinguished
  triangle extensions" returned eight t-structure/degree-bound declarations, no
  exact pro-etale constructible finite-Tor triangulated statement.
- msearch loogle: `"TorAmplitude"` returned zero hits.
- rg over upstream WeilConjectures, all Mathlib, and project lean/Sheaf with
  `finite_ctf|[Ff]inite[Cc][Tt][Ff]|[Tt]or.?[Aa]mplitude|tor.?dimension` found abstract
  monoidal derived-category APIs, module/etale results, and recorded pro-etale
  predicates; no exact statement. I opened upstream DerivedCategory/TorAmplitude:
  it requires a monoidal-derived framework and does not state this conjunction
  or the recorded representative predicate, so it is not an exact attachment.
- Read coord/pefw-upstream-framework.md and searched the exact side-clone
  finite-coefficient framework and ModuleObject/Derived/BoundedConstructible.lean
  for ctf, IsTriangulated, torAmplitude: no matching declaration. No implicit
  comparison with the module-object/condensed categories is used.

No mathematical mismatch was found; the Lean file is unchanged. One metadata
mismatch was repaired: lean.statement had collapsed whitespace; it now contains
the signature verbatim, including its line breaks. No node mathematics changed.
There is a single named sorry theorem, no new or hollow definition, no hollow
hypothesis, no local notation/instance, and all six proof-plan steps appear in
its source/blueprint docstring. The unavailable projection-mate theorem is solely
a stage-3 proof dependency, not needed to type this statement.

Validation: prescribed scompile.py from the sandbox passed both sandbox (2.2 s)
and library-path (2.4 s) compilation, with no errors or warnings. An initial
invocation from the clone failed to find the sandbox-relative file and was
rerun from the correct directory; it made no changes.
