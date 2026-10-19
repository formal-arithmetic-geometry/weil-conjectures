## Worker report

The module `Sheaf.AlgebraicGeometry.NormalityPerfectClosureTest` states
`AlgebraicGeometry.normal_stalks_perfectClosure_iff` with a whole-proof `sorry`.
It defines no new notion. Read the source in `varieties.tex`,
`lemma-geometrically-normal` (Tag 038O), conditions (2) and (6), and in
`algebra.tex`, `lemma-perfection` (Tag 046W), including the characteristic-zero
case and uniqueness of the perfect purely inseparable overfield.

Hypotheses and clauses:

- Fields k and K: `(k K : Type u) [Field k] [Field K]`.
- The inclusion k into K: `[Algebra k K]`, with injective `algebraMap k K`.
- q is 1 in characteristic zero and p in characteristic p: `ringExpChar k`.
  Its definition is `max (ringChar k) 1`; the field instance makes it the
  exponential characteristic.
- Each a in K has a q-power iterate in k: `hpower` quantifies over `a : K`,
  `n : ℕ`, and `b : k`, with `algebraMap k K b = a ^ (ringExpChar k ^ n)`.
- K is perfect: `[PerfectField K]`. This is the Mathlib perfect-field class;
  for fields it is equivalent to surjectivity of positive-characteristic
  Frobenius (see `PerfectRing.toPerfectField` and `PerfectField.toPerfectRing`).
- An arbitrary k-scheme: `(T : Scheme.{u}) (f : T ⟶ Spec (CommRingCat.of k))`.
  The explicit structure morphism is used to form each base change.
- Clause (1): `∀ x : pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))), ...`.
  The conjunction is `IsDomain` and `IsIntegrallyClosed` of that scheme's
  `presheaf.stalk x`, exactly the prescribed normal-domain encoding.
- Equivalence: `↔`.
- Clause (2): `∀ (L : Type u) [Field L] [Algebra k L], ∀ x : pullback ...`,
  followed by the identical conjunction on the L-base-change stalk.
- No finite type, reducedness, nonemptiness, separatedness, or integrality
  hypothesis occurs. In particular `IsNormalScheme` from the project is not
  applicable: it additionally requires an integral scheme.

Dependencies read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` and `algebraMap`
  (def-pc-field-extension).
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Spec`, `Spec.map`
  (def-pc-scheme and def-weil-affine-spectrum).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`
  (def-pc-fibre-product); `Mathlib.AlgebraicGeometry.Pullbacks` supplies
  existence of scheme pullbacks.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  together with `IsDomain`, used inline as the record for
  def-weil-pbc-normal-ring prescribes. No dependency repair is needed.
- Proof-only imports: `Sheaf.FieldTheory.CommonExtensionFields`, declaration
  `Field.exists_common_extension`; `Sheaf.FieldTheory.SeparableExtension`,
  declarations `Algebra.IsSeparablyGenerated` and `Algebra.IsSeparableExtension`;
  `Mathlib.FieldTheory.SeparablyGenerated`, declaration
  `exists_isTranscendenceBasis_and_isSeparable_of_perfectField`;
  `Mathlib.AlgebraicGeometry.FunctionField`, including
  `functionField_isFractionRing_of_affine` and the imported
  `StructureSheaf.IsLocalization.to_stalk`; and
  `Mathlib.RingTheory.TensorProduct.Basic`, for `TensorProduct`.
- The proof dependencies lem-weil-pbc-normal-algebra-separable-scalar-extension
  and lem-weil-pbc-normal-ring-field-extension-descent have no recorded Lean
  declaration, so their future modules cannot yet be imported. They are named
  in the proof docstring. This does not affect the statement dependencies.

Edge cases checked: the empty scheme gives vacuous stalk conditions on both
sides; disconnected schemes are included since no integral-scheme predicate is
used; n = 0 is allowed; in characteristic zero q = 1 and hpower forces every
K-element into the image of k; in characteristic p the stated Frobenius
perfectness has its usual meaning. Nonreduced schemes are not excluded as
inputs. The universe u is arbitrary and is shared by the fields and schemes,
so test fields are not quantified in an independent smaller universe. Every
field extension and scheme can be placed in a common universe; smaller ones
can be lifted. No cardinal bound such as finite or countable is imposed.

Searches made:

- `msearch.py leanfinder`: "A scheme is geometrically normal if its base change
  to a perfect purely inseparable extension is normal". Eight hits, all about
  scheme normalization morphisms; none states the criterion.
- `msearch.py loogle`: `"GeometricallyNormal", "PerfectField"`. Zero hits.
- `msearch.py grep`: `geometricallyNormal|geometrically_normal|normal.*perfect`.
  Eight unrelated group-theoretic/topological hits, no match.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` with the same
  criterion patterns and the item id. No existing scheme criterion. The
  project `Algebra.normal_tensor_perfectClosure_iff` in
  `Sheaf.RingTheory.GeometricallyNormalPerfectClosureCriterion` was read in
  full: it concerns prime localizations of scalar-extended algebras, not the
  arbitrary-scheme stalk criterion, so it is not an exact existing match.
- Read the existing normal-scheme definition in
  `Sheaf.AlgebraicGeometry.NormalScheme`: its integral-scheme conjunct makes
  it unsuitable here, as the empty and disconnected cases show.

No statement correction, new nodes, dependency modules, or disputed statement.

Validation: scompile.py compiled the delivered module cleanly on the server
(nice 19, two threads, 60 seconds per file; elapsed 1.3 seconds).

## Second reading by NH

I independently read the delivered node, its six proof steps, its Lean module,
all statement-dependency records, the declarations behind those records, and
Stacks varieties.tex, lemma-geometrically-normal (038O), together with
algebra.tex, lemma-perfection (046W). The source assumes only a field and a
scheme over it; (2) and (6) impose no finite-type or separatedness condition.
046W identifies the perfect purely inseparable extension with the perfect closure.

Item-by-item statement inventory and verdict:

- Base field k and overfield K: `(k K : Type u) [Field k] [Field K]`.
  Mathlib `Field` extends `CommRing` and `DivisionRing`, including nontriviality.
  Verdict: exactly the node's fields, not rings or algebraically closed fields.
- Inclusion k into K: `[Algebra k K]` and `algebraMap k K`.
  I opened `Algebra` in Mathlib.Algebra.Algebra.Defs: it supplies a unital ring
  homomorphism, injective for fields. This is precisely the recorded
  def-pc-field-extension encoding. Verdict: exact, no extra structure hypothesis.
- Exponential characteristic q: `ringExpChar k` is `max (ringChar k) 1`.
  Verdict: 1 in characteristic zero and p in characteristic p, as required.
- Pure inseparability: `hpower : ∀ a : K, ∃ n : ℕ, ∃ b : k,
  algebraMap k K b = a ^ (ringExpChar k ^ n)`.
  Verdict: every element has some iterated q-power in k; n may depend on a,
  with no uniform exponent, finiteness, or algebraicity assumption added.
- Perfectness of K: `[PerfectField K]`. I opened the class and both
  `PerfectRing.toPerfectField` and `PerfectField.toPerfectRing`. Its irreducible-
  polynomial definition is equivalent to the source's Frobenius condition for
  fields in positive characteristic, and is automatic in characteristic zero.
  Verdict: exact.
- Arbitrary k-scheme T: `(T : Scheme.{u}) (f : T ⟶ Spec (CommRingCat.of k))`.
  I opened `Scheme`, `Spec`, and `Spec.map` in Mathlib.AlgebraicGeometry.Scheme.
  Verdict: the actual scheme and its structure map, with no extra property.
- Base change T_K: `pullback f (Spec.map (CommRingCat.ofHom
  (algebraMap k K)))`. I opened the recorded `pullback` abbreviation and the
  scheme `HasPullbacks` instance. The Spec map points from Spec K to Spec k.
  Verdict: the required fibre product, not an arbitrary scheme or tensor object.
- Clause (1): universal x in T_K, followed by `IsDomain (T_K.presheaf.stalk x)`
  and `IsIntegrallyClosed (T_K.presheaf.stalk x)`. I opened `IsIntegrallyClosed`,
  defined using the fraction ring. This is the recorded normal-domain encoding
  of def-weil-pbc-normal-ring. Verdict: every local ring is an integrally closed
  domain; no global integral-scheme condition is introduced.
- Equivalence: `↔`. Verdict: both directions, in the node's order.
- Clause (2): `∀ (L : Type u) [Field L] [Algebra k L], ∀ x : pullback ...`,
  with the same two stalk predicates after replacing K by L.
  Verdict: every extension precedes every point, with no separability,
  perfectness, algebraicity, finite generation, or embedding into K required of L.

Edge cases: the empty scheme has no points after either base change and both
conditions are vacuous. Disconnected schemes are included; each stalk, rather
than a global coordinate ring, must be a domain. Nonreduced inputs are allowed,
although normality can fail. The zero ring is not a field and is correctly
excluded from k, K, and L; the empty affine scheme Spec(0) remains included.
For n = 0, the exponent is 1. In characteristic zero every exponent is 1 and
hpower makes k → K surjective. Positive characteristic permits every prime p.
The arbitrary shared universe u contains the schemes and all fields under
consideration; the test-field universe is not independent and smaller than the
base. Any given set of these objects can be placed in a common universe, and no
finite or countable cardinality bound is imposed. There is no index-set condition.

Independent duplicate searches, using different words from the first reader:

- `msearch.py leanfinder`: "All local rings remain integrally closed after
  arbitrary scalar extension if they do after perfection of the base field".
  Eight hits, about integral closure of rings/localizations or normal closures
  of field extensions; none is the scheme criterion.
- `msearch.py loogle`: `"IsIntegrallyClosed", "pullback"`: zero hits.
- `msearch.py grep`: `normal_stalks|normal.*baseChange|normal.*perfection|IsNormalScheme`:
  zero indexed hits. Direct rg of project Sheaf and upstream WeilConjectures
  and Mathlib algebraic geometry additionally used
  `geometric.*normal|normal.*perfect|perfect.*normal`.
- `msearch.py leansearch`: "Normality of every stalk after base change to a
  perfect closure implies geometric normality of a scheme": service unavailable
  (Internal Server Error), recorded as unavailable, with no mathematical verdict.
- I opened the project's `Algebra.normal_tensor_perfectClosure_iff`: its
  prime-localization statement concerns scalar extensions of one algebra,
  not all stalks of an arbitrary scheme, so it is not an existing match.
  I also opened `IsNormalScheme`: its `IsIntegral` conjunct excludes empty
  and disconnected cases and cannot replace the node's stalkwise conjunction.
  No duplicate declaration of the delivered theorem was found.

There are no new definition nodes, dependency modules, statement corrections,
or disputed statements in this delivery. All five statement dependencies supply
exactly the notions used; no private or hollow substitute was introduced.
I also opened the proof-only common-extension and separable-extension modules,
the separating-basis theorem, the Spec-stalk localization instance, and the
fraction-field instance. The two unstated normality ascent/descent dependencies
cannot yet be imported and remain explicitly named in the six-step docstring.
The available proof dependencies are imported without `public` as required.
The module and theorem docstrings have the source and blueprint tag; the proof
reproduces all six node steps, including affine coverage, tensor associativity,
and descent. The only proof is a whole-theorem `sorry`; no new fact is proved.
Every variable and universe is bound, no local notation or local instance occurs,
and all lines are at most 100 characters.

Mismatches found: none. I left the Lean module and node unchanged and appended
this independent reading. The node's `lean.statement` was checked byte-for-byte
against the multiline signature in the delivered file and agrees.

Validation: scompile.py compiled the delivered module cleanly on the server,
nice 19, two threads, 60 seconds per file, elapsed 1.3 seconds. No errors or
warnings were emitted.
