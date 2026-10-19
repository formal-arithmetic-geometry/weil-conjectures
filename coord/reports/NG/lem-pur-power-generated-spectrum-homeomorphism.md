## Worker report

The module `Sheaf.RingTheory.PowerGeneratedSpectrumHomeomorphism` states
`AlgebraicGeometry.universally_isHomeomorph_specMap_of_power_generated` with a sorry proof.
The node is unchanged except for `lean`. No new nodes, dependency modules, or statement
corrections are needed. Read Stacks Algebra, Tag 0BRA, lemma-p-ring-map, including its proof
at algebra.tex lines 10868–10909. The node selects the universal-homeomorphism and
base-change assertions; it does not assert the source's additional residue-field clause.

Hypothesis and conclusion correspondence:

- Commutative rings and the map φ: `{R B : Type u} [CommRing R] [CommRing B]
  [Algebra R B]`. The map is `algebraMap R B`. This is the standard recorded encoding
  of a ring map: every commutative-ring homomorphism supplies this algebra structure
  through `RingHom.toAlgebra`; no extra property of φ is required.
- Prime integer p: `(p : ℕ) (hp : p.Prime)`, identifying positive integer primes with
  natural primes. No characteristic assumption is imposed.
- Every kernel element is nilpotent: `hker : ∀ r : R, algebraMap R B r = 0 → IsNilpotent r`.
  There is no uniform exponent requirement.
- Generation as an R-algebra: `(s : Set B) (hgen : Algebra.adjoin R s = ⊤)`. Giving an
  arbitrary witnessing set as a binder expresses the node's generation hypothesis;
  it does not require finiteness or special generators.
- For each generator, one common positive exponent for both conditions: `hpow` quantifies
  `∀ x ∈ s, ∃ n : ℕ, 0 < n ∧ ...`, with `x ^ (p ^ n)` and `(p ^ n : B) * x` in
  `(algebraMap R B).range`. Multiplication by the natural-number cast is precisely
  integer multiplication by the positive integer p^n.
- Universal homeomorphism of the induced scheme morphism: the first conjunction is
  `(topologically IsHomeomorph).universally
  (Spec.map (CommRingCat.ofHom (algebraMap R B)))`. This quantifies arbitrary scheme
  pullback squares, rather than just affine base changes.
- Every commutative R-algebra R': `∀ (R' : Type (max u v)) [CommRing R'] [Algebra R R']`.
  The universe includes that of R and B and can be enlarged by v; it cannot make the
  test-algebra condition vacuous by restricting to a smaller independent universe.
- The base-change map is `algebraMap R' (R' ⊗[R] B)`, namely r' ↦ r' ⊗ 1.
- The same two hypotheses after base change are the conjunction of
  `∀ r : R', algebraMap R' (R' ⊗[R] B) r = 0 → IsNilpotent r` and existence of a set
  `s'` with `Algebra.adjoin R' s' = ⊤` whose elements satisfy the same two range
  conditions for a positive n and the same p.
- The final clause is `IsHomeomorph (PrimeSpectrum.comap
  (algebraMap R' (R' ⊗[R] B)))`, the actual contraction map on prime spectra.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.CategoryTheory.MorphismProperty.Limits`:
  `CategoryTheory.MorphismProperty.universally`; together with
  `Mathlib.AlgebraicGeometry.Morphisms.Constructors`, `AlgebraicGeometry.topologically`,
  and `Mathlib.Topology.Homeomorph.Defs`, `IsHomeomorph`.
- The algebra notion recorded by `def-weil-pbc-algebra-hom-quotient` is `[Algebra R B]`
  and its structure map. Read `AlgHom` in `Mathlib.Algebra.Algebra.Hom`.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: the recorded `TensorProduct` base-change
  carrier; read `LinearMap.baseChange` and its docstring. The tensor ring/algebra and
  canonical left map are from `Mathlib.RingTheory.TensorProduct.Basic`.
- `Mathlib.Algebra.Algebra.Subalgebra.Lattice`: existing `Algebra.adjoin`, the least
  subalgebra containing the set. No new notion is defined here.

Proof-only Mathlib imports retain the recorded proof plan:
`PrimeSpectrum.isHomeomorph_comap` in `Mathlib.RingTheory.Spectrum.Prime.Homeomorph`;
`AlgebraicGeometry.pullbackSpecIso` in `Mathlib.AlgebraicGeometry.Pullbacks`;
the `Surjective` base-change instance in `Mathlib.AlgebraicGeometry.PullbackCarrier`;
`PrimeSpectrum.zeroLocus_eq_iff` in `Mathlib.RingTheory.Spectrum.Prime.Topology`;
`Algebra.TensorProduct.productMap` in `Mathlib.RingTheory.TensorProduct.Maps`.
The addition-subring proof dependency has no recorded Lean module, so no import is
available yet; it is named in the proof docstring for stage 3.

Edge cases checked mathematically: s may be empty (then the algebra map is surjective);
R or B may be the zero ring, with the nil-kernel assumption forcing the appropriate
empty-spectrum behavior; base-change rings may be zero. Nilpotence is elementwise.
The characteristic may be zero, p, or different from p. Exponents are positive and
may vary by generator; the same exponent witnesses both conditions. Arbitrary scheme
base changes include the empty scheme. No nonemptiness or finite-generation assumption
is added. A shared ambient universe for the two starting rings permits both to be
placed in any common larger universe.

Searches for an existing exact declaration:

- `msearch.py leanfinder`: “A ring map with nil kernel generated by elements whose prime
  power and prime multiple lie in the image induces a universal homeomorphism”. Eight
  results, notably `PrimeSpectrum.isHomeomorph_comap`, its bijective and purely
  inseparable variants, and quotient-kernel results. The general result assumes powers
  for every element and gives only one homeomorphism, not this generator criterion or
  preservation of the two hypotheses. Field results restrict to fields.
- `msearch.py loogle`: `PrimeSpectrum.isHomeomorph_comap, Algebra.adjoin`: zero hits.
- `msearch.py grep`: `isHomeomorph_comap|power.*[Gg]enerat|universally.*IsHomeomorph`:
  25 hits; the spectrum results above and unrelated generated-power material, no match.
- `msearch.py leansearch`: “Ring map with nil kernel and prime power generators gives a
  universal homeomorphism”: service unavailable (Internal Server Error); recorded as
  unavailable, with no mathematical verdict attributed to that service.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for the node id,
  `powerGenerated|power_generated|isHomeomorph_comap|universally.*IsHomeomorph`:
  only uses of the all-element and field results, including DualNumbers,
  ProEtale/IntegralLocal, SepClosedTensorReduction and RadicialPrimeUniqueDegreeP;
  no exact statement. Searching the proposed declaration name in Mathlib, upstream,
  `dag/lean_names_upstream.json`, and project modules gave no collision.

Validation: server-only `scompile.py NG lem-pur-power-generated-spectrum-homeomorphism`
compiled the delivered module cleanly (1.4 seconds; nice 19, two threads, 60-second limit).
No local Lean invocation. No disputed statement or node fault was found.

## Second reading by NG

I independently opened the node, its delivered Lean module, all four statement-dependency
nodes and their recorded declarations, and Stacks algebra.tex, lemma-p-ring-map (Tag
0BRA), lines 10868–10909. The chapter conventions explicitly allow commutative rings
with 1 including the zero ring. There are no ambient characteristic, Noetherian,
nonzero, or finiteness hypotheses. The source additionally discusses residue fields;
that is not a conclusion of this DAG node and is correctly absent here.

Object/hypothesis/conclusion checklist, in node order:

1. Commutative rings R and B and a ring map φ: `{R B : Type u} [CommRing R]
   [CommRing B] [Algebra R B]`, with φ rendered by `algebraMap R B`. PASS:
   `RingHom.toAlgebra` and `RingHom.algebraMap_toAlgebra` in Algebra/Algebra/Defs
   recover every ring homomorphism. The scalar module structure imposes no extra
   property. I read `AlgHom` in the recorded Algebra/Algebra/Hom module; the item
   uses only the algebra-structure clause of that dependency, not its quotient clauses.
2. Prime integer p: `(p : ℕ) (hp : p.Prime)`. PASS: natural primes are precisely
   the positive prime numbers intended by the source, with no characteristic restriction.
3. Every kernel element nilpotent: `hker : ∀ r : R, algebraMap R B r = 0 →
   IsNilpotent r`. PASS: elementwise, not a uniform nilpotence exponent or injectivity.
4. Algebra generators: `(s : Set B) (hgen : Algebra.adjoin R s = ⊤)`. PASS:
   I read `Algebra.adjoin` in Subalgebra/Lattice: it is the minimal subalgebra
   containing the given set and the image of R. The arbitrary witnessing set binder
   is equivalent to applying the result to any witnesses for generation; no finite
   generation assumption or choice of canonical generators is added.
5. Generator conditions: `∀ x ∈ s, ∃ n : ℕ, 0 < n ∧ x ^ (p ^ n) ∈
   (algebraMap R B).range ∧ (p ^ n : B) * x ∈ (algebraMap R B).range`. PASS:
   n depends on x and the same n witnesses both conditions; the cast is the integer
   multiple from the source, in every characteristic.
6. Universal homeomorphism of the induced spectrum map: `(topologically
   IsHomeomorph).universally (Spec.map (CommRingCat.ofHom (algebraMap R B)))`.
   PASS: I read `Spec` and `Spec.map` in Scheme (lines 470 and 480),
   `topologically` in Morphisms/Constructors (259), and `universally` in
   MorphismProperty/Limits (872). These are the dependency records' declarations;
   the last quantifies every scheme pullback square and tests the projection's
   underlying map. `Spec.map_apply` identifies that map with prime contraction.
7. Every commutative R-algebra R': `∀ (R' : Type (max u v)) [CommRing R']
   [Algebra R R']`. PASS: the enlarged test universe is at least u. The base-change
   carrier is `R' ⊗[R] B`, using the recorded TensorProduct, not a replacement.
   I read `LinearMap.baseChange` in Tower (661), and the tensor ring's
   `algebraMap_apply` in Basic (302): the displayed structure map is exactly
   r' ↦ r' ⊗ 1, with no flatness or compatibility instances assumed from the user.
8. Same nil-kernel hypothesis after base change: `∀ r : R', algebraMap R'
   (R' ⊗[R] B) r = 0 → IsNilpotent r`. PASS, including elementwise nilpotence.
9. Same generator hypothesis after base change: `∃ s' : Set (R' ⊗[R] B),
   Algebra.adjoin R' s' = ⊤ ∧ ∀ x ∈ s', ∃ n : ℕ, 0 < n ∧ ...` with both
   range conditions and the original p. PASS: this asserts existence, not an
   unnecessarily stronger specification of s' or a uniform exponent.
10. Homeomorphism of prime spectra after base change: `IsHomeomorph
    (PrimeSpectrum.comap (algebraMap R' (R' ⊗[R] B)))`. PASS: the contraction
    map of the required ring map, with the Zariski topology. All three base-change
    clauses occur after the universally quantified R' and its algebra structure.

Edge cases: the set s can be empty; then `adjoin R ∅ = ⊤` expresses surjectivity.
No nonempty spectrum or scheme is required. If B is the zero ring, hker forces 1
nilpotent in R, so R is zero too; zero R' is allowed. Empty scheme base changes
are included in `universally`. The condition n > 0 excludes n = 0 exactly as in
Stacks, while allowing all positive exponents independently for each generator.
Characteristic zero, p, and every other characteristic are covered. R and B share
an arbitrary ambient u, so any pair can be placed in their common larger universe;
v permits arbitrarily larger base-change rings. All binders and both universe
variables are explicit; no auto-implicit variable, local instance, or hidden
hypothesis occurs.

Independent searches, using different terms from the worker:

- LeanFinder via msearch: “Subalgebra generated by elements satisfying p-power and
  p-torsion image conditions gives universally bijective spectrum map”: eight hits,
  involving unramified/étale algebras, images of basic opens and localization;
  none states the generator criterion and its base-change conclusions.
- Loogle via msearch: `"IsHomeomorph", "adjoin"`: zero hits.
- LeanSearch via msearch: “Nil kernel and prime power algebra generators preserve
  homeomorphism of spectra under tensor products”: unavailable (Internal Server
  Error); no mathematical verdict is attributed to this service.
- Direct rg over Mathlib, upstream WeilConjectures, project lean/Sheaf and the
  upstream declaration-name inventory for `p_ring_map|pRingMap|power_generated|
  powerGenerated|universally_isHomeomorph|isHomeomorph.*adjoin|
  adjoin.*isHomeomorph|locally nilpotent kernel`. The relevant Mathlib match is
  `PrimeSpectrum.isHomeomorph_comap`, whose actual signature I read: it assumes
  a positive power condition for every element and asserts only the original
  spectrum homeomorphism. It is the node's proof input, not this statement.
  Upstream UniversalHomeomorphism gives the general scheme property and its
  implication to the recorded universal-topological predicate, not this generator
  theorem. I opened that implication too. No exact existing theorem or name
  collision was found, and no new notion is defined in this delivery.

H5–H9: there is one named theorem with whole proof `sorry`, no definition and no
proved auxiliary fact. The module and theorem docstrings cite Tag 0BRA and this
blueprint id. The proof docstring follows all six DAG steps: form T and its
closure, addition lemma, all-element criterion, nil kernel via base-change
surjectivity and radicals, tensor generators and repeated criterion, affine-chart
argument for arbitrary scheme base change. The imports include the recorded
statement notions and all available proof-dependency modules; the addition lemma
has no recorded module yet and is correctly listed for stage 3. No new definition
nodes, dependency modules or statement corrections are present or needed.

Verdict: no mathematical or Lean mismatch found. I preserved the statement, node
record, imports and docstrings; only this independent review was appended. The
node's lean.statement was checked verbatim against the file's theorem signature.
Validation uses only the prescribed server scompile.py, with every delivered file
compiled separately; delivery dry run and final delivery also enforce preflight.
