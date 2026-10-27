## Worker report

The module `Sheaf.AlgebraicGeometry.MonoidPrincipalOpenFace` defines the displayed
set `AlgebraicGeometry.FineFan.principalFace` and states
`AlgebraicGeometry.FineFan.monoid_principalOpen_face`, with its proof `sorry`.
The set is constructed from its witnesses, with no postponed data. The helper
belongs to this node's own displayed definition and is listed in lean.declarations;
no independent missing notion or dependency repair is needed.

The recorded dependency uses multiplicative notation. This changes notation only:
its `1` is the node's additive `0`, multiplication is addition, `a ^ n` is `n a`,
and the product of a numerator with an inverse denominator in the Grothendieck
group is subtraction. No torsion-free or saturated assumption is imposed.

Hypotheses and clauses, in statement order:

- `P : Type u`, `[CommMonoid P]`, and `hP : IsFine P` mean a commutative fine
  monoid: the recorded `IsFine` is finite generation and injectivity of the
  canonical map to `Algebra.GrothendieckGroup P`.
- The spectrum is precisely `MonoidPrime P` with the recorded generated topology
  and `basicOpen a`. `Algebra.faceLocalization P (Submonoid.powers a)` is the
  recorded fraction submonoid inside this same group completion, namely `P_a`.
- `principalFace a = {c | ∃ (d : P) (n : ℕ), c * d = a ^ n}` is exactly `F_a`.
  The complement `(principalFace a)ᶜ` is exactly `m_a`.
- The first universal clause includes `1 ∈ principalFace a`, `a ∈ principalFace a`,
  closure under multiplication, and both factor memberships when their product
  belongs to the face. These render all four face assertions separately.
- `∃ m : MonoidPrime P, m.carrier = (principalFace a)ᶜ` asserts that this very
  complement is a proper prime ideal; the structure includes ideal absorption,
  properness, and multiplicative closure of the complement, and permits the empty
  ideal. `m ∈ basicOpen a` and `q.carrier ⊆ m.carrier` are membership in `D(a)`
  and greatestness among its primes.
- `∀ U : Opens (MonoidPrime P), m ∈ U → basicOpen a ≤ U` is exactly the
  assertion about every open neighborhood of this prime.
- A cover by relative opens is represented by a set `S` of ambient opens all
  contained in `basicOpen a`, with `sSup S = basicOpen a`. Every relative open
  in an open subspace is an ambient open. `basicOpen a ∈ S` asserts that the
  cover contains the whole open as a member. This representation handles arbitrary
  indexed covers by their range, so places no universe bound on their index sets.
- `principalFace (1 : P) = {p | IsUnit p}` and `basicOpen (1 : P) = ⊤` are the
  additive-zero face and basic-open assertions.
- For every `a,c`, the two biconditionals give exactly `D(c) ⊆ D(a) iff a ∈ F_c`
  and `a ∈ F_c iff ∃ d,n, a+d=nc`. Natural exponents include zero.
- Under the basic-open inclusion the statement supplies an inclusion `h` of the
  two *specified submonoids of the same completion*. The actual homomorphism is
  Mathlib's `Submonoid.inclusion h`, whose definition sends a subtype element
  `⟨x,hx⟩` to `⟨x,h hx⟩`. Thus it is literally the identity of the ambient group,
  and sends every fraction `p-ma` to that same element. There is no arbitrary map
  or existential choice of localization objects.
- `IsUnit q → IsUnit (Submonoid.inclusion h q)` asserts preservation of units.
  For `q ∈ P_a`, `r ∈ P_c` with `r.val = q.val`, the final equation asserts
  `sharpenMap (Submonoid.inclusion h) (Associates.mk q) = Associates.mk r`.
  This is the requested sharpening formula on the same fraction, independent of
  its representation. Since every localization element is a fraction, it covers
  every displayed `p-ma` and all possible representative choices.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineFanBlowup`: `AlgebraicGeometry.FineFan.IsFine`,
  `MonoidPrime` (extending Mathlib `SemigroupIdeal`), `spectrumTopology`,
  `basicOpen`, and `sharpenMap`, including their full definitions and docstrings.
- The same public dependency imports `Sheaf.TraceFormula.FaceLocalizationFs`,
  which gives `Algebra.faceLocalization`, the explicit numerator/denominator
  submonoid, using Mathlib's `Algebra.GrothendieckGroup` and its canonical `of`.
- Mathlib `Submonoid.powers`, `Submonoid.inclusion`, `IsUnit`, and `Associates`
  supply powers, the actual canonical inclusion, units and quotient by units.
  No proof-only import is missing: the sole proof dependency is the same fan node.

Source checked directly: the local ILO PDF, PDF pages 104--105, printed pp.98--99,
Exposé VIII 3.1.1 (sharpening), 3.1.2 (localization inside group completion),
3.1.3 (spectrum including the empty ideal and basic opens), and Remark
3.1.4(i),(iii) (maximal prime and trivial covers). The seven-step natural-language
proof of the node is included in the theorem docstring, in multiplicative notation.

Edge cases checked before writing:

- The trivial monoid and any finite abelian group have every element a unit:
  all principal faces are all of `P`, the complementary prime is empty, the
  spectrum is one point, and the cover assertion includes these cases.
- For additive `ℕ` and `a=0`, the face is `{0}` and the open is the whole spectrum;
  for positive `a`, the face is all of `ℕ`, and the greatest prime is empty.
- For additive `ℕ²` and `a=(1,0)`, the face is `ℕ × {0}` and its complement is
  exactly the greatest prime avoiding `a`. This checks the containment direction.
- A torsion unit factor, such as `(ℤ/2ℤ) × ℕ`, remains allowed: `IsFine` does
  not impose torsion-freeness. Nonsaturated integral fine monoids are allowed too.
- `a=0`, `c=0`, `a=c`, units and exponent zero are retained. For `c=0`,
  containment holds exactly when `a` is a unit, and the transition then lands
  in the original monoid. The empty cover cannot cover a basic open because the
  specified greatest prime belongs to it. No nonempty-index hypothesis is added.

Searches made (all msearch services returned successfully):

- `msearch.py ... leanfinder` with “The principal face of a fine monoid determines
  the greatest prime in a basic open and inclusions of monoid basic opens induce
  localization homomorphisms”: eight results about ring structure sheaves,
  including `AlgebraicGeometry.StructureSheaf.toBasicOpen` and
  `toBasicOpen_to_map`. Their signatures require a commutative ring and ring
  spectra, rather than monoid primes. No exact statement.
- `msearch.py ... loogle '"MonoidPrime", "basicOpen"'`: zero hits.
- `msearch.py ... grep 'MonoidSpectrum|MonoidPrime|principalFace|faceLocalization'`:
  zero Mathlib hits.
- `msearch.py ... leansearch` with “The complement of the face of divisors of
  powers of an element of a monoid is the greatest prime in its principal open
  subset”: eight hits, including `Prime.dvd_of_dvd_pow`, `PrimeSpectrum.basicOpen`,
  `Ideal.primeCompl`, and order-theoretic prime ideals. None states this result;
  the ring-spectrum definitions require a semiring and ring ideals.
- `rg -n 'principalFace|MonoidPrime|faceLocalization|monoid-principal-open-face'`
  in both `lean/WeilConjectures` and `lean/Sheaf`: the recorded fan definitions,
  face localization and their consumers were found and read. The parent
  `AffineFanLocalizationSections` repeats the principal-face argument in its
  docstring but its theorem states sections/stalks, not this lemma. It is not
  imported, avoiding a downstream dependency.
- `rg` for `principalFace|principalOpen_face|monoid_principalOpen` in Mathlib,
  both project source roots, and `dag/lean_names_upstream.json`: no declaration
  conflict. `grep -rn 'lem-trf-monoid-principal-open-face' lean/WeilConjectures`
  found no existing module for this node.
- Additional search for faces of powers and `IsFace` found no existing definition
  of this principal face. General convex-polyhedral facets are unrelated.

No statement correction, disputed statement, new node, or dependency-interface
fault was needed. Every variable and universe is explicit; `autoImplicit` is false.

## Second reading by Q40

No independent worker reading is claimed: this dispatcher assignment prohibits
starting other agents and authorizes direct delivery. The maintainer performs
independent review. I re-read the node and the final Lean signature clause by
clause; the correspondence above records that check, including the empty prime,
arbitrary covers, additive-zero case, both equivalences, the identity-induced
canonical restriction and its sharpening formula.

Validation: `scompile.py Q40 lem-trf-monoid-principal-open-face` compiled the
sandbox and library module cleanly. `deliver2.py ... --no-push` then reported
`OK (dry run)`: preflight passed and the module compiled. No non-sorry warning
or compilation error remained.
