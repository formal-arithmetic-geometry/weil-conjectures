## Worker report

The module `Sheaf.RingTheory.PthRootPresentationDifferentials` states
`KaehlerDifferential.pthRootPresentation_differentials`, with its sole proof `sorry`.
There are no new notions, new nodes, dependency modules, or statement corrections.

Hypotheses and objects, matched with the node:

- The prime p is `p : ℕ` with `[Fact p.Prime]`.
- The commutative ring A is `A : Type u` with `[CommRing A]`, with arbitrary universe u.
- The hypothesis p·1_A = 0 (equivalently, an F_p-algebra) is
  `[Algebra (ZMod p) A]`. A homomorphism from ZMod p exists precisely when p·1_A = 0,
  and is unique (the source file `Mathlib.Algebra.Algebra.ZMod` explicitly records
  `Subsingleton (Algebra (ZMod p) A)`). In particular this permits the zero ring,
  unlike `[CharP A p]` for prime p. It adds no choice of mathematical structure.
- The finite family a_1,...,a_n is `n : ℕ`, `a : Fin n → A`.
- Local notation P is exactly `MvPolynomial (Fin n) A`.
- Local notation I is the ideal `Ideal.span (Set.range (fun j : Fin n =>
  (MvPolynomial.X j : P) ^ p - MvPolynomial.C (a j)))`.
- Local notation B is exactly `P ⧸ I`, the node's A'. These are syntax abbreviations
  of existing Mathlib constructions, not new definitions or abstract replacement algebras.
- The relative and absolute modules and d are Mathlib's `KaehlerDifferential` (Ω notation)
  and its universal derivation `D`. The polynomial and quotient algebra structures give
  the tower ZMod p -> A -> B; the ZMod scalar tower is supplied by Mathlib.

Conclusions, matched clause by clause:

1. `∃ b : Module.Basis (Fin n) B Ω[B⁄A], ∀ j, b j = ...` asserts precisely a free
   basis indexed by the n variables, identifying each basis vector with
   `D A B (Ideal.Quotient.mk I (MvPolynomial.X j))`. It specifies the actual differentials,
   rather than merely an unspecified free module of rank n.
2. The first map ε is `Finsupp.linearCombination B
   (fun j => (1 : B) ⊗ₜ[A] D (ZMod p) A (a j))`. Its domain is `Fin n →₀ B`,
   the n-fold direct sum, and it sends e_j to exactly 1 tensor d(a_j).
3. The map w is `mapBaseChange (ZMod p) A B`. Reading its definition and
   `mapBaseChange_tmul` together with `map_D` shows it sends c tensor d(a) to
   c • D (ZMod p) B (algebraMap A B a), exactly the map of the node.
4. The map z is `map (ZMod p) A B B`, B-linear, and `map_D` identifies its action
   as D over ZMod p of c' going to D over A of c'; B-linearity gives the formula
   for c • d(c').
5. `Function.Exact ε w` asserts exactness at B tensor Ω[A/F_p].
6. `Function.Exact w z` asserts exactness at Ω[B/F_p].
7. `Function.Surjective z` asserts exactness at Ω[B/A] followed by zero.
   There is no injectivity assertion on ε; the sequence has no initial zero.

Dependency declarations read and used:

- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial` and the universal property
  `MvPolynomial.aeval`, `MvPolynomial.algHom_ext`, in
  `Mathlib.Algebra.MvPolynomial.Basic` / `Mathlib.Algebra.MvPolynomial.Eval`.
  The statement uses MvPolynomial, X and C directly, importing the commutative-ring
  module to obtain the ring and quotient algebra instances.
- `def-weil-pbc-kahler-differentials`: `KaehlerDifferential`, `KaehlerDifferential.D`,
  and `KaehlerDifferential.linearMapEquivDerivation` in `Mathlib.RingTheory.Kaehler.Basic`.
  The same file supplies the two canonical maps used here; their full signatures and
  generator formulas were read.

Source: the Stacks source tree is not present in this read-only clone, so the cited
[Tag 07E5](https://stacks.math.columbia.edu/tag/07E5) was opened online. Its proof of
(2) => (4) computes these differentials and the connecting map from the relations.
The DAG already explains the extension of that calculation to every F_p-algebra,
using the conormal sequence and comparison of presentations. The declaration docstring
records all six proof steps and their cited nodes, including the harmless sign in the
connecting map. No proof-dependency theorem is imported merely for this docstring.

Edge cases checked before writing:

- n = 0: the quotient has no relations and is A; relative differentials vanish;
  an empty basis and the standard absolute differential sequence give the stated result.
- A is the zero ring: its unique ZMod p algebra is allowed, B is also zero, the
  differential modules are zero, and a basis indexed by Fin n is valid over the zero ring.
- Repeated a_j and p-th powers among the coefficients are allowed; ε can have
  a kernel or be zero. No independence of d(a_j) is asserted or assumed.
- p = 2 is allowed; p = 0 and p = 1 are excluded exactly by primality.
- A need not be a field, reduced, Noetherian, local, or a domain. None is imposed.

Searches for existing declarations:

- `msearch.py ... leanfinder "Kaehler differentials adjoining pth roots in characteristic p
  free basis exact sequence"`: eight results, including
  `Algebra.Generators.cotangentSpaceBasis`, `toKaehler_cotangentSpaceBasis`, and
  `Algebra.SubmersivePresentation.basisKaehler_apply`. They describe polynomial cotangent
  spaces or submersive presentations; none states either clause for this quotient.
- `msearch.py ... loogle "KaehlerDifferential.mapBaseChange, KaehlerDifferential.map"`:
  found `range_mapBaseChange`, `exact_mapBaseChange_map`, and `mapBaseChange_tmul`.
  These supply the standard maps and latter part of the exact sequence, but not its
  computed kernel or the relative basis; no exact match for the item.
- `msearch.py ... grep "pth|CharP|ExpChar" RingTheory/Kaehler`: zero hits.
- `msearch.py ... leansearch "Kaehler differentials quotient by pth powers characteristic p
  free basis"`: unavailable, Internal Server Error; other searches used as required.
- `rg` for `pth.root|pthRoot|p.th.root|root.presentation` in upstream WeilConjectures
  and project lean/Sheaf: no implementation of this statement. Project hits include
  references to this node in `GeometricallyRegularH1Injective` and unrelated root lemmas.
- `rg` for the item's full id in upstream WeilConjectures: no matches.
- `rg` for `pthRootPresentation_differentials` in `dag/lean_names_upstream.json`,
  Mathlib, upstream WeilConjectures, and the project's lean/Sheaf: no matches.

Validation: the single module compiled on the server with exit code 0 in 2.4 seconds,
with no warnings. No disputed statement or node fault was found.

## Second reading by E1

I independently read the item's node, both statement-dependency nodes and their recorded
Mathlib declarations, the delivered module and its Lean record. No mathematical mismatch
was found; the Lean module and node record are unchanged. This reading adds the review
below to the report. There are no new definition nodes, dependency modules or statement
corrections to review, and no corrected-statement citer verdicts are required.

Source check: the repository has no Stacks .tex checkout. I read the actual .tex from
https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex, lines
8697–8825, and the rendered Tag 07E5 at https://stacks.math.columbia.edu/tag/07E5.
The enclosing proposition assumes a Noetherian local algebra over a characteristic-p
field, and its proof initially chooses coefficients in that field with independent
differentials. Those assumptions concern the regularity argument, not the isolated
quotient calculation in this node. The node explicitly generalizes the calculation to
arbitrary F_p-algebras and supplies a direct conormal/presentation proof in place of
base change from a field. Checking its six steps shows this generality is valid: relative
relation differentials vanish, and the absolute relation differential contributes only
the coefficient differential. No local, Noetherian, field, flatness or independence
hypothesis is needed in the delivered statement. No unit statement needs correction.

Objects, hypotheses and conclusions, item by item:

1. Prime p: `p : ℕ` and `[Fact p.Prime]`. PASS: precisely primes, including 2.
2. Commutative ring A: `A : Type u` and `[CommRing A]`. PASS: no domain,
   nontriviality, reducedness, finiteness or local hypothesis; u is arbitrary.
3. p times 1_A vanishes: `[Algebra (ZMod p) A]`. PASS: any such algebra kills
   the natural-number cast p. Conversely a ring killed by p receives the unique
   unital map from integers modulo p. Thus this is exactly the F_p-algebra
   hypothesis, including the zero ring. `Mathlib.Algebra.Algebra.ZMod` records
   `Subsingleton (Algebra (ZMod p) A)`; there is no extra mathematical choice.
4. A finite family of n coefficients: `n : ℕ`, `a : Fin n → A`. PASS: the
   change from indices 1,...,n to Fin n is a reindexing, with no restriction on a.
5. The polynomial ring P: local notation `P` is `MvPolynomial (Fin n) A`.
   PASS: the recorded dependency def-weil-pbc-mv-polynomial-ring is used directly.
   I opened its signatures in Basic.lean (`MvPolynomial`, `algHom_ext`) and Eval.lean
   (`aeval`, `aeval_X`). They give the finite monomial algebra and its universal
   property for arbitrary commutative coefficient rings, not a field specialization.
6. Relations and A': local notation `I` is the ideal span of the range of
   `fun j => (MvPolynomial.X j : P)^p - MvPolynomial.C (a j)`; `B` is `P ⧸ I`.
   PASS: precisely the quotient by the stated relations. The quotient algebra map
   A → B is the composite constant-polynomial map followed by quotient, with
   no auxiliary quotient or abstract algebra substituted.
7. Ω and d: `Ω[B⁄A]`, `Ω[A⁄ZMod p]`, `Ω[B⁄ZMod p]` and `D` are Mathlib's
   `KaehlerDifferential` and universal derivation from the recorded dependency
   def-weil-pbc-kahler-differentials. PASS: I opened the definitions and
   `linearMapEquivDerivation` in Basic.lean. Its module is implemented as the
   diagonal ideal modulo its square, and the universal property identifies it
   with the node's generators-and-relations description. These are the same
   differentials, not a private presentation. The needed scalar towers are
   derived instances, not additional statement hypotheses.
8. Relative differential basis: `∃ b : Module.Basis (Fin n) B Ω[B⁄A], ∀ j,
   b j = D A B (Ideal.Quotient.mk I (MvPolynomial.X j))`. PASS: basis vectors
   are the actual differentials of the images of the variables. Merely asserting
   a free module of rank n would not suffice; the delivered equality supplies
   exactly the node's identification.
9. First map ε and its source: `Finsupp.linearCombination B
   (fun j => (1 : B) ⊗ₜ[A] D (ZMod p) A (a j))`. PASS: domain `Fin n →₀ B`
   is the n-fold direct sum, target is `B ⊗[A] Ω[A⁄ZMod p]`.
   I opened `linearCombination` and `linearCombination_single`; the standard
   vector `Finsupp.single j 1` is sent to exactly `1 ⊗ da_j`.
10. Map w: `mapBaseChange (ZMod p) A B`. PASS: Basic.lean defines it as the
    B-linear base extension of `map (ZMod p) (ZMod p) A B`.
    `mapBaseChange_tmul` and `map_D` together give
    `c ⊗ da ↦ c • D (ZMod p) B (algebraMap A B a)`, the stipulated formula.
11. Map z: `map (ZMod p) A B B`. PASS: its type is B-linear from absolute
    to relative differentials; `map_D` gives `dc' ↦ dc'` since `algebraMap B B`
    is the identity. B-linearity supplies the stated formula on `c • dc'`.
12. Exactness at B tensor Ω[A/F_p]: the first `Function.Exact ε w`. PASS:
    it identifies the kernel of w with the image of precisely the ε above.
13. Exactness at Ω[B/F_p]: `Function.Exact w z`. PASS: exactly the middle
    kernel/image equality, not a separate unspecified exact sequence.
14. Exactness at Ω[B/A] followed by zero: `Function.Surjective z`. PASS:
    exactly the final clause. There is no initial zero and no assertion that ε
    is injective. The existential basis and all exactness clauses are conjoined
    under the same parameters, as in the node.

Edge cases: n = 0 has an empty relation ideal, polynomial ring canonically A,
B canonically A, zero relative differentials and an empty basis. Both exactness
conditions specialize correctly. If A is the zero ring, its ZMod p algebra is
allowed and B and the differential modules are zero; a Fin n basis is valid
because its coordinate module is also zero. Repeated coefficients and p-th-power
coefficients are permitted, including a zero ε; no independence is imposed.
p = 2 is included, while p = 0 and p = 1 are excluded by primality exactly as
required. No scheme or empty-scheme object occurs. Every variable and the single
universe u is bound; Fin n and ZMod p impose no upper bound on A's universe.

Independent searches, using queries different from the first reader's:

- LeanFinder via msearch.py: "Module of differentials for purely inseparable
  polynomial relations X_i^p minus constants, basis and kernel of scalar extension".
  Eight results included `Algebra.Generators.cotangentSpaceBasis`, its generator
  formula and `toKaehler_cotangentSpaceBasis`, `KaehlerDifferential.mvPolynomialBasis`,
  and submersive-presentation bases. These concern the polynomial cotangent space
  or a submersive presentation, not this inseparable quotient calculation.
- Loogle via msearch.py: `KaehlerDifferential, MvPolynomial`. Twelve polynomial
  basis and coordinate results; none gives the quotient basis and computed kernel.
- LeanSearch via msearch.py: a full query about the quotient by X_i^p-a_i,
  its dX_i basis and the da_i absolute kernel. The service returned Internal Server
  Error; this is recorded as unavailable, not as a negative search result.
- Mathlib grep via msearch.py: `insepar|[Pp]th|[Pp]ower|CharP` in RingTheory/Kaehler,
  no hits. Independent rg with `differential.*root|root.*differential|[Pp]th.*[Dd]ifferential`
  and the delivered declaration name in upstream WeilConjectures, project lean/Sheaf
  and dag/lean_names_upstream.json found only the citation in
  GeometricallyRegularH1Injective. No existing implementation of this statement
  was found. Broader searches of purely inseparable and root material found field
  and étale constructions, not the claimed differential presentation.

H5–H9: the local notations only abbreviate existing Mathlib constructions and are
not hollow definitions. The sole theorem proof remains `by sorry`; nothing was
proved. Its docstring names the source and blueprint and carries all six node proof
steps, including presentation comparison and the harmless connecting-map sign.
The header, topic directory and namespace follow the project convention; every
line is at most 100 characters. All three imports supply used constructions or
instances. I checked the recorded `lean.statement` against the signature verbatim:
they agree, including the local P/I/B notations in scope.

Repairs: none were needed in Lean or in the node. Only this independent reading
was appended. Validation and delivery checks are recorded below.

Second-reader server compilation: scompile.py compiled the single delivered module
in 2.4 seconds, exit code 0, no errors or warnings.
Second-reader delivery dry run: deliver2.py --no-push printed OK; the packet
passes the preflight and compiles.
