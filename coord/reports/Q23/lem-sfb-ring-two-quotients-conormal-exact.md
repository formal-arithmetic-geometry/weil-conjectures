## Worker report

The module `Sheaf.RingTheory.TwoQuotientsConormalExact` states
`Algebra.Extension.two_quotients_conormal_exact`, with its sole proof `sorry`.
No definition, extra theorem, new node, dependency repair, or statement correction
is needed. The source read is Stacks Project `algebra.tex`, Tag 065V,
`lemma-application-NL`, lines 35518–35536, with the two tensor factors exchanged.
The node's five proof steps are reproduced in the theorem docstring, naming their
dependency nodes. The provided CompactObject example is withdrawn locally; its
recorded upstream replacement was read for the module/public-section conventions.
There is no repair note for this item.

Hypotheses and clauses, matched individually:

- Commutative rings A, B, C: `{A : Type u} {B : Type v} {C : Type w}` and the three
  `CommRing` instances. The three universe levels are independent.
- Maps α : A → B and β : B → C: `Algebra A B` and `Algebra B C`. The structure
  `Algebra A C` and `IsScalarTower A B C` specify π = β ∘ α, without restricting
  either map. Every pair of commutative-ring homomorphisms supplies these algebra
  structures through `RingHom.toAlgebra` and the composite.
- Only π is assumed surjective: `hπ : Function.Surjective (algebraMap A C)`.
  In particular, neither α nor β has a surjectivity hypothesis.
- The stated consequence that β is surjective is the conclusion
  `∃ hβ : Function.Surjective (IsScalarTower.toAlgHom A B C), ...`.
  This proof is also the input to Mathlib's quotient-extension constructor.
- I = ker π and I/I²: `(ofSurjective (Algebra.ofId A C) hπ).ker` and its
  `.Cotangent`. Here the extension's ring is A and its map to C is π.
- J = ker β and J/J²: `(ofSurjective (IsScalarTower.toAlgHom A B C) hβ).ker`
  and its `.Cotangent`. Here the extension's ring is B and its map to C is β.
- Canonical C-module structures: `Algebra.Extension.Cotangent.module` uses a
  preimage of a scalar in the surjection; multiplication on classes is independent
  of this lift because the kernel annihilates its conormal module. This is the
  ordinary quotient-ring action transported to C. `Cotangent.val_smul'` states
  compatibility with the action of the presenting ring.
- Existence, well-definedness, and C-linearity of u: the conclusion quantifies
  `∃ u : ...Cotangent →ₗ[C] ...Cotangent` on the actual quotient modules.
- Formula u([a]) = [α(a)]: for every kernel representative a and kernel
  representative b with `b.1 = algebraMap A B a.1`, the first conjunct says
  `u (Cotangent.mk a) = Cotangent.mk b`. Such a b exists for every a by the
  scalar-tower equation. This binder form avoids an embedded membership proof;
  it does not restrict which representatives are covered. `Cotangent.mk_surjective`
  shows that this specifies u on every class.
- Well-defined C-linear v and its target: the existing map
  `(ofSurjective (IsScalarTower.toAlgHom A B C) hβ).cotangentComplex` has type
  `J/J² →ₗ[C] C ⊗[B] KaehlerDifferential A B`. The abbreviation `.CotangentSpace`
  unfolds to that precise tensor product, not a free module of a chosen
  polynomial presentation.
- Formula v([b]) = 1 ⊗ db: this is the existing `cotangentComplex_mk` equation,
  which is definitionally true (`rfl`) in Mathlib. The actual canonical v is
  used directly, rather than an arbitrary map or an additional assumption.
- Surjectivity of v: the final `Function.Surjective ...cotangentComplex`.
- ker v = im u: `Function.Exact u ...cotangentComplex`. This means exactly
  `∀ y, v y = 0 ↔ ∃ x, u x = y` and includes the zero-composite assertion.
- Absence of extra hypotheses: there is no smoothness, flatness, finiteness,
  Noetherian, nonzero-ring, or characteristic assumption. There is no assertion
  that u is injective.

Dependency declarations read and used:

- `def-weil-pbc-kahler-differentials`: public import
  `Mathlib.RingTheory.Kaehler.Basic`; `KaehlerDifferential` (153ff),
  `KaehlerDifferential.D` (198ff), and `linearMapEquivDerivation` (327ff).
  `cotangentComplex` uses exactly these differentials and this derivation.
- `def-weil-pbc-module-tensor-product`: public import
  `Mathlib.LinearAlgebra.TensorProduct.Basic`, with its imported `Defs`;
  `TensorProduct` (Defs:81), `TensorProduct.mk` (Defs:376), `TensorProduct.lift`
  and `ext'` (Basic:123–134). The recorded tensor-map API in Map:331–410
  was also read. No replacement tensor construction is introduced.
- `lem-weil-pbc-jacobi-zariski-surjection-h1`: plain proof import
  `Mathlib.RingTheory.Extension.ExtendScalars`;
  `Algebra.Extension.h1CotangentEquivCotangent` (121ff) and
  `h1CotangentEquivCotangent_comp_map` (146ff). Its other clause is
  `KaehlerDifferential.subsingleton_of_surjective` (Basic:247ff).
- `lem-weil-pbc-jacobi-zariski-homology-sequence`: plain proof import
  `WeilConjectures.RingTheory.JacobiZariskiHomologySequence`;
  `Algebra.jacobiZariski_homology_sequence`. Its complete signature and
  coefficient-formula docstring were read. All four proof dependencies are
  therefore imported with the prescribed visibility.
- Additional existing interface: public import
  `Mathlib.RingTheory.Extension.Cotangent.Basic`, with `CotangentSpace`,
  `cotangentComplex`, and `cotangentComplex_mk` at lines 58–68.
  `Extension.ofSurjective`, `Extension.ker`, `Extension.Cotangent`,
  `Cotangent.module`, and `Cotangent.mk` were read in Extension/Basic.
  This uses Mathlib's existing quotient-module interface, without a private copy.

Edge cases checked mathematically before writing:

- A = B = C with identity maps: both kernel conormals and the differential module
  vanish. Exactness and surjectivity hold without excluding zero rings.
- A = C = k, B = k[x], evaluation x ↦ 0: I = 0, J/J² is k generated by x,
  and v identifies this generator with dx. This checks the direction and target.
- A = k[t], B = k[t,x], C = k by t,x ↦ 0: u sends t to t in the two-dimensional
  J/J², v kills t and sends x to dx. Its kernel is exactly im u, while α need
  not be surjective.
- A = k[t], B = k[t]/(t²), C = k: u is an isomorphism on the one-dimensional
  conormals and Ω[B/A] = 0, checking the nonflat case.
- A = B = k[t]/(t²), C = k: relative differentials are zero and u is identity;
  smoothness and reducedness have not slipped into the hypotheses.
- C = 0: both kernel ideals are the whole rings and their squares are themselves;
  the two conormals and the target tensor product vanish. The extension constructor
  and statement have no nontriviality requirement.

Searches actually run (their complete machine results are in `searches.jsonl`):

- LeanFinder: “For compatible ring maps A to B to C with A to C surjective,
  the conormal sequence I/I squared to J/J squared to C tensor over B Kahler
  differentials B over A is right exact”. Eight results included
  `Algebra.H1Cotangent.exact_map_δ` and
  `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`. These give
  H1 exactness or the one-quotient differential sequence, not this whole statement
  with both conormal identifications and representative formula.
- Loogle: `Ideal.Cotangent, KaehlerDifferential`. Eleven results included
  `kerCotangentToTensor`, `kerCotangentToTensor_toCotangent`, and
  `exact_kerCotangentToTensor_mapBaseChange`. The first two supply an existing
  canonical arrow, not the right-exact sequence asserted here.
- Grep through msearch: `Cotangent|mapCotangent|exact` in
  `RingTheory/Ideal/Cotangent.lean`. Five hits included `Ideal.Cotangent` and
  its quotient-ring action. The full local file was subsequently read.
- LeanSearch: “Exact conormal sequence I/I squared to J/J squared to C tensor
  Kahler differentials for A to B to C with composite surjective”. Eight results
  included `Extension.exact_cotangentComplex_toKaehler` and the single-quotient
  exactness theorem. None states the complete requested two-quotient sequence.
- Local rg of `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the node id, conormal/exact combinations,
  `twoQuotients`, `two_quotients_conormal_exact`, `065V`, and `application-NL`:
  no exact duplicate. The upstream `Algebra.Extension.smooth_conormal_sequence_exact`
  was found and read in full: it adds `[Algebra.Smooth A B]` and concludes
  injectivity of u, so it cannot serve as an existing match for this item.
  Its existing use of `ofSurjective` confirms the shared conormal encoding.

Validation: scompile.py compiled both its sandbox check and the actual library
module on the live published server build, cleanly (5.3 s and 1.4 s respectively).
There are no additional declarations or auto-bound variables. The theorem has
only the expected postponed proof. No statement dispute or node fault was found.

## Second reading by Q23

I reopened the delivered module and compared its entire signature with the node
and the source. This is a fresh reading by the same worker: the dispatcher forbids
starting another agent; the maintainer supplies the independent delivery review.

The three CommRing binders match the three commutative rings, and the algebra/tower
binders impose exactly the compatibility of π with α and β. The only nonstructural
hypothesis is hπ. The existential hβ is a conclusion, not an extra premise. Reading
`Extension.ofSurjective` confirms that the first ring really is A and the second
really is B; reading `Extension.Cotangent.module` confirms the required canonical
C-actions. The representative implication is not vacuous: for each a in I, its
image under α is in J by compatibility. Every quotient class has a representative,
so the implication fixes the first map everywhere. Reading `CotangentSpace` and
`cotangentComplex_mk` confirms that the second map is C-linear into the requested
C tensor over B Ω[B/A], with exactly the coefficient 1 and the universal derivative.
The two final conjuncts are middle exactness and surjectivity, with no injectivity
assertion. Independent universe binders retain unequal ring universes and the zero
ring. No mismatch was found and no signature change was needed. No new or dependency
modules need a second reading in this delivery.
