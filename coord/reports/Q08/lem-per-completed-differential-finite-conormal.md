## Worker report

The module `Sheaf.RingTheory.CompletedDifferentialFiniteConormal` states
`KaehlerDifferential.completed_finite_conormal`, with one `sorry` and no new definitions.
It uses `AdicCompletion (maximalIdeal A) (KaehlerDifferential F A)` directly for M_F(A).
No node field other than `lean` changes.

Hypotheses and conclusions, clause by clause:

- The subfield is represented by `(F : Type u) [Field F] [Algebra F A]`. A is nontrivial
  because `[IsLocalRing A]`, so the field algebra map is injective; this is exactly a
  specified subfield embedding, without requiring the residue extension to be separable.
- `(A : Type v) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]` renders the Noetherian
  local ring. `[IsAdicComplete (maximalIdeal A) A]` renders its completeness and separation.
- The residue extension hypothesis is `[Module.Finite F (ResidueField A)]`, using the
  canonical induced F-algebra structure on the residue field. It means finite field
  extension, not essential finite type of A over F.
- `AdicCompletion` is literally the compatible sequences of ordinary differentials modulo
  `(maximalIdeal A)^n` times the module, with the componentwise A-module structure.
  The induced differential is `(AdicCompletion.of ...).compDer (D F A)`. The displayed
  elements in the statement are its evaluations.
- The first conjunct is `Module.Finite A ...`. The second is `Submodule.span A (Set.range
  (fun a : A ↦ AdicCompletion.of ... (D F A a))) = ⊤`. These give precisely finite
  generation and generation by exact differentials (and therefore a finite subset of
  exact differentials also generates).
- For each finite complete module N, the third conjunct says `Function.Bijective` of
  `fun h ↦ h.compDer ((AdicCompletion.of ...).compDer (D F A))`. This is the asserted
  composition map to *all* F-derivations, without a continuity restriction. The F-module
  and scalar-tower binders express the usual restriction of scalars along F → A.
  N lives in `Type (max v w)`, for arbitrary w, allowing modules of any size by universe
  lifting; finite A-modules are small relative to A. No ring-universe equality is imposed.
- For every `(I : Ideal A)` with `I ≠ ⊤`, the fourth conjunct asserts
  `IsAdicComplete ((maximalIdeal A).map (Ideal.Quotient.mk I)) (A ⧸ I)`.
  For a proper ideal of a local ring this image is exactly m/I. No extra hypothesis on
  the ideal (prime, radical, or finitely generated) is imposed.
- `I.Cotangent` is Mathlib's I/I², with its canonical A/I-module structure. The arrow δ
  is A/I-linear and is specified by `δ (I.toCotangent a) = 1 ⊗ da`. The arrow π is
  A/I-linear and sends `c ⊗ da` to `c • d(class a)`. The completed quotient differential
  module is completed at the image of m, exactly as in the quotient completeness clause.
  `Function.Exact δ π ∧ Function.Surjective π` means exactness in the middle and at
  the final nonzero term, followed by zero. No injectivity of δ is asserted.
- Tensor factors are canonically reversed throughout: `C ⊗[A] M` instead of `M ⊗[A] C`.
  The symmetry sends the node's `da ⊗ 1` to the stated `1 ⊗ da`, preserving the entire
  sequence. Existential arrows with these complete generator formulas state the existence
  and exactness of the canonical arrows. They do not allow arbitrary maps: the preceding
  span assertion and surjectivity of `I.toCotangent` determine them uniquely.
- The last conjunct assumes `IsReduced A` and `q ∈ minimalPrimes A` and uses any field
  L with `[IsFractionRing (A ⧸ q) L]` and the compatible A-algebra structure. This is
  Frac(A/q), without choosing a separate model or requiring another field embedding.
  It supplies a linear equivalence between the two stated scalar extensions, with its
  value `l ⊗ da ↦ l ⊗ d(class a)` on generators. Thus it is exactly the canonical map
  of the node and proves that map is an isomorphism. No chosen isomorphism unrelated to
  this formula is asserted. The quotient completion ideal is again the image of m.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete`, `AdicCompletion`,
  `AdicCompletion.submodule`, `AdicCompletion.of`.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `KaehlerDifferential.D`,
  `KaehlerDifferential.linearMapEquivDerivation`; `LinearMap.compDer` from its public
  derivation dependency. The linear-map/derivation equivalence is expressed directly
  by composition as the node requests.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, its bilinear `mk` and
  pure tensors (publicly available through `Kaehler.Basic`). Mathlib's `Ideal.Cotangent`
  is likewise a public dependency of ordinary differentials.
- Proof-only imports include `WeilConjectures.RingTheory.FiniteModuleComplete`
  (`finite_module_complete_over_complete_noetherian`),
  `WeilConjectures.RingTheory.FiniteOverCompleteRing`
  (`Module.finite_and_span_eq_top_of_adicComplete`),
  `Mathlib.RingTheory.AdicCompletion.Completeness`,
  `Mathlib.RingTheory.KrullDimension.Zero`, and
  `Mathlib.LinearAlgebra.TensorProduct.RightExactness`. The ordinary Jacobi--Zariski
  dependency is already publicly imported in `Kaehler.Basic`.

Source reading: opened the local EGA-IV-1 PDF through `pdftotext -layout`, reading
0_IV 20.7.14–20.7.16, 20.7.20 and 21.9.1. EGA 21.9.1 even allows finitely generated
residue field extensions; the assigned node states the finite-extension specialization.
20.7.20 gives dense image in the kernel; the node's proof correctly upgrades this to
exactness using finite modules over a complete Noetherian ring. The local latest blueprint
ancestor `lem-per-artin-gabber-affine-curve.md` was also read; this auxiliary algebra
statement is not the unit's own statement.

Edge cases checked before writing: A a field (m=0) gives ordinary differentials of the
finite extension; inseparable residue extensions are allowed. The zero ring is excluded by
local-ring nontriviality, as it must be for containing a subfield. N=0 is included. I=0
is included and gives the identity quotient sequence; I=m is included and gives the
residue differential sequence; I=top is excluded exactly as the node requires. For reduced
A a domain, q=0 is included and the last equivalence is the identity after scalar extension.
For multiple minimal primes the statement applies separately to each. No characteristic,
perfectness or separability hypothesis was introduced.

Searches actually run:

- `msearch.py ... leanfinder "Completed Kahler differentials finite residue field extension
  complete Noetherian local ring conormal exact sequence"`: eight hits, including ordinary
  `KaehlerDifferential.finite` (requires essential finite type), cotangent finite
  dimensionality, and ordinary extension exactness. No completed theorem match.
- `msearch.py ... loogle "KaehlerDifferential, AdicCompletion"`: zero hits.
- `msearch.py ... grep "(completed|continuous).*(Kaehler|differential)|(Kaehler|differential).*(completed|continuous)"`:
  seven unrelated analytic/manifold hits; no algebraic completed theorem.
- `msearch.py ... leansearch "completed Kahler differentials finite complete local algebra
  residue extension conormal sequence"`: eight hits, ordinary differentials, their maps
  and ordinary conormal sequences; no exact match.
- `rg` in `lean/WeilConjectures` for completed differentials and for this blueprint id:
  no matching theorem. `rg` in `lean/Sheaf` found continuous quotient differentials and
  finite-type Jacobian/completion comparisons. Read `ContinuousKaehlerDifferential.lean`:
  its inverse limit of differentials of quotient rings is not the node's inverse limit
  of the reductions of ordinary differentials. The present statement uses the existing
  Mathlib completion directly and introduces no competing definition of either notion.
- Read Mathlib completion, differential, cotangent, tensor, finite-module and residue-field
  signatures and docstrings with `sed`/`rg`. The full name
  `KaehlerDifferential.completed_finite_conormal` is new.

Validation: `scompile.py Q08 lem-per-completed-differential-finite-conormal <module>`
compiled both the sandbox and library module cleanly (1.9 s and 1.5 s respectively).
`autoImplicit` is false and universes are explicitly bound. The one theorem has `sorry`.
There are no statement disputes, corrections, dependency repairs, or new nodes.

## Second reading by Q08

I reopened the node and the completed file for a separate clause-by-clause reading.
The field embedding follows from nontriviality rather than an additional faithfulness
assumption. The residue field has precisely the finite F-module hypothesis. Completion
uses ordinary differentials modulo m-powers, not a different inverse system. Both finite
generation and the exact-differential span are present. The bijection has the correct
source and target and includes arbitrary derivations. The proper-ideal condition is
explicit, completeness uses the image of m, and both conormal arrows have the prescribed
values, exactness and final surjectivity. Reversing tensor factors is uniform and all
scalar rings agree. The minimal-prime clause includes reducedness, the fraction field,
the correct two completions, and the canonical differential formula on the equivalence.
All five statement dependencies use their recorded Mathlib notions; proof imports follow
the recorded proof dependencies. No mismatch requiring a node change was found.
This second reading is by the same worker, following the dispatcher's instruction not
to start other agents; the maintainer's independent review remains the delivery review.
