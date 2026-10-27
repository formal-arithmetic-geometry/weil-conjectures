## Worker report

The module `Sheaf.Analysis.Normed.WeakSpectralCompletionProduct` states
`exists_weak_spectral_completion_product`, with `sorry` as its entire proof. It also supplies
only the concrete carrier/interface helpers required to express this node: the type synonym
`SpectralNormedExtension F E`, its original field and algebra operations, the normed commutative
ring structure from Mathlib's `spectralAlgNorm`, its normed algebra structure, and the constant-class
algebra map `SpectralNormedExtension.toCompletion`. These are helpers of the owning completion
statement, not new independent mathematical notions. Their data are fully written; none uses
`sorry`, an existence choice, or an arbitrary unspecified map.

Clause-by-clause correspondence:

- The field F and its nontrivial real-valued multiplicative nonarchimedean absolute value are
  `[NontriviallyNormedField F] [IsUltrametricDist F]`. There is no `CompleteSpace F` assumption.
  `UniformSpace.Completion F` is precisely H, with Mathlib's canonical complete normed-field
  structure, supplied by `NormedField.instCompletableTopField` and the completion instances.
- The finite field extension is `[Field E] [Algebra F E] [FiniteDimensional F E]`.
  `(n : ℕ) (hn : 0 < n) (w : Module.Basis (Fin n) F E)` says its dimension is n >= 1 and gives
  the required basis. A basis of this cardinality is the dimension condition, rather than a
  restriction on the extension. Universes u and v are independent and explicitly bound.
- The spectral norm is exactly `spectralNorm F E` from the recorded dependency. The norm installed
  on the type synonym is `(spectralAlgNorm F E).toRingNorm.toNormedRing`; its function is
  definitionally `spectralNorm F E`, not a chosen extension valuation. It need not be multiplicative.
- The positive real constants are `(c C : ℝ) (hc : 0 < c) (hC : 0 < C)`. For every coordinate
  vector a, `hw` states both `c * ‖a‖ ≤ spectralNorm F E (∑ i, a i • w i)` and the upper bound
  by `C * ‖a‖`. Mathlib's finite Pi norm is the maximum of the coordinate absolute values
  (`Pi.norm_def`, Group/Constructions.lean:310), so this is exactly the displayed pair of bounds.
- The completed space is the actual `UniformSpace.Completion (SpectralNormedExtension F E)`.
  Its metric is induced by s(x-y); the completion norm is `Completion.extension Norm.norm`,
  so on Cauchy classes it is the limit of the spectral norms. `Completion.norm_coe` identifies
  the norm on constant classes. This uses Mathlib's equivalent uniform completion model rather
  than redefining a quotient of sequences. Metric uniform completion has the canonical dense
  embedding and exactly the same Cauchy-sequence equivalence classes up to canonical isometry.
- The completed ring is Mathlib's commutative uniform ring completion, whose continuous operations
  extend those of E. In particular multiplication is the extension of multiplication and agrees
  with termwise multiplication of Cauchy representatives. No ring structure on this completion
  is quantified or chosen.
- The completed H-algebra structure is a CONCLUSION, `∃ (_ : Algebra H completion), ...`.
  Its first required clause fixes its algebra map pointwise to
  `Completion.extension (fun a : F ↦ (algebraMap F (SpectralNormedExtension F E) a : completion))`.
  This completely specifies the canonical scalar action: its algebra map is the extension of the
  original isometric base map, and algebra scalar multiplication is multiplication by that map.
  On representatives it is therefore exactly `[(a_m)] • [(x_m)] = [(a_m x_m)]`. The existential
  is part of the theorem's asserted construction, not an arbitrary map supplied as a hypothesis.
- The canonical E map is the fully defined F-algebra homomorphism `toCompletion F E`.
  `Isometry` and `DenseRange` are the first two conjuncts. Isometry implies injectivity and
  continuity, so this is the isometric F-algebra embedding with dense image from the node.
- `FiniteDimensional H completion` and `Module.finrank H completion = n` give the dimension clause.
- `∃ (r : ℕ) (_ : 0 < r) (L : Fin r → Type v) (_ : ∀ j, Field (L j))
  (_ : ∀ j, Algebra H (L j)) (_ : ∀ j, FiniteDimensional H (L j)) ...` is exactly a nonempty
  finite list of finite field extensions of H. Universe v suffices for the factors because they
  can be the residue-field quotients of the completion of E, itself in Type v; no equality
  between the independent universes of F and E is imposed.
- `θ : completion ≃ₐ[H] (∀ j, L j)` is the required H-algebra product isomorphism.
  Its required equality `∀ z, ‖z‖ = ⨆ j : Fin r, spectralNorm H (L j) (θ z j)` is the maximum
  formula: a finite nonempty supremum in ℝ is the maximum, and r > 0 excludes the empty case.
- `(∑ j : Fin r, Module.finrank H (L j)) = n` is the total degree clause.
- Neither stability nor separability occurs among the hypotheses.

Dependencies read and used:

- `def-weil-field`: Mathlib `Field` in Algebra/Field/Defs.lean, extending the commutative ring
  and division-ring structures, with nontriviality and inverses of nonzero elements.
- `lem-sfb-normed-field-completion`: Mathlib Analysis/Normed/Module/Completion.lean supplies
  the completed normed field, with the `CompletableTopField` instance from
  Analysis/Normed/Field/Instances.lean; Topology/UniformSpace/Completion.lean supplies
  `Completion.completeSpace`; Topology/Algebra/UniformRing.lean supplies
  `Completion.coeRingHom`; Topology/MetricSpace/Completion.lean supplies `Completion.coe_isometry`.
  These full signatures and the completion norm definition were read. The original completion
  dependency needs no interface repair.
- `lem-trf-incomplete-spectral-algebra-norm`: `spectralAlgNorm`,
  `isNonarchimedean_spectralNorm`, and `spectralNorm_one` in
  Mathlib.Analysis.Normed.Unbundled.SpectralNorm, whose signatures and docstrings were read.
  `spectralAlgNorm_def` identifies the norm function, and `spectralNorm` is the minimal-polynomial
  spectral value. Only algebraicity and ultrametricity, not completeness, are required.
- Proof dependencies `lem-trf-algebraic-spectral-norm-powers` and
  `lem-trf-power-multiplicative-algebra-norm-unique` use `isPowMul_spectralNorm` and
  `spectralNorm_unique` in the same publicly imported module. The theorem docstring gives all
  five proof steps and names every proof-dependency node.
- Proof dependencies `lem-weil-pbc-finite-dim-algebra-artinian` and
  `lem-sfb-reduced-artinian-residue-product` use `IsArtinianRing.of_finite` and
  `IsArtinianRing.equivPi` in Mathlib.RingTheory.Artinian.Module, imported without `public`.
  The finite-maximal-spectrum and quotient-field instances and component formula were read too.

Edge cases were checked before writing: n = 1 and E = F give a single H factor; n = 0 is
explicitly excluded by the original statement; r = 0 would give the zero ring and is excluded
by r > 0. All characteristics and inseparable extensions remain allowed. In an inseparable
case where scalar completion would create nilpotents, the two-sided coordinate bound cannot
hold: the power-multiplicative completion norm forces reducedness. Thus the theorem does not
silently impose separability. The base may be incomplete, and the completed E is not asserted
to be a field. Zero coordinates and the zero element have both sides of the bounds/max formula
zero. No source or statement correction was needed.

Searches for an existing statement (all via the prescribed msearch.py wrapper):

- leanfinder: "Completion of a finite spectral normed field extension with coordinate bounds
  is a product of finite extensions of the completed base with maximum spectral norm".
  Eight results, including `spectralNorm.completeSpace`, `spectralNorm.normedField`,
  `spectralNorm.nontriviallyNormedField`, `spectralNorm_eq_invariantExtension`,
  `spectralNorm.normedAddCommGroup`, `spectralNorm.normedSpace`,
  `IsUltrametricDist.invariantExtension`, `spectralNorm_extends_of_finiteDimensional`.
  None states the product theorem; the first normed structures require a complete base.
- loogle: `"spectralNorm", "Completion"`: zero results.
- grep: `spectralNorm.*[Cc]ompletion|[Cc]ompletion.*spectralNorm|[Ss]pectral.*[Pp]roduct|[Pp]roduct.*[Ss]pectral`:
  two files, Analysis/InnerProductSpace/Spectrum.lean and
  Analysis/Normed/Unbundled/SpectralNorm.lean, no completion-product theorem.
- leansearch: "Completion finite dimensional reduced nonarchimedean algebra product of fields
  maximum spectral norm": eight results, including `spectralNorm.completeSpace`,
  `spectralNorm_unique_of_finiteDimensional_normal`, `spectralAlgNorm`,
  `isNonarchimedean_spectralNorm_of_finiteDimensional_normal`, `spectralAlgNorm_mul`,
  `isNonarchimedean_spectralNorm`, `spectralNorm_mul`, `spectralNorm.normedField`.
  These give component axioms and complete-base field norms, not the theorem.
- rg of lean/WeilConjectures and lean/Sheaf for spectral/completion combinations and
  `weakSpectralCompletion`, plus the prescribed grep of the item's id in lean/WeilConjectures:
  no matching statement. rg of the upstream-name index and both source roots found no collision
  for the delivered carrier/theorem names. Further searches read `AlgebraNorm`,
  `RingNorm.toNormedRing`, the completion ring/algebra interfaces, and finite Pi norms directly.

The current blueprint unit sk-i-curve-zero and lem-trf-local-term-locality statement/proof
were read in literature/blueprint/latest. The analytic node is inherited historical support,
as its blueprint.from explains; no unit statement or route is altered. The source node records
that the BGR archival PDF is unavailable locally and marks this completion proof agent-written.
This delivery uses that recorded proof and Mathlib source; it does not claim to have read BGR.

Validation: single-file compilation via scompile.py, then deliver2.py --no-push and deliver2.py.
The only postponed proof is `exists_weak_spectral_completion_product`.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
