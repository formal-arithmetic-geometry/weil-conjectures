## Worker report

The module `Sheaf.RingTheory.IntegralNormalResidueEtaleSplitting` states
`Algebra.exists_integral_normal_residue_etale_splitting`, with its entire proof `by sorry`.
There are no helper definitions, new nodes, dependency repairs, or statement corrections.
Only the item's `lean` record changes.

Source read: `literature/stacks-project/more-morphisms.tex`,
`lemma-etale-makes-integral-split` (Tag 0BSR), including both proofs;
`literature/stacks-project/pione.tex`, `lemma-inertia-invariants-etale` (Tag 0BST),
the reduction using normal algebraic residue extensions with finite automorphism groups.
The docstring records all seven DAG proof steps, including the finite intermediate model,
idempotent decomposition, uniqueness and pure inseparability after base change, and lifting
the prescribed prime. The source itself only needs finite separable subextensions; the node
uses the stated normal finite-automorphism-group sufficient condition.

Clause-by-clause translation:

- A homomorphism of commutative rings A to D is `[CommRing A] [CommRing D] [Algebra A D]`,
  with map `algebraMap A D`. Every unital homomorphism supplies exactly this algebra data.
  A and D have separately bound universes `u v`.
- Integrality is `[Algebra.IsIntegral A D]`; no finite-generation or module-finiteness
  hypothesis is imposed.
- The specified primes are `p : PrimeSpectrum A` and `q : PrimeSpectrum D`.
  `hq : PrimeSpectrum.comap (algebraMap A D) q = p` states their contraction.
- `hfibre` is `Set.Finite` of all primes r of D contracting to p.
- For every such r, `hnormal r hr` is `Normal` for the canonical embedding
  `Ideal.ResidueField.map p.asIdeal r.asIdeal (algebraMap A D) ...`.
  Mathlib's `Normal` extends `Algebra.IsAlgebraic` and requires splitting of every minimal
  polynomial, so it renders both algebraicity and normality, without an extra hypothesis.
- `hauto r hr` is `Finite` of the type `AlgEquiv` of the residue field with itself over
  p's residue field, with precisely the same canonical algebra structure on both sides.
  This is finiteness of the full automorphism group, with no finite-dimensionality premise.
- `Ideal.ResidueField` is Mathlib's residue field at a prime; its existing
  `IsFractionRing (R ⧸ I) I.ResidueField` instance gives exactly the node's fraction field.
- The conclusion existentially supplies `B : Type u`, its commutative ring and A-algebra,
  and `AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map
  (CommRingCat.ofHom (algebraMap A B)))`, exactly the node's scheme definition of étale.
  The étale algebra may be chosen in the base's universe, as a finite-presentation algebra.
- `p' : PrimeSpectrum B` and its comap equality express p' over p.
- `q' : PrimeSpectrum (B ⊗[A] D)` is the lifted prime. Its contraction along
  `Algebra.TensorProduct.includeRight.toRingHom` is q; its contraction along
  `algebraMap B (B ⊗[A] D)` is p'. These are respectively d to 1 tensor d and b to b tensor 1.
- `n : ℕ` and `hn : 0 < n` express a nonempty finite product. The family
  `Dj : Fin n → Type (max u v)` carries existential commutative-ring and B-algebra structures.
  `e : (B ⊗[A] D) ≃ₐ[B] (∀ j, Dj j)` is the B-algebra product isomorphism.
- `∀ j, Algebra.IsIntegral B (Dj j)` is integrality of every factor.
- `qj : ∀ j, PrimeSpectrum (Dj j)` and `hlying` give one prime over p' in each factor.
  The next universally quantified implication says that every prime over p' equals qj j,
  so existence and uniqueness are both stated.
- Applying `RingHom.IsPurelyInseparable` to each canonical residue-field embedding induced
  by `hlying j` gives exactly the purely inseparable residue extension. This existing
  definition covers characteristic zero and all positive characteristics.
- The last equality identifies q'.asIdeal with the comap of the first factor's prime under
  `(Pi.evalRingHom Dj ⟨0, hn⟩).comp e.toRingHom`. Lean's index 0 is the node's index 1.
  This is the prime corresponding to q_1 under the specified isomorphism, rather than an
  unrelated prime or a mere assertion that some prime lifts.

Statement dependencies read and used:

- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`; their full definitions and
  docstrings were read. The spectrum points are the existing `PrimeSpectrum`.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`; its affine-local full signature and docstring were read.
- `def-weil-pbc-module-tensor-product`: its Mathlib match is `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`. Read that quotient definition,
  `TensorProduct.mk`, `TensorProduct.lift` and `TensorProduct.ext'` in the matched modules.
  `Mathlib.RingTheory.TensorProduct.Basic` provides the usual commutative algebra
  multiplication and the two canonical inclusions; no new tensor product is introduced.

Proof imports follow the recorded DAG plan: the generic finite-residue splitting module,
`WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField`, and Mathlib's
PurelyInseparable.Basic, Morphisms.Finite, Pullbacks, IntegralClosure.Algebra.Basic,
Spectrum.Prime.Topology, PullbackCarrier, TensorProduct.Nontrivial,
Spectrum.Maximal.Basic, and Morphisms.UniversallyInjective. The two proof-only inputs
`lem-dl-a1-normal-finite-aut-separable-subfield` and
`lem-dl-a1-integral-finite-residue-model` have no declaration record at the time of reading;
they are named in the proof docstring and require no object for typing this statement.

Edge cases checked before writing: zero rings cannot carry the specified primes, so they
are excluded by the existing data, not an added nontriviality premise. The selected q makes
the original fibre nonempty; the conclusion therefore requires n positive. Noninjective
A to D maps and nonreduced rings are allowed. An infinite purely inseparable field
extension has trivial automorphism group and is allowed; no full residue dimension bound
appears. In characteristic zero purely inseparable residue maps are isomorphisms. The
single-factor case uses Fin 1 and its index 0 without a separate exception. Independent
input universes are retained; factors live in the tensor product's maximum universe.
There is no disputed statement or node fault.

Searches (logged in the sandbox's `searches.jsonl`):

- LeanFinder: "An integral algebra with finite fibre and normal algebraic residue
  extensions with finite automorphism groups splits etale locally into factors with
  singleton purely inseparable fibres". Eight hits, including
  `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq` (the search index reported
  a Module.Finite version; reading the current source found FiniteType and QuasiFiniteAt),
  `Algebra.Etale.iff_exists_algEquiv_prod` (étale algebras over fields), and polynomial
  splitting results; none says the arbitrary-integral-algebra assertion.
- Loogle: `Algebra.Etale, Algebra.IsIntegral`. Zero hits.
- Mathlib grep via msearch: `exists_etale|iff_exists_algEquiv_prod`, RingTheory.
  Nineteen hits in étale finite-algebra, field and polynomial material; no match.
- LeanSearch: "Integral algebra etale base change product decomposition purely
  inseparable residue fields normal extensions finite automorphism group". Eight hits
  on purely inseparable extensions, étale base change and finite-type field algebras;
  none matches the full statement.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for integral-normal residue,
  étale splitting, `exists_etale`, `iff_exists_algEquiv_prod`, and for normal/purely
  inseparable residue fields found the generic finite-residue geometric theorem and
  different finite/free tensor splitting results, not this statement.
- The exact blueprint id search in `lean/WeilConjectures` had no hit. The chosen
  theorem name has no existing declaration in the searched source trees.

Validation: `scompile.py` compiled the sandbox and intended library module cleanly
(2.5 seconds each on the initial run). No error or warning was emitted. All variables
and universes are explicitly bound. The final module, including explicit dependency imports, passed deliver2.py --no-push:
commit 82f13e5efb9 passed the server preflight and per-file compilation. The only subsequent
change is this report's clarification of the current source signature of the search hit.

## Second reading by N6

Reread the source node and the entire signature after compilation. This is a second
pass by the same worker; the dispatcher prohibits starting other agents, and the delivery
receives the maintainer's independent review.

The ring and integrality assumptions, finite fibre, fixed q over p, normality including
algebraicity, and finiteness of automorphisms match the node. Checked that both occurrences
of the residue algebra in `hauto` are the same canonical map used by `hnormal`, and that
hr.symm has the orientation p = comap r required by `Ideal.ResidueField.map`.
Checked both q' contractions separately and that the B-algebra structure on B tensor D
is through its left factor. Checked that the dependent product carries the given B-algebras,
all factors are integral, the qj family witnesses existence, and the universal clause gives
uniqueness among exactly the primes above p'. Checked that each purely inseparable map
is the one determined by hlying. Finally the last equality is the preimage of the first
factor prime along projection composed with e, so the specified q' is tied to that factor.
No clause or hypothesis changed on this reading. Added explicit imports for the recorded
Spec/tensor-product dependencies and the affine-pullback proof dependency before final
validation. No statement correction, new notion or unusable dependency interface was found.
