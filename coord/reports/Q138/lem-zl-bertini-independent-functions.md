## Worker report

The delivery states `Algebra.bertini_independent_functions` in
`Sheaf.AlgebraicGeometry.BertiniIndependentFunctions`. Its only postponed proof is
`by sorry`; no definitions, extra hypotheses, or helper nodes are introduced.
The original node is changed only in `lean`.

Source read: `literature/stacks-project/more-morphisms.tex`, Tag 0G4E,
`lemma-algebraically-independent`, statement and complete proof, lines 9011–9052.
The Lean follows that statement, including finite base fields. Its docstring carries
all six steps of the node's proof with the named dependencies.

Clause-by-clause correspondence:

- A field k: `(k : Type u) [Field k]`. No infinitude, perfectness or characteristic
  condition is assumed.
- A finite type k-algebra A that is an integral domain:
  `(A : Type v) [CommRing A] [Algebra k A] [FiniteType k A] [IsDomain A]`, where
  `FiniteType` in namespace `Algebra` is the recorded `Algebra.FiniteType`.
- n ≥ 2 and the n elements: `(n : ℕ) (hn : 2 ≤ n) (g : Fin n → A)`. Paper indices
  1 and 2 become `⟨0, Nat.zero_lt_of_lt hn⟩` and `⟨1, hn⟩`. These are explicit
  bound proofs, not new hypotheses.
- The closed locus V(g₁,g₂) is `PrimeSpectrum.zeroLocus ({g …, g …} : Set A)`.
  By the definition of zero locus its points are exactly the prime ideals containing
  both elements, including the case that the two elements coincide. `PrimeSpectrum A`
  is the underlying topological space of the dependency's affine scheme
  `AlgebraicGeometry.Spec (CommRingCat.of A)`; no scheme structure is changed.
- The component hypothesis is `hcomp : ∃ W : Set (PrimeSpectrum.zeroLocus …),
  W ∈ irreducibleComponents (PrimeSpectrum.zeroLocus …) ∧ …`. Thus W is a component
  of the common zero locus itself, with its subspace topology, rather than a component
  of all of Spec A.
- Dimension W = dim A − 2 is encoded by
  `topologicalKrullDim W + 2 = ringKrullDim A`. This is an equivalent additive
  rendering, not a statement correction: finite type over a field implies dim A is
  a finite natural number (the recorded dimension/trdeg dependency). An irreducible
  component is nonempty, hence has nonnegative dimension, so this equality says
  exactly dim W = dim A − 2 in integers, and correctly rules out dim A < 2.
  It avoids natural-number truncated subtraction, which would wrongly allow some
  low-dimensional cases. `topologicalKrullDim W` is computed in the twice-induced
  subspace topology, the same topology as its image in Spec A.
- K = Frac(A) is Mathlib's actual construction `FractionRing A`. The field in the
  conclusion is exactly `FractionRing (MvPolynomial (Fin n) (FractionRing A))`.
  It is the paper's K(x₁,…,xₙ) = Frac(K[x₁,…,xₙ]), with the canonical scalar tower
  supplied by Mathlib. Neither field is replaced by an arbitrary extension.
- Existence of c₁,…,cₙ in k is `∃ c : Fin n → k`.
- The n+2-element family is indexed by `Fin n ⊕ Fin 2`. All branches are first
  polynomials over `FractionRing A`, then mapped by the canonical `algebraMap` into
  that polynomial ring's fraction field.
- For `Sum.inl i`, the branch `MvPolynomial.X i` is xᵢ.
- For `Sum.inr 0`, `Fin.cases` selects
  `∑ i : Fin n, MvPolynomial.C (algebraMap A (FractionRing A) (g i)) *
  MvPolynomial.X i`, exactly sum gᵢxᵢ.
- For `Sum.inr 1`, `Fin.cases` selects
  `MvPolynomial.C (∑ i : Fin n, algebraMap k (FractionRing A) (c i) *
  algebraMap A (FractionRing A) (g i))`, exactly the constant sum cᵢgᵢ. No xᵢ
  occurs in this last combination.
- `AlgebraicIndependent k` of the displayed family means there is no nonzero
  polynomial over k vanishing on it, the required conclusion for the entire family.

Dependency declarations and inspected interfaces:

- `def-weil-pbc-finite-type-algebra`:
  `Mathlib.RingTheory.FiniteType`, `Algebra.FiniteType`, with field
  `(⊤ : Subalgebra k A).FG`. Its finite-polynomial-surjection equivalence was read.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `Spec.map`, including their docstrings and signatures.
  The statement uses its underlying `PrimeSpectrum A` and the standard zero locus.
- `def-weil-irreducible-components`: the node's `mathlib_match`,
  `Mathlib.Topology.Irreducible`, `irreducibleComponents X = {s | Maximal IsIrreducible s}`.
  The recorded Mathlib match is usable without a `lean` record repair.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim A : WithBot ℕ∞`, defined from prime-ideal chains.
- `def-kun-transcendence-degree`: `Mathlib.RingTheory.AlgebraicIndependent.Basic`,
  with recorded `Algebra.trdeg` and its underlying `AlgebraicIndependent` from
  `Mathlib.RingTheory.AlgebraicIndependent.Defs`. The full definition of independence
  is injectivity of the polynomial evaluation homomorphism; no replacement predicate.
- `def-weil-pbc-mv-polynomial-ring`: `Mathlib.Algebra.MvPolynomial.Basic`,
  `MvPolynomial`, `MvPolynomial.algHom_ext`, and `MvPolynomial.aeval` in
  `Mathlib.Algebra.MvPolynomial.Eval`. Read the construction, universal-property
  signatures and docstrings. The statement uses `MvPolynomial`, `C` and `X` directly.
- `def-kun-topological-krull-dimension` (already a proof dependency):
  `Mathlib.Topology.KrullDimension`, `topologicalKrullDim`, the dimension of the
  space of irreducible closed subsets. It is public because it occurs in the type.
- Proof-only imports retain the plan: `Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg`
  (`finiteType_domain_ringKrullDim_eq_trdeg`); `Mathlib.RingTheory.KrullDimension.Polynomial`
  (`MvPolynomial.ringKrullDim_of_isNoetherianRing`); and the Noetherian spectrum and
  component results in `Mathlib.RingTheory.Spectrum.Prime.Noetherian` and
  `Mathlib.Topology.NoetherianSpace` for `lem-wf-affine-noetherian-components`.
  The finite type module also supplies `Algebra.FiniteType.isNoetherianRing`.
  `lem-zl-finite-type-fibre-component-lower-bound` has no recorded Lean declaration
  yet; it is a proof-only dependency, so no missing statement object is needed here
  and no import of an unstated module is invented. Its use is preserved in the proof
  docstring. There is no import cycle.

Edge cases checked against the source:

- n = 2 is allowed and both first indices exist; n = 0 or 1 fails exactly hn.
- The zero ring is excluded by `IsDomain A`, as in the source.
- An empty common zero locus has no irreducible components, so cannot satisfy hcomp.
- dim A = 0 or 1 cannot satisfy the additive dimension equality for a nonempty W;
  there is no accidental truncated-subtraction hypothesis.
- If one of g₁,g₂ is zero, the codimension-two condition fails by the principal ideal
  bound; the formal statement imposes no extra nonvanishing condition.
- A = k[s,t], g₁=s, g₂=t realizes the dimension-zero component case (dim A = 2).
  The expected choice c₂=1 gives the family xᵢ, sum gᵢxᵢ, t.
- Finite k is allowed; the source proof chooses only 0 and 1, with no generic-k-point
  existence argument. Positive characteristic and nonperfect fields are retained.
- Universes u and v of k and A are explicitly independent. The fraction fields and
  the finite variable type do not impose an equality of universes.

Searches (2026-10-17 UTC), made through the required launcher search wrapper:

- `leanfinder`: "Codimension two common zero locus of two elements in a finite type
  domain yields algebraic independence of variables, their generic linear combination
  and a scalar linear combination". Eight hits: `algebraicIndependent_of_finite_type`,
  `AlgebraicIndepOn`, `algebraicIndependent_of_finite_type'`, `AlgebraicIndependent`,
  `AlgebraicIndependent.linearIndependent`, `algebraicIndependent_iff`,
  `Algebra.SubmersivePresentation.linearIndependent_aeval_val_pderiv_relation`,
  `MvPolynomial.linearIndependent_X`. These are general independence or derivative
  statements; none has the codimension-two hypothesis and this conclusion.
- `loogle`: `AlgebraicIndependent, MvPolynomial`. Twelve hits, comprising
  `algebraicIndependent_iff_injective_aeval`, `AlgebraicIndependent.aevalEquiv`,
  `.repr`, `.eq_zero_of_aeval_eq_zero`, `algebraicIndependent_iff`,
  `.aeval_comp_repr`, `.aevalEquiv_apply_coe`, `.aeval_repr`,
  `.algebraMap_aevalEquiv`, `.aevalEquivField`, `.reprField`,
  `.aevalEquivField_apply_coe`. All are evaluation or adjoin criteria, not this result.
- `leansearch`: "Algebraic independence of variables and two linear forms under a
  codimension two common zero hypothesis in a finite type domain". Eight hits:
  `AlgebraicIndependent`, `.linearIndependent`, `algebraicIndependent_of_finite`,
  `algebraicIndependent_iff`, `MvPolynomial.algebraicIndependent_X`,
  `algebraicIndependent_of_finite_type`, `AlgebraicIndepOn`,
  `algebraicIndependent_iff_ker_eq_bot`. No exact theorem.
- Wrapper `grep`: `[Aa]lgebraicIndependent.*(height|codim)|[Bb]ertini|algebraicallyIndependent.*linear`:
  zero Mathlib hits.
- `rg` on `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`,
  `/home/ubuntu/weil-newtargets-shared/lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the item id, proposed name and the same codimension/Bertini patterns. No item-id
  or proposed-name declaration. Existing upstream Bertini files concern the finite-cover
  curve theorem or specialization of irreducible polynomials; their relevant signatures
  and docstrings were read. The landed `BertiniIrreducibleMember` proof refers to this
  item but does not state it. No existing match, no duplicate notion introduced.

Validation: the required `scompile.py Q138 lem-zl-bertini-independent-functions <file>`
compiled the final statement at both its sandbox and library module paths, with no
errors and no warnings. The theorem is deliberately postponed as required by stage 2.
No statement dispute or node fault was found. No statement correction is needed.

## Second reading by Q138

A separate final self-reading reopened the node, Stacks 0G4E, and the completed Lean
module. This is a solo dispatcher worker's self-check; the maintainer performs the
independent delivery review. It verified every binder against the node: Field k,
CommRing/Algebra/FiniteType/IsDomain A, arbitrary n ≥ 2 and all n elements. It verified
that W is a component of the subspace V(g₁,g₂), not of Spec A, and that the additive
dimension equality excludes dim A < 2. It read both `Fin.cases` branches and the outer
fraction-field injection: the first gives sum gᵢxᵢ and the second is the constant
sum cᵢgᵢ, without multiplying it by any variable. The n variables remain separate
indices, so the statement asserts independence of the family, not merely of its range.
It checked that the canonical k-algebra scalar maps are used, no private construction
or arbitrary map is substituted, and the conclusion lies in the specified rational
function field. Explicit universes and both Fin bound proofs were checked. Preliminary
elaboration drafts were replaced with the final subtype component, additive dimension
condition and full n+2-member fraction-field family before validation. The final node's
statement, dependencies and proof are unchanged, and the `lean.statement` is extracted
verbatim from the compiling declaration. No further mismatch was found.
