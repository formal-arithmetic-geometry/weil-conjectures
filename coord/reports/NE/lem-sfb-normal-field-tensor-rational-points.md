## Worker report

The module `Sheaf.FieldTheory.NormalTensorRationalPoints` states
`Algebra.TensorProduct.normal_tensor_rational_points`, with `sorry` as its whole
proof. No definitions or further theorems are introduced. The node is unchanged
except for its `lean` record. There are no missing notions, dependency repairs,
statement corrections, or disputed statements.

Source checked: Milne, Algebraic Groups (2017), Theorem B.37, Step 2,
printed p.605 (PDF p.617). The second paragraph chooses a finite normal
extension receiving the residue fields and asserts that all points above them
are rational. Stacks `fields.tex`, definition-normal, Tag 09HM, defines normality
by splitting minimal polynomials and does not require separability. The node's
six-step algebraic proof is included in the theorem docstring.

Hypotheses and clauses, matched against the node:

- The ground field and the two extension fields are `{k : Type u}`,
  `{E : Type v}`, `{K : Type w}` with `[Field k] [Field E] [Field K]`.
  `[Algebra k E] [Algebra k K]` specify their given ground-field maps.
  Universes are explicit and independent; the tensor and its spectrum lie in
  the maximum of the extension universes.
- Finiteness of each extension is `[FiniteDimensional k E]` and
  `[FiniteDimensional k K]`. The receiving embedding is `_u : E →ₐ[k] K`;
  an algebra homomorphism between fields is automatically injective. Its name
  starts with an underscore because only its existence is used in the conclusion.
- Normality is `[Normal k K]`, the Mathlib class with its exact minimal-polynomial
  splitting field `Normal.splits'`. Its algebraicity field follows already from
  finite dimension. It imposes no separability condition.
- `E ⊗[k] K` uses Mathlib's existing tensor construction, commutative-ring
  multiplication, and unit. `Algebra.TensorProduct.tmul_mul_tmul` gives exactly
  the multiplication formula in the node. Each structural map starts with
  `(includeRight : K →ₐ[k] E ⊗[k] K).toRingHom`, whose value on a scalar is
  `1 ⊗ₜ a`. The statement consequently uses the specified right-hand K-algebra
  structure, independently of the default left-hand tensor algebra instance.
- Finiteness and nonemptiness are the first two conjuncts:
  `{q : Ideal (E ⊗[k] K) | q.IsPrime}.Finite` and the same set's `.Nonempty`.
  This is literally the set of prime ideals, equivalent to the carrier of
  `PrimeSpectrum (E ⊗[k] K)`.
- The third conjunct quantifies over every ideal `q` and its primality and states
  `Function.Bijective ((Ideal.Quotient.mk q).comp includeRight.toRingHom)`.
  A bijective ring homomorphism is exactly an isomorphism through that map;
  no unrelated quotient isomorphism is chosen.
- The fourth conjunct is `Set.BijOn` from `Set.univ` of `E →ₐ[k] K` to
  `{q | q.IsPrime}`, for `σ ↦ RingHom.ker (productMap σ (AlgHom.id k K)).toRingHom`.
  `productMap_apply_tmul` evaluates this existing map as `σ(e) * a`.
  `Set.BijOn` includes membership in the prime-ideal set, injectivity, and
  surjectivity onto that set, so it states the entire indicated bijection.
- The last conjunct quantifies over every point `x` of the actual scheme
  `Spec (CommRingCat.of (E ⊗[k] K))` and states bijectivity of the composite
  `K → E ⊗[k] K → Γ(Spec B, ⊤) → (Spec B).residueField x`.
  The three maps are `includeRight`, `(Scheme.ΓSpecIso _).inv`, and
  `(Spec _).Γevaluation x`. By the definitions of `Γevaluation`, `evaluation`,
  `residue`, and `residueField`, the last map is the germ followed by the
  stalk-to-residue-field quotient. This is precisely the canonical structural
  map to the residue field in the node, rather than just an abstract field
  isomorphism. The recorded scheme residue-field declaration is used directly.
- No separability, reducedness, Galois, characteristic, or nonzero-dimension
  hypothesis has been inserted. The given three fields already exclude the
  zero ring; nilpotents of the tensor are permitted.

Statement dependencies read and used:

- `def-weil-field`: `Mathlib.Algebra.Field.Defs`, `Field`.
- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra`.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`: the recorded Mathlib
  declarations in `Mathlib.RingTheory.TensorProduct.Basic` and `.Maps`, notably
  `Algebra.TensorProduct.instCommRing`, `.tmul_mul_tmul`, `.includeRight`,
  `.productMap`, and `.productMap_apply_tmul`. Evaluation is not redefined.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, with `Scheme.ΓSpecIso` for its canonical sections.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField`. The same module's `Scheme.Γevaluation`
  supplies the actual germ/quotient structural map.

Every statement dependency is a Mathlib leaf; no recorded project interface
needs replacement. The required public imports expose these declarations,
normality, and finite dimension. Plain proof imports retain the stated plan:
`Mathlib.RingTheory.Artinian.Module` for `IsArtinianRing.of_finite` and
`IsArtinianRing.setOfPred_isPrime_finite`;
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic` for
`Algebra.IsIntegral.of_finite`;
`Mathlib.FieldTheory.Separable` for the recorded minimal-polynomial/separability
node (only its minimal-polynomial notion is used);
`Mathlib.AlgebraicGeometry.AffineScheme` for the affine germ/stalk localization;
and `Mathlib.RingTheory.LocalRing.ResidueField.Ideal` for the prime-residue-field
fraction-ring interface. The module imports cover all recorded proof nodes.

Edge cases checked mathematically before writing:

- `E = k`: the tensor is K, with one prime, one embedding, and identity scalar
  maps after the canonical identification. `K = k` also works, since the receiving
  embedding then forces E to be the trivial extension up to k-isomorphism.
- A purely inseparable extension of degree p, with E = K, such as adjoining a
  pth root of t to F_p(t), is normal. The tensor is a truncated polynomial ring
  with one prime and nilpotents. The conclusion still holds: its quotient and
  residue field are K, with one embedding. Nothing here asks B to be a domain.
- For E = K = Q(i) over Q the two embeddings give the two primes of K × K.
- Without normality, E = K = Q(cuberoot(2)) has another prime whose residue
  extension over K is nontrivial. The actual normality hypothesis excludes it.
- Finiteness alone does not guarantee a nonempty spectrum of an arbitrary ring;
  here the given evaluation into the nonzero field K supplies a prime, as the
  docstring explains. No separate nontriviality assumption on B is needed.

Searches for an existing exact statement:

- `msearch.py leanfinder`: “For finite extensions E and K of k with K normal
  receiving E, prime ideals of E tensor K are kernels of evaluations at embeddings
  E into K, with every prime quotient and residue field canonically K”. Eight
  hits: prime-fiber equivalences, Galois prime actions, and purely inseparable
  spectrum homeomorphisms; none states the complete assertion.
- `msearch.py leansearch`: “Normal field extension tensor product prime ideals
  are kernels of evaluation at embeddings and the residue fields are the normal
  field”. Eight hits on `Normal` and its basic interfaces; no tensor theorem.
- `msearch.py loogle`: `Normal, "residue"`. Zero hits.
- `msearch.py grep`: `Normal.*Tensor|Tensor.*Normal|ker.*productMap|productMap.*ker`
  in FieldTheory. Zero hits. A direct Mathlib `rg` search for
  `Normal.*TensorProduct|TensorProduct.*Normal|productMap.*IsPrime|IsPrime.*productMap`
  in FieldTheory and RingTheory also found no exact result.
- Direct `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for the item id
  and `normalFieldTensor|normal_field_tensor` found no declaration. The only
  item-id hit is the proof docstring of the already landed finite-closed-set
  rational-lifts consumer. Searches of field/ring modules for a `BijOn` kernel
  correspondence found none. The upstream declaration index has no item-id hit.

Validation: `scompile.py NE lem-sfb-normal-field-tensor-rational-points` compiled
both the sandbox check and the final library module in 1.6 seconds each, with
no errors or unexpected warnings. Only the permitted theorem proof is postponed.

## Second reading by NE

(Written by the maintainer's independent second reader, cc review of
c638564dcdac, 2026-10-24; the delivered section was a same-worker self-check.)

Node statement as a list, with the Lean rendering and verdict:

1. Field k [def-weil-field]: `{k : Type u} [Field k]`. OK.
2. Finite-dimensional extensions E/k, K/k [def-pc-field-extension]:
   `[Field E] [Field K] [Algebra k E] [Algebra k K] [FiniteDimensional k E]
   [FiniteDimensional k K]`, independent universes u, v, w. OK.
3. A k-embedding u : E → K: `(_u : E →ₐ[k] K)` (field homs are injective). OK.
4. K/k normal (minimal polynomials split; no separability): Mathlib `[Normal k K]`
   = algebraic ∧ `minpoly` splits; algebraicity is implied by finiteness, so no
   stronger assumption. OK.
5. B = E ⊗_k K with (e⊗a)(e'⊗a') = ee'⊗aa' and K-structure a ↦ 1⊗a
   [lem-weil-pbc-algebra-tensor-pushout-universal-property]: Mathlib
   `Algebra.TensorProduct` commutative ring (`tmul_mul_tmul`); the K-structure is
   used explicitly through `includeRight` (`includeRight a = 1 ⊗ₜ a`), not the
   default left algebra instance. OK.
6. Prime ideals finite and nonempty: `{q | q.IsPrime}.Finite ∧ ….Nonempty`. OK.
7. For every prime q, K → B/q is an isomorphism: bijectivity of
   `(Ideal.Quotient.mk q).comp includeRight.toRingHom` (bijective ring hom =
   isomorphism through the structural map). OK.
8. σ ↦ ker(ev_σ) bijection from k-embeddings to primes, ev_σ(e⊗a) = σ(e)a:
   `Set.BijOn (σ ↦ RingHom.ker (productMap σ (AlgHom.id k K)).toRingHom) Set.univ
   {q | q.IsPrime}`; `productMap_apply_tmul` is `rfl` = σ e * a. BijOn = MapsTo
   (kernels prime) + InjOn + SurjOn: the full bijection. OK.
9. Residue fields of Spec B canonically K through the structural maps
   [def-weil-affine-spectrum, def-weil-residue-field]: for every
   `x : Spec (CommRingCat.of (E ⊗[k] K))`, bijectivity of
   `Γevaluation x ∘ (ΓSpecIso _).inv ∘ includeRight` into `(Spec _).residueField x`;
   `Γevaluation` is the Mathlib abbrev `X.evaluation ⊤ x trivial` (germ then
   residue), so this is the structural map, not an abstract isomorphism. OK.
10. No separability, B possibly non-reduced: no such hypothesis inserted. OK.

Edge cases: E = k (B ≅ K, one prime); K = k (forces E ≅ k); purely inseparable
E = K = F_p(t^{1/p}) over F_p(t) (B = K[ε]/ε^p, one prime, nilpotents, statement
holds; normality without separability is exactly Mathlib `Normal`); Q(i)⊗Q(i)
(two primes, two embeddings); Q(∛2) shows normality is needed. Universes: B and
Spec B live in max v w, no universe equality imposed.

Dependency records: all five stmt_deps are Mathlib leaves with existing:true
records (Field, Algebra, Algebra.TensorProduct declarations, AlgebraicGeometry.Spec,
Scheme.residueField); the Lean uses exactly these (plus Mathlib's
`Scheme.ΓSpecIso`, `Scheme.Γevaluation` from the recorded modules). The item node
differs from the live node only in its `lean` record; `lean.statement` is verbatim
the file's signature. Docstrings carry the source place (Milne B.37 Step 2,
Stacks 09HM) and `(blueprint: lem-sfb-normal-field-tensor-rational-points)`, and
the theorem docstring carries the six proof steps. Proof is `sorry` only; no
definitions introduced.

Searches: Mathlib `Algebra.TensorProduct.isField_of_isAlgebraic` (needs the
tensor to be a domain), `PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable`
and `Normal.minpoly_eq_iff_mem_orbit` are ingredients, not the statement; no
project declaration with this content (side-live lean/ grep). No mismatch found;
no change to the Lean or the node.
