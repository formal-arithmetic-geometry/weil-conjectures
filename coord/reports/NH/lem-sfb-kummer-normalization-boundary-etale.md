## Worker report

The new module `Sheaf.RingTheory.KummerNormalizationBoundaryEtale` states
`RingTheory.kummer_normalization_boundary_etale`. It contains one theorem with
`sorry` as its entire proof, no definitions, and no additional declarations.
The node is changed only in `lean`; its statement and reviewed seven-step proof
are unchanged. No new nodes, dependency repairs, or statement correction are needed.
The module docstring and theorem docstring cite the source and blueprint id;
the theorem docstring carries all seven steps of the recorded proof.

Sources opened: ILO, Travaux de Gabber, IX Proposition 2.1(i), printed pp.133–134
(the local PDF, extracted with pdftotext); Stacks `more-algebra.tex`,
`lemma-abhyankar` (0BRM); `algebra.tex`,
`lemma-Noetherian-normal-domain-finite-separable-extension` (032L) and
`lemma-integral-closure-localize` (0307). The ILO proposition supplies the tame
normalization context; the node is the local-algebra subargument assembled from
the Stacks results, rather than a restatement of that entire proposition.

The following matches every hypothesis and conclusion with its Lean rendering.

| Node clause | Lean rendering |
| --- | --- |
| R and B are commutative Noetherian normal domains | `CommRing`, `IsDomain`, `IsNoetherianRing`, `IsIntegrallyClosed` instances on each ring, as prescribed by the normal-domain dependency |
| Injective R into B | `[Algebra R B]` and `hRB : Function.Injective (algebraMap R B)` |
| K and E are their fraction fields | `[Field K] [Algebra R K] [IsFractionRing R K]` and the corresponding B/E instances |
| Induced fraction-field inclusion K into E | `[Algebra K E]` and `hKE`, equating the two composites from R; a field algebra map is injective, and compatibility makes this the unique induced fraction-field map |
| Positive integer n invertible in R | `n : ℕ`, `hn : 0 < n`, `hnunit : IsUnit (n : R)` |
| Nonempty finite family of L_j/K | `J : Type uJ`, `[Finite J] [Nonempty J]`, `L : J → Type uL`, field and K-algebra instances |
| Every L_j/K finite Galois | `[∀ j, FiniteDimensional K (L j)] [∀ j, IsGalois K (L j)]` |
| Each degree divides n | `hdegree : ∀ j, Module.finrank K (L j) ∣ n` |
| Finite family of F_a/E | `I : Type uI`, `[Finite I]`, `F : I → Type uF`, field and E-algebra instances |
| Finite separable F_a/E | `FiniteDimensional E (F a)` and `Algebra.IsSeparable E (F a)` instances |
| Given E-algebra decomposition of the product of L_j tensor_K E | `decomposition : @AlgEquiv E (∀ j, L j ⊗[K] E) (∀ a, F a) ...`; the explicit domain algebra is `Pi.algebra` of Mathlib's `Algebra.TensorProduct.rightAlgebra` |
| Each F_a has the induced field/tensor-factor structure | The decomposition is E-linear, not just a ring equivalence. Its coordinate projection to a field selects a unique j by the product idempotents, so the specified F_a is a factor of that tensor algebra. The B-structure on each F_a is constrained by `hBF` to the composite B to E to F_a |
| C_a is the integral closure of B in F_a | The actual Mathlib subalgebra `integralClosure B (F a)`, used directly throughout |
| C is the product of the C_a | The actual dependent product type `(∀ a, integralClosure B (F a))`, with its coordinatewise ring and B-algebra structures |
| Height-one prime q, in the node's explicit sense | `(q : Ideal B) [q.IsPrime]` and `hheight : q ≠ ⊥ ∧ ∀ r : Ideal B, r.IsPrime → r < q → r = ⊥` |
| p is the contraction of q | Written directly as `q.comap (algebraMap R B)` |
| V = R_p and A = B_q are DVRs | `IsDiscreteValuationRing` instances on the two actual `Localization.AtPrime` types |
| The induced V to A map is finite | `hfinite : RingHom.Finite (Localization.localRingHom ... rfl)` |
| The same map is injective | `hinjective : Function.Injective (Localization.localRingHom ... rfl)` |
| m_V A = m_A^n | `hindex`, with `Ideal.map` along that same canonical `localRingHom` and the nth ideal power |
| C is a finite B-algebra | First conjunct `Module.Finite B (∀ a, integralClosure B (F a))` |
| C is finitely presented over B | Second conjunct `Algebra.FinitePresentation B (∀ a, integralClosure B (F a))` |
| For every a and prime Q_a over q, Omega((C_a)_Q_a/A) = 0 | Third conjunct quantifies `a`, an ideal `Q` of `integralClosure B (F a)`, `[Q.IsPrime]`, and `hQ : q = Q.comap ...`; it asserts `Subsingleton (@KaehlerDifferential (Localization.AtPrime q) (Localization.AtPrime Q) ... (Localization.localRingHom ... hQ).toAlgebra)` |
| For every prime Q of C over q | Fourth conjunct quantifies the actual ideal `Q` of the product C, its prime instance, and the same contraction equality |
| C_Q is flat over A | `RingHom.Flat (Localization.localRingHom q Q (algebraMap B C) hQ)`, with C expanded in the file |
| (Omega(C/B))_Q = 0 | `Subsingleton (LocalizedModule Q.primeCompl (KaehlerDifferential B C))`, with C expanded |
| There is g outside Q giving an etale principal source neighbourhood | `∃ g : C, g ∉ Q ∧ Algebra.Etale B (Localization.Away g)`; this is the affine ring formulation of `Spec C[1/g] → Spec B`, accepted by the etale dependency's affine characterization and the recorded pointwise criterion |
| No excellence assumption | No excellence binder appears anywhere |

`Subsingleton` is exactly vanishing for these additive modules, rather than a
categorical `IsZero` on an unbundled type. The orientation `q = Q.comap ...`
is chosen to pass the contraction equality directly to `localRingHom`; it is
logically the same lying-over condition. `hKE` and `hBF` bind compatibility of
specified algebra structures, not additional restrictions on field extensions.
There is no arbitrary local algebra map, arbitrary normalization, or existential
choice of a canonical construction. All eight universes are explicitly declared,
and all variables are explicitly bound. There are no statement-level lets or
file-local notations, instances or private definitions.

Dependency declarations used (their recorded signatures and docstrings were read):

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  together with `IsDomain` for normal domains.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap`.
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`,
  and its canonical `Localization.localRingHom`.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`; its universal property
  `KaehlerDifferential.linearMapEquivDerivation` is used in the proof plan.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, equivalent to `Module.Flat`
  for the algebra induced by the specified map.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec` and `Spec.map`, and
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`,
  are rendered by their affine algebra formulation `Algebra.Etale`, as in
  `Algebra.isEtaleAt_iff_exists_away_etale_iff_flat_localized_kaehler`.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`, used with
  the ring structure and canonical B-algebra supplied by ring localization.

All proof dependencies with usable declarations are present as imports:
`IsIntegralClosure.finite` (DedekindDomain.IntegralClosure),
`Algebra.FinitePresentation.of_finiteType` (FinitePresentation),
`IsLocalization.integralClosure` (Localization.Integral),
`RingTheory.dvr_galois_normalization_ramification_dvd`
(WeilConjectures.RingTheory.DvrGaloisNormalizationRamificationDvd),
`RingTheory.dvr_tame_tensor_factor_formallyUnramified`
(WeilConjectures.RingTheory.DvrTameTensorFactorUnramified),
`IsDiscreteValuationRing` (DiscreteValuationRing.Basic),
`Module.Flat.flat_iff_torsion_eq_bot_of_isBezout` (Flat.TorsionFree),
`KaehlerDifferential.isLocalizedModule_map` (Etale.Kaehler),
`KaehlerDifferential` (Kaehler.Basic), and
`Algebra.isEtaleAt_iff_exists_away_etale_iff_flat_localized_kaehler`
(Sheaf.AlgebraicGeometry.EtaleAtPrimeFlatUnramifiedCriterion).
Imports used by the signature are public; the remaining proof imports are plain.

Edge cases checked before drafting:

- n = 0 is explicitly excluded, as in the node. For n = 1 the Galois degrees
  are one, so each field is K, the tensor fields are E, and the normalized
  factors are B; the conclusions reduce to localizations of the identity.
- An empty J is excluded exactly as stated. Empty I needs no additional
  exclusion: a decomposition from a nonempty product of nonzero tensor field
  algebras to the empty product cannot exist. No extra nonemptiness hypothesis
  is imposed on I.
- Repeated factors and one-element families remain allowed, with distinct
  coordinate primes in their products. No claim that the product C is a domain
  is made, and no finiteness assumption on the number of primes is added.
- q = (0) is excluded by `hheight`. Primes Q and Q_a need not be supplied at all;
  all corresponding conclusions are universally quantified, hence vacuous
  when there is no prime over q.
- In positive characteristic p, p dividing n is excluded by `hnunit` and the
  domain hypotheses. Characteristic zero is allowed without further assumptions.
- For k containing the nth roots of unity, with n prime to the characteristic,
  R = k[t], B = k[s], t = s^n and L = K(t^(1/n)), the tensor product splits
  over E = k(s), its normalized factors are B, and every boundary conclusion holds.
- Independent ring, field, and index universes do not impose a size equality.
  The result uses affine ring etaleness, so it needs no same-universe Spec binder.
- No regularity, strict henselianity, excellence or separability of the base
  extension E/K is assumed beyond what follows from the actual hypotheses.

Searches for an existing statement (2026-10-22):

- `msearch.py ... leanfinder`, query: "Finite Galois extensions of degree dividing n
  after base change by a DVR extension of ramification n have normalization etale
  at boundary primes". Eight hits included
  `Ideal.ramificationIdxIn_mul_ramificationIdxIn`, `Algebra.IsEtaleAt`,
  `Algebra.IsUnramifiedAt`, `Algebra.IsUnramifiedAt.of_liesOver`, and
  `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`; none is the
  normalized tame tensor-product assertion with its global finite product.
- `msearch.py ... loogle`, initial query `ramificationIdx, Etale`: zero hits,
  unknown identifier `ramificationIdx`. Repeated with name-fragment syntax
  `"ramificationIdx", "Etale"`: zero hits.
- `msearch.py ... grep`, query
  `Abhyankar|tame.*tensor|tensor.*tame|ramificationIdx.*Etale`: zero Mathlib hits.
- `msearch.py ... leansearch`, query: "Normalization of Galois tensor field factors
  becomes etale after a DVR base change whose tame ramification index is divisible
  by the Galois degrees". Eight hits included `Algebra.Etale.baseChange`,
  `Algebra.FormallyEtale.instTensorProduct`, `Algebra.Unramified.baseChange`,
  `IsGalois.to_normal` and an ideal-norm formula. These assume etaleness or
  unramifiedness already, or only give numerical Galois facts; none states this node.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the same tame tensor
  and Abhyankar patterns found the recorded DVR proof lemmas and the parent
  `Sheaf.Paper.StrictLocalPrimeToPKummerSplitting`. The parent was opened:
  its proof steps 11–13 contain the argument abstracted here, but its theorem
  has the strict-local root-cover hypotheses, not this node's statement.
- Direct `rg` for `kummer_normalization_boundary_etale|KummerNormalizationBoundaryEtale`
  in Mathlib, both library roots, and `dag/lean_names_upstream.json` found no existing
  declaration. `grep -rn` for this node id in `lean/WeilConjectures` found no match.

No statement dispute or node fault was found. The current node is already split
and reviewed at stage 1; this delivery supplies its missing stage-2 statement.

Validation: the file was compiled using the prescribed `scompile.py` against the
server's published live library, both as a sandbox module and under its final
module name, with no errors or non-sorry warnings (2.5 and 2.4 seconds).
The JSON copy changes only `lean`; the signature is extracted verbatim from the
file. Every Lean line is at most 100 characters.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
