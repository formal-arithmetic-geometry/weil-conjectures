## Worker report

Delivered one statement, `RingTheory.fibre_regular_localization_spectrum`, in
`Sheaf.RingTheory.FibreRegularLocalizationSpectrum`. The only proof is `sorry`.
No definitions, new nodes, dependency repairs, or statement changes were needed.
The source read was Stacks Project, More on Flatness, `flat.tex`, Tag 05DE
(`lemma-homothety-spectrum`), statement and complete proof, lines 1781–1821.
The seven-step proof docstring follows all seven accepted DAG steps, including the
quotient-annihilator calculation, empty prime-family case, and maximal-ideal argument.

Hypotheses, one by one:

- The arbitrary homomorphism of commutative rings is `[CommRing A] [CommRing B]
  [Algebra A B]`; its map is `algebraMap A B`. Every unital commutative ring map
  has this algebra structure. No locality condition on this map, no locality of B,
  and no Noetherianity of A or B is imposed.
- A is local with maximal ideal m_A: `[IsLocalRing A]` and
  `IsLocalRing.maximalIdeal A`. Mathlib's local-ring class includes nontriviality,
  as does the source's requirement of a proper maximal ideal.
- N is an arbitrary B-module: `N : Type w`, `[AddCommGroup N] [Module B N]`.
  The independent universes u, v, w allow unrelated sizes for A, B and N.
- The ideal I = m_A B is `(IsLocalRing.maximalIdeal A).map (algebraMap A B)`.
  C is literally `B ⧸ I`, not an arbitrary quotient or tensor model.
- The closed-fibre module M = N/m_A N is literally
  `N ⧸ (I • (⊤ : Submodule B N))`. The B-action is the ordinary quotient action.
  The C-action is Mathlib's canonical quotient-ring module instance, supplied by
  `Mathlib.Algebra.Module.Torsion.Basic`; its `Submodule.Quotient.mk_smul_mk`
  says `[b] • [n] = [b • n]`. Thus there is no chosen or assumed extra action.
- C is Noetherian: `[IsNoetherianRing (B ⧸ I)]`.
- M is finite as a C-module: `[Module.Finite (B ⧸ I) (N ⧸ (I • ⊤))]`.
  There is no finite-generation assumption on N itself.

Conclusions, one by one (I and M in this report abbreviate the explicit terms in Lean;
no file-local notation, abbreviation or let binder occurs in the module):

- Sigma is `nonZeroSMulDivisors B M`, an existing `Submonoid B` whose real data
  include one and multiplicative closure. The first conjunct explicitly identifies
  `b ∈ Sigma` with `Function.Injective (fun z : M ↦ b • z)`. The kernel-zero
  condition in its carrier is equivalent to injectivity for additive group modules
  (`isSMulRegular_iff_mem_nonZeroSMulDivisors`), exactly the node's set.
- The ring of fractions is the standard `Localization Sigma`, with contraction
  along `algebraMap B (Localization Sigma)`.
- The spectrum identification is `Set.BijOn (PrimeSpectrum.comap ...) Set.univ`
  onto `{p : PrimeSpectrum B | ∃ q ∈ annihilatorAssociatedPrimes B M,
  p.asIdeal ≤ q}`. BijOn states both injectivity and that every and only the
  specified primes occur. `PrimeSpectrum` is the underlying space of the recorded
  `AlgebraicGeometry.Spec`; the public Scheme import supplies that definition.
- Semilocality is exactly `{J : Ideal (Localization Sigma) | J.IsMaximal}.Finite`.
  It permits zero maximal ideals and assumes no ring nontriviality.
- The exact maximal-ideal classification is a second `Set.BijOn`, this time for
  `Ideal.comap`, from the maximal ideals onto
  `{q | Maximal (fun q ↦ q ∈ annihilatorAssociatedPrimes B M) q}`.
  The order on ideals is inclusion. In particular this does not assert that every
  associated prime gives a maximal ideal when associated primes are nested.
- For every maximal J, the next conjunct supplies a Q in
  `annihilatorAssociatedPrimes (B ⧸ I) M`, with contraction of J equal to
  `Ideal.comap (Ideal.Quotient.mk I) Q`. This is the stated inverse-image clause.
- The zero-module boundary case is expressed by an implication from
  `Subsingleton M`: Sigma is the top submonoid (all of B), the localization is
  `Subsingleton` (the zero ring), `IsEmpty (PrimeSpectrum ...)`, and
  `∀ J, ¬ J.IsMaximal`. No `Nontrivial M` or nonempty-spectrum assumption is present.

Recorded dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` (lines 193–204), with `isNoetherianRing_iff_ideal_fg`.
- `def-weil-finitely-generated-module`: `Mathlib.RingTheory.Finiteness.Defs`,
  `Module.Finite` (lines 116–120): the top submodule is finitely generated.
- `def-weil-pbc-module-localization`: `Mathlib.Algebra.Module.LocalizedModule.Basic`,
  `LocalizedModule` and its fraction equality criterion (lines 86–103).
  Its `example_localization_eq_localizedModule` (lines 92–95) verifies that
  the ring `Localization Sigma` is exactly this localization with module B.
- `def-weil-pbc-annihilator-associated-primes`:
  `WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes`,
  `RingTheory.annihilatorAssociatedPrimes` (lines 25–31). The definition uses the
  exact annihilator `(⊥ : Submodule R M).colon {z}`, without a radical and
  without Noetherianity of R. It is used over both B and C.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `Spec.map` (lines 469–480). The underlying prime
  spectrum and the ring-map contraction encode the point correspondence here.

Plain proof imports match the recorded proof leaves:
`Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness` for
`associatedPrimes.finite`, and its public Basic import for
`biUnion_associatedPrimes_eq_zero_divisors` and `isAssociatedPrime_iff` (the latter
translates Mathlib's radical definition to exact annihilators over Noetherian C);
`Mathlib.RingTheory.Spectrum.Prime.Topology` for
`PrimeSpectrum.localization_comap_isEmbedding` and `localization_comap_range`;
`Mathlib.RingTheory.Ideal.Operations` for `Ideal.subset_union_prime`.
The relevant full source signatures and docstrings were read. No missing proof
module or import cycle was found.

Edge cases checked before writing and checked again against the final statement:

- M = 0, including N nonzero with N/m_A N = 0: Sigma contains zero, T = 0,
  both prime and maximal-ideal domains are empty, and both BijOn clauses are valid.
- B = 0 is allowed; A remains a nonzero local ring, and the fibre and localization
  are zero rings. No extra nontriviality instance is needed for B, C or T.
- Field base A = k: I = 0, so this specializes to the finite-module regular-scalar
  localization over a Noetherian B, as expected.
- B = k[x,y], N = B/(x) ⊕ B/(x,y): associated primes are nested and only (x,y)
  is maximal in the associated-prime set. The Maximal predicate gives this result.
- B = k[x,y]/(xy), N = B: two incomparable associated primes give two maximal
  ideals of the total fraction ring.
- A = Z_(p), B = A[t], N = B: only C = F_p[t] is used as Noetherian, and the
  contracted maximal ideal (p) of T need not be maximal in B. The signature
  imposes neither B-locality nor maximality of that contraction in B.

Searches actually run:

- `msearch.py leansearch`, query “Localization at elements injective on a finite
  module over a Noetherian quotient is semilocal with spectrum below associated
  primes”: 8 hits, including `PrimeSpectrum.localization_comap_injective`,
  `localizedModuleIsLocalizedModule`, and `Module.Finite.of_localized_maximal`.
  These state individual localization or finiteness facts, not this theorem.
- `msearch.py loogle`, query `associatedPrimes, IsLocalization`: 3 hits in
  `Mathlib.RingTheory.Ideal.AssociatedPrime.Localization`, concerning transfer
  of associated primes under localization, not the regular-scalar spectrum and
  maximal-ideal classification. Their signatures do not give an exact match.
- `msearch.py grep`, query
  `homothety|semilocal.*associated|associated.*semilocal|nonZeroSMulDivisors`,
  directory `RingTheory`: one unrelated power-series substitution hit.
- Earlier msearch grep of `RingTheory/LocalProperties` for
  `homothety|associatedPrimes|semilocal` found the Semilocal module, whose results
  assume a semilocal ring and prove local-to-global module properties; they do
  not construct the semilocal ring here.
- Direct rg of Mathlib found `nonZeroSMulDivisors`, its injectivity characterization,
  the canonical quotient-module action in Torsion.Basic, and the existing fraction
  and prime-contraction APIs, all reused rather than copied.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for `05DE`,
  `homothety-spectrum`, and `fibre_regular_localization_spectrum`, and
  `grep -rn 'lem-sfb-fibre-regular-localization-spectrum' lean/WeilConjectures`,
  found no declaration of the theorem. The Sheaf hits were docstrings referring
  to this item and the distinct 05DF universal-injectivity theorem. The latter
  has stronger hypotheses and a different conclusion and cannot serve this node.
- `dag/lean_names_upstream.json` contains the existing exact-annihilator definition
  but no declaration for this theorem. No new notion needed a new node.

The source statement, all accepted split fields and the five stmt_deps are
unchanged. No node fault or statement dispute was found.

Validation: the complete module compiled through scompile.py in both sandbox
and library naming modes, with no errors or warnings (10.5 s / 4.8 s before the
final import cleanup). The required delivery dry run recompiles the final file
and runs server preflight. All variables and universes are explicitly bound.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
