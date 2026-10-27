## Worker report

The module Sheaf.RingTheory.FiniteMaximalSupportLocalization states
`Module.bijective_pi_localization_of_finite_maximal_support`, with one `sorry`
and no new definitions. The node's statement and dependencies are unchanged.

Hypothesis and clause correspondence:
- A commutative Noetherian ring is `(R : Type u) [CommRing R] [IsNoetherianRing R]`.
- A finite R-module is `(M : Type v) [AddCommGroup M] [Module R M]
  [Module.Finite R M]`. Ring and module universes are independent.
- The finite list of maximal ideals is `(r : ℕ) (m : Fin r → MaximalSpectrum R)`;
  each `(m i).asIdeal` is maximal by the bundled structure.
- Distinctness is `hdistinct : Function.Injective m`; equality of bundled maximal
  ideals is equivalent to equality of their ideals by extensionality.
- Every prime outside the list is represented by `q : PrimeSpectrum R` with
  `∀ i : Fin r, q.asIdeal ≠ (m i).asIdeal`. The `hsupport` hypothesis asserts
  `Subsingleton (LocalizedModule q.asIdeal.primeCompl M)`. A module is nonempty,
  so this is exactly vanishing, not merely a bound on its cardinality.
- The canonical R-linear map is `LinearMap.pi fun i : Fin r ↦
  LocalizedModule.mkLinearMap (m i).asIdeal.primeCompl M`. Mathlib's pi construction
  sends a vector to the tuple of component maps; mkLinearMap sends it to m/1.
- Being an isomorphism is `Function.Bijective` of that linear map; its inverse
  as a linear map is equivalently provided by `LinearEquiv.ofBijective`.
- The conclusion covers every listed ideal without requiring its localization
  to be nonzero. It also covers `r = 0`: the target is the one-element empty
  dependent product, so bijectivity states precisely that M is zero.

Dependency declarations used, with their signatures and docstrings read:
- def-weil-pbc-noetherian-ring: Mathlib.RingTheory.Noetherian.Defs,
  `IsNoetherianRing`, the abbreviation for being Noetherian over itself.
- def-weil-finitely-generated-module: Mathlib.RingTheory.Finiteness.Defs,
  `Module.Finite`, whose field says the top submodule is finitely generated.
- def-weil-pbc-module-localization: Mathlib.Algebra.Module.LocalizedModule.Basic,
  `LocalizedModule` and `LocalizedModule.mkLinearMap`, the latter explicitly m/1.
- The canonical product map uses Mathlib.LinearAlgebra.Pi, `LinearMap.pi`.
  The ideal complements use `Ideal.primeCompl`, and the index objects use
  `MaximalSpectrum` and `PrimeSpectrum`, with their ideal and primality fields.

Proof dependencies are imported privately: Mathlib.RingTheory.Support supplies
`Module.mem_support_iff_of_finite` and `Module.support_eq_zeroLocus` (00L2);
Mathlib.RingTheory.Spectrum.Prime.Topology supplies
`PrimeSpectrum.zeroLocus_eq_iff`, the ideal operations including
`Ideal.radical_eq_sInf`, and `MaximalSpectrum.toPiLocalizationEquiv` (00JA).
Their recorded declarations were read. The six proof steps of the node appear
in the theorem docstring, including the empty sublist and insertion of zero
factors. Source checked in literature/stacks-project/algebra.tex:
lemma-support-closed (00L2), lemma-product-local (00JA), and
lemma-artinian-finite-length (00JB).

Edge cases checked mathematically before writing:
- M = 0: all localization factors are zero, including arbitrary extraneous ideals.
- r = 0: the premise forces empty support; finite generation and the
  support-annihilator lemma force M = 0, as the product-map conclusion requires.
- The zero ring: there are no maximal ideals; r must be zero and every unital
  module is zero. No Nontrivial binder excludes this case.
- R = Z, M = Z/6, listed ideals (2), (3), optionally (5): the third factor is
  zero and does not obstruct bijectivity; the two retained factors give Z/2 × Z/3.
- R = k[x], M = R/(x²), with the maximal ideal (x): the localization map is an
  isomorphism even though R itself is not zero-dimensional. Thus the existing
  ring decomposition theorem cannot replace this module theorem directly.
- Listing an additional zero factor is harmless, but repeated nonzero factors
  would destroy surjectivity; the distinctness binder is retained.

Searches made through msearch.py (Q119, this item):
- leanfinder: "A finite module supported at finitely many distinct maximal ideals
  is isomorphic to the product of its localizations at those ideals". Eight
  hits, including Module.Finite.of_isLocalized_maximal,
  MaximalSpectrum.toPiLocalizationEquiv, and Dedekind-domain quotient results;
  none states the module map for this arbitrary ambient ring.
- loogle: "LocalizedModule.mkLinearMap, LinearMap.pi". Zero hits.
- grep in RingTheory: "support.*(IsMaximal|isMaximal)|pi.*[Ll]ocaliz|[Ll]ocaliz.*pi".
  Twenty-five hits; ring decompositions, finiteness descent, and tensor-product
  results do not state this canonical finite-support module decomposition.
- leansearch: "A finite module with finite support in the maximal spectrum is
  the product of its localizations". Eight hits on PiLocalization for rings,
  projectivity and finite-generation descent, without an exact module statement.
- rg in lean/WeilConjectures and lean/Sheaf for finite maximal support,
  localization bijectivity, and product localizations; grep of the item id in
  lean/WeilConjectures; rg of the proposed declaration name in both roots and
  dag/lean_names_upstream.json. No duplicate. The nearby upstream theorem
  Module.length_lt_top_of_finite_maximal_support proves finite length under
  different hypotheses; the existing AffineIsolatedDeformationLift module cites
  this item as a needed input without stating it.

No statement dispute, correction, missing notion, or unusable dependency found.
The statement compiles via scompile.py; only the expected sorry is present.

## Second reading by Q119

Independent reading (maintainer second reader, 2026-10-24) of the node, its
three statement dependencies, Stacks 00L2/00JA/07JZ and the module
Sheaf.RingTheory.FiniteMaximalSupportLocalization. It replaces the delivered
self-check section, which was not an independent reading.

Node clauses and their Lean:
- Commutative Noetherian ring R: `(R : Type u) [CommRing R] [IsNoetherianRing R]`
  (def-weil-pbc-noetherian-ring = `IsNoetherianRing`). Correct; the hypothesis
  is the node's own (mathematically unneeded, kept as stated).
- Finite R-module M: `(M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]`
  (def-weil-finitely-generated-module = `Module.Finite`). Correct; independent
  universes u, v, no extra instance.
- Distinct maximal ideals m_1..m_r: `(r : ℕ) (m : Fin r → MaximalSpectrum R)
  (hdistinct : Function.Injective m)`. Correct (MaximalSpectrum.ext gives
  injectivity on ideals). r = 0 allowed.
- M_q = 0 for every prime q not among the m_i: `hsupport : ∀ q : PrimeSpectrum R,
  (∀ i, q.asIdeal ≠ (m i).asIdeal) → Subsingleton (LocalizedModule q.asIdeal.primeCompl M)`
  (def-weil-pbc-module-localization = `LocalizedModule`). Subsingleton of a module
  is vanishing. Exactly the node; no condition at the listed ideals.
- Canonical map m ↦ (m/1)_i is an isomorphism: `Function.Bijective (LinearMap.pi
  fun i ↦ LocalizedModule.mkLinearMap (m i).asIdeal.primeCompl M)`; mkLinearMap is
  m ↦ m/1, LinearMap.pi is the tuple map; a bijective R-linear map is an
  R-linear isomorphism (LinearEquiv.ofBijective). Not weaker, not stronger.

Edge cases: r = 0 (target is the one-point product; bijectivity ⇔ M = 0, as the
node says); listed ideals with M_m = 0 (factor zero, still bijective, e.g. Z/6 at
(2),(3),(5)); M = 0; zero ring (no maximal ideals, r = 0, M = 0); positive-dimensional
R (k[x], M = k[x]/(x²) at (x)). The distinctness binder is necessary (repeated
nonzero factor breaks surjectivity). Truth of the statement checked against the
node proof (support = V(Ann M), 00JA decomposition of R/Ann M, idempotents).

H4: grep of Mathlib for `LinearMap.pi` with `mkLinearMap`, support/maximal
decompositions (only ring-level `MaximalSpectrum.toPiLocalizationEquiv` and
`CompleteOrthogonalIdempotents.bijective_pi`); project lean/WeilConjectures and
lean/Sheaf: nearest is `Module.length_lt_top_of_finite_maximal_support`
(lem-sc-finite-length-finite-maximal-support, finite length, different
conclusion). No duplicate.

Gates: module and theorem docstrings carry the source place and
`(blueprint: lem-sfb-finite-maximal-support-localization)`; the six proof steps
are in the docstring; proof is `sorry`; no definitions; `lean.statement` is
verbatim the file's signature; stmt_deps match the declarations used
(LinearMap.pi, Ideal.primeCompl, Maximal/PrimeSpectrum are ambient Mathlib API).
No mismatch found; no Lean change.
