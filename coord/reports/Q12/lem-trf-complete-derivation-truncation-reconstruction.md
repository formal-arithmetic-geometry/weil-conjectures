## Worker report

The module `Sheaf.RingTheory.CompleteDerivationTruncationReconstruction` states
`KaehlerDifferential.completeDerivationTruncationReconstruction`, with exactly one
postponed theorem and no new definitions. The node is unchanged except for `lean`.
The full six-step natural-language proof is in the theorem docstring.

Sources read: `literature/stacks-project/algebra.tex`, the presentation preceding
Definition `definition-differentials` (Tag 07BK), Lemma `lemma-universal-omega`
(Tag 00RO), and Lemma `lemma-differential-mod-power-ideal` (Tag 02HQ). The full
reconstruction is the agent auxiliary argument recorded in the node, not a claim
that Stacks states this entire theorem. The current blueprint proof of
`lem-trf-local-term-locality` was also read: its contracting-correspondence argument
does not assert this inherited completed-Jacobian auxiliary lemma, as the node
already records.

The Lean index is `n : ℕ`, corresponding throughout to the node's `r = n + 1`.
No positive truncation is omitted. Here is every hypothesis and clause:

| Node | Lean |
| --- | --- |
| Commutative ring k and commutative k-algebra R | Independent `k : Type u`, `R : Type v`, `[CommRing k] [CommRing R] [Algebra k R]`. |
| R-module N | Independent `N : Type w`, `[AddCommGroup N] [Module R N]`; `[Module k N] [IsScalarTower k R N]` expose its compatible restricted scalar action for Mathlib's derivation type. Any R-module has this restricted action; no finiteness or universe equality is assumed. |
| Ideal m | `m : Ideal R`. |
| Canonical iota is an isomorphism | `hcomplete : Function.Bijective (AdicCompletion.of m N)`. This is the actual canonical linear map, not an arbitrary isomorphism. Mathlib includes exponent zero, where `m ^ 0 • ⊤ = ⊤`, so that quotient is zero. Deleting or adjoining its unique component gives exactly the positive-index limit. |
| k-derivation delta | `δ : Derivation k R N`. |
| Finite generating values delta(x_i), allowing d = 0 | `d : ℕ`, `x : Fin d → R`, and `hgen : Submodule.span R (Set.range (fun i : Fin d ↦ δ (x i))) = ⊤`. |
| R_r and C_r | Written directly as `R ⧸ m ^ (n + 1)` and `KaehlerDifferential k (R ⧸ m ^ (n + 1))`, with their quotient-induced R-module structures. |
| tau_r | Existing `KaehlerDifferential.adicTransition k R m n`. |
| C, the compatible-tuples limit | Existing `KaehlerDifferential.Continuous k R m`, whose coordinate n is C_(n+1). |
| Given R-linear phi_r | The family `φ : ∀ n : ℕ, N →ₗ[R] KaehlerDifferential k (R ⧸ m ^ (n + 1))`. |
| tau_r phi_(r+1) = phi_r | `hcompat`, equality of the composed linear maps. |
| phi_r delta(a) = d(a mod m^r) for every a | `hφ`, using the existing universal derivation `D` and `Ideal.Quotient.mk`. |
| delta(m^(r+1)) is contained in m^r N | First conjunct, `∀ n a, a ∈ m ^ (n + 2) → δ a ∈ (m ^ (n + 1) • ⊤ : Submodule R N)`. |
| Existence of the shifted R-linear eta_r | Existential family `η`, from differentials modulo `m ^ (n + 2)` to `N ⧸ (m ^ (n + 1) • ⊤)`. |
| Values of eta_r on all d(a mod m^(r+1)) | First conjunct under `∃ η`, with `D`, `Ideal.Quotient.mk`, and the module quotient `mkQ`. |
| Uniqueness of eta_r | Next conjunct: for every n and every R-linear f of that same type, the stated differential-symbol values imply `f = η n`. Together with the preceding values this is exactly unique existence at each level. |
| rho_r and pi_r are the quotient maps | Existing `Submodule.factorPowSucc m N (n + 1)` and `(m ^ (n + 1) • ⊤ : Submodule R N).mkQ`. |
| rho_r eta_(r+1) = eta_r tau_(r+1) | Next conjunct, equality of composed linear maps. Both sides have domain C_(r+2) and codomain Q_r. |
| eta_r phi_(r+1) = pi_r | Next conjunct, `(η n).comp (φ (n + 1)) = ...mkQ`. |
| Each phi_r induces phibar_r | Existential R-linear family `φbar`, with `(φbar n).comp ...mkQ = φ n`. Surjectivity of mkQ determines the induced map uniquely; it is not an arbitrary map. |
| phibar_r eta_r = tau_r | Next conjunct, `(φbar n).comp (η n) = adicTransition k R m n`. |
| Phi(z) = (phi_r(z))_r | Existential R-linear `Φ` into the existing `Continuous` module, followed by `∀ z n, (Φ z).val n = φ n z`. Equality of tuples uniquely specifies Phi. |
| Psi(c) = iota inverse applied to (eta_r(c_(r+1)))_r | Existential R-linear `Ψ`; for every c there is `q : AdicCompletion m N` whose every positive component is `η n (c.val (n + 1))`, and `Ψ c = (LinearEquiv.ofBijective (AdicCompletion.of m N) hcomplete).symm q`. The zero component is forced, so q is precisely the displayed compatible tuple, not an additional choice or hypothesis. |
| Psi Phi = id_N and Phi Psi = id_C; Phi is an isomorphism | Final two equalities `Ψ.comp Φ = LinearMap.id ∧ Φ.comp Ψ = LinearMap.id`. These give both inverse identities and precisely express that the specified linear maps are mutually inverse isomorphisms. |

Dependency declarations read and used:

- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`,
  `KaehlerDifferential.D`, and the universal property
  `KaehlerDifferential.linearMapEquivDerivation`. These are the recorded
  declarations of `def-weil-pbc-kahler-differentials`; the first two occur in the
  signature and the universal property supplies Step 2 of its proof docstring.
- `Sheaf.RingTheory.ContinuousKaehlerDifferential`:
  `KaehlerDifferential.adicTransition`, `continuousSubmodule`, `Continuous`, and
  `continuousD` were read in full. The first and third occur in the signature.
  This is the unchanged record of `def-trf-continuous-kahler-differentials`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`,
  `AdicCompletion.of`, and `AdicCompletion.eval` were read, including the actual
  compatible-family definition and canonical coordinates.
- The imported Mathlib transition interface `Submodule.factorPowSucc`, in
  `Mathlib.RingTheory.Ideal.Quotient.PowTransition`, is the actual quotient map.

Edge cases checked before writing:

- `d = 0` is allowed. The empty span equals bottom, so the generation hypothesis
  forces N to be zero, exactly as Step 3 of the node says. No nonempty family
  instance or positive-d hypothesis was introduced.
- The first level `n = 0` means r = 1: delta(m²) lies in mN, eta maps C₂ to Q₁,
  and its transition equation has domain C₃. The inverse uses c₂ at this level.
- `m = ⊥` is allowed. The positive quotients of R are R and N's completion is N;
  the statement reduces to universal-differential reconstruction under the
  specified splitting and generation assumptions.
- `m = ⊤` is allowed. All quotients and differentials are zero; completeness
  forces N to be zero. Both inverse identities then concern zero modules.
- The zero ring, zero module, arbitrary characteristic, and non-Noetherian rings
  are all allowed. No finite generation of m or additional complete-ring
  hypothesis is present. The completeness hypothesis is exactly bijectivity of
  the canonical module map, not a claim that all completions are complete.
- The three type universes are independent. The differential module has R's
  universe; the module quotients have N's universe. Both families of linear maps
  and the reconstruction compile without equating them.

Searches actually made with the prescribed msearch.py wrapper:

- LeanFinder: `A complete module generated by a derivation is isomorphic to the
  inverse limit of Kahler differentials of ideal power quotients via compatible
  maps` returned 8 hits, including `KaehlerDifferential.endEquivDerivation'`,
  `KaehlerDifferential.linearMapEquivDerivation_symm_apply`,
  `Derivation.liftKaehlerDifferential_apply`, and quotient-kernel equivalences.
  None states this shifted reconstruction theorem.
- Loogle: `KaehlerDifferential, AdicCompletion` returned 0 hits.
- Mathlib grep under RingTheory:
  `continuous.*[Dd]ifferential|[Dd]ifferential.*[Cc]omplet|derivation.*[Aa]dic`
  returned 0 hits.
- LeanSearch: `Reconstruct an adically complete module from a generating
  derivation and compatible maps into quotient Kahler differentials` returned
  8 hits, including `AdicCompletion`, `IsAdicComplete`, `AdicCompletion.of`, and
  the completion lift API. These supply the existing completion notion, not the
  differential reconstruction result.
- Source/project rg over `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `complete_derivation`, `truncation_reconstruction`, `adicTransition`, and
  `continuousSubmodule` found the recorded continuous-differential module and
  related adic constructions, but no reconstruction theorem. A separate search
  for the proposed declaration name in these trees and
  `dag/lean_names_upstream.json` found no collision.

Validation: scompile.py compiled the sandbox and canonical library module on the
server successfully (1.5 s and 1.6 s), with no diagnostics. No statement fault or
STATEMENT-DISPUTED issue was found. No new nodes or dependency repairs are needed.

## Second reading by Q12

A second pass by this same dispatcher-started worker, without starting another
agent as the brief requires, compared the node and completed Lean file directly.
The crucial index check is that `η n` has domain C_(n+2), while `φ n` targets
C_(n+1). Thus the shifted inverse uses `c.val (n + 1)`, the rho compatibility uses
`adicTransition ... (n + 1)`, and the phibar compatibility uses
`adicTransition ... n`. All three match the node's distinct formulas. The
uniqueness quantifier ranges over R-linear maps, not just quotient-ring-linear
maps, as the node requires. The proof of this equivalence of scalar linearity is
included in the natural-language descent argument.

The rereading also checked that hcomplete concerns the canonical map; the
completion witness q has every positive coordinate prescribed and only a forced
zero coordinate; both inverse identities are explicit; and the induced quotient
map is tied to φ by its factorization equation. The scalar restriction binders
are compatible module structures, not finiteness or completeness assumptions.
Every node hypothesis and conclusion is accounted for in the table above. No
mismatch was found, and no statement or dependency change was made.
