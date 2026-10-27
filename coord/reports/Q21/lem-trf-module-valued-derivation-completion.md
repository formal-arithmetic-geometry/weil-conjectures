## Worker report

Item: `lem-trf-module-valued-derivation-completion`, group Q21, 2026-10-24 UTC.

The module `Sheaf.RingTheory.ModuleValuedDerivationCompletion` states
`Derivation.exists_unique_continuous_module_completion`, with one `sorry` and no definitions.
The original node is unchanged except for its `lean` record. No new nodes, dependency repairs,
or statement corrections are needed.

The source was read in `literature/stacks-project/more-algebra.tex`,
`lemma-derivation-extends` (Tag 07PE), especially the shifted-quotient proof of (1), and
Mathlib's statements of Tag 05GG in `AdicCompletion/Completeness.lean`.
The declaration docstring carries all six proof steps of the node, including the
module-valued Leibniz calculation, compatibility, the completion-kernel identification,
the continuity bound, and uniqueness by separatedness.

Hypotheses and objects, clause by clause:

| Node | Lean rendering |
| --- | --- |
| A commutative ring k | `{k : Type u} [CommRing k]` |
| A commutative k-algebra A | `{A : Type v} [CommRing A] [Algebra k A]` |
| A finitely generated ideal I | `(I : Ideal A) (hI : I.FG)` |
| An arbitrary A-module M | `(M : Type w) [AddCommGroup M] [Module A M]`; no finiteness or separatedness assumption |
| A k-derivation d into M | `@Derivation k A M ... (Module.compHom M (algebraMap k A))`; the base action is canonically induced by the A-action |
| C and N are the indicated inverse limits | `AdicCompletion I A`, `AdicCompletion I M` |
| Canonical map iota | `algebraMap A (AdicCompletion I A)` |
| Canonical map j | `AdicCompletion.of I M` |
| Componentwise C-action on N | Mathlib's `AdicCompletion.module I`; the class argument of each completed derivation is synthesized from this instance |
| Extended ideal J = IC | `I.map (algebraMap A (AdicCompletion I A))` |
| Q_r = M/I^r M | `M ⧸ (I ^ r • ⊤ : Submodule A M)` |
| Reduction q_r | `AdicCompletion.transitionMap I M (Nat.le_succ r)` |
| Positive indices | Every family or conclusion has `(hr : 1 ≤ r)` or `1 ≤ r →`; the family is indexed by both r and its positivity proof |
| d_r is a k-derivation A/I^(r+1) → Q_r | The existential family `dQ` has exactly the `Derivation` type for those source and target types |
| Scalar action through A/I^(r+1) → A/I^r | The source-ring action in `dQ` is `Module.compHom Q_r (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ r)))`, pulling back Mathlib's quotient-module action; its k-action is the canonical restriction from A |
| Formula d_r(a mod I^(r+1)) = d(a) mod I^r M | The first conjunct, `dQ r hr (Ideal.Quotient.mk ... a) = (I ^ r • ⊤).mkQ (d a)`; this also determines each d_r on all classes |
| delta_r(x) = d_r(x_(r+1)) | Written directly as `dQ r hr (AdicCompletion.evalₐ I (r + 1) x)` |
| q_r delta_(r+1) = delta_r | Second conjunct applies the canonical reduction to `dQ (r + 1) ... (evalₐ I (r + 2) x)` and equates it to delta_r |
| Existence of a k-derivation D : C → N | `∃ D : @Derivation k (AdicCompletion I A) (AdicCompletion I M) ...`; the k-action is restriction of the canonical C-action |
| D iota = j d | First conjunct under D, quantified over `a : A` |
| Continuity with positive s for each positive r | Next conjunct `∀ r, 1 ≤ r → ∃ s, 1 ≤ s ∧ ∀ x, x ∈ J ^ s → D x ∈ I ^ r • (⊤ : Submodule A N)` |
| Uniqueness among all continuous extensions | Next conjunct quantifies every completed derivation E, assumes only its extension equality and the same continuity criterion, and concludes `E = D`; it does not assume the coordinates or the sharper bound for E |
| Coordinates of D | Next conjunct, `AdicCompletion.eval I M r (D x) = dQ r hr (AdicCompletion.evalₐ I (r + 1) x)` |
| Equivalent formula for any lift a modulo J^(r+1) | Next conjunct assumes `x - algebraMap A C a ∈ J ^ (r + 1)` and equates the r-coordinate to `(I ^ r • ⊤).mkQ (d a)` |
| D(J^(r+1)) is contained in I^r N | Last conjunct, pointwise membership for each positive r |

Mathlib includes the zeroth coordinate in `AdicCompletion`; that coordinate is the unique
class in M/M (and A/A). Removing it gives exactly the positive-index inverse limits of
the node. No extra condition or case is introduced. There are no local notations, local
instances, auxiliary copies of definitions, `let` expressions in the signature, or
unbound implicits. The universes u, v, w are independent and explicitly declared.

Dependency declarations read and used:

- `def-weil-pbc-kahler-differentials`: recorded module
  `Mathlib.RingTheory.Kaehler.Basic`, declarations `KaehlerDifferential`,
  `KaehlerDifferential.D`, and `KaehlerDifferential.linearMapEquivDerivation`.
  Their signatures and docstrings identify the derivation notion; the statement uses
  the existing `Derivation` type made available by that public import.
- `def-weil-pbc-adic-completion`: recorded module
  `Mathlib.RingTheory.AdicCompletion.Basic`, declaration `AdicCompletion` and companion
  `IsAdicComplete`. Public import `Mathlib.RingTheory.AdicCompletion.Algebra` supplies
  these same definitions, `evalₐ`, `eval`, `of`, and the componentwise completed action.
  Both the recorded compatible-sequence definition and these map signatures were read.
- Proof dependency `lem-weil-pbc-module-completion-complete`: its Mathlib match identifies
  `AdicCompletion.isAdicComplete`, `AdicCompletion.pow_smul_top_eq_ker_eval`, and
  `AdicCompletion.eval_surjective`. The completeness module is imported privately, as a
  proof dependency; its relevant theorem signatures and docstrings were read.
- The quotient action uses existing `Module.compHom`, `Ideal.Quotient.factor`,
  `Ideal.pow_le_pow_right`, and Mathlib's `Module (A ⧸ I^r) (M ⧸ I^r • ⊤)` instance
  in `Mathlib.Algebra.Module.Torsion.Basic` (transitively imported).

Edge cases checked before and after writing:

- `I = ⊥`: the positive quotients recover A and M, J is zero, and D is d under those
  canonical identifications; continuity holds for every derivation. The quotient at
  index zero remains harmless.
- `I = ⊤`: C and N and all positive quotients are zero; the sole completed derivation
  and all quotient derivations are zero. No nontriviality hypothesis excludes this case.
- `M = 0`, zero rings, and zero derivation: all constructions and identities remain typed.
- `r = 1`: the quotient derivation is A/I² → M/IM; compatibility uses coordinates 3
  and 2, and the last bound is D(J²) ⊆ IN. No first-positive-coordinate case is lost.
- Nilpotent I: the limits stabilize; the shifted formula and uniqueness agree with d.
- M need not be finitely generated, faithful, or initially complete. Only I is FG,
  matching Tag 05GG's module theorem. No characteristic or universe is restricted.

Searches made (all on 2026-10-24; wrapper records are in sandbox `searches.jsonl`):

- `msearch.py ... leansearch "A derivation into a module extends uniquely continuously
  to the ideal adic completion"`: 8 hits, including `AdicCompletion.map_ext'`,
  `AdicCompletion.map_ext''_iff`, completion extensions of continuous linear maps,
  `AdicCompletion`, and `IsAdicComplete`; none is the module-derivation theorem.
- `msearch.py ... leanfinder "A module valued derivation extends uniquely and
  continuously to the adic completions via shifted quotient derivations"`: 8 hits,
  including `IsAdicComplete.lift`, `AdicCompletion.lift`, `AdicCompletion.map`,
  `AdicCompletion.map_ext''`, and `derivationToSquareZeroEquivLift`; no exact match.
- `msearch.py ... loogle "Derivation, AdicCompletion"`: zero hits.
- `msearch.py ... grep "[Dd]erivation.*[Cc]ompletion|[Cc]ompletion.*[Dd]erivation"`:
  zero Mathlib hits.
- `rg` with the same concept regex over `lean/WeilConjectures` and `lean/Sheaf` found
  `WeilConjectures.RingTheory.Derivation.CompletionAndLocalization` and specialized
  completed-differential comparisons. Its full completion theorem and construction
  were read: the upstream theorem is for Z-derivations R → R, and neither states this
  arbitrary-target-module result nor the continuous uniqueness assertion. Its quotient
  constructions are private and ring-valued. The specialized comparisons impose local
  and differential-module hypotheses absent here.
- `rg` for `lem-trf-module-valued-derivation-completion` in both source roots found no
  existing declaration. `rg` for the new declaration name in both roots and
  `dag/lean_names_upstream.json` also found no collision.

Validation: `scompile.py Q21 lem-trf-module-valued-derivation-completion
<.../ModuleValuedDerivationCompletion.lean>` succeeded for the sandbox module and the
library module, each in 1.5 seconds under the default 60-second limit, with no errors or
unexpected warnings. The single postponed theorem is intentional stage-2 work.
No node faults or disputed statements were found.

## Second reading by Q21

The dispatcher explicitly forbids starting other agents and assigns independent review to
the maintainer. This section records this worker's separate second pass with the original
node and finished Lean file open; it does not claim a second agent reviewed the delivery.

The second pass checked every row above against the node's exact wording. In particular,
`dQ` is a genuine Mathlib derivation with the source action through the successive quotient,
not just an additive map; the family only asserts positive indices; the compatibility
indices are r+2 and r+1; both coordinate formulations are present; and uniqueness requires
only continuity and the original extension equation, not the constructed coordinate
formula or the stronger exponent bound. The input and output k-actions are induced from
the given A-action and the canonical C-action, so there is no hidden extra module-action
hypothesis. The explicit `Module.compHom` arguments avoid making such a choice an input.
The bound uses J in the domain and the A-submodule I^r N in the codomain, exactly as stated.
All variables and universes are bound, the proof is only `sorry`, and the node's fields
outside `lean` are identical to the original. No mismatch or further change was found.
