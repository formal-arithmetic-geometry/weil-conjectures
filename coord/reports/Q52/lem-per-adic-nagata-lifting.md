## Worker report

The module `Sheaf.RingTheory.AdicNagataLifting` states
`isNagataRing_of_isAdicComplete_quotient`, with its entire proof postponed by `sorry`.
No definitions, extra hypotheses, dependency repairs, or statement changes are needed.
The copied DAG node differs only in `lean`.

Statement correspondence, checked against the node and the definitions:

- A commutative ring A: `(A : Type u) [CommRing A]`, with `universe u` explicitly declared.
- A Noetherian ring: `[IsNoetherianRing A]`. This is the recorded Mathlib notion, every ideal finitely generated.
- An arbitrary ideal I of A: `(I : Ideal A)`. No properness, finite generation, principality, or locality assumption is added.
- A is I-adically complete: `[IsAdicComplete I A]`. Mathlib's class includes both separatedness and precompleteness. `AdicCompletion.of_bijective_iff` identifies this class with bijectivity of the canonical completion map, exactly the dependency node's definition.
- A/I is Nagata: `(h : IsNagataRing (A ⧸ I))`, using the actual quotient by I and the recorded upstream Nagata predicate.
- The conclusion A is Nagata: `IsNagataRing A`, with both Noetherianity and the N-2 condition for every prime quotient, as specified by the dependency definition.

Statement dependency declarations read and used:

- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete`, with its full signature, Hausdorff and precomplete parent classes, and `AdicCompletion.of_bijective_iff` at line 647.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, its docstring and abbreviation, and `isNoetherianRing_iff_ideal_fg`.
- `WeilConjectures.RingTheory.NagataRing`: `IsNagataRing`, its full definition and docstring; the module also defines `IsUniversallyJapanese`, which is not substituted for the node's Nagata predicate.

All recorded statement-dependency modules are public imports. Stated proof dependencies are plain imports: `WeilConjectures.RingTheory.JapaneseDomain` (`IsN2`), `WeilConjectures.RingTheory.FiniteModuleComplete` (`finite_module_complete_over_complete_noetherian`), and `WeilConjectures.RingTheory.FiniteOverNagata` (`finite_over_nagata_is_nagata`). Their definitions or full theorem signatures and docstrings were read. The two new statement-only normalization nodes, `lem-per-japanese-quotients-noetherian-normalization` and `lem-per-adic-noetherian-normalization-finite`, have no Lean attachment at the time of delivery, so there is no module to import yet; both remain named in the four-step proof docstring. They are proof prerequisites, not notions required to type this statement.

Source check: opened [Kurano–Shimomoto](https://www.isc.meiji.ac.jp/~kurano/ronbun/kurano40.pdf). Theorem 5.1 Step 1 (1-3), printed p.8, applies Marot's lifting property. Appendix A Definition A.1, printed p.14, defines lifting for any Noetherian ring complete along an ideal; printed p.15 states that Nagata has this property, citing Marot. This confirms exactly the node's hypotheses and conclusion. The theorem docstring carries all four accepted DAG proof steps, naming the finite-module completeness, quotient permanence, normalization Noetherianity, and normalization finiteness inputs.

Edge cases checked before writing:

- I=0: completeness imposes no restriction; the hypothesis is the Nagata property of A/0, so the conclusion agrees with the same property of A.
- I=top: separatedness forces A to be the zero ring. This case is retained and Nagata holds with no prime ideals; there is no Nontrivial assumption.
- Zero ring, arbitrary ideal: allowed. The prime quotient condition is vacuous.
- Nonlocal rings, nonprincipal ideals, positive or mixed characteristic: all retained; no local-ring, characteristic, or ideal-generator binders occur.
- Ring and quotient share the single arbitrary universe u; there are no quantifiers over test objects in smaller universes.

Searches actually run:

- `msearch.py leanfinder`, query `A Noetherian ring complete along an ideal is Nagata if its quotient by the ideal is Nagata`: eight hits, including Noetherian quotients, completion flatness, and Hausdorffness of domains, none stating Nagata lifting.
- `msearch.py loogle`, query `"IsNagataRing"`: zero hits.
- `msearch.py grep`, query `Nagata|Marot|UniversallyJapanese`: three Mathlib hits, all historical comments in Noether normalization and Euclidean domains.
- `rg -n 'Nagata|Marot|UniversallyJapanese|lem-per-adic-nagata-lifting'` in both `lean/WeilConjectures` and `lean/Sheaf`, followed by the focused RingTheory search `IsNagataRing|Marot|adic.*[Nn]agata|[Nn]agata.*adic`: existing Nagata definitions, quotient/localization/finite-algebra results, and complete-local Nagata theorem; no exact match for arbitrary complete Noetherian pairs.
- `grep -rn 'lem-per-adic-nagata-lifting' lean/WeilConjectures`: no match.
- Exact proposed theorem-name search in both Lean roots: no match. Search of `dag/lean_names_upstream.json` and current blueprint for the item id: no match.
- Repair-note filename/content search for this item: no matching note.

Validation: prescribed `scompile.py` compiled the sandbox and library forms successfully, in 1.3 and 1.7 seconds respectively, with no error or warning. Every binder is explicit and the file has no diagnostic commands. The declaration is a theorem with `sorry`, not a proof or a definition with missing data.

## Second reading by Q52

Independent clause-by-clause reading by the maintainer's reviewer (cc stage-2 review of head e3de97c1, 2026-10-24), replacing the worker's self-check.

Node statement as a list, with its Lean rendering and verdict:

- Objects: a commutative ring A; an ideal I of A. Lean: `(A : Type u) [CommRing A]`, `(I : Ideal A)`. Exact; I arbitrary (no properness or finite generation).
- Hypothesis: A Noetherian (def-weil-pbc-noetherian-ring = Mathlib `IsNoetherianRing`, every ideal f.g.). Lean: `[IsNoetherianRing A]`. Exact.
- Hypothesis: A I-adically complete (def-weil-pbc-adically-complete-ring: A → lim A/I^n bijective). Lean: `[IsAdicComplete I A]`, equivalent by `AdicCompletion.of_bijective_iff`. Exact, the recorded declaration.
- Hypothesis: A/I Nagata (def-weil-pbc-nagata-ring clause (2)). Lean: `(h : IsNagataRing (A ⧸ I))`, `IsNagataRing R := IsNoetherianRing R ∧ ∀ p prime, IsN2 (R ⧸ p) (FractionRing (R ⧸ p))` (WeilConjectures.RingTheory.NagataRing). Exact; not the universally Japanese clause.
- Conclusion: A Nagata. Lean: `IsNagataRing A`. Exact, neither weaker nor stronger.

Universes: one universe u for A; A ⧸ I lives in u, so `IsNagataRing` (Type u) applies without lift. No smaller-universe quantifier.

Edge cases: I = 0 (hypothesis is the conclusion); I = ⊤ (separatedness forces A = 0, conclusion vacuous on primes and Noetherian holds); zero ring; nonlocal A; any characteristic: all expressible, no Nontrivial/IsLocalRing/proper-ideal binder.

Source: Kurano–Shimomoto Theorem 5.1 Step 1 (1-3) and Appendix A (Marot, Prop. 2.3): a Noetherian ring complete along an ideal whose quotient is Nagata is Nagata. The statement is this, and true.

Duplicates: no project declaration states Nagata lifting for arbitrary complete Noetherian pairs; `isNagataRing_of_complete_local` (lem-weil-pbc-complete-local-nagata) is the narrower local case, `isQuasiExcellent_iff_quotient_of_isAdicComplete` is the quasi-excellent analogue (different node). The declaration name is free in lean/WeilConjectures and lean/Sheaf.

Records: node copy differs from the live node only in `lean`; `lean.statement` is verbatim the file signature; stmt_deps modules are public imports; proof-dep modules are plain imports; the module docstring has the source place and `(blueprint: lem-per-adic-nagata-lifting)`, the theorem docstring carries the four DAG proof steps; the proof is `sorry` only; no definitions.

No mismatch found; no change to the Lean or the node.
