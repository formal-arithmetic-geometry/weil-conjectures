## Worker report

The module `Sheaf.RingTheory.NagataNormalFormalFibresLifting` states
`normal_formal_fibres_of_adically_complete`, with its whole proof `sorry`.
The item's statement is unchanged; no new definition or dependency module is needed.
The auxiliary condition N is expanded twice in the theorem, rather than introducing a
second definition of a ring-theoretic notion. All its constituents are existing declarations.

Clause-by-clause correspondence:

- Commutative Noetherian A: `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
- Ideal I of A: `(I : Ideal A)`, without a properness or nonzero restriction.
- I-adic completeness: `[IsAdicComplete I A]`. This includes separatedness and is
  equivalent to bijectivity of the canonical completion map, as the dependency specifies.
- Nagata closed fibre: `(hNagata : IsNagataRing (A ⧸ I))`, using the upstream predicate.
- The hypothesis N(A/I): the entire binder `hN`, beginning with
  `∀ (p : Ideal (A ⧸ I)) [p.IsPrime]`.
- The conclusion N(A): the same expression with `∀ (p : Ideal A) [p.IsPrime]`.
- In either N expression, B = R_p is `Localization.AtPrime p` and the completion C is
  `AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
  (Localization.AtPrime p)`. The maximal ideal is pB by
  `Localization.AtPrime.map_eq_maximalIdeal` in the recorded localization dependency.
  Mathlib indexes completion from n = 0; its zero quotient is forced and adding it to
  the inverse system indexed from n = 1 does not change the compatible sequences.
- Every prime q of B: `(q : Ideal (Localization.AtPrime p)) [q.IsPrime]`.
- Every finite purely inseparable k/κ(q): `(k : Type (max u v)) [Field k]
  [Algebra q.ResidueField k] [Module.Finite q.ResidueField k]
  [IsPurelyInseparable q.ResidueField k]`. Both finiteness and pure inseparability
  use their recorded declarations. There is no separate characteristic assumption.
- The tested extended fibre is `TensorProduct q.ResidueField k (q.Fiber C)`.
  By the recorded fibre declaration, `q.Fiber C = q.ResidueField ⊗[B] C`.
  The source writes C ⊗[B] κ(q) instead; the canonical tensor symmetry identifies
  these κ(q)-algebras, so no change of fibre or additional hypothesis is involved.
- Normality of that ring is exactly `∀ (s : Ideal (TensorProduct ...)) [s.IsPrime],
  IsDomain (Localization.AtPrime s) ∧ IsIntegrallyClosed (Localization.AtPrime s)`.
  This is the inline convention recorded for def-weil-pbc-normal-ring, not the
  stronger assertion that the entire extended fibre is a domain.

Statement dependency declarations read and used:

| Node | Module | Declaration |
| --- | --- | --- |
| def-weil-pbc-noetherian-ring | Mathlib.RingTheory.Noetherian.Defs | IsNoetherianRing |
| def-weil-pbc-localization-at-prime | Mathlib.RingTheory.Localization.AtPrime.Basic; Mathlib.RingTheory.LocalRing.ResidueField.Ideal; Mathlib.RingTheory.LocalRing.ResidueField.Fiber | Localization.AtPrime; Ideal.ResidueField; Ideal.Fiber |
| def-weil-pbc-adic-completion | Mathlib.RingTheory.AdicCompletion.Basic; Mathlib.RingTheory.AdicCompletion.Algebra | AdicCompletion |
| def-weil-pbc-finite-purely-inseparable-extension | Mathlib.FieldTheory.PurelyInseparable.Basic | IsPurelyInseparable; Module.Finite |
| def-weil-pbc-normal-ring | Mathlib.RingTheory.IntegralClosure.IntegrallyClosed; Mathlib.RingTheory.Localization.AtPrime.Basic | IsIntegrallyClosed; IsDomain; Localization.AtPrime, inline as recorded |
| def-weil-pbc-adically-complete-ring | Mathlib.RingTheory.AdicCompletion.Basic | IsAdicComplete |
| def-weil-pbc-nagata-ring | WeilConjectures.RingTheory.NagataRing | IsNagataRing |

The source signatures and docstrings of all seven dependencies were read locally.
The imports of statement dependencies are public. Plain proof imports retain the
already recorded proof interfaces: FiniteOverNagata, FormalFibreQuotientIso,
FiniteModuleComplete, JapaneseDomain, CompletionFiniteExtension, tensor cancellation
(Mathlib.RingTheory.TensorProduct.Maps), integral-closure fraction fields
(Mathlib.RingTheory.Localization.Integral), localization base change
(Mathlib.RingTheory.Localization.BaseChange), and fraction-field localization
(Mathlib.RingTheory.Localization.LocalizationLocalization). Integral closedness under
localization is already publicly imported. The three proof nodes
lem-per-adic-nagata-lifting, lem-per-finite-algebra-normal-formal-fibres and
lem-per-normal-minimal-quotient-analytic-normality have no recorded Lean module in the
read snapshot, so have no import yet. They are proof prerequisites, not notions needed
to type the present statement. The theorem docstring includes all six proof steps and
names their nodes, including the nonzero-contraction argument and zero localizations.

Edge cases checked before writing:

- Zero ring: no primes p, so N is vacuous; no Nontrivial or IsDomain binder excludes it.
- I = 0: completeness is automatic, and the conclusion is the same N condition assumed
  on the canonically identical quotient. This case is retained.
- I = top: separatedness forces A to be the zero ring; it remains a permitted case.
- The identity field extension is permitted, including in characteristic zero.
- In positive characteristic, all finite purely inseparable extensions are tested,
  rather than only the identity or one chosen perfect closure.
- Fibres may be zero or products: normality uses prime localizations and is vacuous
  for the zero ring. No domain assumption is imposed on a whole fibre.
- The field universe is `max u v`, never an independent smaller universe. Every
  residue field has universe u and can be lifted to this universe; finite extensions
  have a universe-u representative because they are finite dimensional. Thus the test
  is not empty for size reasons and omits no extension up to algebra isomorphism.

Searches (all made through the prescribed msearch wrapper or read-only rg/grep):

1. leanfinder: `An ideal adically complete Noetherian ring has geometrically normal
   formal fibres when its quotient is Nagata and has geometrically normal formal fibres`.
   Eight hits: completion flatness and tensor completion, smooth flatness, quasi-finite
   fibres/at-prime, formally smooth flatness, and scheme normalization. No lifting match.
2. loogle: `"IsAdicComplete", "IsIntegrallyClosed"`. Zero hits.
3. Mathlib grep: `Nishimura|[Nn]ormalFormal|[Nn]ormal[Ff]ormal|[Gg]eometricallyNormal|
   [Gg]eometrically[Nn]ormal|formal.*[Ff]ib.*[Nn]ormal`. Zero hits.
4. rg over lean/WeilConjectures and lean/Sheaf for normal-formal-fibre terminology,
   geometrically normal names, and the item id: only unrelated formal normalization,
   conormal, or geometrically-normal scalar-extension modules. No N predicate or lifting
   theorem. A narrower scan of RingTheory likewise found no match.
5. `grep -rn "lem-per-nagata-normal-formal-fibres-lifting" lean/WeilConjectures`: no hits.
6. rg over both project roots, Mathlib and dag/lean_names_upstream.json for the chosen
   name `normal_formal_fibres_of_adically_complete`: no hits.
7. DAG search for geometrically normal formal fibres and Z-ring found this node and
   its related theorem nodes, not an independent existing definition of N.

Source checked: https://www.isc.meiji.ac.jp/~kurano/ronbun/kurano40.pdf,
Theorem 5.1 Step 1 (1-4), Appendix A Definition A.1(1) and the Nagata Z-ring row.
These identify the lifting property and the cited Nishimura–Nishimura input.
No statement correction, dependency repair, or STATEMENT-DISPUTED issue was found.

Validation: scompile.py compiled the sandbox file and its library module separately
against the live publication, in 2.8 s and 2.9 s respectively, with no errors or
unexpected warnings. Every theorem proof remains `sorry`; no data definition is added.

## Second reading by Q34

The dispatcher explicitly prohibits starting another agent. This is therefore a second
in-thread reading, not a claim of an independent worker review; the maintainer's
independent review is requested by the delivery workflow.

Reopened the node copy and complete Lean module. Matched the Noetherian ring, ideal,
completeness and Nagata hypotheses; matched N on A/I and A separately. In each copy,
checked the sequence of primes p of R, q of R_p, arbitrary finite purely inseparable
k/κ(q), and s of the actual extended fibre. Checked both normal-domain conjuncts at s.
The inner tensor orientation is the mandated Ideal.Fiber convention and differs from
the displayed order by its canonical algebra symmetry only. The larger common field
universe retains all finite tests. No extra proper/nonzero/domain or characteristic
restriction occurs. There are no lets, auto-bound variables, file-local notation,
private notions, auxiliary sorries, new nodes or statement changes. No mismatch was
found, and no mathematical change was made on this second reading.

Dry-run repair: removed the terminal `:=` from lean.statement, as the preflight
records the signature up to (excluding) the proof delimiter. Lean source unchanged.
