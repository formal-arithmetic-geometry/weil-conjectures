## Worker report

The module `Sheaf.RingTheory.FibrewiseZeroKaehlerDifferentials` states
`KaehlerDifferential.finite_and_vanishing_of_fiber_vanishing`. Its only theorem proof
is `sorry`; there are no definitions or additional helper statements. Only the item's
`lean` field changes. No new nodes, dependency repairs, or statement corrections are needed.

Sources read: `literature/stacks-project/algebra.tex`, lemma-unramified (00UV), especially
proofs (7)--(9) and (11); lemma-differentials-base-change (00RV);
lemma-differentials-finitely-generated (00RZ); lemma-NAK (00DV), especially part (8).
Also read morphisms.tex, lemma-unramified-etale-fibres (02G8), part (2). The theorem's
docstring carries all seven DAG proof steps, including the canonical fraction/tensor maps,
Nakayama for the empty family, and the maximal-localization zero-map argument.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Commutative rings R and A: `(R : Type u) (A : Type v) [CommRing R] [CommRing A]`.
  Both universes are explicitly declared and independent.
- Ring homomorphism R → A: `[Algebra R A]`, whose homomorphism is `algebraMap R A`.
  This represents every unital ring homomorphism via its `RingHom.toAlgebra` structure;
  no injectivity, surjectivity, field, or nonzero-ring condition is assumed.
- Finitely many R-algebra generators: `[Algebra.FiniteType R A]`, the standard
  finite-generation-of-the-top-subalgebra predicate, not module finiteness or finite
  presentation. It does not restrict the cardinality of R or A.
- Every prime p of R: `∀ (p : Ideal R) [p.IsPrime]` in `hfib`.
- κ(p) = R_p / pR_p: `p.ResidueField`, Mathlib's residue field of
  `Localization.AtPrime p`.
- Ordinary fibre C_p and its natural κ(p)-algebra structure: `p.Fiber A` is definitionally
  `p.ResidueField ⊗[R] A`, with its standard left-factor algebra structure. The recorded
  localization dependency explicitly specifies this tensor-factor convention. The
  node's A ⊗_R κ(p) is canonically isomorphic through `Algebra.TensorProduct.comm`;
  switching factors preserves the distinguished κ(p)-algebra and its differentials.
  This is an ordinary algebra fibre, not a geometric fibre or a localized algebra.
- Vanishing of Ω[C_p/κ(p)] for every p: the remainder of `hfib` is
  `Subsingleton (KaehlerDifferential p.ResidueField (p.Fiber A))`.
  Since these are additive groups, `Subsingleton` is exactly the zero-module condition.
- M = Ω[A/R]: written directly as `KaehlerDifferential R A` throughout; no arbitrary M
  or additional identification is introduced.
- M finitely generated over A: the first conjunct is
  `Module.Finite A (KaehlerDifferential R A)`.
- Every prime q of A: `∀ (q : Ideal A) [q.IsPrime]` in the middle conjunct.
  The p mentioned in the node's conclusion is the contraction
  `q.comap (algebraMap R A)`, determined by q; neither displayed conclusion involves p.
  Therefore a separate p binder/equality is unnecessary. The proof docstring identifies
  the contraction, its residue-field map and the corresponding use of `hfib`.
- M ⊗_A κ(q) = 0: the first primewise conjunct is
  `Subsingleton (TensorProduct A (KaehlerDifferential R A) q.ResidueField)`.
  Its tensor factors are in exactly the node's order.
- M_q = (A \ q)^(-1)M = 0: the second primewise conjunct is
  `Subsingleton (LocalizedModule q.primeCompl (KaehlerDifferential R A))`.
  Thus the module is localized, not replaced by a different algebra's differential module.
- Consequently Ω[A/R] = 0: the last conjunct is
  `Subsingleton (KaehlerDifferential R A)`.

Dependency declarations read and used:

- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` in
  `Mathlib.RingTheory.Localization.AtPrime.Basic` (read lines 46--60),
  `Ideal.ResidueField` in `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`
  (read lines 23--44), and `Ideal.Fiber` in
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber` (read lines 60--67).
  Both the recorded module and the module exposing the fibre clause are public imports.
- `def-weil-pbc-kahler-differentials`: `KaehlerDifferential`, its universal derivation
  `KaehlerDifferential.D`, and `KaehlerDifferential.linearMapEquivDerivation`, in
  `Mathlib.RingTheory.Kaehler.Basic`; full signatures and docstrings read around
  lines 145--158, 194--208, and 323--335. The theorem uses the recorded differential type.
- `def-weil-finitely-generated-module`: `Module.Finite`, in
  `Mathlib.RingTheory.Finiteness.Defs`, lines 116--129; first conjunct uses it directly.
- `def-weil-pbc-module-tensor-product`: its mathlib_match `TensorProduct`, in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, lines 65--90; the theorem uses it directly.
- `def-weil-pbc-module-localization`: `LocalizedModule`, in
  `Mathlib.Algebra.Module.LocalizedModule.Basic`, lines 84--104; the theorem uses it
  with `q.primeCompl`.

Proof-only imports mirror every stated proof dependency not already public:
`Mathlib.RingTheory.Kaehler.TensorProduct` exposes
`KaehlerDifferential.tensorKaehlerEquivBase` and `tensorKaehlerEquiv` (00RV),
`Mathlib.RingTheory.LocalRing.Module` exposes `IsLocalRing.map_mkQ_eq_top` and
`map_tensorProduct_mk_eq_top` (00DV), and
`Mathlib.RingTheory.LocalProperties.Exactness` exposes
`bijective_of_localized_maximal`. Their full signatures were read; no project-owned
copy of any notion is used.

Edge cases checked before writing:

- A = 0: no primes of A, both primewise claims vacuous, and every unital A-module is
  zero. No `[Nontrivial A]` binder excludes this case.
- R = 0: every unital R-algebra is also the zero ring, so the vacuous fibre hypothesis
  has exactly the correct conclusion.
- Fibres that are zero rings (including fibres with no points) have zero differential
  module; they are allowed without a nontriviality or faithful-flatness assumption.
- Empty algebra-generator family: the image of R generates A and every differential
  vanishes; finite type includes this case.
- All characteristics, nilpotents, and non-Noetherian rings are permitted. Finite
  presentation, flatness, and Noetherian hypotheses are not used or inserted.
- Quantification ranges over all prime ideals, including nonmaximal primes. Independent
  universes u and v permit rings in different universes without narrowing a test category.

Searches actually run with `msearch.py Q12 lem-trf-fibrewise-zero-kahler-differentials`:

- LeanFinder: `finite type algebra with vanishing Kahler differentials on every residue
  field fibre has zero differentials`. Eight hits: standard-smooth relative-dimension-zero
  differential vanishing, formally unramified/etale vanishing and equivalences, and smooth
  finite-presentation/basis results. None states the whole fibre criterion together with
  finite generation and both primewise conclusions.
- Loogle: `KaehlerDifferential, Algebra.FiniteType`. Successful response, zero hits.
- LeanSearch: `finite type algebra with vanishing differentials on all residue field
  fibres has zero Kahler differentials`. Eight hits: `KaehlerDifferential`, its derivation
  descriptions, standard-smooth vanishing, and formal unramified/etale equivalences.
  None is an exact match.
- Mathlib grep: `(fiber|Fiber|residueField|ResidueField).*(subsingleton|Subsingleton|unramified|Unramified)|([Ss]ubsingleton|[Uu]nramified).*(fiber|Fiber|ResidueField)`
  in `RingTheory`. Twelve hits concern spectrum fibres and unramified residue fields;
  read `Unramified/Locus.lean` around `IsUnramifiedAt.residueField`, which goes from
  unramifiedness to unramifiedness of a fibre and does not state this lemma.
- Project `rg -n` in both `lean/WeilConjectures` and `lean/Sheaf`, and in
  `dag/lean_names_upstream.json`: searched the item id, fibrewise/fiberwise differential
  wording, subsingleton/fibre combinations, and the proposed declaration name.
  No exact match. A nearby result, `Ideal.subsingleton_of_forall_fiberDegree_eq_zero`,
  assumes an etale algebra and vanishing fibre degrees and concludes the ring itself
  vanishes; its signature was read and it is not this differential-module statement.
- Additional local searches for Kahler/Kaehler declarations in the project's ring-theory
  directories, and `grep -rn` for the item id in `lean/WeilConjectures`, found no existing
  version. Read the existing smooth-quotient fibre rank statement as another nearby but
  different use of `Ideal.Fiber` and `KaehlerDifferential`.

Validation: the prescribed `scompile.py` completed with exit 0. Its initial compiler
backend reported OSError(28), no space left on device, and the wrapper automatically
confirmed against the current server sources (1.3 seconds); no Lean error or unexpected
warning was returned. The prescribed `deliver2.py --no-push` then printed `OK (dry run)` for
commit `5348c4ab9f3`: preflight passed and the sandbox and library module compiled;
nothing was pushed by the dry run.

## Second reading by Q12

Author's separate second pass, with both the original node JSON and the final module open;
no independent agent was started, in accordance with the dispatcher's explicit instruction.
The maintainer supplies the independent review.

I rechecked that the hypothesis concerns the ordinary algebra fibre's relative differentials,
not M tensored with κ(p) as an A-module (κ(p) is generally not an A-algebra). The code
correctly uses Ω[p.Fiber A / p.ResidueField]. Its scalar algebra is the canonical one on
the residue-field-first tensor, so no unspecified map has been introduced. I then matched
the three conclusion blocks: `Module.Finite A M`, the universal primewise pair with
M ⊗_A κ(q) in the first component and `LocalizedModule q.primeCompl M` in the second,
and the final `Subsingleton M`. Contraction p is only explanatory data and does not
require an additional binder in these conclusions. All five recorded statement interfaces
are used directly and all three proof-only Mathlib dependency modules are imported.
No mismatch or false edge case was found, so no change to the node's text was needed.
Every variable and both universes are explicitly bound; the only postponed proof is the
item's own named theorem with its source and seven-step proof docstring.
