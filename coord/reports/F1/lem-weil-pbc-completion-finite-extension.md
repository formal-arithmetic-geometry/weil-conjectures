## Worker report

The module `Sheaf.RingTheory.CompletionFiniteExtension` states
`AdicCompletion.completion_finite_extension`, with `sorry` and no proved helpers.
The node is unchanged apart from `lean`. No new notions or dependency modules were needed.

Hypothesis and clause correspondence:

- Commutative rings and the ring map R → S: `(R : Type u) (S : Type v)` with
  `[CommRing R] [CommRing S] [Algebra R S]`. The map is `algebraMap R S`;
  arbitrary ring maps are represented by their associated algebra structure.
- R Noetherian: `[IsNoetherianRing R]`.
- S finitely generated as an R-module: `[Module.Finite R S]`.
- The prime p: `(p : Ideal R) [p.IsPrime]`.
- All primes q of S with contraction p: `Q := p.primesOver S`. Mathlib defines
  this set as `q.IsPrime ∧ q.LiesOver p`, and `LiesOver.over` says
  `p = q.comap (algebraMap R S)`. No enumeration, duplicate primes, or extra
  finiteness assumption is imposed. `Finite Q` is the asserted finiteness.
- R_p and its maximal-ideal completion: `A := Localization.AtPrime p`,
  `m := IsLocalRing.maximalIdeal A`, `C := AdicCompletion m A`.
- Each S_q and its maximal-ideal completion: `D q` is
  `AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.1))
  (Localization.AtPrime q.1)`. Mathlib's instance on `q : Q` supplies primality.
- The displayed tensor-to-product S-algebra isomorphism: the existential
  `e : (C ⊗[R] S) ≃ₐ[S] (∀ q : Q, D q)`. The local `rightAlgebra` instance
  gives the tensor product the S-algebra map `s ↦ 1 ⊗ s`. Each factor has
  its S-algebra structure through S → S_q → completed S_q, and the product
  structure is componentwise.
- The map on completed base rings is induced by R_p → S_q: the ring maps
  `g : ∀ q : Q, C →+* D q` satisfy, for every n, a and representative r,
  `evalₐ m n a = mk (m^n) r → evalₐ maximalIdeal n (g q a) =
  mk (maximalIdeal^n) (Localization.localRingHom ... r)`.
  This specifies the map on every quotient coordinate. Each quotient coordinate
  has a representative, so this determines the induced completion map, rather
  than merely its restriction to the original ring. `localRingHom` uses exactly
  `Ideal.LiesOver.over` for the contraction equality.
- Compatibility with the C-algebra structures: `∀ a q, e (a ⊗ₜ[R] 1) q = g q a`.
  A ring homomorphism from C defines the C-algebra structure of each commutative
  target, so this equality expresses precisely the required commutative square.
  Ring multiplicativity also gives `e (a ⊗ s) q = g q a * algebraMap S (D q) s`.
- The middle completed ring: `B := A ⊗[R] S`, the symmetric presentation of
  S_p = S ⊗[R] A via Mathlib's tensor commutativity isomorphism;
  `J := p.map (algebraMap R B)` is pS_p. Its completion is `AdicCompletion J B`.
- Both displayed rings are also isomorphic to that completion:
  `Nonempty ((C ⊗[R] S) ≃ₐ[S] AdicCompletion J B)` gives the left identification;
  composing its witness with `e.symm` gives the right identification. This uses
  the same e and thus asserts both, without an unrelated replacement product.
- If there are no primes above p, `∀ q : Q, D q` is the empty product, whose
  unique element is both zero and one. No nontriviality requirement excludes it.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`; its docstring and signature identify it
  with the Noetherian self-module, equivalently finitely generated ideals.
- `def-weil-finitely-generated-module`: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs`; its field is finite generation of the top submodule.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`,
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, localization at `p.primeCompl`;
  the local-ring instance and maximal ideal are the existing Mathlib structures.
  Also `Localization.localRingHom` in this module, with the full contraction
  equality as input, gives the induced local homomorphism.
- `def-weil-pbc-adic-completion`: `AdicCompletion`,
  `Mathlib.RingTheory.AdicCompletion.Basic`, compatible sequences of module quotients;
  the imported `Mathlib.RingTheory.AdicCompletion.Algebra` gives its commutative
  ring/algebra structure and `AdicCompletion.evalₐ` to the ideal-power quotients.
  For the ring self-module, these are precisely A/m^n.
- Existing support: `Ideal.primesOver`, its primality and lying-over instances,
  and `Ideal.LiesOver.over` from `Mathlib.RingTheory.Ideal.Over` (imported by AtPrime.Basic);
  `Algebra.TensorProduct.rightAlgebra` from `Mathlib.RingTheory.TensorProduct.Basic`.

Edge cases checked before writing: S may be the zero ring, the map need not be
injective or faithful, and no prime may lie over p; all give the empty product
case above. R cannot be the zero ring when a prime p is given, as in the node.
p may be zero; no domain, nonzero-prime, characteristic or residue-field
restriction is imposed. Quotient coordinates include n = 0 (the zero quotient),
so the inverse limit is the usual one, and the condition at zero is vacuous.
Separate universes u and v allow arbitrary base and extension ring sizes; Q
has the universe of ideals of S. No hypothesis of Noetherianity of S or of the
localizations is added: those are consequences for the later proof.

Searches made (recorded by msearch.py in searches.jsonl):

- LeanFinder: “adic completion of finite algebra localized at prime decomposes
  as product of completed localizations at primes lying over”. Eight results:
  Dedekind valuation completions, Dedekind primes-over equivalences, and spectrum
  products of localizations. None states the general Noetherian completion theorem.
- Loogle: `AdicCompletion, Ideal.primesOver`: zero results.
- LeanSearch: “completion of finite algebra is product of completions at primes
  over a prime”: service unavailable (Internal Server Error); no verdict asserted.
- Mathlib grep via msearch.py: `primesOver|LiesOver|finite.*extension` in
  `RingTheory/AdicCompletion`: zero hits.
- Source repository rg: `completion.*finite.*extension|07N9|completion_finite|CompletionFinite`
  and the exact item/dependency blueprint ids: no existing statement.
- Project lean/Sheaf rg with those patterns: only a proof-docstring mention in
  `PolynomialFormalFiber.lean`, no declaration of the node's statement.
- Name collision check: `completion_finite_extension` in
  `dag/lean_names_upstream.json`, source repository and lean/Sheaf: no hits.

Source check: the local literature/stacks-project/algebra.tex is unavailable
in this remote checkout. Read the actual source at
https://stacks.math.columbia.edu/tag/07N9 instead: Lemma 10.97.8 asserts the tensor,
localized p-adic completion, and product of maximal-ideal completions under the
same hypotheses. The full natural-language six-step DAG proof is rendered in
the declaration docstring, referring to its dependency lemma names. There is
no statement correction or disputed clause.

Validation: the server single-file compile completed cleanly. The final dry-run
preflight and compile are recorded by the delivery tool; the independent second
reading is left to the assigned second reader.

## Second reading by F1

Independently read the node, the delivered module, all four statement-dependency
nodes and their Mathlib declarations. Read the Stacks algebra.tex source directly
from https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
label lemma-completion-finite-extension (Tag 07N9), including its entire proof
and the introduction of section-completion-noetherian. The local literature
checkout lacks this file. The section adds no ambient hypotheses beyond those
explicitly stated in the lemma. Also checked the rendered source at
https://stacks.math.columbia.edu/tag/07N9.

Object, hypothesis and conclusion checklist (in node order):

- R is a commutative Noetherian ring: `(R : Type u) [CommRing R]
  [IsNoetherianRing R]`. Verdict: exact. Read Noetherian/Defs.lean:196:
  this means Noetherian as its own module, equivalently finitely generated ideals.
- S is a commutative ring and phi : R -> S is any ring map making S a finite
  R-module: `(S : Type v) [CommRing S] [Algebra R S] [Module.Finite R S]`.
  Verdict: exact. Any commutative-ring hom gives this algebra structure;
  Finiteness/Defs.lean:117 has `fg_top`, with no injectivity or faithfulness.
- p is a prime ideal of R: `(p : Ideal R) [p.IsPrime]`. Verdict: exact;
  no maximality or nonzero hypothesis is added.
- All primes q of S whose contraction is p, and their finiteness:
  `Q := p.primesOver S`, `Finite Q`. Verdict: exact. Read Ideal/Over.lean:376:
  membership is precisely primality and LiesOver; LiesOver.over at line 125
  says p equals the comap along algebraMap. The subtype is the whole set, not
  a selected family. The membership instances give exactly the required
  primality and contraction proofs, not additional assumptions.
- R_p and its maximal-ideal completion: `A := Localization.AtPrime p`,
  `m := IsLocalRing.maximalIdeal A`, `C := AdicCompletion m A`.
  Verdict: exact. AtPrime.Basic defines localization at the complement of p,
  and its map_eq_maximalIdeal identifies m with pA. AdicCompletion.Basic:171
  is the compatible sequence inverse limit; Algebra.lean:132 identifies evalₐ
  with the quotient by the corresponding ideal power.
- Each S_q and its maximal-ideal completion: `D q` uses
  `Localization.AtPrime q.1` and its maximalIdeal in `AdicCompletion`.
  Verdict: exact, using the same recorded dependency notions as for R_p.
- S-algebra isomorphism between completed-base tensor S and the product:
  `e : (C ⊗[R] S) ≃ₐ[S] (∀ q : Q, D q)`.
  Verdict: exact. Read TensorProduct.Basic.lean:492: rightAlgebra is induced
  by includeRight, so the left S-structure is s -> 1 tensor s. Each completed
  factor has the S-algebra structure through its localization; the Pi instance
  gives the componentwise product structure. Replacing an enumeration of all
  q_i by their subtype changes neither the object nor the claim.
- Compatibility with the completed-base algebra structures, with the specified
  induced local maps: `g : ∀ q : Q, C →+* D q`, the quotient-coordinate
  implication for every q, n, a, r, and `e (a ⊗ₜ[R] 1) q = g q a`.
  Verdict: exact. Read localRingHom in AtPrime.Basic.lean:241: its input is
  precisely the contraction equality, and it is the induced map on fractions.
  A local hom takes m^n into the target maximal ideal's n-th power. Every
  evalₐ coordinate has a representative r, so the implication fixes every
  coordinate of g q a as the induced quotient map; it neither imposes an
  extra continuity hypothesis nor leaves an arbitrary extension on completion.
  A commutative-target ring hom defines its algebra structure. The displayed
  equality is precisely compatibility for the C inclusion; S-linearity of e
  then specifies the mixed pure tensors as well.
- Both rings are isomorphic to the pS_p-adic completion of S_p:
  `B := A ⊗[R] S`, `J := p.map (algebraMap R B)`, and
  `Nonempty ((C ⊗[R] S) ≃ₐ[S] AdicCompletion J B)`.
  Verdict: exact. Tensor commutativity identifies B with the node's
  S tensor_R A, preserving its S-structure and the image ideal J. J is pB,
  equivalently mB. The witness gives the left identification; composing it
  with e.symm gives the product identification. The node's final clause asks
  that both rings are isomorphic; no additional commuting diagram for that
  intermediate identification is omitted.

Edge cases: Q can be empty and its dependent product is the zero ring, as
required. S can be the zero ring, or the map nonfaithful. No Nontrivial S
instance is assumed. A prime p makes R nonzero, exactly as in the source.
The zero prime is allowed; no characteristic, domain or residue-field
restriction is present. Quotient coordinates include n = 0, where both
quotients are zero, so that condition is vacuous. The ordinary ring-theoretic
objects do not involve schemes or an empty-scheme case. Independent universes
u and v impose no equality of universe sizes. Finiteness is a conclusion,
not an instance assumption on Q. No separate Noetherianity assumption on S,
A or S_q was smuggled into the binders.

Independent searches, with different conceptual wording from the worker:

- LeanFinder via msearch.py: "semilocal finite algebra completion splits into
  completed local rings" returned eight hits. isLocalRing_of_isAdicComplete_maximal
  is only locality of a completed ring, MaximalSpectrum.toPiLocalizationEquiv
  is a decomposition for discrete spectra without the completion claim,
  and the remaining hits concern Dedekind valuations, finite generation or
  unramified algebras. None states this lemma.
- Loogle via msearch.py: `AdicCompletion, AlgEquiv` returned eleven hits:
  completion of already complete rings, power-series comparisons and their
  evaluation formulas. No finite-extension product decomposition.
- LeanSearch via msearch.py: "semilocal Noetherian algebra completion
  decomposition into local factors" was unavailable (Internal Server Error).
  No negative verdict inferred from that failure.
- Grep via msearch.py: `semilocal|primesOver|LiesOver` produced number-field
  completion and primes-over results, which have narrower hypotheses.
- Independently rg searched Mathlib/RingTheory/AdicCompletion, the full
  WeilConjectures source and project lean/Sheaf for semilocal, completion
  decomposition/splitting, primes with completion, and the declaration name.
  The project hits concern conductors and normalization, and the source hits
  concern divisor and flat-rank arguments. No existing matching declaration.
  The exact name also has no collision in dag/lean_names_upstream.json.

No new definition node or dependency module was delivered; none is missing.
The four dependencies genuinely provide the notions used, so no private
copies or unusable-record replacements are needed. No statement correction
was delivered or needed. The docstring follows all six DAG proof steps,
including the positive-power quotient decomposition, its inverse limit,
change of adic ideal, tensor cancellation, and empty-product conclusion.
The sole theorem proof is `sorry`; no helper is proved and no definition
contains postponed data. Imports serve the completion algebra, prime
localization, finiteness/Noetherian hypotheses, and tensor construction.

Mismatches found: none. Changes: appended this independent second reading;
left the correct Lean module and node record unchanged. Checked the recorded
lean.statement is verbatim equal to the signature through the last conclusion.
Server single-file compile succeeded in 2.4 seconds with no errors or warnings.
