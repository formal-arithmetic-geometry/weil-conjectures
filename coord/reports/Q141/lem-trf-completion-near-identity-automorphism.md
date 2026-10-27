## Worker report

The module `Sheaf.RingTheory.AdicCompletionNearIdentityAutomorphism` states
`AdicCompletion.nearIdentity_automorphism`, with its sole proof `sorry`.
It renders the entire node without correcting its statement or adding definitions.
The docstring includes the source and all four natural-language proof steps.

Hypothesis and conclusion correspondence (write D = AdicCompletion
(IsLocalRing.maximalIdeal C) C in this report only):

- The commutative local nonzero ring C is `(C : Type u) [CommRing C]
  [IsLocalRing C]`. Mathlib's `IsLocalRing` extends `Nontrivial C` and expresses
  the unique-maximal-ideal condition. No extra nontriviality hypothesis is needed.
- Noetherianity is `[IsNoetherianRing C]`, the declaration recorded on
  `def-weil-pbc-noetherian-ring`.
- The completion D is Mathlib's `AdicCompletion (IsLocalRing.maximalIdeal C) C`.
  Its canonical map iota is `algebraMap C D`. Mathlib indexes powers by all
  naturals; the zero coordinate is the singleton quotient C/C and carries no
  extra data, so this is the specified inverse limit over positive powers.
- The extended ideal n is the binder `(n : Ideal D)` with defining equality
  `hn : n = (IsLocalRing.maximalIdeal C).map (algebraMap C D)`.
  Quantifying over this named ideal with its defining equality merely names
  the ideal specified in the node; it does not vary the mathematical ideal.
- A unital ring endomorphism is `(h : D →+* D)`.
- Ideal preservation is `hmem : ∀ d ∈ n, h d ∈ n`.
- Congruence to identity modulo the square is `hcongr : ∀ d, h d - d ∈ n ^ 2`.
- Locality of D and the asserted maximal ideal are the first two conjuncts
  `IsLocalRing D` and `IsLocalRing.maximalIdeal D = n`.
- Completeness is the third conjunct `IsAdicComplete n D`.
- The identity induced on D/n is expressed on every representative by
  `∀ d, Ideal.Quotient.mk n (h d) = Ideal.Quotient.mk n d`.
  The quotient map is surjective, so this is exactly equality with the identity.
- The identity on every n^r/n^(r+1) for r ≥ 1 is the representative formulation
  `∀ (r : ℕ) (d : D), d ∈ n ^ (r + 1) → h d - d ∈ n ^ (r + 2)`.
  Equality of representatives modulo n^(r+2) also gives preservation of n^(r+1).
- The equivalences `eQ : ∀ r : ℕ, (D ⧸ n^(r+1)) ≃+* (D ⧸ n^(r+1))`
  express that every positive-level induced map is an isomorphism. Their
  characterization on all representatives is the conjunct
  `eQ r (Ideal.Quotient.mk (n^(r+1)) d) =
    Ideal.Quotient.mk (n^(r+1)) (h d)`.
  This rules out arbitrary, unrelated quotient equivalences and implicitly
  asserts well-definedness of the induced quotient maps.
- Compatibility of all inverses uses every `r s : ℕ` with `hrs : r ≤ s`,
  every `d : D ⧸ n^(s+1)`, and the equality between
  `Ideal.Quotient.factorPow n (Nat.add_le_add_right hrs 1) ((eQ s).symm d)`
  and `(eQ r).symm (Ideal.Quotient.factorPow n
  (Nat.add_le_add_right hrs 1) d)`. Thus all positive-level transitions occur,
  including identical levels.
- The ring automorphism is `e : D ≃+* D` with `e.toRingHom = h`.
- The canonical identification is `α : D ≃+* AdicCompletion n D`, with
  `α.toRingHom = algebraMap D (AdicCompletion n D)`.
  It is characterized as the canonical completion map, rather than an arbitrary
  equivalence between the underlying rings.
- For every compatible sequence `x : AdicCompletion n D` and every positive
  level `r+1`, the last conjunct says
  `AdicCompletion.evalₐ n (r+1) (α (e.symm (α.symm x))) =
    (eQ r).symm (AdicCompletion.evalₐ n (r+1) x)`.
  This is exactly the requested coordinatewise formula for the inverse under
  the canonical identification. Evaluation at all positive indices determines
  a compatible sequence; the zero coordinate is unique.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`,
  `isNoetherianRing_iff`, `isNoetherianRing_iff_ideal_fg`, and
  `Ideal.fg_of_isNoetherianRing`. This is the first statement dependency.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion` (its compatible
  sequence definition), `IsAdicComplete` (Hausdorff and precomplete),
  `AdicCompletion.of`, and `AdicCompletion.of_bijective_iff`. This is the
  completion dependency; no replacement definition is introduced.
- `Mathlib.RingTheory.AdicCompletion.Algebra`: completion ring/algebra
  structures, `AdicCompletion.evalₐ` and its quotient-valued signature,
  `AdicCompletion.evalₐ_of`, and `AdicCompletion.ofAlgEquiv`.
- `Mathlib.RingTheory.AdicCompletion.LocalRing`: the Noetherian local completion
  instance, `AdicCompletion.maximalIdeal_eq_map`, and
  `AdicCompletion.isAdicComplete_self`. The two proof-dependency nodes
  `lem-weil-pbc-local-completion-local-ring` and
  `lem-weil-pbc-adic-completion-mod-ideal` already have usable Mathlib matches
  here and in `Mathlib.RingTheory.AdicCompletion.Completeness`, which is imported
  by LocalRing. Their complete node statements and matches were read; no
  dependency repair is necessary. LocalRing is a public import because the
  signature also uses its locality instance to name D's maximal ideal.
- `Mathlib.RingTheory.Ideal.Quotient.PowTransition`:
  `Ideal.Quotient.factorPow`, the canonical quotient reduction.
  It is already transitively exposed by the completion imports.

Source checked: `literature/stacks-project/more-morphisms.tex`,
`lemma-isomorphism-approximation` (Tag 0CAV), especially the associated-graded
rings generated in degree one, the successive quotient exact sequences, and
passage to completions. The theorem docstring spells out the node's specialized
near-identity argument: the telescoping product expansion, induction for both
injectivity and surjectivity, commutation of quotient inverses, and recovery of
h's inverse on compatible sequences.

Edge cases checked before finalizing the statement:

- The zero ring is excluded by `IsLocalRing C`, exactly as the node requires.
- For a field, the maximal ideal and its extension are zero and `hcongr` forces
  h to be the identity. Every conclusion specializes correctly.
- The first positive quotient and graded level occur at Lean index r = 0;
  there is no missing r = 1 case and no unwanted r = 0 graded claim.
- Equal transition levels r = s are included. Natural-number indexing covers
  exactly the positive integer levels by r+1.
- Nilpotent maximal ideals, including n² = 0, are allowed without any added
  separatedness, domain, characteristic, residue-field, or topology assumptions.
- A single arbitrary universe u accommodates every ring in the statement;
  no universe equality or finite-dimensionality restriction is imposed.
- The automorphism is only a ring automorphism: no C-linearity or identity on
  the image of C has been assumed.

Searches performed using the prescribed `msearch.py` wrapper (Q141, this item):

- LeanSearch: "An endomorphism of a complete local ring inducing identity modulo
  maximal ideal squared is bijective" returned 8 hits, including
  `IsNoetherian.bijective_of_surjective_endomorphism`, localization criteria,
  and residue-field identity maps. None states this theorem: the Noetherian
  module endomorphism criterion additionally assumes surjectivity and linearity.
- LeanFinder: "A local endomorphism of a Noetherian local ring completion
  congruent to identity modulo the square of the maximal ideal is an
  automorphism" returned 8 hits, including `IsAdicComplete.henselianRing`,
  `HenselianLocalRing`, `AdicCompletion.ofAlgEquiv`, and local-completeness
  lemmas. The completed-ring canonical equivalence is an ingredient, not the
  specified near-identity theorem.
- Loogle: `AdicCompletion, RingEquiv` returned zero hits.
- Mathlib grep: `near.*identity|identity.*[Aa]utomorph|bijective` restricted to
  `RingTheory/AdicCompletion` returned 15 hits on tensor-product completion,
  residue-field maps and canonical completion bijectivity, none an exact match.
- Project rg on `lean/WeilConjectures` and `lean/Sheaf`:
  `near.?[Ii]dentity|identity.*(maximalIdeal|[Aa]dic)|completionNear|NearIdentity`.
  The only related result is the private
  `injective_near_identity_nilpotent` in
  `WeilConjectures/RingTheory/Smooth/AugmentationPolynomialTruncationsInjective.lean`.
  Its full signature was read: it assumes ideal nilpotence and only proves
  injectivity; it neither states the completion theorem nor supplies all clauses.
  Other hits are unrelated identity maps. The new full declaration name is absent.
- Exact item-id search in `lean/WeilConjectures` returned no results, and
  `dag/lean_names_upstream.json` has no `nearIdentity_automorphism` match.

No statement fault or STATEMENT-DISPUTED issue was found. No new nodes or
additional dependency modules are needed. All variables and the universe are
explicitly bound, and `autoImplicit` is disabled.

Validation: prescribed `scompile.py` compiled the file in sandbox and library
module modes against the server's live published library, without errors or
unexpected warnings. The prescribed `deliver2.py --no-push` passed preflight and compilation
(OK, dry-run commit 7136b139dd0).

## Second reading by Q141

Author's second reading, performed here without another agent as required by
this dispatch. This is not presented as the maintainer's independent review.
Reopened the node and the complete Lean file and matched all hypotheses and
clauses above. In particular I checked that `hn` fixes n to the generated
extended ideal, `e.toRingHom = h` fixes the automorphism, every `eQ r` is fixed
on all quotient representatives, and α is fixed to the canonical map. The final
formula quantifies over all compatible sequences, rather than only those with
an unspecified origin. The only reindexing is positive level r+1; residues,
positive graded pieces, all quotient inverse transition squares, and the entire
inverse formula are present. No mismatch or statement correction was found.
