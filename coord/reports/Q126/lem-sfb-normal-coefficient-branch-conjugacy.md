## Worker report

The module `Sheaf.RingTheory.NormalCoefficientBranchConjugacy` states
`Algebra.normalCoefficientBranchConjugacy`, with one postponed proof and no new definitions.
The node is unchanged except for `lean`. Source read: Stacks Project more-algebra.tex,
`remark-construction` (09EM), lines 33882–33964, and `lemma-galois-relative` (09EU),
lines 34609–34645. The finite-dimensional and possibly inseparable version is exactly the
node's existing corrected formulation. Its six proof steps are included in the docstring.

Clause-by-clause reading:

- The two DVRs are `[CommRing A] [IsDomain A] [IsDiscreteValuationRing A]` and the corresponding
  three instances for B. The map is `algebraMap A B`, injective by `hAB` and local by
  `[IsLocalHom (algebraMap A B)]`.
- The fraction fields are K and L with their `Field`, `Algebra`, and `IsFractionRing`
  instances. `Algebra K L` encodes the inclusion K into L. The A-algebras and scalar towers
  through B and K say this is the fraction-field map induced by A to B. The analogous
  A-to-K-to-N tower gives the A-algebra used in its integral closure.
- `[FiniteDimensional K N] [Normal K N]` says precisely finite-dimensional normal N/K.
  `Normal` uses splitting of minimal polynomials; for this algebraic extension it is
  equivalent to the node's irreducible-polynomial formulation. No separability is required.
- E is written directly everywhere as `(L ⊗[K] N) ⧸ nilradical (L ⊗[K] N)`. Mathlib's
  `nilradical` consists exactly of nilpotent elements (`mem_nilradical`). The two normalized
  rings are the actual `integralClosure A N` and `integralClosure B E` subalgebras.
- `i` is the inclusion of the lower integral closure in the upper one. Its first equation
  fixes its underlying value to the class of `1 ⊗ r`; it is not an unconstrained map.
  The source's nonzero reduced tensor algebra makes this inclusion injective. The statement
  uses the canonical underlying-value characterization, without adding injectivity as an
  assumption or constructing a second integral closure.
- G is `N ≃ₐ[K] N`. The monoid homomorphisms `ρN`, `ρE`, `ρC` into groups of ring
  equivalences give the actions and their identity/composition laws. The next three
  conjuncts specify restriction to N, the displayed formula on every reduced pure tensor,
  and restriction from E to its B-integral closure, respectively. Pure tensors generate
  the quotient, so these equations determine the actions uniquely. They also imply their
  compatibility with i, rather than requiring any arbitrary action as a hypothesis.
- Arbitrary `q q' : PrimeSpectrum (integralClosure B E)` with the two `IsMaximal` premises
  range over every maximal ideal. `∃ σ` followed by
  `Ideal.map (ρC σ).toRingHom q.asIdeal = q'.asIdeal` is the asserted transitivity.
- The witnesses `n n'` are prime ideals of the lower integral closure. The equalities
  `hn` and `hn'` identify them exactly as the contractions along i. Their image equality
  under `ρN σ` states that the same sigma sends n to n'. No equality n = n' is imposed.
- The two maps of branches are Mathlib's canonical
  `Localization.localRingHom n.asIdeal q.asIdeal i hn` and its primed counterpart.
  That existing construction is a local ring homomorphism; its instance
  `Localization.isLocalHom_localRingHom` and its `localRingHom_mk'` formula supply precisely
  r/s mapping to r/s. They are not additional existential maps.
- `eN` and `eC` are ring equivalences between the indicated lower and upper localizations.
  Both have explicit `IsLocalHom` conclusions. The equality of ring-hom composites is the
  commuting square of branch maps.
- `hN` and `hC` express preservation of admissible denominators, already forced by the
  two ideal-image equalities. The last two conjuncts explicitly state the fraction formulas
  `e (mk' b s) = mk' (sigma b) (sigma s)`, with the denominator membership proofs supplied
  by hN and hC. Thus the local isomorphisms themselves are fixed on all fractions.
- There are no completeness, henselianity, separability, localness of the lower integral
  closure, or equal-contraction hypotheses. All five carrier universes are independent and
  explicitly bound. Every variable is bound; no `let` or local notation hides a notion.

Dependency declarations read and used:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, lines 53–60, including its docstring
  and local PID/nonfield structure; the domain instance is separately bound as required.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`, lines 91–102,
  with the field instances. This is imported transitively through the tensor/field modules.
- `def-weil-pbc-integral-closure`: `integralClosure`,
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, lines 213–226, the actual subalgebra
  of integral elements, not a chosen normalization.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`,
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, lines 76–89; its ring structure comes from
  `Mathlib.RingTheory.TensorProduct.Basic`, including `leftAlgebra` and `instCommRing`.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`,
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, lines 49–58. The full canonical-map
  interface and docstring were read at lines 234–275, including `localRingHom`,
  `localRingHom_mk'`, and the local-hom instance.

Available proof-dependency imports are included without `public`: Galois prime transitivity,
finite embeddings, CRT, integral contraction of maximal ideals, and the PID structure.
The normalization-structure and invariant-power proof nodes have no recorded Lean modules
in the read DAG, so there is no module to import for those planned proof inputs.
No statement dependency requires repair, and no new definition node is needed.

Edge cases checked: N = K gives the identity coefficient action and a single upper branch;
purely inseparable finite normal N/K allows a trivial automorphism group, consistently with
the unique branch in 09EM; a separable normal extension may have several distinct lower
contractions and the theorem permits them; arbitrary noncomplete DVRs and positive
characteristic are admitted. The tensor reduction is nonzero because field scalar extension
is faithful and N/K is a nonzero finite field extension. No zero tensor algebra or field
case of a DVR was silently allowed by the data. Distinct n and n' are explicitly permitted.

Searches performed using `/home/ubuntu/weil-launcher-all/batch2/msearch.py`:

- LeanFinder: "Automorphisms of a finite normal field extension act transitively on maximal
  ideals of the normalization of a reduced tensor algebra over a DVR". Eight hits, including
  `Ideal.isPretransitive_of_isGaloisGroup`, `Ideal.exists_smul_eq_of_isGaloisGroup`, and
  `Ideal.exists_comap_galRestrict_eq`. None states this reduced-tensor normalization result
  for possibly inseparable normal coefficients or its compatible localization square.
- Loogle: `Ideal.isPretransitive_of_isGaloisGroup, Localization.AtPrime, integralClosure`.
  Zero hits.
- Mathlib grep: `isPretransitive_of_isGalois|normal.*[Bb]ranch|coefficient.*[Cc]onjug`.
  Five hits, only the prime-transitivity result and unrelated categorical Galois statements.
- LeanSearch: "Automorphisms of normal coefficient fields conjugate prime ideals in reduced
  tensor integral closures". Eight hits, including galRestrict, tensor integral closure,
  and field Galois prime actions. No exact statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id, intended declaration name,
  and `isPretransitive_of_isGalois`: no exact statement found. Broader tensor and branch
  searches found `NormalTensorComponentJoinModel` and other unrelated branch constructions.
  `dag/lean_names_upstream.json` has no proposed-name match. The intended full declaration
  name is new. Mathlib's Galois invariant-ring theorem does not provide the purely inseparable
  invariant-power correction or this local square.

Validation: prescribed scompile.py compiled the module on the server in 4.4 seconds with
no errors or warnings. The local attempt reported an out-of-space error; the wrapper then
successfully performed its current-server-source confirmation. No local compiler was run
outside the wrapper. Only the allowed sandbox was written.

## Second reading by Q126

The delivered section was the worker's own second pass. The maintainer's independent reader
replaced it with this reading of the node, Stacks 09EU/09EM and the Lean signature
`Algebra.normalCoefficientBranchConjugacy`.

Node clauses and the Lean that renders them:

- A→B injective local map of DVRs: `[IsDomain] [IsDiscreteValuationRing]` on A and B,
  `[IsLocalHom (algebraMap A B)]`, `hAB : Injective`. Injectivity is not automatic (the
  kernel could be m_A), so `hAB` is the node's own hypothesis. Correct.
- K ⊆ L fraction fields: `IsFractionRing A K`, `IsFractionRing B L`, `Algebra K L` with towers
  A→B→L and A→K→L. Those towers force K→L to be the map induced by A→B (unique
  extension from A to Frac A), so they add nothing beyond the node. Correct.
- N/K finite and normal: `FiniteDimensional K N`, `Normal K N`. For algebraic extensions,
  Mathlib's minpoly-splitting definition is equivalent to the node's irreducible-polynomial
  definition. No separability is assumed. Correct.
- E = (L⊗_K N)_red: `(L ⊗[K] N) ⧸ nilradical (L ⊗[K] N)`, written inline (no def node
  exists for it). The only `Algebra B` structure on it is `Algebra.TensorProduct.leftAlgebra`
  through `Algebra B L`, since there is no `Algebra B N`. So C = `integralClosure B E` is
  the node's C, and R = `integralClosure A N` with A acting through K. Correct.
- R ⊂ C: `i` is pinned by `(i r).val = [1 ⊗ r]`. It is canonical, not arbitrary.
- G-actions: `ρN`, `ρE`, `ρC` are monoid homs into ring automorphisms. Mathlib's `RingEquiv`
  multiplication is composition, so this matches the left action. They are pinned by
  restriction, by the pure-tensor formula l⊗x ↦ l⊗σx (pure tensors generate), and by
  restriction from E. They therefore exist and are unique. Correct.
- Transitivity: for all maximal q, q' there is σ with `Ideal.map (ρC σ) q = q'`. Correct.
- n = q∩R and n' = q'∩R: the `hn`/`hn'` equalities with `comap i`, plus
  `Ideal.map (ρN σ) n = n'`. There is no assertion that n = n' or that R is local.
- Branch maps are Mathlib's canonical `Localization.localRingHom … i hn` (r/s ↦ r/s, a local
  hom by instance). `eN` and `eC` are local ring isomorphisms pinned on all fractions by
  b/s ↦ σb/σs, using the same σ. The commuting square is
  `eC ∘ loc(n→q) = loc(n'→q') ∘ eN`. Correct.
- The theorem has no completeness, henselianity or separability hypotheses. Correct.

Edge cases: N = K (G trivial, one branch); N/K purely inseparable (G trivial; 09EM gives a
unique branch, which is consistent); Z_(5)[i]/Z_(5) (n ≠ n' is allowed); E ≠ 0 always. The
five carrier universes are independent and bound.

One-definition check: no recorded Lean module for lem-sfb-normal-tensor-invariant-powers,
lem-sfb-dvr-algebraic-normalization-structure or lem-sfb-epp-normal-base-branch-conjugacy.
EppEssentiallyFiniteTypeTraits has a theorem-module abbreviation for a reduced tensor of
other fields; it is not a def node and not this notion. Mathlib's
`Ideal.isPretransitive_of_isGaloisGroup` needs invariant-ring hypotheses that fail in the
inseparable case. There is no duplicate.

Records: the node differs from live only in `lean`. `lean.statement` is verbatim the
signature in the file. stmt_deps are unchanged, and all five are Mathlib definitions used
directly. The docstrings give the source place and the blueprint id, and carry the six
proof steps. The proof is `sorry` only, and there are no new definitions.

Mismatches found: none in the Lean. The only change is this replacement section.
