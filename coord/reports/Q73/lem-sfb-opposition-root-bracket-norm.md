## Worker report

The module `Sheaf.Algebra.Lie.OppositionRootBracketNorm` states
`LieAlgebra.opposition_root_bracket_norm`, with its sole proof `sorry`.
The node's statement, dependencies and proof are unchanged; only `lean` is added.
No new definitions or dependency repairs are needed.

Source reading: Milne, Algebraic Groups (2017), Section 23h, printed pp.508–509,
especially Theorem 23.71 and its definition of the lower root-string endpoint.
The node is explicitly an agent-stated conditional local version of that calculation,
rather than the existence theorem for a Chevalley basis. Its five proof steps are
included in the theorem docstring, including the scalar recurrence and both signs in
the Killing-invariance calculation. The current blueprint unit
`sk-thm-sf-ctf-stability` and detail `det-thm-sf-ctf-stability-direct-images` were read;
this is an internal supporting lemma, and no unit statement or route changes.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| Finite-dimensional rational Lie algebra g | `L : Type u`, `[LieRing L]`, `[LieAlgebra ℚ L]`, `[FiniteDimensional ℚ L]` |
| Semisimple, meaning no nonzero solvable ideal | `[HasTrivialRadical ℚ L]`, exactly the dependency's Mathlib predicate |
| Subalgebra h | `H : LieSubalgebra ℚ L` |
| Abelian and maximal among abelian subalgebras | `[IsLieAbelian H]` and `hmax : ∀ A, H ≤ A → IsLieAbelian A → A = H` |
| Acting diagonally over Q | `hsplit`: the supremum of the rational eigenspaces of each `ad ℚ L (h : L)` is top |
| Reduced crystallographic root system R in h dual, with coroots in H | `P : RootPairing I ℚ (Module.Dual ℚ H) H`, with `[Finite I]`, `[P.IsRootSystem]`, `[P.IsCrystallographic]`, `[P.IsReduced]` |
| The pairing is evaluation, not an unrelated perfect pairing | `heval : ∀ ξ h, P.toLinearMap ξ h = ξ h` |
| Nonzero distinct roots | `P.root` is an embedding and `RootPairing.ne_zero` excludes zero over Q |
| g_alpha consists of simultaneous eigenvectors with eigenvalue alpha(h) | `LieModule.weightSpace L (P.root i)`; its exact pointwise meaning is `LieModule.mem_weightSpace` |
| Internal decomposition g = H direct-sum all root spaces | `hdecomp : DirectSum.IsInternal (Sum.elim (fun _ : Unit ↦ H.toSubmodule) (fun i ↦ (LieModule.weightSpace L (P.root i)).toSubmodule))` |
| Each root space has dimension one | `hdim : ∀ i, Module.finrank ℚ (LieModule.weightSpace L (P.root i)) = 1` |
| h_alpha belongs to [g_alpha,g_-alpha] and lies in H | `hcoroot` puts `(P.coroot i : L)` in the span of exactly the opposite-root brackets; `P.coroot i` itself has type `H` |
| alpha(h_alpha) = 2 | `P.root_coroot_two i` together with `heval` gives this normalization; it is a field of the supplied root pairing, not a postponed helper |
| Rational linear Lie automorphism theta | `θ : L ≃ₗ⁅ℚ⁆ L` |
| theta squared is identity | `hθsq : ∀ z : L, θ (θ z) = z` |
| theta acts as minus identity on H | `hθH : ∀ h : H, θ (h : L) = -(h : L)` |
| theta carries each root space to its opposite | `hθroot` gives membership in the opposite weight space for each member of the original space |
| alpha,beta,gamma are roots and gamma = alpha + beta | `i j k : I` and `hadd : P.root k = P.root i + P.root j` |
| u and v lie in the indicated spaces | `hu` and `hv` |
| [u,-theta(u)] = h_alpha and [v,-theta(v)] = h_beta | `hunorm` and `hvnorm` |
| p is the largest nonnegative integer with beta - p alpha a root | `P.chainBotCoeff i j`, the existing Mathlib lower string endpoint |
| w = [u,v] | The bracket `⁅u, v⁆` is written directly throughout the conclusion, without a hidden let binder |
| [w,-theta(w)] = (p+1)^2 h_gamma | First conjunct, with `P.chainBotCoeff i j` cast to Q before addition, squaring and scalar multiplication |
| In particular w is nonzero | Second conjunct `⁅u, v⁆ ≠ 0` |

The root set is enumerated by the arbitrary finite index type `I`, just as in
`Sheaf.Algebra.Lie.ChevalleyRootNormalization`; this adds no choice of a Chevalley basis.
`P.root` identifies `I` with its range. The internal decomposition, nonzero roots and
one-dimensionality identify that range with all nonzero weights, so no extra roots or
omitted roots are introduced. `hcoroot` is exactly membership in the bracket span:
the inclusion of the whole bracket span in H follows from Jacobi, opposite weights
and maximal abelianness (the zero weight space is H). Since its coroot is nonzero and
both root spaces are lines, that span is the coroot line. Thus the root pairing's
coroot is the node's characterized normalized element.

The forward membership formulation `hθroot` also expresses equality of the two spaces:
negation permutes the root family; applying it to the negative root and using `hθsq`
gives surjectivity onto the opposite space. No weaker meaning of “carrying” is used.
The maximality and splitting hypotheses are written out even though portions of them
can also be recovered from the supplied root decomposition.

Dependency declarations and imports:

- `def-wf-lie-algebra`: Mathlib's `LieRing`, `LieAlgebra`, `LieSubalgebra`,
  `LieModule`, and `LieAlgebra.ad`; full signatures/docstrings were read in
  `Mathlib.Algebra.Lie.Basic`, `Subalgebra`, and `OfAssociative` as applicable.
- `def-wf-semisimple-lie-algebra`: `LieAlgebra.HasTrivialRadical` in
  `Mathlib.Algebra.Lie.Semisimple.Defs`, publicly imported through
  `Mathlib.Algebra.Lie.Semisimple.Basic`. The recorded equivalence
  `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals` was read there as well.
- Existing Mathlib statement notions: `LieModule.weightSpace` and
  `LieModule.mem_weightSpace` in `Mathlib.Algebra.Lie.Weights.Basic`;
  `DirectSum.IsInternal` through `Mathlib.Algebra.DirectSum.Module`;
  `RootPairing`, its mixins, and `RootPairing.chainBotCoeff` through
  `Mathlib.LinearAlgebra.RootSystem.Chain`.
- Already stated proof dependency `lem-sfb-split-semisimple-root-decomposition`:
  `LieAlgebra.exists_splitSemisimple_rootDecomposition` in
  `Sheaf.Algebra.Lie.SplitSemisimpleRootDecomposition`, read with its full docstring
  and signature and imported using plain `import`.
- The two root-string Mathlib proof leaves are
  `RootPairing.root_add_zsmul_mem_range_iff` and
  `RootPairing.chainBotCoeff_sub_chainTopCoeff` in the imported Chain module.
  Their full types and the independence hypotheses were read.
- `lem-sfb-rational-killing-root-duality` and
  `lem-sfb-root-string-adjacent-length-ratio` currently have no Lean record or
  Mathlib match; they are proof dependencies only, so there is no module to import.
  Their mathematical content is preserved in the proof plan, not assumed as a new
  hypothesis. No statement dependency is missing or unusable.

Edge cases checked before writing:

- If L is zero, I is empty and there are no indices i,j,k satisfying the hypotheses.
  No nontriviality assumption on L, H or I was added. The index universe v is arbitrary.
- Rank one cannot provide a root sum: i=j would require twice a root, and opposite
  roots would sum to zero. Reducedness excludes both, and forces independence of the
  two roots. This justifies using the genuine endpoint branch of `chainBotCoeff`;
  its fallback for dependent roots is never used under `hadd`.
- p=0 is allowed and yields scalar 1. A2 with theta given by negative transpose
  and u=E12, v=E23 gives w=E13 and precisely the stated normalization.
- In the non-simply-laced cases p may be positive: the output uses the square,
  not p+1 itself. The proof plan's relation q d_gamma=(p+1)d_beta accounts for this.
- u=0 or v=0 is ruled out by the corresponding normalization and coroot evaluation
  2, not by adding separate nonzero hypotheses. The second conjunct follows from
  the same coroot evaluation and the positive integer p+1.
- Scalars, the involution, all weight values and the final norm are rational;
  no extension to an algebraically closed field or positivity hypothesis on theta
  is silently imposed.

Searches performed (2026-10-24, all via prescribed msearch.py or read-only rg/grep):

- LeanFinder: “Opposition involution normalized root vectors bracket squared norm
  p plus one squared times coroot”. Eight hits: Killing-form opposite-root identities,
  root/coroot evaluations, root forms and chain-length formulas. None states the
  conditional squared norm of arbitrary theta-normalized root vectors.
- Loogle: `LieAlgebra.IsKilling.lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg`.
  One hit, the named Killing-form identity. Its Cartan/Killing assumptions and
  conclusion are different: it does not give the opposition normalization or string
  coefficient. Both this declaration and its auxiliary ordinary-weight version were read.
- LeanSearch: “Lie bracket opposition involution normalized root vectors squared root
  string structure constant”. Eight hits, mostly vector-field brackets and the same
  Killing-form auxiliary identity; no exact match.
- Mathlib grep via msearch: `opposition|root.*bracket|lie_eq_killingForm` in `Algebra/Lie`.
  Five hits in Weights/Killing, all belonging to the above identities.
- Project/source rg: `opposition|Opposition|rootBracketNorm|opposition_root_bracket`
  in both `lean/WeilConjectures` and `lean/Sheaf`. Only docstring citations in
  ChevalleyRootNormalization and an unrelated highest-weight docstring; no declaration.
  The required recursive grep for the exact item id in `lean/WeilConjectures` had no hit.
  The split-semisimple decomposition and Chevalley-normalization interfaces were read
  to reuse their notions and index conventions rather than introduce private copies.

No statement correction and no STATEMENT-DISPUTED flag: the supplied conditional
statement passes these mathematical and interface checks.

Validation: the delivered module is compiled with the prescribed `scompile.py`;
the final dry run also checks the JSON attachment and all delivery conventions.
All binders/universes are explicit and both auto-implicit options are disabled.
No definitions, helper axioms or proved theorems are introduced.

## Second reading by Q73

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
