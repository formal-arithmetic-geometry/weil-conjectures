## Worker report

The module `lean/Sheaf/RingTheory/RegularSequenceKoszulRegular.lean` states all three
assertions of `lem-weil-pbc-regular-sequence-koszul-regular`. Its three named theorems
have only `sorry` proofs. No definitions, dependency modules, or new nodes are needed;
the item copy changes only `lean`.

Source checked: [Stacks Tag 062F](https://stacks.math.columbia.edu/tag/062F), Lemma
15.31.2, statement and proof. The local `literature/stacks-project/more-algebra.tex`
was absent, so the source was opened on the Stacks website. The node's statement
matches the source. The docstring includes the node's induction from the final
entry and its full cone cycle chase, including degree one, rather than leaving the
inductive mechanism implicit.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A commutative ring `R`: `{R : Type u} [CommRing R]`, without a domain, local,
  Noetherian, nontriviality, or characteristic restriction.
- An arbitrary `R`-module `M`: `(M : Type v) [AddCommGroup M] [Module R M]`.
  The universe `v` is independent of `u`, as supported by the landed tensor complex.
- A finite sequence of length `r ≥ 0`: `{r : ℕ} (f : Fin r → R)`;
  `List.ofFn f` lists these same entries in their original increasing-index order.
- Successive multiplication maps are injective: `h : IsWeaklyRegular M (List.ofFn f)`.
  Its field `regular_mod_prev` is exactly
  `∀ i (h : i < rs.length), IsSMulRegular
  (M ⧸ (Ideal.ofList (rs.take i) • ⊤ : Submodule R M)) rs[i]`.
  `IsSMulRegular` is defined as injectivity of scalar multiplication. For
  `rs = List.ofFn f`, the prefix at index `i` consists of exactly the earlier
  entries. This imposes no condition that the final quotient be nonzero.
- The first conclusion, `M`-Koszul-regularity: `IsKoszulRegularOn M f` in
  `isKoszulRegularOn_of_isWeaklyRegular`. The recorded dependency definition is
  `∀ i : ℕ, i ≠ 0 → IsZero
  ((ExteriorAlgebra.koszulComplexTensor R r f M).homology i)`.
  Thus the asserted vanishing is that of precisely `K_•(f) ⊗[R] M`, for every
  nonzero degree, with the dependency's negative-degree zero convention.
- Every `M`-regular sequence is `M`-Koszul-regular:
  `RingTheory.Sequence.IsRegular.isKoszulRegularOn` takes
  `h : IsRegular M (List.ofFn f)` and concludes `IsKoszulRegularOn M f`.
  Mathlib's `IsRegular` extends the preceding successive-injectivity predicate
  with `top_ne_smul`, the nonzero final quotient condition in the node's definition.
- Every regular sequence in `R` is Koszul-regular:
  `RingTheory.Sequence.IsRegular.isKoszulRegular` takes
  `h : IsRegular R (List.ofFn f)` and concludes `IsKoszulRegular f`.
  This last predicate uses the untensored `ExteriorAlgebra.koszulComplex`, so
  the last clause is explicitly stated, without leaving the tensor-unit
  identification as an unstated conclusion.

Dependency declarations read and used:

- `Sheaf.RingTheory.KoszulRegularSequence`:
  `RingTheory.Sequence.IsKoszulRegularOn` and `RingTheory.Sequence.IsKoszulRegular`;
  all four definitions of its node were read in full.
- `Sheaf.Paper.KoszulComplex` (imported through the preceding module):
  `ExteriorAlgebra.koszulComplex`, `ExteriorAlgebra.koszulComplexTensor`,
  `koszulBoundary`, and their named supporting theorems. The full signatures and
  docstrings were read. The predicates refer directly to these existing complexes.
- `Mathlib.RingTheory.Regular.RegularSequence`:
  `RingTheory.Sequence.IsRegular` (the regular-sequence node's `mathlib_match`),
  `IsWeaklyRegular`, and `isWeaklyRegular_iff_Fin`; full signatures and docstrings
  read in the pinned source. The regularity field's scalar injectivity was checked
  against `Mathlib.Algebra.Regular.SMul`, `IsSMulRegular`.

Edge cases checked before writing:

- `r = 0`: `Fin 0` is empty and `List.ofFn f = []`; weak regularity is vacuous.
  The empty Koszul tensor complex is concentrated in degree zero. Thus the first
  assertion applies even for `M = 0`. The regular-sequence consequences require
  the nonzero final quotient exactly when Mathlib's `IsRegular` does.
- `M = 0`: every successive map on zero quotients is injective and every term
  of the tensor complex is zero. No nontrivial-module hypothesis is added.
- The zero ring is allowed: it forces every module to be zero, so the main theorem
  still holds; its `IsRegular R` corollary has an impossible antecedent.
- A one-element sequence says injectivity on `M` kills its first Koszul homology.
- A unit entry can force the final quotient to be zero, but this is allowed in
  the first assertion; its complex is acyclic. No proper-ideal condition is added.
- Homology in degrees above `r`, and negative degrees, is included in the
  vanishing requirement through the existing complex and its zero conventions;
  degree zero is deliberately not asserted to vanish.

Searches for an existing statement (all before writing):

- `msearch.py ... leanfinder` query: `A regular sequence on a module is Koszul
  regular: all positive Koszul homology vanishes`. Eight hits, all ordinary
  regular-sequence definitions and properties (`IsRegular`,
  `IsRegular.toIsWeaklyRegular`, cons lemmas, `isRegular_iff`); no Koszul implication.
- `msearch.py ... loogle` query: `"IsWeaklyRegular", "IsKoszulRegular"`.
  Zero hits.
- `msearch.py ... grep` query: `koszul|KoszulRegular`, subdirectory `RingTheory`.
  Only `Regular/RegularSequence.lean:21`, the TODO for Koszul regular sequences.
- `msearch.py ... leansearch` query: `A weakly regular sequence on an arbitrary
  module has vanishing positive Koszul homology`. Service unavailable (Internal
  Server Error); recorded as unavailable, not a negative result.
- `rg -n -i 'koszul|KoszulRegular'` in the read-only
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found only Koszul sign-rule
  material and the different sheaf Koszul sequence on the projective line.
- `grep -rn 'lem-weil-pbc-regular-sequence-koszul-regular'` in that source tree
  returned no match.
- `rg -n 'IsKoszulRegular|isKoszulRegular.*of|[Kk]oszul.*[Rr]egular'` in the
  repository's `lean/Sheaf` found the dependency predicates, the closed-immersion
  application, and a conormal proof docstring, but no theorem stating this node.
- Exact-name grep for all chosen theorem names in Mathlib, the source repository,
  and `lean/Sheaf` returned no match.

Validation: `scompile.py C1 lem-weil-pbc-regular-sequence-koszul-regular
lean/Sheaf/RingTheory/RegularSequenceKoszulRegular.lean` completed on the server
with exit code 0 (1.5 seconds), no errors and no warnings. All variables and
universes are explicitly bound. No statement correction or disputed statement.


## Second reading by C1

Independent reader: opened the item node, its sandbox copy and all 76 lines of
`RegularSequenceKoszulRegular.lean`, then each of the three statement dependency
nodes and their recorded declarations. No mismatch found; no Lean or node change.
Only this second-reading section was appended. There are no new definition nodes
or dependency modules in this delivery, and no statement correction to review.

Source: the local Stacks `.tex` files are absent on this machine. Read the actual
upstream [more-algebra.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex)
at `section-koszul-regular`, `definition-koszul-regular-sequence`,
`lemma-regular-koszul-regular` and `lemma-cone-koszul`; also read
[algebra.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex)
at `definition-regular-sequence`. Checked the rendered
[Tag 062F](https://stacks.math.columbia.edu/tag/062F) and section 062D.
The lemma and surrounding section impose no global Noetherian, local, finite-module,
nontriviality or characteristic assumptions. The nonzero ultimate quotient occurs
in the definition of regular sequences, not the main lemma's hypothesis.

Node checklist, matched item by item:

1. Object: arbitrary commutative ring R. Lean `{R : Type u} [CommRing R]`
   in all three theorems. Verdict: exact; no field/domain/local-ring restriction.
2. Object: arbitrary R-module M. Lean `(M : Type v) [AddCommGroup M]
   [Module R M]` in the main theorem, implicit M in the module corollary.
   Verdict: exact, arbitrary independent carrier universe and no finite-generation
   or nonzero condition.
3. Object: ordered finite sequence with r >= 0. Lean `{r : ℕ} (f : Fin r → R)`
   (implicit f in corollaries). `List.ofFn f` preserves the increasing Fin order;
   index j corresponds to the paper's entry j+1. Verdict: exact, including r=0.
4. Hypothesis: multiplication by each entry injective on M modulo the submodule
   generated by preceding entries. Lean
   `h : IsWeaklyRegular M (List.ofFn f)`. Opened Mathlib's actual structure:
   `regular_mod_prev : ∀ i (h : i < rs.length), IsSMulRegular
   (M ⧸ (Ideal.ofList (rs.take i) • ⊤ : Submodule R M)) rs[i]`.
   Opened `IsSMulRegular`: `Function.Injective ((c • ·) : M → M)`.
   `Ideal.ofList (rs.take i) • ⊤` is precisely the preceding entries times M.
   Verdict: exact, with no requirement on the final quotient.
5. Main conclusion: H_i(K(f) tensor M)=0 for every i != 0. Lean
   `IsKoszulRegularOn M f`. Opened its body in the recorded module
   `Sheaf.RingTheory.KoszulRegularSequence`: it quantifies over every nonzero
   natural degree and uses `IsZero` of the homology of
   `ExteriorAlgebra.koszulComplexTensor R r f M`. Opened
   `Sheaf.Paper.KoszulComplex`: terms are exterior powers of `Fin r →₀ R`
   tensored with M, differential is the restriction of `contractLeft` with
   `Finsupp.linearCombination R f`, then `rTensor M`. This linear form sends
   the ith standard generator to f i. Homology is Mathlib's module homology,
   zero precisely when its kernel/image quotient is zero. Negative degrees are
   zero under the dependency's extension convention. Verdict: exact; H_0 is
   deliberately excluded and no degrees above r are dropped.
6. Corollary: every M-regular sequence is M-Koszul-regular. Lean
   `IsRegular.isKoszulRegularOn`, hypothesis `IsRegular M (List.ofFn f)`.
   Opened the recorded Mathlib declaration: it extends the preceding weak
   regularity with `top_ne_smul`, equivalent to nonzero final quotient.
   Verdict: exact, with the additional condition only in this corollary.
7. Corollary: every regular sequence in R is Koszul-regular. Lean
   `IsRegular.isKoszulRegular`, hypothesis `IsRegular R (List.ofFn f)`,
   conclusion `IsKoszulRegular f`. Opened that predicate: it uses the untensored
   `ExteriorAlgebra.koszulComplex R r f`. Verdict: exact, explicitly covers
   the ring conclusion rather than stopping at the tensored-R predicate.

Edge cases: Fin 0 and its empty list are admitted; the empty complex has only
M in degree zero, so the main implication permits both M=0 and M nonzero.
For M=0 successive injectivity is automatic and the tensor complex vanishes.
The zero ring is admitted (its modules are zero); the regular-sequence antecedent
for R is then impossible, just as in the source. Units and a zero final quotient
are admitted in the main implication. For r=1 the sole positive homology tests
injectivity on M. Negative degrees are zero by convention and degrees above r
vanish because exterior powers above the free rank vanish; degree zero need not
vanish. No characteristic or universe limitation is added: the tensor complex
lives in `ModuleCat.{max u v} R`. Empty schemes are irrelevant to this ring lemma.

Independent searches used different phrasing from the first worker:

- LeanFinder through `msearch.py`: "Injective multiplication on successive quotient
  modules implies acyclicity of the exterior-power contraction complex in strictly
  positive degrees". Eight hits: exterior-algebra injectivity, an alternating
  constant complex, exact four-term sequence lemmas, and
  `IsSMulRegular.smulShortComplex_shortExact`; none states this implication.
- Loogle through `msearch.py`: `"koszul"`; zero hits.
- LeanSearch through `msearch.py`: "Successive nonzerodivisors on quotient modules
  give exact Koszul complexes in positive degrees". Service unavailable (Internal
  Server Error); not treated as a negative search result.
- `msearch.py` grep: `contractLeft|koszul|KoszulRegular` finds contraction machinery
  and Koszul mentions, without this regularity theorem. Direct `rg` additionally
  checked `acyclic|koszul|regular.*homology|homology.*regular` in Mathlib's regular
  sequence files and LocalCohomology: only the Koszul TODO and a docstring mention.
- Direct `rg` in all source `WeilConjectures`, repository `lean/Sheaf`, and
  `dag/lean_names_upstream.json` checked `KoszulRegular`, `koszulComplex`, and
  the proposed theorem names. No existing implication or name collision.
  The project has the recorded predicates/complexes and applications to closed
  immersions and diagonals; upstream has the different sheaf sequence on P1.
  Thus retaining this module meets the one-definition/statement rule.

The first theorem's docstring carries the node's four steps: empty case and
prefix H_0 identification, exterior-power split with signed cone differential,
cycle chase with separate degree-one injectivity, then the regular-sequence
corollaries in their own docstrings. Sources and blueprint tags are present for
all three named theorems. No definitions or extra hypotheses were introduced;
all three proofs remain `sorry`. Both imports are used, all lines are <=100
characters, and u, v, R, M, r, f and h are explicitly bound.

Validation: `lean.statement` equals the main file signature verbatim; the only
changed node field against the read-only base is `lean`. Recompiled independently
using `scompile.py C1 lem-weil-pbc-regular-sequence-koszul-regular
lean/Sheaf/RingTheory/RegularSequenceKoszulRegular.lean` from the sandbox: exit 0,
1.5 seconds, no errors or warnings. The initial invocation from the repository
had a relative-path FileNotFoundError; running from the specified sandbox fixed
that invocation without changing any source or tool.
