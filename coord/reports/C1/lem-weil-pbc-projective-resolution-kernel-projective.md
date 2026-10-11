## Worker report

The module `Sheaf.RingTheory.ProjectiveResolutionKernelProjective` states the
kernel assertion and both particular cases of
`lem-weil-pbc-projective-resolution-kernel-projective` as three named theorems.
Every proof is `sorry`. No definitions, new nodes, dependency modules, or node
corrections are needed.

Hypothesis and clause correspondence:

- The commutative ring is `{R : Type u} [CommRing R]`; modules are arbitrary
  `ModuleCat.{v} R`, with independent explicitly declared universes `u v`.
- The nonnegative integer bound is `d : ℕ`; the module `M` is `S.right` in the
  first two statements, and an explicit `M : ModuleCat.{v} R` in the third.
  Naming the last object of the finite sequence as `M` introduces no extra
  equality or isomorphism assumption.
- The resolution-length hypothesis is exactly the dependency's
  `ModuleCat.HasProjectiveResolutionLE S.right d` (or `... M 0`). It is not
  Mathlib's Ext-based projective-dimension predicate.
- The main statement uses `e : ℕ` and `he : d ≤ e + 1`, equivalent to
  `e ≥ d-1` for nonnegative `e`. `S : ComposableArrows (ModuleCat R) (e+1)`
  encodes `F_e → ... → F_0 → M`, in left-to-right order, without adding an
  arrow out of the leftmost term. `hS : S.Exact` requires precisely exactness
  at the intermediate objects. `[Epi (S.map' e (e+1))]` gives surjectivity
  of `F_0 → M`, hence exactness at `M` in the sequence ending in zero.
- Each projective term is supplied by `hF : ∀ i hi, Module.Projective R
  (S.obj' i (Nat.le_of_lt hi))`, with `hi : i < e+1`. These are precisely
  `F_e,...,F_0`, excluding `M`.
- The main conclusion is `Module.Projective R
  (kernel (C := ModuleCat.{v} R) (S.map' 0 1))`. This is the kernel of
  `F_e → F_{e-1}` for `e>0`, and of `F_0 → M` for `e=0`.
  Mathlib's `ModuleCat.kernelIsoKer` identifies the categorical kernel with
  the usual linear-map kernel submodule.
- The positive-bound particular case is
  `ModuleCat.projective_of_exact_partial_projective_resolution`:
  `hd : 1 ≤ d`, `S : ComposableArrows (ModuleCat R) d` records the sequence
  `F_{d-1} → ... → F_0 → M`; `K` and `j : K ⟶ S.left` are arbitrary.
  `[Mono j]` is exactness at `K` after the initial zero.
  `(S.precomp j).Exact` is exactness at `F_{d-1}` and all subsequent
  intermediate modules, and `[Epi (S.map' (d-1) d)]` is exactness at `M`.
  `hF` ranges over `i<d`, precisely all the projective `F_i`.
  `hM` is the same resolution-length hypothesis; the conclusion is
  `Module.Projective R K`.
- The zero-bound particular case is separately stated as
  `ModuleCat.projective_of_projective_resolution_length_zero`, with
  `HasProjectiveResolutionLE M 0` and conclusion `Module.Projective R M`.

Dependency declarations read and used:

- `Sheaf.RingTheory.GlobalDimension`, `ModuleCat.HasProjectiveResolutionLE`:
  existence of a `CategoryTheory.ProjectiveResolution M` whose terms in
  degrees greater than `d` are zero; the resolution's fields include
  projectivity and a quasi-isomorphic augmentation. Read its full definition
  and docstring, and the underlying `ProjectiveResolution` structure.
- `Mathlib.Algebra.Homology.ExactSequence`,
  `CategoryTheory.ComposableArrows.Exact`: a complex with every consecutive
  short complex exact. Read its structure, the `ShortComplex.Exact` structure,
  and the `obj'`, `map'`, `right`, `left` and `precomp` conventions.
- `Mathlib.Algebra.Module.Projective`, `Module.Projective`: the canonical
  free-module surjection splits. Read the class and docstring; the dependency
  identifies this with the direct-summand and lifting definitions.
- `Mathlib.Algebra.Category.ModuleCat.Abelian` supplies the abelian structure
  and hence the kernel existence used by the first statement. No additional
  hypothesis on the ring or module is needed.

Source checked: Stacks Project Tag 00O5,
https://stacks.math.columbia.edu/tag/00O5 (the local literature checkout is
absent on this machine). Its induction on the projective dimension, splitting
in dimension zero, Schanuel step, two shortened sequences, and the final
kernel identification agree with the node's detailed proof. The docstrings
carry all nine proof steps, across the three declarations. The node uses a
resolution-length upper bound rather than exact minimal dimension, as its
inductive proof explicitly explains; no source-driven correction is needed.

Edge cases checked before writing: `d=0` allows every `e≥0` and includes
projectivity of `M`; `e=0` allows `d=0` or `d=1`, imposes only the surjection
`F_0 → M`, and concludes projectivity of its kernel. For `d=1` the particular
case is exactly `0 → K → F_0 → M → 0`. Zero modules and the zero ring are
allowed, and no finite-generation, Noetherian, or nonzero assumption occurs.
The bound `d≤e+1` avoids truncated-subtraction ambiguity. The main finite
sequence has no initial-zero exactness condition. Natural-number indices
cover the nonnegative integers; negative `e` cannot index the named `F_e`.
Arbitrary module universes are retained.

Searches (all remote searches logged by msearch.py in searches.jsonl):

- LeanSearch: query "kernel in any partial projective resolution is projective
  if the module has projective dimension at most d". Service unavailable
  (Internal Server Error); no verdict inferred from this outage.
- Loogle: `Module.Projective, LinearMap.ker`. One hit, `Module.eval_ker`,
  about injectivity of double-dual evaluation, not the node's statement.
- LeanFinder: "If M has a projective resolution of length at most d, the kernel
  of any exact sequence of e+1 projective modules ending in M is projective
  for e >= d-1". Returned canonical projective-resolution terms and the
  one-step `ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃_iff` and
  related Ext-dimension lemmas, not the arbitrary finite-sequence assertion.
- Mathlib grep via msearch.py: `syzyg|kernel.*projective|projective.*kernel`
  under CategoryTheory. Hits describe canonical projective covers of kernels,
  not projectivity of these kernels under a resolution-length bound.
- Source and landed-project rg: `syzyg|projective_resolution_kernel|
  lem-weil-pbc-projective-resolution-kernel-projective` under WeilConjectures,
  lean/Sheaf, and dag/lean_names_upstream.json. Only unrelated syzygies and
  a proof-plan reference in MinimalFiniteFreeResolutionLocal; no declaration
  matching the statement. The exact blueprint id has no source declaration.

Validation: server single-file compile, then deliver2.py --no-push. The second
reader supplies the independent reading; no second-reading section is authored
by this worker. No STATEMENT-DISPUTED issue found.

## Second reading by C1

I read the node copy, all nine proof steps, the three dependency nodes and
their recorded declarations, and the delivered Lean independently. The local
Stacks checkout is absent. I read the source TeX at
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
including `section-conventions`, `lemma-independent-resolution` (Tag 00O5)
and its proof; the fetched copy is in scratchpad/algebra.tex, not delivered.
The conventions make rings commutative with identity and include the zero
ring. No Noetherian, local, finite-generation or characteristic hypothesis
is assumed in this lemma. The source's minimal dimension formulation implies
the node's length-bound formulation, and its induction works for that bound.
No correction of the natural-language node is needed.

Object, hypothesis and conclusion checklist (all verdicts refer to the
repaired file):

- Ring R: `{R : Type u} [CommRing R]`. PASS: the source's commutative unital
  ring, including the zero ring; no extra instance on R.
- Module M: `S.right` in the first two theorems, and explicit
  `(M : ModuleCat.{max u v} R)` in the third. PASS: naming M as the last
  object of S does not constrain it. The module universe includes the ring
  universe; both u and v are explicitly bound and arbitrary.
- Nonnegative bound d: `(d : ℕ)` (in `(d e : ℕ)` for the main theorem).
  PASS: exactly the nonnegative integer resolution bound.
- Existence of a projective resolution of length at most d:
  `hM : HasProjectiveResolutionLE S.right d`, or `... M 0` in the zero case.
  PASS after the universe repair. I opened GlobalDimension.lean:
  this is `∃ P : ProjectiveResolution M, ∀ i, d < i → IsZero (P.complex.X i)`.
  I opened the ProjectiveResolution structure: projective terms, a chain
  complex, and a quasi-isomorphic augmentation to M in degree zero.
  In ModuleCat this is exactly the node's augmented exact finite resolution,
  padded by zero objects. It uses the recorded dependency, not Ext dimension.
- Index e and bound: `(e : ℕ)` and `he : d ≤ e + 1`. PASS: the node's
  nonnegative e with e ≥ d-1, including every e when d=0.
- Terms and arrows: `S : ComposableArrows (ModuleCat.{max u v} R) (e + 1)`.
  PASS: I opened ComposableArrows.Basic; obj' indexes from left to right,
  right is index e+1, map' gives the indicated linear maps. This encodes
  F_e through F_0 followed by M, with no arrow into F_e.
- Exactness: `hS : S.Exact` and `[Epi (S.map' e (e + 1))]`. PASS:
  I opened ExactSequence.lean and ShortComplex.Exact. The former requires
  zero consecutive composites and exact consecutive short complexes, hence
  image equals kernel at precisely the interior terms. The epi is precisely
  surjectivity of F_0 to M and exactness at M after adjoining zero.
  No injectivity at F_e is imposed.
- Every F_i projective: `hF : ∀ i hi, Module.Projective R
  (S.obj' i (Nat.le_of_lt hi))` for `hi : i < e+1`. PASS: these are exactly
  all F terms, excluding M. I opened Module.Projective, its splitting and
  lifting interpretation, and ModuleCat.Projective's comparison declarations.
- Main conclusion: `Module.Projective R
  (kernel (C := ModuleCat.{max u v} R) (S.map' 0 1))`. PASS:
  the first arrow is F_e to F_(e-1), or F_0 to M when e=0.
  I opened ModuleCat.kernelIsoKer: this categorical kernel is isomorphic
  to the usual linear-map kernel submodule; the conclusion is the full
  module-projectivity assertion, not projectivity in a smaller category.
- Particular case d≥1: `hd : 1 ≤ d`, `S : ComposableArrows ... d`, the
  same hM, `K : ModuleCat.{max u v} R`, and `j : K ⟶ S.left`. PASS: these
  introduce exactly K and F_(d-1) through F_0 followed by M.
  `[Mono j]`, `(S.precomp j).Exact` and `[Epi (S.map' (d-1) d)]`
  render exactness of the entire sequence starting and ending with zero.
  I opened precomp: it adds j on the left. hF ranges over i<d, exactly the
  F terms, and the conclusion `Module.Projective R K` is exactly the clause.
- Particular case d=0: `HasProjectiveResolutionLE M 0 → Module.Projective R M`
  is the third theorem. PASS: the case is stated separately, not lost through
  the positive-bound hypothesis of the second theorem.

Mismatch and repair: the draft used ModuleCat.{v} R with independent ring
universe u. The dependency's ProjectiveResolution terms are categorically
projective; the converse comparison to Module.Projective requires
`[Small.{v} R]` (ModuleCat.Projective.lean, lines 32–43). This size premise
is not supplied at arbitrary independent u,v. I changed every module-category
occurrence in the three statements to ModuleCat.{max u v} R, so the size
premise is automatic, with no extra mathematical hypothesis. Arbitrarily
large modules remain covered by arbitrary v; smaller carriers can be lifted
to this common universe. This follows the landed MinimalFiniteFreeResolutionLocal
encoding. I updated lean.statement verbatim to the repaired main signature.
The Worker report above describes the original draft and is retained as
requested; its claim that independent universes need no repair is superseded
by this reading. No other statement or docstring was rewritten.

Edge cases: d=0 permits every e and the third theorem asserts M projective;
e=0 gives one arrow and interior exactness is vacuous, but the epi remains
the necessary surjectivity, with d≤1. At d=1 the second theorem is precisely
0→K→F_0→M→0. Zero modules, zero ring and every characteristic are allowed.
There is no variable index set and no scheme, so empty sets or schemes add
no condition; the possibly empty collection of interior exactness tests is
handled correctly at e=0. The positive-bound theorem excludes d=0 only
because that clause has its own third statement. No unbound universes or
variables remain.

Independent searches, using wording different from the first reader:

- LeanFinder via msearch: "An arbitrary finite exact sequence of projective
  modules has projective leftmost kernel when its length exceeds a finite
  projective resolution of its last module". Eight hits: the one-step
  ShortExact.hasProjectiveDimensionLT_X₃_iff and related dimension shifts,
  ProjectiveResolution.projective/exact₀/of and canonical resolution terms.
  I opened the dimension-shift signature: it is about Ext projective
  dimension and one short exact sequence, not the node's arbitrary chain
  under its resolution-length predicate. No exact match.
- Loogle via msearch: `ComposableArrows.Exact, Projective` was not a valid
  indexed identifier, so I repeated with
  `CategoryTheory.ProjectiveResolution, CategoryTheory.Projective`. Four
  hits (self, projective, mk, instProjectiveXIntCochainComplex) describe
  supplied resolution terms; none states this node.
- LeanSearch via msearch: "Any sufficiently high kernel in a finite exact
  projective resolution is projective if a bounded projective resolution
  exists". Service unavailable (Internal Server Error); no no-match verdict
  inferred from that outage.
- Mathlib grep via msearch: `independent-resolution|00O5|projective.*kernel|
  kernel.*projective` found canonical projective covers, a cokernel fact
  about a given resolution, unrelated probability kernels, and localization
  dimension shifting. None states the arbitrary finite-chain assertion.
- Direct rg across pinned Mathlib's Algebra and CategoryTheory, the full
  WeilConjectures source, landed lean/Sheaf and dag/lean_names_upstream.json:
  `projective_kernel|projective.*resolution.*length|resolution.*length.*projective|
  independent-resolution|00O5|syzygy.*projective` plus all three full
  declaration names and HasProjectiveResolutionLE. Project hits are the
  existing resolution-length definition and specialized finite-free or
  localization statements; MinimalFiniteFreeResolutionLocal cites this
  still-missing assertion in its proof plan. No duplicate declaration found.
  Remote queries and results are also recorded in searches.jsonl.

No new definition nodes or dependency modules were supplied, so H12/H13
require no additional source reading. No statement_change is present.
The module has no definitions and exactly three sorry theorem proofs.
The source/blueprint docstrings carry proof steps 1–8 in the kernel theorem
and step 9 (including the zero case) in the particular cases. Imports serve
the resolution predicate, exact chains and module-category kernels.
Compilation of the repaired module through scompile.py succeeded (exit 0,
1.4 seconds) with no warnings or errors.
