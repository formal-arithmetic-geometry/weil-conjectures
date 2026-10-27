## Worker report

The module `Sheaf.Algebra.Module.GradedLocalIsomorphismTail` states
`LocalizedModule.graded_local_isomorphism_tail`, with `sorry` as its only proof.
Its three real auxiliary definitions package clauses of this same node, as
permitted for owning-node helpers by the launcher brief: no independent notion,
second localization, arbitrary comparison map, or new axiom is introduced.

Read the whole item and all four statement-dependency nodes, the two additional
proof dependencies, and their recorded declarations. Read Stacks
`literature/stacks-project/coherent.tex`, Tag 0AG7,
`lemma-recover-tail-graded-module`, especially the proof's final paragraphs
through the homogeneous-generator bound (lines 3901–3929). The source's sheaf
argument is already abstracted in the accepted node; this delivery retains that
node's abstract hypotheses and all its intermediate conclusions. There is no
statement correction and no disputed assertion. No repair note exists for the
item. The example Sheaf CompactObject module is now withdrawn; its recorded
upstream module `WeilConjectures.CategoryTheory.CompactObject` was read as the
header/docstring example instead.

Hypotheses, clause by clause:

- The commutative Noetherian ring is `S : Type u`, `[CommRing S]`,
  `[IsNoetherianRing S]`. Its nonnegative internal grading is
  `𝒜 : ℕ → AddSubgroup S`, `[GradedRing 𝒜]`.
- The finite family, including r = 0, is `r : ℕ`, `f : Fin r → S`.
  `hf` puts it in degree one; `hgen` is exactly
  `Algebra.adjoin (𝒜 0) (Set.range f) = ⊤`.
- M and N have independent universes v and w, additive groups and S-module
  structures. Their integer gradings are `𝓜`, `𝓝`, with internal direct-sum
  conditions `h𝓜`, `h𝓝`. `hsmulM` and `hsmulN` say exactly
  S_a M_n ⊆ M_(a+n) and S_a N_n ⊆ N_(a+n), with a nonnegative and n integral.
- `ψ : M →ₗ[S] N` is S-linear; `hψ` says it preserves every integer degree.
- `[Module.Finite S M]` is finiteness of M. `hfinite` is finite generation of
  the S-span of all nonnegative N_n. Under the stated grading compatibility,
  this span is exactly N+: multiplying its homogeneous generators by each
  homogeneous scalar stays in nonnegative degrees, and general scalars are
  finite sums of their components. Conversely every N_n, n >= 0, belongs to
  that span. Thus this is exactly finite generation of N+, with no condition
  at all on the negative-degree truncation of N. Submodule.FG and
  Module.Finite on that submodule are Mathlib's equivalent forms.
- `hloc` is `Set.BijOn` for the canonical `IsLocalizedModule.map` of ψ between
  the two recorded `degreeZeroFractions` subsets. These use powers of f_i
  and the nonnegative degree pieces, so they represent x/f_i^a with x in M_a
  or N_a. In a direct grading a nonzero power f_i^a can have only degree a;
  a zero denominator makes the localization zero. Hence the recorded
  equal-degree fraction definition gives precisely the node's fraction set,
  including nilpotent f_i. The ordinary localization supplies its equivalence
  relation and operations. The canonical localized S-linear map commutes
  with localized scalars, so bijectivity on these degree-zero subsets is
  exactly the asserted isomorphism; no arbitrary map is assumed.

Conclusions, clause by clause:

- The existential `P : Submodule S M`, `R : Submodule S N` have additive
  subgroups exactly `⨆ n : ℕ, 𝓜 n` and `⨆ n : ℕ, 𝓝 n`. These are internal
  sums, hence exactly M+ and N+. Specifying their subgroup carriers uniquely
  determines the submodules. Their existence is a conclusion, not a new
  hypothesis or an unspecified construction.
- `φ : P →ₗ[S] R` satisfies `(φ x : N) = ψ (x : M)` for every x. This
  uniquely determines ψ+, including its ordinary module operations.
- K is literally `φ.ker`; Q is literally `R ⧸ φ.range`, using Mathlib's
  kernel, range and quotient. No alternate modules are substituted.
- `𝓚 n` is specified as the inverse image of M_n under K → P → M.
  `𝓠 n` is specified as the image of N_n ∩ N+ under R → Q. These formulas
  uniquely determine the induced gradings and give Q_n = N_n/ψ(M_n) for
  n >= 0. Negative pieces vanish.
- `GradedTailConclusion 𝒜 f 𝓚 BK` and its Q counterpart include
  `Module.Finite S T`, `DirectSum.IsInternal 𝓣`, scalar-degree compatibility,
  zero negative pieces, and `∀ i x ∈ degreeZeroFractions ..., x = 0`.
  The latter is precisely T_(f_i) = 0 (the zero fraction belongs to the set).
- `IsTailGeneratingFamily` says `span S (range t) = ⊤`, t_j ∈ T_(e_j),
  b_ij >= 1, and f_i^b_ij • t_j = 0. The index `Fin k` permits every finite
  family, including the empty one. `e : Fin k → ℕ` gives exactly e_j >= 0.
  The helper is just the conjunction of these conditions, with real data.
- Each `GradedTailConclusion` supplies such k,t,e,b and identifies B with
  `tailGeneratorBound e b`. This definition is `Finset.univ.sup` of
  e_j + sum_i b_ij, hence exactly max({0} union {e_j + sum_i b_ij}).
- The final conjunct of `GradedTailConclusion` quantifies over EVERY such
  family and exponents and states T_n = 0 for n strictly greater than its
  own bound. It does not restrict this assertion to the selected witnesses.
- The final theorem clause uses n >= the integer cast of `1 + max BK BQ`.
  This is the requested n0, which is nonnegative because it is a natural
  number. It gives `e : 𝓜 n ≃+ 𝓝 n` whose underlying function is ψ_n, and
  the scalar formula for all a : 𝒜 0 and x,y in the piece with y = a • x.
  This is exactly S_0-linearity of the additive isomorphism in ambient
  representatives, without an extra chosen module instance. Bijectivity and
  the forward scalar identity imply that its inverse is S_0-linear too.

Dependency declarations used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, `Submodule.FG`.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule.Away`,
  `LocalizedModule.mkLinearMap`, `IsLocalizedModule.map` (its fraction map).
- `WeilConjectures.Algebra.Module.DegreeZeroFractions`:
  `LocalizedModule.degreeZeroFractions`, read in full including its docstring.
- Proof import `Mathlib.RingTheory.Noetherian.Basic`: `Submodule.FG.of_le`,
  the recorded Mathlib match of lem-weil-pbc-noetherian-submodule-finite.
- Proof import `Sheaf.Algebra.Module.GradedLocalizationExact`:
  `LocalizedModule.graded_localization_exact`, including its full signature
  and degree-zero exactness clause. It is proof-only; its older let-based
  signature is neither restated nor used in the new theorem's interface.

Edge cases checked mathematically before writing:

1. r = 0: algebra generation forces S = S_0; a generator contributes only
   in its own degree. The empty i-sum is zero, and the bound still works.
2. Zero T and empty t: span of the empty set is top exactly for zero T;
   Finset.sup is zero. No Nonempty assumption is present anywhere.
3. f_i = 0 or nilpotent: localizations are zero with the ordinary relation;
   the annihilator exponents exist and can be enlarged to be at least one.
4. M = N = 0, and also the zero ring: all clauses retain their meaning.
5. Nontrivial torsion: S = k[t], M = S/(t^2), N = S/(t), ψ the quotient.
   K has a degree-one generator killed by t, so B_K = 2; Q is zero. This
   verifies that the strict bound and the n0 shift allow low-degree failures.
6. Negative generator degrees of M are allowed; only the truncations K,Q
   require nonnegative generator degrees. N can have an arbitrarily large,
   nonfinite negative part (e.g. over S = S_0 with r = 0). No inference of
   Module.Finite S N is made. Distinct ring/source/target universes remain
   independent, and no site or size restriction has been added.

Searches actually made using msearch.py Q123 lem-sfb-graded-local-isomorphism-tail:

- LeanFinder: "A degree preserving map of graded modules over a Noetherian
  ring generated in degree one is an isomorphism in high degree if its
  degree zero localizations are isomorphisms". Eight results: Proj.toSpec
  isomorphisms, HomogeneousLocalization.Away eventual denominator and span
  facts, basicOpenIsoAway and related Proj facts. None states this result.
- Loogle: `DirectSum.IsInternal, Module.Finite`. Seven results, on traces
  and primary torsion decompositions; no eventual graded map theorem.
- Grep: `eventual|annihilat|truncat` in RingTheory/GradedAlgebra. One result,
  HomogeneousLocalization.Away.eventually_smul_mem, a ring fraction fact.
- LeanSearch: "A finite graded module with vanishing homogeneous
  localizations at degree one generators has zero homogeneous pieces in
  sufficiently high degrees". Eight results on homogeneous ring
  localization, span of fractions, scalar towers and zero numerator or
  denominator facts; no module-tail statement.
- Local rg in both lean/WeilConjectures and lean/Sheaf for graded tail,
  nonnegative truncations, degreeZeroFractions, and homogeneous generators
  found the parent FiniteGradedModuleSectionTail, homogeneous-fraction
  helpers and specialized projective-line finite homogeneous generators.
  They do not state the abstract kernel/cokernel and arbitrary bound result.
  `grep -rn lem-sfb-graded-local-isomorphism-tail lean/WeilConjectures`
  returned no occurrence. Searching all of Mathlib, WeilConjectures and
  Sheaf for the four proposed declaration names returned no collision.
  dag/lean_names_upstream.json also has no attachment for this statement.

Validation: scompile.py compiled both the sandbox probe and the module cleanly
on the server (16.3 s and 6.9 s). The first probe exposed the missing
Algebra.adjoin import, repaired by importing Algebra.Subalgebra.Lattice.
No theorem was proved; all helper definitions contain real data and no sorry.
The node copy changes only `lean` and preserves indent 1 and final newline.

## Second reading by Q123

This is the dispatcher's worker self-reading, not an independent review; the
maintainer supplies the independent review as prescribed in the direct-delivery
brief. Reopened the node and read the final module from imports through the
last scalar identity. Checked each hypothesis and clause against the mapping
above. In particular, verified that hfinite concerns N+ rather than N, that
both induced gradings are tied to the actual kernel and quotient, that the
vanishing bound is universal in the generators and exponents, and that the
final isomorphism is the restriction of ψ and includes S_0-linearity. The
zero localization assertion is about the recorded fraction subset rather
than the whole ordinary localization. The generators of K,Q are existential
conclusions, never assumptions. Natural exponents/degrees and Fin indices
retain zero and empty cases; integer grading and independent universes
retain all original modules. The initial missing import was fixed. No
mathematical mismatch, statement correction, dependency repair or new node
was needed.
