## Worker report

The module `Sheaf.RingTheory.CohenMacaulayFreeResolution` states
`IsLocalRing.exists_finite_free_resolution_to_maximalCohenMacaulay`, with only `sorry`
as its proof. No definitions or auxiliary theorems were needed, and the node's statement
is unchanged.

Hypothesis and conclusion correspondence:

- The commutative Noetherian local ring is `{R : Type u} [CommRing R]
  [IsNoetherianRing R] [IsLocalRing R]`. Its maximal ideal is the one used by
  `IsLocalRing.depth`; no separate choice of maximal ideal is needed.
- Finite Krull dimension `d` is `(d : ℕ)` and
  `hdim : ringKrullDim R = (d : WithBot ℕ∞)`. The negative-infinity and infinity cases
  are not inadvertently identified with finite dimension.
- The Cohen–Macaulay hypothesis is `hcm : (d : ℕ∞) ≤ depth (R := R) R`.
- The nonzero finite module is `(M : Type v) [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Nontrivial M]`. All universes and variables are explicit.
- Since the depth definition is extended-natural-valued, `∃ e : ℕ,
  depth (R := R) M = (e : ℕ∞) ∧ e ≤ d` both establishes that depth is finite and gives
  the asserted bound. This asserts finiteness as a conclusion, not an extra hypothesis.
- Put `k = d - e`. `S : ComposableArrows (ModuleCat.{max u v} R) (k + 3)` has `k + 4`
  objects, ordered `0, K, F_{k-1}, …, F₀, M, 0`. `S.Exact` is precisely exactness of
  the consecutive arrows, including their zero compositions. `IsZero (S.obj' 0)` and
  `IsZero (S.obj' (k + 3))` require both zero endpoints. The endpoint object at `k + 2`
  is identified with the given module by `Nonempty ((S.obj' (k + 2)) ≃ₗ[R] M)`.
  Transport along this equivalence recovers a sequence ending in the original `M`.
- For every `i : Fin k`, `S.obj' (i.val + 2)` is finite and free using
  `Module.Finite` and `Module.Free`. In left-to-right order this term is `F_{k-1-i}`.
  Over a commutative local ring, a finite free module has a finite basis, so these are
  exactly modules isomorphic to `R^{⊕ n_i}` with natural `n_i`, including zero rank.
- `∃ hK : Module.Finite R (S.obj' 1)` requires the kernel term to be finite. Installing
  that witness with `letI := hK` permits the existing finite-module depth definition.
  `Subsingleton (S.obj' 1) ∨ depth (R := R) (S.obj' 1) = (d : ℕ∞)` states exactly
  the alternative “zero or depth d”. It does not strengthen the alternative to nonzero.
- When `e = d`, `Fin (d - e)` is empty: no free terms. The four objects are `0,K,M,0`.
  Exactness forces the sole map `K → M` to be both injective and surjective, hence
  an isomorphism. Thus the parenthetical zero-length case is included.

Dependency declarations inspected and used:

- `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing` (all ideals finitely generated).
- `Mathlib.RingTheory.KrullDimension.Basic`, `ringKrullDim : WithBot ℕ∞`.
- `Sheaf.RingTheory.Depth`, `Ideal.depth` and its local specialization `IsLocalRing.depth`.
  Read their full signatures/docstrings and their regular-sequence supremum definitions.
- `Mathlib.RingTheory.Finiteness.Defs`, `Module.Finite` (finitely generated top submodule),
  imported transitively through the depth module.
- `Mathlib.Algebra.Homology.ShortComplex.Exact`, `CategoryTheory.ShortComplex.Exact`,
  and the exact-sequence dependency's recorded finite-sequence specialization
  `CategoryTheory.ComposableArrows.Exact` in `Mathlib.Algebra.Homology.ExactSequence`.
  Read the signatures and docstrings of both. The dependency record already explicitly
  names this specialization, so it needs no replacement dependency module.
- `Mathlib.LinearAlgebra.FreeModule.Basic`, `Module.Free` (existence of a basis).
- `Mathlib.Algebra.Category.ModuleCat.Abelian` supplies the abelian category of R-modules.

Edge cases checked: dimension zero gives `e = 0` and the identity-length resolution;
`e = d` has no free terms; `e = 0 < d` has exactly `d` free terms; zero-rank free terms
are permitted; the zero kernel is explicitly permitted; the input zero module is excluded
exactly as the node requests. There is no restriction on characteristic. The sequence's
module universe is `max u v`, so it accommodates finite free modules over `R` even when
`M` lives in a smaller universe. Its last module is related to `M` by a cross-universe
linear equivalence, avoiding any additional smallness hypothesis.

Searches for an existing statement (recorded by `msearch.py` in `searches.jsonl`):

- LeanSearch: “Cohen Macaulay local ring finite module finite free resolution maximal
  Cohen Macaulay syzygy”; service unavailable (Internal Server Error).
- LeanFinder: same query; eight hits on finite modules, free-of-flat over local rings,
  cotangent dimension and localization, none about depth or this resolution.
- Loogle: `Module.Free, Module.Finite`; twelve hits, including finite presentations
  and finite bases, none asserting this finite resolution or the final depth condition.
- Mathlib grep: `Cohen.?Macaulay|mcm_resolution|depth.*resolution|resolution.*depth`;
  no hits.
- `rg` with the same concept pattern and the node id in the source checkout's
  `WeilConjectures/` and this project's `lean/Sheaf/`: no hits. A separate exact-name
  search in both libraries, Mathlib and `dag/lean_names_upstream.json` found no collision.

The repository's `literature/stacks-project/algebra.tex` is absent on this machine.
Read the primary source online instead: https://stacks.math.columbia.edu/tag/00NG
and https://stacks.math.columbia.edu/tag/00NE. Tag 00NG states the exact displayed
resolution with finite free terms and maximal Cohen–Macaulay kernel; 00NE supplies
the dimension-shifting input. No statement correction or disputed statement was needed.
The declaration docstring carries all seven steps of the node's natural-language proof.

Validation: the server single-file compile succeeded cleanly (1.5 seconds, no errors
or warnings). The bound proof for the repeated kernel index initially caused a Lean
elaboration error; binding `K := S.obj' 1` once resolved it without changing the statement.
The required `deliver2.py --no-push` dry run is the final mechanical check. No second
reading is authored by this worker and nothing is pushed.


## Second reading by J1

Independent reading of the sandbox node, its seven proof steps, the Lean module,
and all six statement-dependency nodes and their recorded declarations. Verdict:
the Lean says exactly what this node says. No mismatch was found; the Lean and node
are retained unchanged. This reading adds this report section only.

Source reading: the repository has no local Stacks algebra.tex. I fetched the
primary Stacks algebra.tex into this item's scratchpad and read the Conventions,
Cohen–Macaulay rings section, lemma-mcm-resolution (00NG), lemma-dimension-shift
(00NE), definition-maximal-CM (00NF), definition-depth (00LI), lemma-bound-depth
(00LK), and lemma-depth-in-ses (00LX). I also opened the official rendered tags
[00NG](https://stacks.math.columbia.edu/tag/00NG),
[00NE](https://stacks.math.columbia.edu/tag/00NE),
[00NF](https://stacks.math.columbia.edu/tag/00NF), and
[00LI](https://stacks.math.columbia.edu/tag/00LI).
The conventions require commutative unital rings; the section adds no standing
field, characteristic, completeness, or regularity hypothesis. The node makes
explicit the nonzero input needed for finite depth and the displayed d-e length.
Its zero-kernel alternative is retained, as required by the node. No statement
correction is present or needed, and there are no new nodes or dependency modules.

Object/hypothesis/conclusion checklist, written from the node before matching:

1. A commutative Noetherian local ring (R, m): `{R : Type u} [CommRing R]
   [IsNoetherianRing R] [IsLocalRing R]`. PASS. I read IsNoetherianRing in
   Mathlib.RingTheory.Noetherian.Defs (IsNoetherian R R, equivalent to all ideals
   finitely generated), and IsLocalRing in Mathlib.RingTheory.LocalRing.Defs.
   Its Nontrivial R requirement matches having a unique maximal ideal, not an
   additional assumption. The implicit maximal ideal is the one used in depth.
2. Finite Krull dimension d: `(d : ℕ)` and
   `hdim : ringKrullDim R = (d : WithBot ℕ∞)`. PASS. The recorded ringKrullDim
   declaration in Mathlib.RingTheory.KrullDimension.Basic is Order.krullDim of
   PrimeSpectrum R; the coercion asserts finite dimension exactly d, not merely
   a bound and not infinity or negative infinity.
3. Cohen–Macaulay hypothesis depth(R) ≥ d: `hcm : (d : ℕ∞) ≤ depth (R := R) R`.
   PASS. I read both Ideal.depth and IsLocalRing.depth in Sheaf.RingTheory.Depth.
   The former is the regular-sequence-length supremum, with infinity when IM=M;
   the latter specializes to maximalIdeal R. Module.Finite R R is inferred, not
   an extra ring hypothesis. Under the node's Noetherian local finite-dimension
   hypotheses this inequality agrees with the source's Cohen–Macaulay condition.
4. Nonzero finite R-module M: `(M : Type v) [AddCommGroup M] [Module R M]
   [Module.Finite R M] [Nontrivial M]`. PASS. The recorded Module.Finite class in
   Mathlib.RingTheory.Finiteness.Defs requires FG of the top submodule, exactly
   finite generation; finite underlying cardinality is not assumed.
5. e is depth(M), finite, and e ≤ d: `∃ e : ℕ, depth (R := R) M = (e : ℕ∞) ∧
   e ≤ d ∧ ...`. PASS. The existential introduces e with its defining equality
   before the resolution; finiteness is concluded, not assumed.
6. An exact sequence of R-modules 0 → K → F_{d-e-1} → ... → F₀ → M → 0:
   `∃ S : ComposableArrows (ModuleCat.{max u v} R) (d - e + 3), S.Exact ∧ ...`.
   PASS. I read ComposableArrows (Fin (n+1) functors), obj', and Exact in
   Mathlib.CategoryTheory.ComposableArrows.Basic and
   Mathlib.Algebra.Homology.ExactSequence. With k=d-e, there are k+3 arrows and
   k+4 objects. Positions 0,1,2,...,k+1,k+2,k+3 are respectively
   0,K,F_{k-1},...,F₀,M,0. Exact extends IsComplex and asserts exactness of every
   consecutive short complex, exactly the dependency node's recorded finite
   specialization. I also read ShortComplex.exact_iff_image_eq_kernel in
   Mathlib.CategoryTheory.Abelian.Exact. ModuleCat carries precisely additive
   groups with R-module structures and linear maps, with its abelian instance.
7. Zero endpoints and the specified terminal module: `IsZero (S.obj' 0) ∧
   IsZero (S.obj' (d - e + 3)) ∧ Nonempty ((S.obj' (d - e + 2)) ≃ₗ[R] M)`.
   PASS. Zero objects are exactly zero modules up to isomorphism; transporting
   the incoming map through the linear equivalence gives the original M.
   No compatibility data are missing because the remaining map goes to zero.
8. Each of exactly k free terms is finite free of nonnegative finite rank:
   `∀ i : Fin (d - e), Module.Free R (S.obj' (i.val + 2) (by omega)) ∧
   Module.Finite R (S.obj' (i.val + 2) (by omega))`. PASS. I read Module.Free in
   Mathlib.LinearAlgebra.FreeModule.Basic: existence of a basis, not projectivity.
   Module.Finite.finite_basis and Free.ChooseBasisIndex.fintype show that finite
   free over this nontrivial ring means a finite basis, hence R^{⊕n} with n≥0.
   The index runs in reverse F-label order, without changing the sequence.
9. K is finite and either zero or maximal Cohen–Macaulay:
   `let K := S.obj' 1; ∃ hK : Module.Finite R K, letI := hK;
   Subsingleton K ∨ depth (R := R) K = (d : ℕ∞)`. PASS. Subsingleton expresses
   the zero module. The witness installs exactly the finiteness instance the
   recorded depth definition requires. There is no added Nontrivial K constraint.
10. Parenthetical e=d case: k=0, the free-term quantifier is over Fin 0 and
    S has objects 0,K,M,0. PASS. Exactness at K gives injectivity and at M gives
    surjectivity of K → M; together with the terminal linear equivalence this
    gives K ≅ M as the node requests. No separate isomorphism conjunct is needed.

Edge cases: d=0 forces e=0 and gives the four-object identity-length sequence;
e=0<d gives exactly d free terms. Fin 0 is allowed, as are empty bases and zero-rank
free modules. Zero K is explicitly covered; zero input M is excluded exactly as
in the node (its depth would be infinity). The zero ring is excluded by locality
and finite dimension, as in the node. Empty schemes/indexed geometric families
are not objects of this algebraic statement. Arbitrary characteristic is allowed.
Universes u and v are independent; max u v accommodates a lifted copy of M and
finite free modules over R. The cross-universe linear equivalence imposes no
smallness hypothesis. All variables and universe names are bound.

Independent searches, using different wording from the first writer (msearch.py
records the service results in searches.jsonl):

- LeanFinder: “syzygies over a local ring with full depth terminate a finite free
  exact sequence”: eight hits, including localized exactness, module length,
  regular-sequence exactness, and categorical projective/injective dimension.
  None asserts this depth-d terminating free resolution.
- Loogle: `"syzygies"`: four hits, Projective.syzygies and Injective.syzygies with
  their instances; these choose categorical projective/injective objects and do
  not assert the ring-theoretic depth and finite free conclusion here.
- LeanSearch: “finite free syzygy with depth equal to Krull dimension of a local
  ring”: service unavailable (Internal Server Error); no search verdict inferred.
- rg over Mathlib/RingTheory, WeilConjectures, and lean/Sheaf with
  `syzyg|[Mm]acaulay|[Aa]uslander|depth.*[Ff]ree|[Ff]ree.*depth`: source hits on
  regular local UFDs, projective dimension, and a graded polynomial resolution;
  project hit TwoVariableSyzygy.lean concerns polynomial-variable syzygies.
  None is this general Cohen–Macaulay depth resolution. Exact declaration-name
  search across Mathlib, both project/source trees, and dag/lean_names_upstream.json
  found no collision. The missing-statement verdict is independently confirmed.

H5–H9: no definitions are delivered, so no hollow data; the sole theorem body
is `by sorry`. Module and theorem docstrings name the source and blueprint id;
the theorem docstring follows all seven node proof steps: depth bound, regularity
on free modules, induction base, finite nonzero first kernel, depth increment,
splicing, and conclusion. Names, topic path, imports, and line widths agree with
the conventions. I checked lean.statement byte-for-byte against the theorem
signature before `:=`; they agree.

Validation: independent scompile.py single-file server compile succeeded cleanly
in 1.5 seconds, exit code 0, no warnings. The required delivery dry run and push
are performed after this report is appended. No Lean or mathematical-node change
was needed; the second-reading report is the only addition.
