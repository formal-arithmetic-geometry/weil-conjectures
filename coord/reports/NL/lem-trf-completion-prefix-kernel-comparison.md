## Worker report

The module `Sheaf.RingTheory.CompletionPrefixKernelComparison` states
`AdicCompletion.completionPrefixKernelComparison`, with its entire proof postponed by
`sorry`. Three real helper definitions expose the prefix multiplication endomorphism,
the canonical completed quotient equivalence, and the multiplication endomorphism on
the extended quotient. These are constructions belonging to this node, not independent
new notions; all four declarations are listed in `lean.declarations`. No other node or
statement has been changed.

Hypotheses and objects, clause by clause:

- A commutative Noetherian local ring is `{R : Type u} [CommRing R]
  [IsNoetherianRing R] [IsLocalRing R]`. The universe `u` is explicitly declared.
- The maximal ideal is `IsLocalRing.maximalIdeal R`; the ring `S` is exactly
  `AdicCompletion (IsLocalRing.maximalIdeal R) R`; its canonical map `c` is
  `algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)`.
  Mathlib's compatible sequences include level zero, which is the zero quotient;
  this adds no data to the inverse limit over positive powers.
- An arbitrary finite sequence is `fs : List R`, of length `t = fs.length`.
  `hfs : ∀ f ∈ fs, f ∈ IsLocalRing.maximalIdeal R` expresses exactly that all
  its entries lie in the maximal ideal. There is no positive-length assumption.
- For `i : Fin fs.length`, `Ideal.ofList (fs.take i)` is `P_i`, the quotient
  `R ⧸ Ideal.ofList (fs.take i)` is `M_i`, and `prefixMultiplication fs i` is
  `LinearMap.lsmul R _ fs[i]`. Its kernel is the actual submodule
  `(prefixMultiplication fs i).ker`, namely `K_i`. Mathlib's zero-based entry
  `fs[i]` is the mathematical `f_{i+1}`.
- For every module used here, its completion is Mathlib `AdicCompletion m N`.
  The completed inclusion is exactly `AdicCompletion.map m
  (prefixMultiplication fs i).ker.subtype`, not an arbitrary map or an existence
  assumption.
- `prefixQuotientEquiv R fs i` has source `AdicCompletion m M_i` and target
  `S ⧸ P_i.map (algebraMap R S)`. It is an `S`-linear equivalence, constructed as
  the inverse of Mathlib's `ofTensorProductEquivOfFiniteNoetherian`, followed by
  the inverse of `Algebra.TensorProduct.quotIdealMapEquivTensorQuot` on linear
  equivalences. Thus it is the specified canonical map `s ⊗ r̄ ↦ s c(r)`;
  the construction chooses no arbitrary quotient isomorphism. The use of inverse
  equivalences is justified by the existing finite-module comparison, which
  determines its inverse uniquely. There is no definition with postponed data.
- `completedPrefixMultiplication fs i` is `LinearMap.lsmul S _ (c fs[i])` on
  `S/P_iS`, using the standard quotient `S`-module structure. This is multiplication
  by `c(f_{i+1})` on that quotient.
- The first conjunct for each `i` is `Function.Injective` of the completed
  inclusion. The next conjunct equates the `LinearMap.range` of that inclusion
  followed by `prefixQuotientEquiv` with the kernel of
  `completedPrefixMultiplication`. Together they say that the actual completed
  inclusion identifies `K_i`'s completion with exactly that kernel.
- The third conjunct is the equality of `S`-linear maps
  `e.toLinearMap.comp (map m (prefixMultiplication fs i)) =
  (completedPrefixMultiplication fs i).comp e.toLinearMap`.
  This states the completed-multiplication compatibility under the same canonical
  equivalence, including all elements of the completed quotient.
- The fourth conjunct is `Subsingleton (AdicCompletion m K_i) ↔ Subsingleton K_i`.
  A module is zero precisely when its underlying additive group is a singleton;
  this encodes both directions of the requested zero-kernel reflection.
- The final conjunct is exactly `RingTheory.Sequence.IsRegular R fs ↔
  RingTheory.Sequence.IsRegular S (fs.map (algebraMap R S))`. This uses the
  dependency's full regularity predicate, including the nonzero final quotient,
  rather than only weak regularity.

Dependency declarations were read in full in the pinned Mathlib sources:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` and `isNoetherianRing_iff_ideal_fg`. The former is publicly
  available through the public completion tensor comparison import.
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `AdicCompletion` and `IsAdicComplete`; its ring/algebra structure is in
  `Mathlib.RingTheory.AdicCompletion.Algebra`. The canonical completed linear map
  `AdicCompletion.map` is in `Functoriality`. These are publicly available through
  `Mathlib.RingTheory.AdicCompletion.AsTensorProduct`.
- `def-weil-pbc-regular-sequence`: public import
  `Mathlib.RingTheory.Regular.RegularSequence`, `RingTheory.Sequence.IsRegular`.
  Its parent `IsWeaklyRegular` explicitly tests each prefix quotient, while
  `top_ne_smul` asserts the nonzero final quotient.
- `lem-weil-pbc-completion-finite-module-tensor`: public import
  `Mathlib.RingTheory.AdicCompletion.AsTensorProduct`,
  `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`, its underlying map
  `ofTensorProduct`, `ofTensorProduct_tmul`, and `ofTensorProduct_naturality`.
  This is used in the actual helper construction as well as the proof plan.
- The quotient specialization uses public import
  `Mathlib.RingTheory.TensorProduct.Quotient`,
  `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`, whose inverse on pure tensors
  is specified by `quotIdealMapEquivTensorQuot_symm_tmul`.
- `lem-weil-pbc-noetherian-submodule-finite`: proof import
  `Mathlib.RingTheory.Noetherian.Basic`, `Submodule.FG.of_le`.
- `lem-weil-pbc-completion-exact-finite-modules`:
  `Mathlib.RingTheory.AdicCompletion.Exactness`, `AdicCompletion.map_injective`,
  `map_exact`, and `map_surjective`, already publicly imported by
  `AsTensorProduct` (no redundant second import).
- `lem-weil-pbc-module-completion-complete`: proof import
  `Mathlib.RingTheory.AdicCompletion.Completeness`, `AdicCompletion.isAdicComplete`
  and `pow_smul_top_eq_ker_eval`; `eval_surjective` is in `Basic`.
- `lem-weil-pbc-nakayama-jacobson`: proof import `Mathlib.RingTheory.Nakayama`,
  `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`.
- `lem-weil-pbc-local-completion-local-ring`: proof import
  `Mathlib.RingTheory.AdicCompletion.LocalRing`, its local-ring instance,
  `maximalIdeal_eq_map` and `mem_maximalIdeal_iff_eval_one_eq_zero`.

The source read was `literature/stacks-project/algebra.tex`, the actual statements
and proofs at `lemma-completion-tensor` (00MA), `lemma-completion-flat` (00MB),
`lemma-hathat-finitely-generated` (05GG), and `lemma-NAK` (00DV).
The current blueprint ancestor proof
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md`
was also read: its locality argument is now by contracting correspondences; this
auxiliary algebra comparison remains exactly the accepted DAG node's statement.
No source-based correction was needed.

Edge cases checked mathematically before writing:

- `fs=[]`: the `Fin 0` assertion is vacuous, but the regularity equivalence is
  still present. Both empty sequences are regular because local rings and their
  maximal-ideal completions are nonzero. No length restriction excludes this case.
- `i=0`: the prefix ideal is zero, giving multiplication on `R` and on `S`.
- A zero next entry: its kernel is the entire prefix quotient; completing its
  inclusion gives the entire kernel of zero multiplication on the completed
  quotient. No regularity is assumed to obtain the kernel assertion.
- Nonregular lists and zero kernels are permitted; injectivity is concluded only
  for the completed submodule inclusion, not for multiplication itself.
- A field has maximal ideal zero; completion is the field itself, and the formula
  still covers lists of zeros and the empty list.
- The prefix ideal lies in the maximal ideal, so no final quotient is silently
  allowed to be zero. The regularity predicate explicitly retains that condition.

Searches actually run:

- `msearch.py leanfinder`: query "Completed prefix multiplication kernels and
  reflection of regular sequences under completion of a Noetherian local ring".
  Eight hits, including `IsWeaklyRegular.regular_mod_prev`, the local
  weak-regularity criterion, and cons/append criteria. None includes the completed
  inclusion and its canonical quotient comparison.
- `msearch.py loogle`: query `AdicCompletion, RingTheory.Sequence.IsRegular`.
  Successful search, zero hits.
- `msearch.py grep`, subdirectory `RingTheory`: query
  `completion.*[Kk]ernel|[Kk]ernel.*completion|isRegular.*[Aa]dic|[Aa]dic.*isRegular`.
  Three hits: the completion kernel evaluation documentation, exactness
  construction documentation, and an unrelated perfectoid comment. No exact match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`: query
  `completionPrefixKernel|prefix.*[Kk]ernel|isRegular.*[Aa]dic|[Aa]dic.*isRegular`.
  Results concern regular ring maps, other prefix arguments, or kernel tests for
  regular quotients; no declaration states every clause here. In particular,
  `CompletedBaseRegularity.isRegular_iff_comp_adicCompletion` concerns regular
  ring maps, not a regular sequence or its prefix kernels.
- `grep -rn` of this item's exact id in `lean/WeilConjectures`: zero matches.
- `rg` of all three proposed helper names and the theorem name in Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no matches.
  The existing canonical tensor quotient equivalence was found and read instead
  of constructing another tensor quotient notion.

Validation: `scompile.py NL lem-trf-completion-prefix-kernel-comparison` compiled the
single delivered file as both its sandbox module and its library module, cleanly
(3.1 and 4.5 seconds). The initial compile required marking the completed
multiplication definition `noncomputable` because Mathlib's completion ring
structure is noncomputable; that annotation was added and the clean compile rerun.
All variables and universes are explicitly bound. The sole postponed theorem is
`AdicCompletion.completionPrefixKernelComparison`; its docstring carries all five
steps of the DAG proof, and the helper definitions contain real data.

No statement dispute, dependency repair, or new node is required.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
