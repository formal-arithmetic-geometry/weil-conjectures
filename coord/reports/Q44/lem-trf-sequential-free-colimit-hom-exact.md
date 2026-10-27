## Worker report

The delivery states `Module.sequential_free_colimit_hom_exact` in
`Sheaf.RingTheory.SequentialFreeColimitHomExact`. Its only postponed proof is the
main theorem. `Module.sequentialHomSystem` is a fully defined helper: the inverse
system of linear Hom modules with precomposition transitions. The compatible-family
module is Mathlib's existing `ModuleCat.sectionsSubmodule` of this system; it is
not defined again. No node statement, dependencies, or proof steps were changed.
No new nodes or dependency repairs are needed.

Sources read: `literature/stacks-project/algebra.tex`, Tag 059X,
`lemma-countgen-projective`, lines 22193–22230 (finite-free Hom rows, ML limit
exactness, and the functorial Hom-colimit identification); and Tag 0598,
`lemma-ML-exact-sequence`, lines 20770–20815. I also read the current blueprint's
`latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`
and its proof. As the accepted split records, this item is historical algebraic
support, while that current locality proof quotes Varshavsky directly. This
statement delivery preserves the assigned algebraic support and the unit route.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| R is a commutative ring | `{R : Type u} [CommRing R]` |
| Modules G_n and adjacent R-linear maps u_n for positive n | `F : ℕ ⥤ ModuleCat.{v} R`; `F.obj n` represents G_(n+1), and `(F.map (homOfLE (Nat.le_succ n))).hom` represents u_(n+1). A functor records exactly the composites supplied by a sequence. |
| Each G_n is finite free, including rank zero | `hfree : ∀ n : ℕ, ∃ r : ℕ, Nonempty (F.obj n ≃ₗ[R] (Fin r → R))` |
| Compatible maps iota_n into P | `c : Cocone F`, with `P = c.pt` and `iota_(n+1) = (c.ι.app n).hom`; cocone naturality is the stipulated compatibility. |
| These maps exhibit P as their colimit | `hc : IsColimit c`, using the recorded category-colimit dependency, rather than assuming a chosen standard direct limit. |
| L_N consists of compatible Hom families with componentwise operations | `ModuleCat.sectionsSubmodule (sequentialHomSystem F N)`. Sections commute with every transition; commuting with adjacent transitions is equivalent by induction. The inherited submodule operations are componentwise. |
| Restriction is an R-linear isomorphism rho_N | `∃ ρ : (N : ModuleCat.{w} R) → (c.pt →ₗ[R] N) ≃ₗ[R] ModuleCat.sectionsSubmodule (sequentialHomSystem F N)` |
| Its value is `(h iota_n)_n` | First conjunct under the existential: `(ρ N h).val (Opposite.op n) = h.comp (c.ι.app n).hom` for every N, h, and n. This uniquely specifies the canonical map; the equivalence is not an arbitrary isomorphism. |
| The isomorphisms are natural for every v : N → N' | Second conjunct under the same existential: `(ρ N' (a.comp h)).val (Opposite.op n) = a.comp ((ρ N h).val (Opposite.op n))` for all N, N', a, h, and n. Together with the restriction formula this is exactly `(v h iota_n)_n`. |
| A short exact sequence N1 → N2 → N3 | The last universal quantifier binds each module and both R-linear maps; assumptions are `Function.Injective a`, `Function.Exact a b`, and `Function.Surjective b`. `Function.Exact` means image equals the zero kernel. |
| The inverse Hom system of N1 is ML | `(sequentialHomSystem F N₁ ⋙ forget (ModuleCat R)).IsMittagLeffler`, exactly the recorded definition on the underlying-set system. Equal ranges of linear maps are equivalently equal images as subgroups. |
| Hom(P,-) is short exact with the stated postcomposition maps | The conclusion is `Function.Injective (fun h ↦ a.comp h) ∧ Function.Exact (fun h ↦ a.comp h) (fun h ↦ b.comp h) ∧ Function.Surjective (fun h ↦ b.comp h)`, with domains explicitly typed. |

The exact-sequence coefficient modules have separate universes `w₁`, `w₂`, and
`w₃`. The natural restriction family is stated for every module in arbitrary
universe `w`; two objects and their naturality map can always be read in a common
universe. Ring, diagram, and coefficient universes are not equated. There are no
implicit variables, local notations, local instances, or private definitions.

Dependencies read and used:

- `def-weil-pbc-category-colimit`: public import
  `Mathlib.CategoryTheory.Limits.HasLimits`; read its chosen `colimit` and the
  full `Cocone` and `IsColimit` definitions in `Limits.Cones` and `Limits.IsLimit`.
  The theorem uses `Cocone` and `IsColimit`, the precise interface for the given
  maps rather than a different chosen colimit object.
- `def-weil-pbc-mittag-leffler-system`: public import
  `Mathlib.CategoryTheory.CofilteredSystem`; read the signature and docstring of
  `CategoryTheory.Functor.IsMittagLeffler` (lines 132–138). This is applied to the
  underlying-set inverse Hom diagram, as its node record directs.
- Proof dependency `lem-weil-pbc-mittag-leffler-limit-exact`: plain import
  `WeilConjectures.CategoryTheory.MittagLefflerLimitExact`; read the full signature
  and proof docstring of
  `CategoryTheory.ShortComplex.mittagLeffler_quotient_and_limit_exact`.
  Its second conjunct supplies exactness of limits with an ML kernel system.
- Existing Mathlib constructions: `Functor.ofOpSequence` in
  `Mathlib.CategoryTheory.Functor.OfSequence`, `LinearMap.lcomp` in
  `Mathlib.LinearAlgebra.BilinearMap`, `ModuleCat.sectionsSubmodule` in
  `Mathlib.Algebra.Category.ModuleCat.Limits`, and `Function.Exact` in
  `Mathlib.Algebra.Exact.Basic`. Their source definitions were read.

Edge cases checked before finalizing:

- Reindexing n >= 1 by Lean n : ℕ preserves the first term and every transition;
  the indexing category is nonempty and no extra zero-indexed source term is added.
- Rank r = 0 is allowed: `Fin 0 → R` is the zero module; all-zero stages and P = 0
  are included. There is no positive-rank, nonzero-ring, or nontriviality assumption.
- Arbitrary, including zero, transition maps are allowed; none is assumed injective
  or surjective. A zero-transition inverse Hom system is ML with stable zero image.
- A zero coefficient module, N1 = 0 or N3 = 0, and a split short exact sequence
  retain their ordinary meanings. The ML hypothesis is imposed on N1 only.
- No flatness, tensor Mittag-Leffler condition, countable generation hypothesis on P,
  or projectivity assumption was added. Finite freeness concerns the stages only.

Searches actually run through `msearch.py` (Q44, this item):

- LeanFinder: `Hom from a sequential colimit of finite free modules is exact when the inverse Hom kernel system is Mittag Leffler`.
  Eight hits, including `Profinite.NobelingProof.succ_exact`, the AB5/AB4* module
  instances and `AdicCompletion.map_exact`; none states this result.
- Loogle: `CategoryTheory.Functor.IsMittagLeffler`.
  Ten hits defining ML and its stable-range properties. The existing definition
  is reused, but none is the conditional Hom exactness theorem.
- Mathlib grep: `Mittag|mittag|[Hh]om.*colimit`, subdirectory `CategoryTheory`.
  Twenty-five displayed hits include `CofilteredSystem` and assorted colimit
  universal-property uses; no full match.
- LeanSearch: `Hom from a colimit is naturally isomorphic to compatible families and is exact when the inverse Hom kernel system is Mittag Leffler`.
  Eight hits include `IsColimit.natIso`, `IsColimit.homIso'`, and `colimit.homIso'`.
  These provide the set-valued universal-property identification, not the complete
  linear and ML exactness statement. No existing record can replace this item.
- Direct `rg` in live `lean/WeilConjectures` and `lean/Sheaf` for sequential Hom,
  Hom colimits, and the Stacks label found the countably generated projectivity
  consumer and unrelated derived Hom/telescope modules, not this statement.
  Direct search for the exact item id in `lean/WeilConjectures` returned no match.
- Direct Mathlib grep for `sectionsSubmodule` found the existing compatible-section
  submodule in `ModuleCat.Limits`; this was reused in the final signature. Searches
  for `sequentialHomSystem` and `sequential_free_colimit_hom_exact` in Mathlib,
  both project source trees, and `dag/lean_names_upstream.json` returned no matches.

Validation: `scompile.py Q44 lem-trf-sequential-free-colimit-hom-exact` compiled the
final module both as a sandbox file and under its actual module name, with no
errors and no warnings. A first draft using a kernel-intersection presentation was
replaced by the existing compatible-sections submodule. The deprecated umbrella
`Mathlib.Algebra.Exact` import was replaced by `Mathlib.Algebra.Exact.Basic`.
No statement fault or unresolved dispute was found.

## Second reading by Q44

This is a separate second pass by the assigned worker; the dispatch brief forbids
starting other agents, and the maintainer supplies the independent review.

I reread the node and final file side by side. `hfree` gives the exact finite-free
hypothesis (zero rank included); `c` retains the given compatible maps and `hc`
retains their universal property. The Hom diagram's transition is precomposition,
not postcomposition or a tensor map, and `sectionsSubmodule` has the stipulated
componentwise module structure. The first rho formula forces restriction by these
same coprojections. The second formula expresses naturality for that same family,
not existence of unrelated isomorphisms. The final implication assumes all three
short-exact clauses and ML of the kernel Hom system only, then concludes precisely
the three Hom short-exact clauses with the correct maps and coefficient modules.
All five natural-language proof steps appear in the theorem docstring. The node
copy changes only `lean`, whose signature was extracted verbatim from the final
file. The helper definition belongs to the explicit inverse Hom system in this
node and contains no postponed data or proof. No further mismatch was found.
