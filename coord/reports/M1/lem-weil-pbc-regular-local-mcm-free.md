## Worker report

The module `Sheaf.RingTheory.RegularLocalMaximalCohenMacaulayFree` states
`IsRegularLocalRing.free_of_depth_eq_ringKrullDim`, with `sorry` as its only proof.
No definitions, new nodes, dependency replacements, or statement corrections are needed.

Hypothesis and conclusion correspondence:
- The commutative ring `(R, m)` is `R : Type u` with `[CommRing R]`.
  `[IsRegularLocalRing R]` supplies exactly localness, Noetherianity, and the
  maximal-ideal generator condition. Its distinguished ideal is `IsLocalRing.maximalIdeal R`;
  introducing another ideal and an equality would add no mathematical data.
- Krull dimension `d` is `(d : ℕ)` and
  `hdim : ringKrullDim R = (d : WithBot ℕ∞)`; the coercion records finite dimension.
- An R-module M is `(M : Type v) [AddCommGroup M] [Module R M]`.
  `[Module.Finite R M]` is precisely finite generation, not finiteness of its underlying set.
- Maximal Cohen–Macaulay means exactly
  `hdepth : IsLocalRing.depth (R := R) M = (d : ℕ∞)`.
  Equality, rather than only an inequality, preserves the node's explicit convention.
- Freeness is `Module.Free R M`. The finite-rank clause is also explicit:
  `∃ r : ℕ, Nonempty (M ≃ₗ[R] (Fin r →₀ R))`.
  Finitely supported functions on `Fin r` are exactly the direct sum of r copies of R;
  `ℕ` means the integer rank is nonnegative. Both clauses are equivalent under finiteness,
  and stating both loses and adds no cases.

Dependencies read in full and used:
- `def-weil-regular-scheme`: `Mathlib.RingTheory.RegularLocalRing.Defs`,
  `IsRegularLocalRing`; its class extends `IsLocalRing` and `IsNoetherianRing`
  with maximal ideal spanFinrank equal to ringKrullDim. Only the ring clause is needed.
- `def-weil-finitely-generated-module`: `Mathlib.RingTheory.Finiteness.Defs`,
  `Module.Finite` (imported through `Sheaf.RingTheory.Depth`), with `fg_top`.
- `def-weil-pbc-depth`: `Sheaf.RingTheory.Depth`, `IsLocalRing.depth` and `Ideal.depth`.
  These use the regular-sequence supremum and depth infinity when IM = M.
- `def-weil-pbc-free-module`: `Mathlib.LinearAlgebra.FreeModule.Basic`, `Module.Free`,
  asserting existence of a basis, including an empty basis.

Source checked: the local Stacks TeX is absent on this machine, so read
https://stacks.math.columbia.edu/tag/00NT and https://stacks.math.columbia.edu/tag/00NF.
00NT states freeness for maximal Cohen–Macaulay modules; 00NF specifies finite modules
with depth equal to ring dimension. The declaration docstring includes all seven
steps of the node's inductive proof and names their dependency nodes.

Edge cases checked before writing:
- d = 0: fields and finite vector spaces are admitted; the base case applies.
- M = 0: depth is infinity by the imported definition, so the finite-depth hypothesis
  fails, as in the node's proof. No additional Nontrivial M hypothesis was added.
- r = 0: `Fin 0 →₀ R` is the zero direct sum; the conclusion allows it.
- The zero ring is excluded by localness itself, in both source and Lean.
- Ring and module universes u and v are independent; the rank index `Fin r` does not
  restrict either universe. No characteristic assumption or positive-dimension assumption.

Searches for an existing statement (2026-10-11):
- `msearch.py ... leansearch "finite maximal Cohen Macaulay module regular local ring is free"`:
  unavailable (Internal Server Error), recorded as unavailable rather than no match.
- `msearch.py ... leanfinder "A finite module of depth equal to the dimension over a regular local ring is free"`:
  eight hits, including `Module.free_of_flat_of_isLocalRing`, freeness over PIDs,
  invariant basis number, and length of a free module. None has the depth hypothesis.
- `msearch.py ... loogle "IsRegularLocalRing, Module.Free"`: zero hits.
- `msearch.py ... grep "depth.*[Ff]ree|[Ff]ree.*depth|[Mm]aximal.*Cohen" RingTheory`:
  zero hits in pinned Mathlib.
- `rg` of `IsRegularLocalRing|IsLocalRing.depth|mcm|MCM|Cohen.Macaulay` in
  source `WeilConjectures` and project `lean/Sheaf/RingTheory`: regular-local
  projective-dimension results and related depth lemmas, no matching theorem.
- `rg` of the item id, `free_of_depth`, `free_of.*[Mm]aximal`, and `CohenMacaulay`
  in source `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  only the different `exists_finite_free_resolution_to_maximalCohenMacaulay` statement.
- Full-name check `free_of_depth_eq_dim|free_of_depth_eq_ringKrullDim` in pinned
  Mathlib, source `WeilConjectures`, project `lean/Sheaf`, and upstream-name index:
  no hits before writing.

No statement fault or dispute found. Compilation and delivery dry run are recorded below.

Validation: `scompile.py M1 lem-weil-pbc-regular-local-mcm-free` compiled the module
on the server in 1.5 seconds, exit code 0, with no errors or warnings.

## Second reading by M1

Independently read the sandbox node and module, all four statement-dependency
nodes and their declaration signatures, and the source Stacks algebra.tex fetched
read-only from https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex
(the repository has no local copy). Read `lemma-regular-mcm-free` (00NT), its proof,
`definition-maximal-CM` (00NF), and the opening of `section-regular`. Also checked
https://stacks.math.columbia.edu/tag/00NT and https://stacks.math.columbia.edu/tag/00NF.
The section adds no standing hypothesis beyond regular localness; 00NF explicitly
requires a finite module over a Noetherian local ring.

Object-by-object, hypothesis-by-hypothesis, and conclusion-by-conclusion list:
- A commutative regular local ring `(R, m)`: `(R : Type u) [CommRing R]
  [IsRegularLocalRing R]`. The recorded regular-scheme dependency lists
  `IsRegularLocalRing` among its declarations. Read its class in
  `Mathlib.RingTheory.RegularLocalRing.Defs`: it extends `IsLocalRing R` and
  `IsNoetherianRing R` and equates maximal-ideal spanFinrank with ringKrullDim.
  The ideal is the unique `IsLocalRing.maximalIdeal R`, so no independent choice
  of m is missing. Verdict: exact, no extra ring hypothesis.
- Dimension d: `(d : ℕ)` and `hdim : ringKrullDim R = (d : WithBot ℕ∞)`.
  Regular Noetherian local rings have finite nonnegative dimension, so this
  explicit dimension parameter omits no source case. Verdict: exact.
- An arbitrary R-module M: `(M : Type v) [AddCommGroup M] [Module R M]`.
  Verdict: exact; no universe identification is imposed.
- Finite generation: `[Module.Finite R M]`. Read its recorded class in
  `Mathlib.RingTheory.Finiteness.Defs`, whose field is `(⊤ : Submodule R M).FG`.
  Verdict: exact; this is not finiteness of the carrier.
- Maximal Cohen–Macaulay: `hdepth : IsLocalRing.depth (R := R) M = (d : ℕ∞)`.
  Read both definitions in `Sheaf.RingTheory.Depth`: local depth uses the
  maximal ideal; ideal depth is infinity when I • top = top, otherwise the
  supremum of lengths of M-regular lists in I. It is exactly the dependency
  node's convention. Verdict: exact equality, no additional nonzero hypothesis.
- M is free: `Module.Free R M`. Read the recorded class in
  `Mathlib.LinearAlgebra.FreeModule.Basic`: existence of a basis, including
  an empty basis. Verdict: exact, not projectivity or flatness substituted.
- Finite-rank isomorphism: `∃ r : ℕ, Nonempty (M ≃ₗ[R] (Fin r →₀ R))`.
  Fin r →₀ R is the direct sum of r copies of R; r is a nonnegative integer.
  The existential follows all ring/module/dimension hypotheses, as in the node.
  The explicit conjunction with freeness is redundant but neither strengthens
  nor weakens this isomorphism conclusion. Verdict: exact.

Edge cases: d = 0 is admitted, as are all characteristics. For M = 0, maximal
ideal • top = top, so depth is infinity and the finite-depth hypothesis fails,
exactly as the node's first proof step says. No Nontrivial M binder is added.
The rank r = 0 and the empty basis are permitted. `IsLocalRing` extends
`Nontrivial R`, agreeing with the source's exclusion of the zero ring.
The universes u and v are independent and explicitly bound; the finite index
Fin r imposes no carrier universe bound. Empty schemes and unrelated index
families are not objects of this ring/module statement.

Independent searches (2026-10-11), using wording different from the worker's:
- LeanFinder: "A finitely generated module over a regular local ring whose depth
  equals Krull dimension admits a finite basis": eight results, involving PID
  torsion-free bases, flatness, invariant basis number, and regular-sequence
  quotient dimension. No theorem with the node's hypotheses and conclusion.
- Loogle: `IsRegularLocalRing, Module.Free`: zero hits.
- LeanSearch: "finite module maximal depth regular local ring has basis":
  service unavailable (Internal Server Error); no negative verdict inferred.
- Independently ran rg with `cohen.?macaulay|free.*depth|depth.*free|
  regularlocalring.*free|free.*regularlocalring` over pinned Mathlib,
  source WeilConjectures, and project lean/Sheaf. Related depth/CM statements
  exist but none states this lemma. Opened the upstream
  `free_of_hasProjectiveDimensionLE_of_annihilator`: it assumes an annihilator
  of the maximal ideal and finite projective dimension, not maximal depth over
  a regular local ring. The project's `exists_finite_free_resolution_to_maximalCohenMacaulay`
  concerns resolutions, not freeness of the maximal-CM module.
- Searched the upstream name index and source for `IsRegularLocalRing`, the item
  id, and `free_of_depth_eq_ringKrullDim`; no existing matching declaration.

No mismatches found; no Lean or node changes were needed. No new definition
nodes, dependency modules, or statement corrections occur in this delivery.
There is no hollow definition, no private CM predicate, and no proof beyond the
single named theorem's `sorry`. The module and theorem docstrings cite the source
and blueprint id; all seven proof steps correspond to the node's split, including
support dimension, quotient depth comparison, and finite basis. Imports serve
regular localness, freeness, and the recorded depth definition. All variables and
universes are bound, and the node's lean.statement is verbatim the file signature.

Second-reader validation: scompile.py M1 lem-weil-pbc-regular-local-mcm-free
lean/Sheaf/RingTheory/RegularLocalMaximalCohenMacaulayFree.lean compiled on the
server in 1.6 seconds, exit code 0, with no errors or warnings.
