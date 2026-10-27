## Worker report

The module `Sheaf.RingTheory.SimultaneousResidueBases` states
`IsLocalRing.exists_simultaneous_residue_bases`, with its sole proof `sorry`.
The node's statement, dependencies, proof and other pre-existing fields are unchanged;
only its `lean` record is added. No new nodes or dependency repairs are needed.

Hypotheses and conclusion, clause by clause:

- The nonzero commutative local ring `(D, m)` is `(D : Type u) [CommRing D]
  [IsLocalRing D]`. Mathlib's `IsLocalRing` extends `Nontrivial D`; for a
  commutative ring it means precisely that there is a unique maximal ideal.
  This ideal is `IsLocalRing.maximalIdeal D`, so no additional choice of ideal
  or maximality hypothesis is required.
- The specified field `k = D/m` is Mathlib's actual quotient
  `IsLocalRing.ResidueField D`; `[Infinite (ResidueField D)]` is exactly its
  infinitude. `IsLocalRing.residue D` is the quotient ring homomorphism.
  The definitions were read in `Mathlib.RingTheory.LocalRing.ResidueField.Defs`.
- The arbitrary `D`-module `Q` is `(Q : Type v) [AddCommGroup Q] [Module D Q]`.
  There is no finiteness, freeness, nonzero or residue-field-module assumption on Q.
- The finite, possibly empty index set is `(I : Type w) [Finite I]`.
  `(r : ℕ)` is exactly the nonnegative integer rank; it may be zero.
- The possibly different target fields are `(K : I → Type x) [∀ i, Field (K i)]`.
  The embeddings are `(ι : ∀ i, ResidueField D →+* K i)`.
  Every unital ring homomorphism out of a field is injective, so this expresses
  embeddings without adding a redundant injectivity hypothesis. The extensions
  are not required to be finite or algebraic.
- The target vector spaces are `(F : I → Type z) [∀ i, AddCommGroup (F i)]
  [∀ i, Module (K i) (F i)]`. The dimension-r hypothesis is precisely
  `[∀ i, Module.Finite (K i) (F i)]` together with
  `(hdim : ∀ i, Module.finrank (K i) (F i) = r)`. Over a field `Module.Finite`
  means finite-dimensional. It is necessary to include this, since Mathlib's
  `finrank` is also zero for infinite-dimensional spaces. These are exactly
  the node's finite dimension assumptions, including the rank-zero case.
- Each specified D-linear map, where D acts through the quotient and embedding,
  is `(ρ : ∀ i, Q →ₛₗ[(ι i).comp (residue D)] F i)`.
  By the definition of `LinearMap σ`, this says additivity and
  `ρ i (d • q) = (ι i (residue D d)) • ρ i q`. This is precisely D-linearity
  for the required induced D-action. Using semilinearity records that canonical
  action directly, without a separate arbitrary D-module structure on F.
- The image-spanning condition is
  `(hspan : ∀ i, Submodule.span (K i) (Set.range (ρ i)) = ⊤)`.
  No surjectivity of ρ as a set map is imposed.
- The conclusion is `∃ y : Fin r → Q, ∀ i, ∃ b : Module.Basis (Fin r) (K i) (F i),
  ∀ j, b j = ρ i (y j)`. Thus a single r-tuple in Q gives a basis in every
  target. `Module.Basis` expresses linear independence and spanning; the
  equalities identify its actual vectors, rather than asserting merely that
  each target has some unrelated basis. Fin r is just the zero-based indexing
  of the node's y_1,...,y_r.

Dependency declarations and imports:

- Statement dependency `def-weil-vector-space-dimension` uses its recorded
  `Module.finrank` in `Mathlib.LinearAlgebra.Dimension.Finrank` (public import).
  I read the full declaration and docstring in the pinned Mathlib source.
- Proof dependency `lem-pc-finite-linear-avoidance` is the Mathlib leaf
  `Subspace.biUnion_ne_univ_of_top_notMem` in `Mathlib.GroupTheory.CosetCover`.
  Its signature and docstring allow an infinite division ring, an arbitrary
  vector space and a finite set of subspaces not containing top. It is
  imported as a proof dependency only.
- Proof dependency `lem-weil-independent-family-card-le-dimension` is the
  Mathlib leaf `LinearIndependent.fintype_card_le_finrank` in
  `Mathlib.LinearAlgebra.Dimension.Finite`. I read its complete signature:
  module finiteness, a finite index type and independence imply the cardinal
  bound. It is imported as a proof dependency only.
- The public imports `Mathlib.Algebra.Module.LinearMap.Defs` and
  `Mathlib.RingTheory.LocalRing.ResidueField.Defs` supply the actual semilinear
  maps and quotient residue field used in the signature. No private copies.

Source and proof docstring: read `literature/stacks-project/algebra.tex`,
Tag 03C1, `lemma-semi-local-module-basis-in-submodule`, including its proof.
The node isolates its simultaneous finite-target coefficient-avoidance
argument. The declaration docstring reproduces every step of the node's
accepted proof: empty targets; induction on the independent tuple; proper
spans and witnesses; proper inverse-image subspaces of k^I; finite linear
avoidance; lifting coefficients to D; the relation argument for independence;
and the dimension bound giving spanning, also at rank zero.

Edge cases checked before writing:

- I empty: the conclusion allows the zero r-tuple; the basis conditions and
  all target assumptions are vacuous. There is no `Nonempty I` requirement.
- r = 0: finiteness and finrank zero force each target to be the zero space;
  `Fin 0 → Q` gives the empty family and `Module.Basis (Fin 0)` its empty basis.
- Q = 0: if a target exists, its image-spanning condition forces F_i = 0 and
  hence r = 0. If I is empty, Q = 0 works for any r.
- Repeated targets and maps are permitted. No distinctness is assumed.
- Infinite-degree field extensions, different target fields, and independent
  universes for D, Q, I, K and F are permitted. No field extension degree
  or universe equality is assumed.
- The infinite-residue-field assumption is substantive: over F_2 the three
  nonzero functionals on F_2^2 have no common nonvanishing vector, giving
  spanning one-dimensional targets with no simultaneous basis vector.

Searches for existing statements (actual logged results are in sandbox searches.jsonl):

- `msearch.py leanfinder`: "Choose elements of a module whose images form bases
  simultaneously in finitely many vector spaces over field extensions of an
  infinite residue field". Eight hits, including
  `Module.exists_basis_of_basis_baseChange`, `Module.Basis.ofIsCoprimeDifferentIdeal`,
  `Module.nonempty_basis_of_flat_of_finrank_eq`, and
  `LinearMap.exists_basis_basis_of_span_eq_top_of_mem_algebraMap`. None is this
  simultaneous selection theorem: the local-ring results require finiteness
  and concern a single base change; the different-ideal construction assumes
  additional disjointness; the pairing result assumes a perfect pairing.
- `msearch.py loogle`: `Module.Basis, Infinite`. Twelve hits concern cardinality
  comparisons of infinite bases and class groups, not simultaneous finite bases.
- `msearch.py grep`: `simultaneous.*bas|exists_basis_of_span|exists_basis_of_basis_baseChange`
  under `RingTheory/LocalRing`. Five hits, all single-base-change/module-basis
  lifting results in `Mathlib/RingTheory/LocalRing/Module.lean`, not a match.
- `msearch.py leansearch`: "A module over a local ring with infinite residue
  field admits a tuple whose images are bases in each of finitely many spanning
  field targets". Eight hits, again local-ring basis lifting, a quotient basis,
  `basisOfTopLeSpanOfCardEqFinrank`, and a localization basis. No exact match.
- Project `rg`: `simultaneous.*[Bb]as|exists.*[Bb]as.*residue` in both
  `lean/WeilConjectures` and `lean/Sheaf`. No matching theorem; the only
  residue-basis spreading hit concerns localization from a prescribed basis.
  Searching the item id in `lean/WeilConjectures` found nothing.
- Declaration-name search `simultaneous_residue_bases|exists_simultaneous_residue_bases`
  in Mathlib, `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  found no pre-existing declaration.

Validation: prescribed `scompile.py Q77 lem-a1-simultaneous-residue-bases`
compiled both its sandbox probe and its library module cleanly (each 1.0 s),
with no errors or warnings. The file starts with `module`, exposes its public
section, disables autoImplicit, and explicitly binds all five universes and
all variables. The only postponed theorem is the item itself. No statement
fault or STATEMENT-DISPUTED issue was found.

## Second reading by Q77

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
