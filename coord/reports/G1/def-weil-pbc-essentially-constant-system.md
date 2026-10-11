## Worker report

The module defines `CategoryTheory.Functor.IsEssentiallyConstant` for an inverse system
`F : ℕᵒᵖ ⥤ AddCommGrpCat.{u}`. The natural numbers reindex the positive integers by
`n ↦ n + 1`. A witness `X` is the value of the essentially constant system.

The node's hypotheses and clauses are rendered as follows:

- Inverse system of abelian groups: `F : ℕᵒᵖ ⥤ AddCommGrpCat.{u}`. Functoriality supplies
  identity and composite transition homomorphisms.
- Value and maps to the system: `∃ (X : AddCommGrpCat.{u}) (π : ∀ n : ℕ, X ⟶
  F.obj (Opposite.op n))`.
- Compatibility with the successor transition: `∀ n : ℕ, π (n + 1) ≫
  F.map (homOfLE (Nat.le_add_right n 1)).op = π n`. These equalities imply compatibility
  with every composite transition.
- Chosen positive index and retraction: `∃ (i₀ : ℕ) (r : F.obj (Opposite.op i₀) ⟶ X)`.
- Clause (a): `π i₀ ≫ r = 𝟙 X`.
- Clause (b): `∀ j : ℕ, ∃ k : ℕ, ∃ (hik : i₀ ≤ k) (hjk : j ≤ k),
  F.map (homOfLE hjk).op = F.map (homOfLE hik).op ≫ r ≫ π j`.

The dependency `def-weil-inverse-system` is the Mathlib leaf
`CategoryTheory.Functor.ofOpSequence` and `CategoryTheory.NatTrans.ofOpSequence` in
`Mathlib.CategoryTheory.Functor.OfSequence`. Its functor representation is used directly;
`F.map` provides the recorded composite transition maps. The source is Stacks Project,
Categories, Definitions 4.22.1(2) (Tag 05PU) and 4.22.2 (Tag 05PV). The local
`literature/stacks-project/categories.tex` was unavailable, so the tagged source pages
were read at `https://stacks.math.columbia.edu/tag/05PU` and `/tag/05PV`.

Edge cases: `n = 0` denotes the first positive index; `i₀`, `j`, and `k` may all be zero.
The zero abelian group can be the value `X`. The definition allows non-isomorphic
transition maps, including a tower with all successor maps zero. There is no empty
index set because the source's positive-integer index is nonempty. The universe `u`
is explicit and unrestricted.

Searches: `msearch.py leanfinder` for an essentially constant abelian-group inverse
system with retraction and eventual factorization returned `InverseSystem.*` limit and
equivalence declarations, none matching; `msearch.py loogle` for
`IsEssentiallyConstant, EssentiallyConstant, IsEventuallyConstant` found no matching
declaration; `msearch.py grep` for essentially/eventually constant names in
`CategoryTheory` found only the stronger eventually-isomorphic condition.
`rg` over the source `WeilConjectures` found only uses of `IsEventuallyConstant`,
and `grep -rn` for this node id there found nothing. `rg` over the repository's
`lean/Sheaf` found no matching declaration. Mathlib source grep found no exact notion.

The server compile via `scompile.py` exited 0 with no messages.

## Second reading by G1

I read the node, `def-weil-inverse-system`, the Lean file, and Stacks Categories
Definitions 4.22.1(2) (Tag 05PU) and 4.22.2 (Tag 05PV). The local
`literature/stacks-project/categories.tex` is absent, so I checked the source at
`https://stacks.math.columbia.edu/tag/05PU` and `/tag/05PV`. The source assumes a
cofiltered index category and a cone; the positive-integer tower has a cofiltered
opposite index category, and the cone is explicitly quantified below. It imposes no
Noetherian, finiteness, field, or characteristic hypothesis.

- Inverse system of abelian groups: `F : ℕᵒᵖ ⥤ AddCommGrpCat.{u}`. The dependency
  `def-weil-inverse-system` identifies a positive-integer tower with this functor,
  reindexed by `n ↦ n + 1`; `Functor.ofOpSequence` constructs precisely such functors.
  `F.map` supplies the composite transition maps and identity maps. Exact match.
- Value `X`: `∃ (X : AddCommGrpCat.{u})`. This is an arbitrary abelian group in the
  same universe as the tower, as the node requires. Exact match.
- Cone maps: `π : ∀ n : ℕ, X ⟶ F.obj (Opposite.op n)`. They are group homomorphisms;
  the successor equation `∀ n, π (n + 1) ≫ F.map
  (homOfLE (Nat.le_add_right n 1)).op = π n` makes them compatible with every
  transition by functoriality and induction. Exact match.
- Chosen index and retraction: `∃ (i₀ : ℕ) (r : F.obj (Opposite.op i₀) ⟶ X)`.
  Natural index `i₀` represents positive index `i₀ + 1`. Exact match.
- Clause (a): `π i₀ ≫ r = 𝟙 X`, which is `r ∘ π_i₀ = id_X`. Exact match.
- Clause (b): `∀ j : ℕ, ∃ k : ℕ, ∃ (hik : i₀ ≤ k) (hjk : j ≤ k),
  F.map (homOfLE hjk).op = F.map (homOfLE hik).op ≫ r ≫ π j`.
  Both inequalities encode `k ≥ max(i₀,j)`; the equality has domain `B_k` and
  codomain `B_j`, and is exactly the source's factorization. The quantifiers have
  the node's order. Exact match.

Edge cases: the index is nonempty by the positive-integer source convention;
`n = 0`, `i₀ = 0`, `j = 0`, and `k = 0` all represent the first term and are
allowed. `X` and any `B_i` may be the zero group, and zero transition maps are
allowed. There is no scheme, numerical degree, or characteristic parameter.
Universe `u` is unrestricted. The definition contains data and no `sorry`; it
proves nothing. The declaration and module docstrings name the source and node.

Independent searches used different terms from the first worker: `msearch.py`
LeanFinder for "inverse tower pro-isomorphic to a constant abelian group retract
eventual factorization" found only limit and eventual-isomorphism results;
Loogle for `"proconstant"` found no hit; `msearch.py grep` for `IsProConstant`,
`ProIsomorphic`, and `stableImage` found no hit. `rg` for proconstant/stable-image
terms over Mathlib's CategoryTheory, the source `WeilConjectures`, and `lean/Sheaf`
found no matching definition. `Functor.IsEventuallyConstantTo` in Mathlib's
`EventuallyConstant.lean` requires all maps into a chosen object to be
isomorphisms, a strictly stronger condition. No existing exact notion was found.

Mismatches found: none. Changed: only this report. The module and node's
`lean.statement` already match verbatim; the single-file compile was clean.
