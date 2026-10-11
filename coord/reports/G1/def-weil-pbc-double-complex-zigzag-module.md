## Worker report

Module: `lean/Sheaf/Algebra/Homology/ZigzagModule.lean`. It defines the diagonal
direct sum, zig-zag equations and cycles, boundary map and its image, the quotient
module, componentwise maps, and induced quotient maps. Only the preservation
statement needed to construct the induced quotient map is postponed, as the named
theorem `HomologicalComplex₂.zigzagTotalMap_preserves : ... := by sorry`. That
statement is clause (b) of the existing DAG node
`lem-weil-pbc-double-complex-zigzag-module-functorial`; its docstring gives the
source and proof outline. The quotient map itself contains no `sorry`.

Clause correspondence:

- Commutative base ring: `{R : Type*} [CommRing R]`; this also permits the zero
  ring. Homological first-quadrant module bicomplex and morphism:
  `HomologicalComplex₂ (ModuleCat R) (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)` and `Φ : A ⟶ B`. Dependency: Mathlib
  `HomologicalComplex₂`, in `Mathlib.Algebra.Homology.HomologicalBicomplex`.
  Its full definition is `HomologicalComplex (HomologicalComplex C c₂) c₁`;
  its docstring identifies `(K.X p).X q` as the component. The same module's
  `d_comm` and `comm_f` encode the commuting squares and morphisms.
- Zero outside the first quadrant and zero boundary differentials: natural
  indices and `ComplexShape.down ℕ`. The `HomologicalComplex` shape condition
  makes arrows not lowering the index by one zero; `d_comp_d` makes two
  consecutive differentials zero. This is the dependency node
  `def-weil-pbc-module-double-complex` as recorded in `mathlib_match`.
- `Tₙ(A)` and its tuples: `ZigzagIndex n` is the subtype of pairs with
  `p + q = n`; `zigzagTotal A n` is the direct sum of `(A.X p).X q` over
  that subtype. Every index set is finite, including the single index at
  `n = 0`.
- Zig-zag equalities and `Zₙ(A)`: `zigzagRelation A n p q h` is the
  horizontal component minus the next vertical component, and
  `zigzagCycles A n` requires it to vanish for every `p + 1 + q = n`.
  At `n = 0` there is no such index, giving all of `A₀,₀`.
- `Dₙ₊₁` and `Bₙ(A)`: `zigzagBoundaryComponent` sends one source summand
  to `d b` at `(p-1,q)` when `p > 0` and `δ b` at `(p,q-1)` when `q > 0`,
  adding the two target vectors. `zigzagBoundary` extends this linearly
  from the direct sum; therefore each target component is the stated sum.
  `zigzagBoundaries A n` is its `LinearMap.range`, including all finite sums
  of the stated generators. Boundary cases omit nonexistent components.
- `𝐇ₙ(A)`: `zigzagModule A n` is the quotient of `zigzagCycles A n` by
  `(zigzagBoundaries A n).comap (zigzagCycles A n).subtype`, precisely the
  internal submodule `Zₙ(A) ∩ Bₙ(A)`. No inclusion `Bₙ ⊆ Zₙ` is assumed.
- Componentwise action: `zigzagTotalMap Φ n` extends the component maps
  `((Φ.f p).f q).hom` over the direct sum. The named preservation statement
  says this map sends `Zₙ(A)` and `Bₙ(A)` into the corresponding submodules
  of `B`. `zigzagMap Φ n` restricts it to cycles and applies `Submodule.mapQ`
  to the quotient, so its value on `[a]` is `[Φ(a)]`. Composition, identity,
  and `Bₙ ⊆ Zₙ` are the separate functoriality node, as the item specifies.

Edge cases checked: `n = 0` has one component and no relation; `D₁` has the
two boundary generators. At any edge of the first quadrant the missing arrow
is omitted. Zero component modules and the zero ring require no exception.
No characteristic hypothesis occurs; the plus sign in `D` is retained in
characteristic two as well. The subtype `p + q = n` does not restrict a
possible degree or index cardinality beyond the node's natural indices.

Searches: `msearch.py leanfinder` with "zig-zag module of a double complex of
modules, cycles satisfying d a = delta a modulo images of d + delta" returned
total-complex and homological-complex hits, none this quotient. `msearch.py
loogle` with "HomologicalComplex₂, zigzag, totalComplex" found no `zigzag`
identifier. `msearch.py grep` for `zigzag|zig.zag|Zigzag` under Mathlib
`Algebra/Homology` found only the unrelated categorical
`zigzag_isConnected`. `rg` in the source project's `WeilConjectures` found
categorical zig-zag identities and bicomplex machinery, no zig-zag module;
`grep -rn` for this DAG id found nothing. `rg` in the repository's `lean/Sheaf`
and in `dag/lean_names_upstream.json` found no match. The local Stacks
checkout is absent; the source place was read from upstream `algebra.tex`
at Tag 00M1. Its displayed denominator uses `d + δ`, while the following
generator sentence uses `-δ`; the node deliberately uses the displayed plus
formula, under which the generated elements satisfy the zig-zag equations.

Compilation: `scompile.py` completed with no errors or warnings.

## Second reading by G1

Independent comparison with the node and Stacks, Algebra, Section Tag 00LY and
Lemma Tag 00M1 (the source checkout has no `algebra.tex`; the tag was read on
the Stacks site). Verdict: the declarations render the node's definition and
map with no extra mathematical hypothesis.

- Base and double complex: `{R : Type*} [CommRing R]` and
  `A : HomologicalComplex₂ (ModuleCat R) (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)`. Mathlib's `HomologicalComplex₂` is a complex of
  complexes: `(A.X p).X q` is `Aₚ,ᵩ`, its outer and inner differentials are
  respectively `d` and `δ`, and its morphisms commute with both. The `down ℕ`
  shape gives precisely the first quadrant and zero maps at its edges. This
  matches dependency `def-weil-pbc-module-double-complex`, including its
  commuting squares, two square-zero laws, and morphisms. Stacks assumes no
  Noetherian, finiteness, or characteristic condition for this construction;
  its row/column resolution hypotheses are for the later homology isomorphism.
- Index set, tuples, and `Tₙ`: `ZigzagIndex n` has pairs with `p + q = n`;
  `zigzagTotal A n` is the direct sum of the corresponding `(A.X p).X q`.
  The index set is finite for every `n`, so it represents all listed tuples.
- Zig-zags `Zₙ`: `zigzagRelation A n p q h` is
  `d(aₚ₊₁,ᵩ) - δ(aₚ,ᵩ₊₁)`; `zigzagCycles A n` requires its vanishing for
  every `p + 1 + q = n`. Reindexing `p + 1` gives exactly every equation in
  the node, with no additional equation.
- Trivial zig-zags and `Dₙ₊₁`: `zigzagBoundaryComponent A n i` places `d b`
  at `(p-1,q)` and `δ b` at `(p,q-1)` for a source at `(p,q)`, omitting an
  impossible position; `zigzagBoundary A n` extends this over the direct
  sum. Thus its `(p,q)` target component is the node's
  `d(bₚ₊₁,ᵩ) + δ(bₚ,ᵩ₊₁)`. `zigzagBoundaries A n` is exactly its range,
  equivalently the submodule generated by those one-source tuples.
- Quotient `𝐇ₙ`: `zigzagModule A n` quotients `zigzagCycles A n` by the
  comap of `zigzagBoundaries A n` under the inclusion of cycles. The comap
  consists of elements in `Zₙ(A) ∩ Bₙ(A)`; it does not assume the inclusion
  `Bₙ(A) ≤ Zₙ(A)` that the separate functoriality node must establish.
- Morphisms and induced map: `Φ : A ⟶ B` is the dependency's bicomplex
  morphism. `zigzagTotalMap Φ n` applies `((Φ.f p).f q).hom` to each summand.
  `zigzagMap Φ n` restricts it to cycles and quotients by boundaries, so on
  classes it sends `[a]` to `[Φ(a)]`. Its needed preservation theorem is
  `zigzagTotalMap_preserves`, named and postponed with `sorry`; its two
  conjuncts are exactly the preservation part of the separate functoriality
  node. Identity, composition, and `Bₙ ≤ Zₙ` remain that node's claims.

Edge cases: at `n = 0`, `ZigzagIndex` contains only `(0,0)` and there is no
relation, while `D₁` includes both possible degree-one sources. At `p = 0`
or `q = 0`, the boundary component explicitly omits the nonexistent target.
Zero modules, the zero ring, and characteristic two require no exceptions;
there is no empty-scheme parameter. The coefficient-ring universe is `Type*`
and the index type is the node's `ℕ`, so no degree or ring universe is excluded.
The source's displayed denominator has a plus sign while its later generator
sentence has a minus sign. The node explicitly chooses the displayed plus
formula, and the Lean matches it; the minus generator generally fails the
zig-zag equation for commuting squares.

Independent searches: `msearch.py leanfinder` for bicomplex cycles satisfying
adjacent differential equalities modulo unsigned boundaries returned total
complex constructions only; `msearch.py loogle` for
`HomologicalComplex₂, Submodule` returned no hit; `msearch.py grep` for
bicomplex/diagonal/total-homology notions found no such quotient. `rg` over
Mathlib's homology files, the source `WeilConjectures/`, and this repository's
`lean/Sheaf/` found total-complex and unrelated categorical zig-zag notions,
but no existing declaration with this definition. No duplicate was found.

Changes: expanded the preservation theorem's docstring into the two proof
steps used by its statement, corrected the module header's outdated Stacks
lemma number to the stable tag, and replaced the handoff placeholder with
this item-by-item review. No mathematical definition or signature changed.
