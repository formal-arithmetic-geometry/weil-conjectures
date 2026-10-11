## Worker report

The module states `directedColimitBaseChangeElementwise` in
`Sheaf.Paper.DirectedColimitBaseChangeElementwise`. It binds a directed preorder of
commutative rings, transition maps and a universal colimit cocone, a base index and
module, and a family of additive transition maps and cocone maps. Its conclusion has
(1) the representative clause `∀ x : M, ∃ i t, μ i t = x`; and (2) the eventual-zero
clause `∀ i t, μ i t = 0 → ∃ j, ∃ hij : i ≤ j, μᵢ hij t = 0`. The ring hypotheses render
the directed system, identity and composition clauses, while `hμ_id`, `hμ_comp`, and
`hμ_cocone` render the module directed system and cocone. The source is Stacks Tags
00D6, 00D7 and 00DD (the node's stated combination).

Dependency declaration used: `CategoryTheory.Limits.colimit` from the Mathlib
record `def-weil-pbc-category-colimit`; the present module uses explicit ring-cocone
fields to avoid redefining that notion.

Edge cases checked: the preorder is only directed (not assumed nonempty separately),
`i₀` is arbitrary with all stages above it, zero is handled by the eventual-zero
clause, and no finiteness or nonzero assumptions are introduced. Searches made:
LeanFinder/LeanSearch for filtered ring-colimit tensor representatives (Mathlib
`TensorProduct.directLimitLeft` and filtered-colimit declarations, no exact theorem);
Loogle for `CategoryTheory.Limits.IsColimit, TensorProduct` (no exact match); grep of
Mathlib and `WeilConjectures/` for directed-colimit base-change elementwise
statements (no project declaration). No `STATEMENT-DISPUTED` marker.

## Earlier second reading (a previous round; superseded)

The node and module were read together. The directed-system hypotheses, colimit
cocone data, base index, module data, representative conclusion, and eventual-zero
conclusion are all present with explicit binders. The module records the dependency's
Mathlib colimit notion through its universal cocone fields.

## Second reading by G1

Read the item's statement, all four proof steps and the sole statement dependency
`def-weil-pbc-category-colimit`, including its recorded Mathlib declarations. Read
`Cocone`, `IsColimit`, and the chosen `colimit` in Mathlib. The dependency is usable
as recorded: `Cocone` includes compatibility and `IsColimit` supplies the universal
factorization and uniqueness; these replace the worker's private universal-property
binder. No new nodes or dependency modules are needed. The node itself is correct
and remains unchanged outside `lean`.

Source read directly in `/home/ubuntu/c1-stacks-review/algebra.tex` (the available
local Stacks source): definition-directed-system (00D4), lemma-directed-colimit
(00D6), lemma-zero-directed-limit (00D7), lemma-tensor-products-commute-with-limits
(00DD), and lemma-colimit-etale (07RI), including the passage lifting generators
and relations. The directed-system definition explicitly allows a preorder, and
00DD is over an arbitrary ring, without finiteness, flatness, or characteristic
conditions. The finite-presentation and étale assumptions in 07RI concern the
application to algebra maps, not the elementwise tensor-colimit assertion.

Objects, hypotheses and conclusion matched item by item:

- Directed set I: `(I : Type u) [Preorder I] [IsDirected I (· ≤ ·)]`.
  Verdict: exact; no partial-order or least-element hypothesis.
- Directed system of commutative rings and transition maps: `A : I ⥤ CommRingCat.{v}`.
  `A.obj i` is A_i and `(A.map (homOfLE h)).hom` is α_ji. Functor identity and
  composition laws render exactly the system laws. Verdict: exact.
- Ring colimit A and coprojections: `c : Cocone A`, `hc : IsColimit c`.
  `c.pt` is the colimit ring and `(c.ι.app i).hom` is α_i. Cocone naturality
  supplies α_j α_ji = α_i. Verdict: exact, using the dependency's declarations.
- Arbitrary base index 0: `(i₀ : I)`. Verdict: exact; it need not be below
  every index. The upper tail is `J := {i : I // i₀ ≤ i}`.
- Base module M_0: `(M₀ : Type w) [AddCommGroup M₀] [Module (A.obj i₀) M₀]`.
  Verdict: exact, with no finite generation or freeness assumed.
- A_0-algebras A_i for i ≥ 0 and A: the two local `Algebra` instances are
  `(A.map (homOfLE i.property)).hom.toAlgebra` and
  `(c.ι.app i₀).hom.toAlgebra`. Opened `RingHom.toAlgebra`: it defines the
  scalar action c • a as α(c) * a, precisely the node's action. Verdict: exact.
- M_i and M: `Mi i := A.obj i.val ⊗[A.obj i₀] M₀` and
  `M := c.pt ⊗[A.obj i₀] M₀`. Verdict: actual Mathlib tensor products;
  the worker's arbitrary unrelated modules are removed.
- Maps μ_i and μ_ji: linear maps `μ` and `μij` with the two displayed
  pure-tensor equations. Verdict: precisely α_i ⊗ id and α_ji ⊗ id.
  These equations specify the maps already prescribed by the node, rather than
  impose a new mathematical assumption: pure tensors generate the tensor product,
  so there is exactly one linear map with each prescribed pure-tensor formula;
  existence follows from the ring-system and cocone compatibility. No additional
  system-law hypotheses on the module maps are required. They follow from these
  formulas and the ring diagram.
- Clause (1): `∀ x : M, ∃ (i : J) (t : Mi i), μ i t = x`.
  Verdict: every element, one stage above i₀, one tensor element; correct order.
- Clause (2): `∀ (i : J) (t : Mi i), μ i t = 0 →
  ∃ (j : J) (h : i.val ≤ j.val), μij i j h t = 0`.
  Verdict: every zero-image tensor dies at one later stage, exact quantifiers.
- Parenthetical equivalent colimit formulation: expressed by its equivalent two
  elementwise conditions for this directed linear system, rather than an extra
  independent conclusion. The docstring's step 3 records the categorical colimit
  formulation and step 4 records its elementwise description (00D6 and 00D7).
  Verdict: no omitted independent clause.

Edge cases: an empty I cannot carry the node's chosen i₀, so neither statement
has an empty-index case with a base module. The upper tail is nonempty (i₀ belongs)
and directed, even if i₀ is not minimal and the preorder is not antisymmetric.
Zero rings, zero M₀, and zero tensors are allowed; no Nontrivial assumption occurs.
No scheme, cohomological n, or characteristic restriction occurs in this node.
The universes u (indices), v (rings) and w (base module) are independent; tensor
carriers live in max v w, removing the worker's artificial requirement that all
specified module carriers have the same universe w. Ring sizes can always be
placed in a common universe. No variable or universe is unbound.

Independent searches (using words different from the first worker):

- LeanSearch: “elements of scalar extension tensor product along a filtered
  colimit of commutative rings lift to a later ring”. Service returned Internal
  Server Error, recorded unavailable; no verdict claimed for it.
- Loogle: `TensorProduct, CategoryTheory.Limits.IsColimit`: successful, zero hits.
- LeanFinder: “An element in the tensor product with a directed colimit of rings
  is represented at some stage, and a tensor mapping to zero vanishes at a later
  stage”: successful, eight hits, mainly Submodule.FG.rTensor/lTensor.directLimit
  and TensorProduct.toDirectLimit. None states this ring-colimit base-change claim.
- Mathlib grep via msearch: `colimit.*tensor|tensor.*colimit|directLimitLeft`.
  Opened TensorProduct.directLimitLeft and its surrounding declarations: they
  concern Module.DirectLimit over a fixed ring, not a categorical colimit of rings
  with its induced base-ring module structure. Also opened ModuleColimit in
  ModuleCat/Presheaf/ColimitFunctor: it constructs a module over a varying ring
  colimit from a separate additive-group colimit, not the present statement.
- rg on WeilConjectures and lean/Sheaf with
  `directedColimitBaseChange|colimit.*tensor|tensor.*colimit|directLimitLeft`:
  general monoidal/sheaf preservation results, no exact ring tensor elementwise
  theorem. A narrower ring/linear-algebra/Paper search also found only distinct
  statements such as ColimitSurjectiveRingMap. Full declaration-name search in
  Mathlib/upstream-name table/project found no name collision.

Mismatches repaired: arbitrary M and M_i replaced by specified tensor products;
least-base-index hypothesis removed and replaced by upper-tail indexing; missing
ring cocone compatibility restored through Mathlib Cocone; private colimit
specification replaced by Mathlib IsColimit; arbitrary additive maps replaced by
linear maps uniquely specified as the prescribed tensor maps; module-carrier
universe restriction removed. Added the standard copyright header, meaningful
TensorProduct namespace, and the node's complete four-step proof with dependency
ids in the docstring. Every proof remains sorry; there is no new definition or
proof and no hollow data. The node's lean.statement is extracted verbatim from
the final signature.

Validation: scompile.py compiled the final module cleanly on the server (1.2 s,
exit 0), with no warnings. The cocone target in the pure-tensor formula is
explicitly supplied to TensorProduct.tmul to avoid a reducibility mismatch in
instance synthesis. No mathematical hypothesis changed for that elaboration fix.

## Reviewer fix (R-dcb1005)

Restated in the landed DIRECTED SETS form (as K1 0c9742193, F1 6e8479f20, G1 a77d3edfd):
`F : I ⥤ CommRingCat` with `[HasColimit F]`, A = `colimit F`, coprojections `colimit.ι F i`,
A₀-structures `(colimit.ι F i₀).hom.toAlgebra` and `(F.map (homOfLE h)).hom.toAlgebra`, instead of a
bare `Cocone`/`IsColimit` pair. The maps μ_i = α_i ⊗ id and μ_{i'i} = α_{i'i} ⊗ id are now the
concrete `LinearMap.rTensor M₀` of the A₀-algebra maps α_i (commutes' from `colimit.w`) and α_{i'i}
(commutes' from `F.map_comp`), instead of universally quantified linear maps characterised by
hypotheses on pure tensors. Stages are indexed by `(i : I) (h : i₀ ≤ i)` as in the landed module
instead of the subtype `{i // i₀ ≤ i}`. Clauses (1) and (2) unchanged in content.
