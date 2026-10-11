## Worker report

The item is already stated by `AlgebraicGeometry.locallyQuasiFinite_npow_id_of_isAlgClosed`
in `WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny`, lines 73–75 of the
read-only slopmaster2 source. No Lean module is added, following one declaration per
statement. Only the item's `lean` record is changed.

Hypothesis and conclusion correspondence:

- The field K is the explicitly universe-bound `{K : Type u} [Field K]` at line 60.
- Algebraic closedness is `[IsAlgClosed K]`.
- A scheme over K is `(A : Over (Spec (.of K)))`.
- A group scheme is `[GrpObj A]`; properness, smoothness and connectedness are
  `[IsAbelianVariety A]`, exactly the definition recorded by def-sc-abelian-variety.
- The positive integer is `(n : ℕ) (hn : 0 < n)`, equivalent to n ≥ 1.
- The multiplication morphism is `(𝟙 A ^ n).left`. The group on morphisms is
  pointwise multiplication from `GrpObj`, so the nth power of the identity sends
  a point to its n-fold sum. The torsionSubgroupScheme docstring recorded by
  def-sc-mult-n explicitly identifies its defining kernel map as `𝟙 A ^ n`.
- The sole conclusion is `LocallyQuasiFinite (𝟙 A ^ n).left`.

Mathlib's LocallyQuasiFinite omits local finite type in general, but this is no
weakening here. Properness of A.hom supplies local finite type; Over.w identifies
`(𝟙 A ^ n).left ≫ A.hom` with A.hom, and
`AlgebraicGeometry.locallyOfFiniteType_of_comp` supplies local finite type of the
multiplication map. Under that condition Mathlib's discrete-fibre criterion is the
Stacks locally quasi-finite condition. The existing theorem's proof also establishes
properness of this map before applying its quasi-finite-locus criterion.

Dependency declarations read in full with their docstrings:

- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`,
  `AlgebraicGeometry.IsAbelianVariety`: proper, smooth, connected; GrpObj is a
  separate binder, as explained in that module.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`,
  `AlgebraicGeometry.torsionSubgroupScheme`: kernel of `𝟙 G ^ n`;
  the docstring supplies the multiplication convention used here.

Edge cases checked: n = 0 is excluded exactly as the node requires; n = 1 is the
identity; no characteristic restriction is introduced, including when the
characteristic divides n. Dimension zero is allowed. The empty scheme cannot be
an abelian variety since its identity section supplies a K-point (and
ConnectedSpace is nonempty). No commutativity binder or other additional
hypothesis is required by the existing theorem. Universe u is arbitrary.

Searches (2026-10-11):

- msearch.py leanfinder, "multiplication by positive n on an algebraically closed
  abelian variety is locally quasi-finite": 8 unrelated/general Mathlib hits,
  no matching abelian-variety theorem.
- msearch.py loogle, "AlgebraicGeometry.LocallyQuasiFinite": 12 generic Mathlib
  hits including its definition and stability declarations, no matching theorem.
- msearch.py grep, "locallyQuasiFinite_npow_id|IsAbelianVariety", AlgebraicGeometry:
  zero Mathlib hits.
- msearch.py leansearch, "locally quasi finite multiplication abelian variety":
  unavailable (Internal Server Error); no verdict assigned.
- rg of the source's AbelianVariety directory for npow_id/quasi/finite found the
  existing theorem. Its full signature, module variable binders and docstring
  were opened and read, together with its proof's properness reduction.
- rg for the item id in WeilConjectures found no literal hit (the source docstring
  instead names its parent lem-sc-mult-n-finite-kernel).
- rg for locally quasi-finite and multiplication declarations in lean/Sheaf found
  the general QuasiFiniteMorphism conventions and no duplicate of this theorem.
- rg of dag/lean_names_upstream.json for the existing theorem name found no hit.

Source checked: the local blueprint literature path is absent on this machine;
[Stacks Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG) was opened instead.
Its ample symmetric module and positive-dimensional fibre contradiction agree
with the node and the existing theorem's docstring. No statement correction,
new node, dependency repair, or STATEMENT-DISPUTED flag is needed.

The existing theorem is reused as-is; no proof is authored at stage 2. The second
reader should independently inspect the signature and the finite-type observation.

## Second reading by H1

The node introduces: an algebraically closed field `K`; an abelian variety `A`
over `K`; and an integer `n` with `n ≥ 1`.  Its conclusion is that multiplication
`[n] : A ⟶ A` is locally quasi-finite.  The existing Lean declaration renders
these as `{K : Type u} [Field K] [IsAlgClosed K]`,
`A : Over (Spec (.of K))` with `[GrpObj A] [IsAbelianVariety A]`,
`n : ℕ` with `hn : 0 < n`, and
`LocallyQuasiFinite (𝟙 A ^ n).left`.  The `GrpObj` and
`IsAbelianVariety` declarations match `def-sc-mult-n` and
`def-sc-abelian-variety`; the power of the identity is the recorded multiplication
morphism.  Quantifier order, universes, and the positive-integer hypothesis agree.

The edge cases are covered: `n = 0` is excluded, `n = 1` gives the identity,
and no characteristic restriction is imposed (including characteristic dividing
`n`).  Arbitrary universes are allowed.  The empty scheme cannot satisfy the
abelian-variety structure, while zero-dimensional abelian varieties remain allowed.

I searched Mathlib and the project source with `msearch.py` (LeanFinder, Loogle,
grep, and LeanSearch), and searched `lean/Sheaf` and `dag/lean_names_upstream.json`;
there is no duplicate declaration.  The source theorem
`AlgebraicGeometry.locallyQuasiFinite_npow_id_of_isAlgClosed` in
`WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny` (lines 73--75) is an
exact existing match.  Stacks Tags 0BFG and 03RP give the finite multiplication
map result underlying the blueprint argument, hence imply the stated local
quasi-finiteness.  No mismatch, statement correction, dependency repair, or new
definition was found.  The node's `lean` record was retained as `existing: true`
for this declaration.
