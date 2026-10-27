## Worker report

Record the existing public root declaration `adjunct_transport` in
`Sheaf.CategoryTheory.AdjunctConjugateOpenFactor`, at
`lean/Sheaf/CategoryTheory/AdjunctConjugateOpenFactor.lean:75`.
No Lean module is added or modified, no theorem is restated or proved, and the
node changes only in `lean`. The local declaration and the current server source
(read using `scompile.py --source Sheaf.CategoryTheory.AdjunctConjugateOpenFactor`)
are identical. No repair note exists for this item.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The five arbitrary categories are `{A B D E F : Type*}` with their five
  `[Category ...]` binders. Each category has its own object and morphism
  universes; there is no imposed universe equality or smallness restriction.
- The named functors `Lr`, `Rr`, `Lp`, `Rp`, `Ji`, `Pi`, `Jb`, `Pb`, `Lq`,
  `Rq`, `Js`, `Jk` have precisely the directions in the node. Lean composition
  `Ji ⋙ Lp` means the node's mathematical composition `L_p J_i`.
- The five specified adjunctions are `(ar : Lr ⊣ Rr)`, `(ap : Lp ⊣ Rp)`,
  `(ai : Ji ⊣ Pi)`, `(ab : Jb ⊣ Pb)`, `(aq : Lq ⊣ Rq)`. None is replaced
  by an existence hypothesis or identified with a different choice.
- The invertible unit hypothesis is exactly `[IsIso ab.unit]`.
- The comparisons are `(β : Ji ⋙ Lp ≅ Lq ⋙ Jb)` and
  `(d : Js ⋙ Jb ≅ Jk)`, with the stated orientations.
- The composite adjunctions are `ai.comp ap` and `aq.comp ab`.
- The specified right-adjoint conjugate of beta inverse is
  `(conjugateIsoEquiv (ai.comp ap) (aq.comp ab) β.symm).hom`.
  Its source is `Rp ⋙ Pi` and target `Pb ⋙ Rq`, exactly `P_i R_p` to
  `R_q P_b`. This uses beta inverse, not beta.
- The given square is `(α : Ji ⋙ Lp ⟶ Lr ⋙ Jk)` and its mate gamma is
  `mateEquiv ar ap α`; `.app M` has source `Ji.obj (Rr.obj M)` and target
  `Rp.obj (Jk.obj M)`.
- `(M : A)` and `(f : Lq.obj (Rr.obj M) ⟶ Js.obj M)` are unrestricted.
- The assumed factorization is the binder `hα`, namely
  `β.inv.app (Rr.obj M) ≫ α.app (Rr.obj M) ≫ Jk.map (ar.counit.app M) =
  Jb.map f ≫ d.hom.app M`. Lean writes composition in traversal order;
  this is exactly the displayed equality in the node.
- The node's z is the inline term
  `Pb.map (d.inv.app M) ≫ inv (ab.unit.app (Js.obj M))`.
  It has source `Pb.obj (Jk.obj M)` and target `Js.obj M`.
- The conclusion first applies `ai.homEquiv` to the mate component, then
  composes with the conjugate component at `Jk.obj M`, then with `Rq.map`
  of that exact z, and equates this to `aq.homEquiv _ _ f`.
  This is precisely the requested adjunct equation, with no extra conclusion.
- There are no geometric, additive, derived, full-faithfulness, nonempty, or
  adjunction-equality assumptions.

Dependency interfaces read in full with their docstrings:

- `def-weil-pbc-composite-adjunction`: Mathlib leaf
  `CategoryTheory.Adjunction.comp`, in `Mathlib.CategoryTheory.Adjunction.Basic`;
  its `comp_homEquiv`, unit and counit formulas give the chosen composite.
- `def-weil-pbc-adjunction-conjugate`: Mathlib leaf
  `CategoryTheory.conjugateEquiv`, with the recorded isomorphism clause
  `CategoryTheory.conjugateIsoEquiv`, in `Mathlib.CategoryTheory.Adjunction.Mates`.
- `def-weil-pbc-adjunction-mate`: Mathlib leaf `CategoryTheory.mateEquiv`,
  in `Mathlib.CategoryTheory.Adjunction.Mates`, with its `TwoSquare` interface.
- `lem-weil-pbc-adjunction-of-natural-bijection`: Mathlib leaf
  `CategoryTheory.Adjunction.mkOfHomEquiv`, in
  `Mathlib.CategoryTheory.Adjunction.Basic`; the needed recorded Hom formulas
  are `CategoryTheory.Adjunction.homEquiv`, `homEquiv_unit`, `homEquiv_counit`.
- Proof dependency `lem-weil-pbc-mate-pasting`: its relevant Mathlib clause
  `CategoryTheory.mateEquiv_conjugateEquiv_vcomp` was read in `Mates.lean`.
  The existing module publicly imports `Mathlib.CategoryTheory.Adjunction.Mates`,
  which supplies all these dependency declarations through its Basic import.

Sources read: Stacks `sites-cohomology.tex`, remark-base-change (07A7),
`categories.tex`, definition-adjoint (0037) and lemma-compose-counits (0DV0),
and the current blueprint `fix-prop-coherence.proof.md` sentence on exceptional
comparisons preserving units and counits. The node is the abstract categorical
normalization of those constructions, not an assertion that Stacks explicitly
states the entire transport formula.

Edge cases checked by reading the actual types and formulas: identity beta and
d give ordinary adjunct cancellation; identity open adjunction reduces z to d
inverse; distinct chosen adjunctions are allowed and accounted for by the
conjugate; terminal categories satisfy the identity; an empty A has no M and
requires no additional inhabitance assumption; no zero object or additive
structure is required. Invertibility of the unit as a natural transformation
supplies invertibility at each component, with no extra hypothesis.

Searches actually run (via the prescribed msearch.py NJ/item wrapper):

- LeanFinder: "Transport a mate through conjugation between composite
  adjunctions and cancel a left adjoint with invertible unit". Eight related
  results, including `mateEquiv_conjugateEquiv_vcomp`, iterated mate identities,
  and `conjugateEquiv_leftAdjointCompIso_inv`; none is the whole statement.
- Loogle: "CategoryTheory.conjugateEquiv, CategoryTheory.Adjunction.homEquiv".
  Service succeeded with zero hits.
- Mathlib grep: "homEquiv.*conjugate|conjugate.*homEquiv|conjugateEquiv_comm|mateEquiv_conjugateEquiv_vcomp"
  in CategoryTheory/Adjunction. Three hits in Mates.lean, related identities.
- LeanSearch: "Transport an adjunct through a conjugate isomorphism between
  composite adjoints and cancel a fully faithful left adjoint with invertible
  unit". Eight related results, including `leftAdjointCompIso`,
  `fullyFaithfulLOfIsIsoUnit`, `unit_conjugateEquiv`; no whole-statement match.
- Project rg on lean/Sheaf and lean/WeilConjectures:
  "adjunct_transport|adjunct_conjugate|conjugate.*open.*factor|lem-sf-adjunct-conjugate-open-factor".
  Found the exact public `adjunct_transport` in the recorded Sheaf module,
  its actual consumer in SemilinearProperOpenMatePasting, and unrelated matches.
  No matching upstream WeilConjectures declaration. The prescribed grep for the
  node id under lean/WeilConjectures and rg of dag/lean_names_upstream.json
  returned no hits.

No statement correction, new node, dependency repair, or disputed statement.
As required for an existing declaration, no duplicate Lean file is delivered and
no worker compilation of live library sources is attempted. The prescribed
server preflight and delivery checks validate the existing attachment.

## Second reading by NJ

Worker read-back only; independent review is performed by the maintainer, as
specified in this dispatch. I reopened the node and the full existing theorem,
checking the five category and adjunction binders, all functor directions,
`[IsIso ab.unit]`, beta/d orientation, the factorization hα, gamma, c and z.
The subtle orientation is correct: `β.symm` has hom beta inverse and produces
`Rp ⋙ Pi ⟶ Pb ⋙ Rq`. The order of all three factors in the conclusion agrees
with the node because Lean's `≫` is traversal-order composition. There is no
mismatch and no change beyond attaching the existing declaration.
