## Worker report

`Sheaf.AlgebraicGeometry.AlgebraicStackOpenDmLocus` states
`CategoryTheory.exists_largest_open_unramified_moduli_diagonal`.
Its only proof is `sorry`. The mathematical statement and seven-step proof plan
of the DAG node are unchanged. This repair removes the extra definition node
`def-sfb-algebraic-moduli-stack` and its module `AlgebraicModuliStack.lean`.
The algebraic-stack hypothesis is now inline, with exactly the `hstack`, `hdiag`,
and `hatlas` binders of the landed `unramifiedModuliDiagonal_iff_etaleAtlas`.
There are no new nodes or dependency modules.

Each hypothesis and clause is rendered as follows:

- The arbitrary base scheme is `{S : Scheme.{u}}`; the stack over that base is
  `(F : BasedCategory.{v, w} (Over S))`. All three universes are explicit and free.
- Stack descent in groupoids is `(hstack : IsModuliStack F)`. Its existing
  definition uses fibred groupoids and effective descent for the etale topology.
  Stacks 026O's discussion identifies this convention with the fppf-stack one
  when the representable diagonal and smooth surjective atlas are supplied.
- Representability of the diagonal is `(hdiag : HasAlgebraicSpaceDiagonal F)`.
  This uses the recorded two-scheme-test/2-fibre-product notion.
- The smooth surjective scheme atlas is `hatlas`: there exist `U : Over S` and
  `a : BasedFunctor (discreteModuli (yoneda.obj U)) F`; for every scheme map
  `t : h_T -> F`, there exist an algebraic space `Z` and its specified projection
  `p : Z.obj.obj ⟶ yoneda.obj T`. `HasSpaceBaseChange a T t Z p` identifies
  `Z` with the actual 2-base change over `T`. `SpaceMapIsSurjective Z T p`
  requires joint surjectivity on the points of its etale scheme charts.
  Every chart `b : yoneda.obj V ⟶ Z.obj.obj` with `AlgebraicSpace.IsEtale b`
  satisfies `AlgebraicGeometry.Smooth ((yoneda.preimage (b ≫ p)).left)`.
  Thus smoothness is tested on the retained projection, rather than an arbitrary
  map. This is the exact atlas hypothesis of the landed criterion.
- Existence of the open substack is `∃ U : OpenModuliSubstack F`. Its existing
  structure is a full subcategory given by an object predicate, stable under
  pullbacks, whose every scheme test is an actual open immersion with the
  specified projection comparison. In a CFG every arrow is cartesian, so the
  closure under arrows in that structure is the required pullback closure.
- The relative diagonal is unramified through
  `HasUnramifiedModuliDiagonal U.category`. Its existing definition retains the
  map to `T ⨯ U` in `Over S`, with both projections identified by 2-isomorphisms.
  `SpaceMapIsUnramified` tests the recorded `IsUnramified` on every etale scheme
  chart. That predicate is locally finite type plus an open-immersion diagonal.
- Maximality is `∀ V : OpenModuliSubstack F,
  HasUnramifiedModuliDiagonal V.category → V.IsContainedIn U`.
  The existing containment predicate is implication of the two object predicates.

Dependency declarations read, including their full signatures and docstrings:

- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsModuliStack`, `HasAlgebraicSpaceDiagonal`, `discreteModuli`,
  `HasSpaceBaseChange`, and `SpaceMapIsSurjective`, together with their CFG,
  discrete-presheaf, 2-fibre-product, and projection interfaces. These are the
  general declarations recorded by `def-sfb-stable-pointed-moduli-groupoids`;
  no curve, genus, or marked-point specialization is introduced.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `AlgebraicGeometry.Smooth`, recorded by `def-sbc-smooth-morphisms`.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack`:
  `CategoryTheory.OpenModuliSubstack`, `.category`, `.IsContainedIn`,
  `SpaceMapIsUnramified`, and `HasUnramifiedModuliDiagonal`.
  Its public import of `Sheaf.AlgebraicGeometry.UnramifiedMorphism` supplies
  `AlgebraicGeometry.IsUnramified`, recorded by `def-weil-unramified-morphism`.
- `Sheaf.AlgebraicGeometry.UnramifiedDiagonalEtaleAtlas` was read to match its
  algebraicity hypotheses exactly. Following the explicit return instruction,
  the delivered file has only the three public statement imports above; the
  previous plain Limits, Etale, and Basic imports are removed. The seven-step
  docstring retains the full proof-dependency plan for stage 3.

Edge cases checked: empty base or empty stack; an already DM stack (the largest
open is the entire stack); `B G_m` (the largest open is empty, as noted immediately
before Stacks 0DSM); mixed DM and non-DM components; and arbitrary, possibly empty,
infinite families of opens. No field, characteristic, nonemptiness, finiteness,
quasi-compactness, or separatedness hypothesis is added. No equality between the
object and morphism universes of the total category is imposed.

Searches in this repair:

- `msearch.py leanfinder`, "Every algebraic stack has a largest open substack with
  unramified relative diagonal": eight hits about scheme formal unramifiedness
  and locality of diagonal properties; none states this theorem.
- `msearch.py loogle`, `"OpenModuliSubstack"`: zero hits.
- `msearch.py grep`, `AlgebraicStack|OpenSubstack|largest_open_unramified`, in
  `Mathlib/AlgebraicGeometry`: zero hits.
- `rg` for `exists_largest_open_unramified_moduli_diagonal|IsAlgebraicModuliStack|
  OpenModuliSubstack` in `lean/WeilConjectures` and `lean/Sheaf` found the existing
  open-substack vocabulary, atlas criterion, specialized proper-curve DM locus,
  and DM-open permanence. No declaration states this arbitrary-stack theorem.
  The item-id search in `lean/WeilConjectures` found no attachment.

Sources read again: Stacks `stacks-morphisms.tex`, the whole statement and proof
of `lemma-open-DM-locus` (0DSM), `definition-absolute-separated`, and
`lemma-separated-implies-morphism-separated` (050N), part (1);
`algebraic.tex`, `definition-algebraic-stack` (026O), including its following
etale-stack convention discussion. The empty-locus example is explicitly present
in the source. No statement dispute or mathematical correction is needed.

## Repair of return e83687d88b33

1. The saved report was inspected and the unchanged packet was dry-run first.
   It reported `OK (dry run): commit 8690e625393 passes the preflight and compiles;
   nothing pushed`. This does not resolve the independent landing-check finding
   in the return, so the explicit requested repair is applied instead of another
   unchanged push.
2. Removed `dag/nodes/sec-six-functors-basics/def-sfb-algebraic-moduli-stack.json`
   and `lean/Sheaf/AlgebraicGeometry/AlgebraicModuliStack.lean` from the packet.
   This also avoids introducing the id/declaration reported in Q18's delivery.
3. Replaced `(hF : IsAlgebraicModuliStack F)` with the exact inline `hstack`,
   `hdiag`, and `hatlas` hypotheses of `unramifiedModuliDiagonal_iff_etaleAtlas`.
   The equivalent conjunction is written as hypotheses, with surjectivity before
   the universal smooth-chart clause, exactly as in that landed statement.
4. The public imports are `StablePointedModuliGroupoids`, Mathlib's
   `Morphisms.Smooth`, and `OpenModuliSubstack`. Removed all three previous unused
   plain imports, as requested. The source and seven-step proof docstrings remain.
5. Rebased the sandbox node on the current read-only repository node, preserving
   every field except `lean` and the authorized addition of the already landed
   `def-sfb-open-moduli-substack` to `stmt_deps`. The dependency list is exactly
   the base three dependencies plus this one. No reachability flag is supplied;
   neither the item nor any live dependency is dropped or edited.

## Self-check by NP

This is the author's self-check; the maintainer supplies the independent review.
The node and final Lean module were reread clause by clause. The base and total
category are arbitrary; stack descent, representable diagonal, and the actual
smooth surjective atlas match the node and the landed criterion. The existential
open, relative unramifiedness over the original base, and containment of every
other such open are unchanged. The previous abstraction was the only interface
change: expanding its three conjuncts adds no mathematical hypothesis. The inline
atlas now has the landed criterion's exact conjunction order. Both projections
in the relative-diagonal definition remain pinned to the product over S.

The saved packet was compared with current main: before repair, only `lean` and
`stmt_deps` differed on the item. The final packet has a single Lean module and
one node, with the exact recorded signature, explicit universes, `autoImplicit
false`, lines at most 100 characters, and one `sorry` theorem. There are no data
definitions or new DAG nodes. Compilation and dry-run results are recorded below.

Validation: `scompile.py NP lem-sfb-algebraic-stack-open-dm-locus` compiled
the sole module in both sandbox and library form (6.0 s and 3.5 s), without
errors or warnings. A direct text comparison confirms that all inline
algebraicity binders are byte-identical to the landed atlas criterion. JSON
comparison confirms only the authorized `lean` and `stmt_deps` changes, and
`lean.statement` is verbatim. The Lean file has one `sorry` and no line over
100 characters.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
