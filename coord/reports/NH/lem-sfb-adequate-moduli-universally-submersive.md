## Worker report

The module `Sheaf.AlgebraicGeometry.AdequateModuliUniversallySubmersive` states
`CategoryTheory.adequate_moduli_universally_submersive`, with `sorry` as its entire
proof. It introduces no definitions and postpones no auxiliary theorem. The node's
natural-language statement and proof are unchanged. Its statement dependencies gain
the already landed definition nodes `def-sfb-stack-point-topological-space`,
`def-sfb-open-moduli-substack`, and `def-sfb-dm-stack-morphism-properties`, for
the topology, canonical second projection, and field-object point classes/maps.
The theorem `lem-sfb-smooth-presentation-closed-subsets` remains only in proof_deps.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field is `(k : Type u) [Field k]`; `Field` is the Mathlib match of
  `def-weil-field` (Mathlib.Algebra.Field.Defs). Its commutative ring,
  nontriviality and nonzero inverse requirements were read in the source.
- The algebraic stack over k is
  `(F : BasedCategory.{v, w} (Over (Spec (.of k))))`
  with `(hF : IsAlgebraicModuliStack F)`.
- The algebraic space Y over k is `(Y : AlgebraicSpace (Spec (.of k)))`.
  The morphism is `(φ : BasedFunctor F (discreteModuli Y.obj.obj))`.
  `discreteModuli` regards the existing fppf sheaf as a fibred groupoid;
  it does not replace F by a set of isomorphism classes.
- Adequacy is exactly `(hφ : IsAdequateModuliSpace F hF Y φ)`. This landed
  predicate includes qcqs, the canonical structure-map isomorphism and local power
  lifting for all quasi-coherent algebras on affine etale base changes.
- Every algebraic-space base change is the unrestricted quantifier
  `∀ (T : AlgebraicSpace (Spec (.of k))) (g : T ⟶ Y)`.
  `g.hom.hom` is its actual natural transformation of presheaves and
  `discreteModuliMap g.hom.hom` its induced based functor.
- `moduliTwoFiberProduct φ (discreteModuliMap g.hom.hom)` is the actual
  2-fibre product. `moduliTwoFiberSnd` gives its canonical projection to T;
  `moduliPointMap` is the map induced on field-object point classes.
- Surjectivity is the first conjunct `Function.Surjective` of that projection's
  point map.
- Every subset V of |T| is quantified as
  `∀ V : Set (ModuliPoints (discreteModuli T.obj.obj))`. The second conjunct is
  exactly `IsOpen V ↔ IsOpen (projection ⁻¹' V)`, with both topologies explicitly
  `moduliPointTopologicalSpace` on the appropriate stack.
- Points are the existing `ModuliPoints`: field objects modulo arrows over field
  extensions and their equivalence closure. This is the common-field-extension
  convention, not rational points over k. The existing smooth topology theorem
  identifies the topology with the quotient topology of any smooth surjective atlas.
  An etale surjective atlas of an algebraic space is also such a smooth atlas,
  so its discrete stack uses precisely the topology specified in the node.
- Continuity is included in the forward implication of the open-set equivalence
  for all V. There is no extra continuity, closedness or adequacy-of-base-change
  hypothesis and no extra conclusion about closed sets.
- There is no Noetherian, finite-type, separatedness, characteristic, reducedness,
  finite-inertia, DM, nonemptiness or flat-base-change assumption.

Recorded dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.AdequateModuliSpace`:
  `CategoryTheory.IsAdequateModuliSpace` (full definition and source docstring).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`:
  `AlgebraicGeometry.AlgebraicSpace`, together with its underlying
  `AlgebraicSpace.IsAlgebraicSpace` and morphism convention (full signatures read).
- `Mathlib.Algebra.Field.Defs`: `Field`, via the existing imports.
- `Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen`:
  `CategoryTheory.moduliPointTopologicalSpace` (full signature, definition, and
  docstring read), the existing:true binding of the definition node
  `def-sfb-stack-point-topological-space`. It is publicly imported and used
  explicitly as the topology in both IsOpen expressions. Its supremum of
  coinduced topologies is real data, with no theorem choice.
- `Sheaf.AlgebraicGeometry.SmoothPresentationClosedSubsets`:
  `CategoryTheory.smooth_presentation_closed_subsets` is a proof dependency only
  and its module is imported without public. No helper definition from it occurs
  in the signature.
- `Sheaf.AlgebraicGeometry.AdequateModuliTopologicalImages`:
  `CategoryTheory.adequate_moduli_topological_images`, now landed, is imported
  without public for the proof plan. Its full signature and proof docstring
  were read against the current main branch.
- The landed constructions `CategoryTheory.ModuliPoints` and
  `moduliPointMap` in `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`,
  `discreteModuli`, `discreteModuliMap`, `moduliTwoFiberProduct` in
  `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`, and
  `moduliTwoFiberSnd` in `Sheaf.AlgebraicGeometry.OpenModuliSubstack` were read.
  The projection and point-map modules are explicitly publicly imported and their
  owning definition nodes are direct stmt_deps; there are no private copies.

Both recorded proof dependencies now have Lean records and are imported without
public. The statement imports the owning topology definition module publicly.

Edge cases checked before writing: empty T gives a map to an empty point set and
both the empty and full subset criteria; identity base change recovers the original
submersion; identity adequate morphisms are covered; arbitrary nonflat g is allowed,
including the characteristic-p base changes of Alper Example 5.2.10 which need not
remain adequate. Empty and full V are included by the unrestricted Set quantifier.
The stack's object/morphism universes v,w are independent, and the site schemes,
field extensions and algebraic spaces all use the same universe u as the base field,
in accordance with the landed definitions and size convention. No independent smaller
test universe makes the conclusion vacuous.

Source check: opened https://arxiv.org/html/1005.2398v3 and read Section 2,
Proposition 5.2.9 and Theorem 5.3.1 with its proof. Section 2 assumes quasi-compact
separated diagonals. The existing reviewed node
`lem-sfb-adequate-moduli-universal-closed-topology` explicitly explains why the
surjectivity and universal-closedness conclusions used here require no such
restriction: etale-local affine reductions use 4.2.1(5) and 5.2.6. Its review
(Q160) explicitly accepts omission of those diagonal assumptions. This item only
assembles those topological conclusions; unlike the geometric-fibre bijection
clause of `lem-sfb-adequate-geometric-fibres-submersion`, it does not require
quasi-separated targets to get geometric rational lifts. Thus no statement
correction or extra diagonal hypothesis is appropriate here.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder "An adequate moduli space is universally submersive
  after any algebraic space base change"`: eight scheme-level hits, including
  UniversallyOpen, UniversallyInjective and UniversallyClosed; none is the item.
- `msearch.py ... loogle '"IsQuotientMap", "AlgebraicGeometry"'`: one hit,
  `AlgebraicGeometry.Flat.isQuotientMap_of_surjective`; it assumes a flat
  quasi-compact scheme morphism, so it does not apply to adequate stack maps.
- `msearch.py ... grep 'adequateModuli|adequate_moduli|universally.?submersive'`:
  zero Mathlib hits.
- `msearch.py ... leansearch "Adequate moduli spaces induce quotient maps after
  arbitrary algebraic space base change"`: eight scheme base-change/properness
  hits, including the flat quotient-map theorem; no match.
- `rg` in `lean/WeilConjectures` for adequate/moduli/submersive and the exact item
  id: no declaration of this theorem (only unrelated ring submersive presentations
  and pro-etale submersive covers).
- `rg` in `lean/Sheaf` for adequacy and quotient/submersive terminology found
  the adequacy definition and the smooth point topology, but no existing theorem.
  Both are reused. DAG search found the sibling geometric-fibre theorem, but it
  has no Lean declaration and contains additional conclusions and assumptions.

Compilation of the repaired signature with the topology definition import passed
through the prescribed scompile.py wrapper (sandbox 6.8 seconds, named library
9.1 seconds). The final file, including the current proof imports, is compiled
again by the dry run and delivery.

No new nodes, dependency modules, statement corrections or disputed statements.

## Second reading by NH

A separate clause-by-clause rereading in this worker session checked the node
against the final file. The dispatcher explicitly forbids starting another agent;
the maintainer's independent review remains pending. No independent second-worker
review is claimed here.

The field, algebraic stack and adequate-map binders match the source node.
The algebraic-space quantifier is arbitrary, and its map has no flatness restriction.
The map in both conjuncts is the same canonical second projection, rather than a
freely chosen function or a scheme presentation. The domain topology is on the
2-fibre-product stack, the codomain topology is on T, and the displayed inverse
image uses that same point map. The forward direction gives continuity and the
reverse direction detects openness, with explicit topologies and no local notation.
The quotient points allow field extensions; all subsets, including empty/full,
are quantified. No finiteness or separatedness assumptions were introduced.
The owning topology definition node, rather than the smooth-presentation theorem,
is now in stmt_deps. The same-session rereading is not an independent worker
review; the returned maintainer review is the independent reading. No mathematical
statement change was needed.

## Repair of returned head ba4c34eedbf7

H2+H4: removed `lem-sfb-smooth-presentation-closed-subsets` from stmt_deps.
Its helper `moduliSmoothPointTopology` was a plain definition, so its occurrence
did not justify a theorem statement dependency. Replaced that dependency with
the landed `def-sfb-stack-point-topological-space` and used its recorded existing
instance `CategoryTheory.moduliPointTopologicalSpace` on both sides. Replaced
the public SmoothPresentationClosedSubsets import with the public owning
StackPointTopologyFlatLfpOpen import. The smooth-presentation theorem remains
in proof_deps and its module is imported without public, as stage 2 requires.
Updated lean.statement verbatim from the revised file.

Advisory: added the landed owning definition nodes
`def-sfb-open-moduli-substack` for moduliTwoFiberSnd and
`def-sfb-dm-stack-morphism-properties` for ModuliPoints/moduliPointMap
to stmt_deps and imported their modules explicitly. The report labels the
same-session rereading accurately; no independent worker review is claimed.

Compared the retained returned packet with current main: only lean and stmt_deps
differed. Refreshed the node from current main, preserving all current fields
except the authorized lean attachment and added definition dependencies.
The proof dependency AdequateModuliTopologicalImages has landed since the
returned packet; its module is now included as a nonpublic proof import.
The mathematical statement, all hypotheses, both conclusions, and proof plan
are unchanged. No new nodes or dependency-module repairs are needed.
