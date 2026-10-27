## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothAtlasAutomorphismDiagonalTest` states
`CategoryTheory.unramifiedModuliDiagonal_iff_smoothAtlas_automorphismSpace`, with
its sole proof `sorry`. It introduces no definitions or additional theorems.
The existing inertia construction supplies the precise automorphism-space
presentation without importing the downstream DM-point theorem.

Hypothesis and conclusion correspondence:

- A scheme S is `{S : Scheme.{u}}`. An algebraic stack over S is
  `(F : BasedCategory.{v, w} (Over S)) (hF : IsAlgebraicModuliStack F)`.
  Expanding the recorded predicate gives exactly a category fibred in groupoids,
  etale stack descent, algebraic-space representability of the diagonal, and
  existence of a smooth surjective scheme atlas. The morphism and object
  universes v,w remain independent of u.
- The scheme P over S and morphism p:P -> F are `(P : Over S)` and
  `(p : BasedFunctor (discreteModuli (yoneda.obj P)) F)`. The hypothesis
  `(hp : IsSmoothModuliAtlas F P p)` says this PARTICULAR map has, for every
  scheme base change, an algebraic-space presentation whose projection is
  smooth and surjective. Smoothness is tested on every representable etale
  scheme chart using `AlgebraicGeometry.Smooth`; surjectivity uses the
  existing joint-surjectivity-on-points convention `SpaceMapIsSurjective`.
- The specified automorphism algebraic space and its projection are
  `(G : AlgebraicSpace S) (π : G.obj.obj ⟶ yoneda.obj P)` and
  `(hG : HasSpaceBaseChange (moduliInertiaProjection F) P p G π)`.
  This is a presentation of the ACTUAL inertia pullback over P, retaining π.
  To check that it says precisely the node's representing property, on a
  scheme V mapping to P an object of that pullback consists of an inertia
  object (x,alpha) and an isomorphism theta:p_V ~ x. Send it to the
  automorphism theta^{-1} alpha theta of p_V. Conversely beta gives
  (p_V,beta,1). Arrows in inertia commute with automorphisms, so this yields
  an equivalence with the discrete groupoid of automorphisms, with unique
  compatible arrows. The formulas commute with restrictions. This is the
  automorphism square in Stacks Tag 050Q. Thus hG introduces exactly the
  assumed representing property, not another restriction or an arbitrary
  map. An algebraic space over S with map to the represented P is exactly
  the data of the algebraic space over P in the node.
- Unramifiedness of the relative diagonal is
  `HasUnramifiedModuliDiagonal F`. Its recorded definition tests two scheme
  maps T,U into F and presents their actual 2-fibre product over T x_S U,
  retaining both projections. These are precisely the diagonal tests;
  arbitrary tests by a common scheme are their pullbacks along the pair
  map to T x_S U. The definition tests etale source charts using the
  recorded scheme-unramified predicate.
- The equivalence is `↔`; its right side is `SpaceMapIsUnramified G P π`.
  This tests every representable etale scheme chart of G, whose composite
  to P must be `IsUnramified`. The target P is already a scheme. Scheme
  base-change stability gives the equivalent source-and-target etale
  testing convention from the node. No implication, hypothesis or clause
  is omitted, and no finite-type, quasi-compactness, Noetherian, field or
  perfectness hypothesis is added.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsModuliStack`, `IsFibredInGroupoids`, `BasedCategory`,
  `ModuliTwoIso`, `moduliTwoFiberProduct`, `HasAlgebraicSpaceDiagonal`,
  `HasSpaceBaseChange`, `discreteModuli`, `SpaceMapIsSurjective`.
  The relevant full signatures and docstrings were read, including the
  equivalence and projection in HasSpaceBaseChange.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale`, and their scheme-test definitions.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified`,
  the conjunction of locally finite type and open-immersion diagonal.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack`, `IsSmoothModuliAtlas`,
  `SpaceMapIsSmooth`.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack`:
  `CategoryTheory.HasUnramifiedModuliDiagonal`, `SpaceMapIsUnramified`.
- `Sheaf.AlgebraicGeometry.ModuliInertia`:
  `CategoryTheory.ModuliInertiaObject`, `moduliInertia`,
  `moduliInertiaProjection`; the latter forgets the actual vertical
  automorphism. Its construction has real data.

The last three existing definition nodes are added to stmt_deps, as permitted
for already landed notions. Existing definition nodes and their Lean records
are unchanged. No new node or dependency repair is needed. In particular the
helper `IsModuliAutomorphismSpace` in `DmPointStabilizer` was inspected (also
via `scompile.py --source`) but is not imported: its owning theorem is a
consumer of this criterion. Using the upstream inertia construction avoids
an import/dependency cycle and an unnecessary duplicate definition.

The stated proof dependency
`Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus` is a plain proof
import. Its recorded theorem and its chartwise/field-lifting conventions
were read. The other four proof-theorem nodes
`lem-sfb-stack-isom-space-locally-finite-type`,
`lem-sfb-space-unramified-permanence`,
`lem-sfb-stack-representable-unramified-descent`, and
`lem-sfb-unramified-pseudo-torsor` have no recorded Lean declaration in the
current DAG, so have no import yet. They are proof prerequisites, not missing
notions required to type this statement. Their seven proof steps and
identifications are retained in the theorem docstring.

Edge cases checked before writing:

- The empty stack and empty scheme atlas are allowed: no Nonempty or
  nonempty-fibre hypothesis occurs. All tests retain their ordinary empty
  cases, and both sides give the expected unramifiedness.
- For a stack represented by a scheme, the automorphism space over the
  atlas is P with identity projection; the relative diagonal of a scheme
  is a monomorphism, hence unramified. The criterion specializes correctly.
- Nontrivial finite etale stabilizers are allowed; the condition is
  unramifiedness, not triviality of automorphisms or monomorphism of F.
- Infinitesimal stabilizers on nonreduced schemes are retained, since hG
  is an equivalence of the actual inertia pullback on all scheme tests,
  not an equality merely on geometric points.
- In the converse Isom_T(a,b) may be empty. The proof uses a pseudo torsor
  and never assumes that a and b become isomorphic on a cover.
- The atlases and test schemes need not be quasi-compact or of finite
  type over S. The local finite type needed for Isom is a proof result,
  not an added hypothesis. Universes u,v,w are explicitly bound and
  autoImplicit is false.

Sources opened: `literature/stacks-project/stacks-morphisms.tex`,
`lemma-diagonal-diagonal` (Tag 0CL0), statement and proof of (4), and
`lemma-inertia` (Tag 050Q), including its cartesian automorphism square.
The node's source-based statement is unchanged. No STATEMENT-DISPUTED
issue was found.

Searches actually run for an existing statement:

- `msearch.py ... leanfinder` with query "An algebraic stack has unramified
  diagonal if and only if the automorphism algebraic space of a smooth
  surjective scheme atlas is unramified" returned eight scheme/ring
  formal-unramifiedness results, no stack/atlas theorem.
- `msearch.py ... leansearch` with query "An algebraic stack has unramified
  diagonal exactly when the automorphism space of a smooth surjective
  atlas is unramified over the atlas" returned eight scheme/ring
  formal-unramifiedness results, no match.
- `msearch.py ... loogle` with query `"Unramified", "Aut"` returned four
  unrelated number-field infinite-place ramification results, no match.
- `msearch.py ... grep` with query
  `AlgebraicStack|ModuliAutomorphism|smooth.*atlas.*unramified` in
  `AlgebraicGeometry` returned zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for algebraic-stack,
  smooth-atlas, unramified-diagonal and automorphism-space names found
  the existing notions listed above, the downstream field-point
  criterion and an etale-atlas criterion, but not this theorem.
  `grep -rn` for this item's id in `lean/WeilConjectures` and `rg` for
  the proposed declaration in `dag/lean_names_upstream.json` found no hit.

Validation: the delivered module compiles through the prescribed scompile.py,
including both its sandbox and intended library module names, with no errors
or unexpected warnings. Dry-run preflight and delivery results follow from
the prescribed deliver2.py invocation.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
