## Worker report

The module Sheaf.AlgebraicGeometry.SpaceProperSupportClosedOperations states
AlgebraicGeometry.AlgebraicSpace.proper_support_closed_operations, with its sole proof
postponed by `sorry`. It renders all three assertions in the unchanged node statement.
No definitions, dependency modules, or new nodes are introduced.

The reduced induced closed structure is introduced by its defining properties, rather
than by a choice of presentation: `R : ClosedSubspace X`,
`IsReduced (R.val : AlgebraicSpace S)`, and
`pointImage R.val.arrow.hom.hom = (T : Set (Point X.obj.obj))`.
The already-stated theorem `exists_unique_reduced_closed_subspace` guarantees exactly
one such subobject for every closed T. These binders therefore mean “let R be the
reduced induced structure on T”; they impose no mathematical restriction on T or X.
This also avoids duplicating the existing scheme-only IsClosedSubsetProperOver or
introducing another algebraic-space construction.

Hypotheses and clauses:

- The base scheme is `{S : Scheme.{u}}`; the two spaces are
  `{X Y : AlgebraicSpace S}`; their arbitrary S-morphism is `(f : X ⟶ Y)`.
- Local finite type on compatible etale scheme charts is exactly
  `hf : MapIsLocally (@LocallyOfFiniteType) f`. There is no Noetherian,
  separatedness, flatness, representability, or finite-presentation assumption on f.
- The point space is the existing `Point X.obj.obj`, carrying its existing
  `pointTopologicalSpace` instance. `TopologicalSpace.Closeds` packages the required
  closed subsets, with no extra restriction on their underlying sets.
- A closed subspace is the existing `ClosedSubspace X`, namely a subobject whose
  arrow is `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)`.
  Its domain is `(R.val : AlgebraicSpace S)` and its inclusion is `R.val.arrow`.
- Reducedness is `AlgebraicSpace.IsReduced`, requiring reducedness of every etale
  scheme chart, as the statement specifies.
- Properness over Y is `MapIsProper (R.val.arrow ≫ f)`. Unfolding the existing
  definition gives a closed relative diagonal, quasi-compactness tested over affine
  schemes, local finite type on etale charts, and closedness on point spaces after
  every algebraic-space base change. This is precisely the four conditions in the
  node, including nonrepresentable proper maps.
- In the first main conjunct, T is an arbitrary closed subset and R its reduced
  induced structure. The first equivalence identifies properness of R -> Y with
  `∃ D : ClosedSubspace X, pointImage ... = T ∧ MapIsProper (D.val.arrow ≫ f)`.
  The second identifies it with `∀ D : ClosedSubspace X, pointImage ... = T →
  MapIsProper (D.val.arrow ≫ f)`. These D are arbitrary closed structures, with
  no reducedness restriction.
- The second main conjunct quantifies closed T and T', with `T' ≤ T`, and their
  respective reduced induced structures R and R'. Its final implication is
  `MapIsProper (R.val.arrow ≫ f) → MapIsProper (R'.val.arrow ≫ f)`.
- The third main conjunct quantifies `n : ℕ` and the family
  `T : Fin n → TopologicalSpace.Closeds (Point X.obj.obj)`. Each member has its
  reduced structure R i and proper composite to Y. For the reduced closed
  structure C on `⋃ i : Fin n, (T i : Set (Point X.obj.obj))`, the conclusion is
  `MapIsProper (C.val.arrow ≫ f)`. The union is closed because the index is finite;
  its reduced structure exists uniquely by the imported existence theorem.

Dependency declarations read and reused:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicGeometry.AlgebraicSpace,
  IsRepresentableWith, and the small etale site underlying reducedness.
- Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology: PointRepresentative.map,
  pointImage, pointTopologicalSpace; Point comes from AlgebraicSpacePointClasses.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace: ClosedSubspace.
- Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace: AlgebraicSpace.IsReduced.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties: MapIsLocally,
  MapIsSeparated, MapIsFiniteType, MapIsUniversallyClosed, MapIsProper.
  MapIsQuasiCompact is the shared definition in ProperCurveModuli.

Only the three already-landed definition nodes def-sfb-space-closed-subspace,
def-sfb-reduced-algebraic-space, and def-sfb-space-morphism-properties are added to
stmt_deps, to cite those notions. Their full source signatures and docstrings were
read. The existing four statement dependencies remain intact.

The module imports the recorded modules of all six currently stated proof dependencies:
ReducedClosedSubspaceSupport, AlgebraicSpacePointOpenCalculus,
SpaceLocalPropertiesChartTest, StackClosedImmersionCalculus,
AlgebraicSpaceCoproduct, and FppfSheafCoproductPartition. The remaining proof dependencies
have no Lean record in the read repository: lem-sfb-space-closed-subspace-proper,
lem-sfb-space-proper-composition, lem-sfb-space-relative-uc-surjection-separated,
lem-sfb-space-thickening-topological-properties, and lem-sfb-stack-finite-type-calculus.
They are named in the complete natural-language proof docstring; no import is invented
for them. None supplies a notion missing from this statement.

Edge cases checked before writing:

- n = 0 is allowed, without Nonempty or positivity assumptions. The indexed union is
  empty, and the reduced structure C is the empty space, proper over every Y.
  The reduced-structure existence theorem prevents a vacuous empty-family reading.
- Empty X, empty T, empty T', empty summands, repeated supports, and T' = T are allowed.
- Arbitrary nonreduced closed structures D are included in both structure-independence
  equivalences. No assertion of reducedness after base change is made.
- The whole construction uses the existing site/space universe u, with no extra equality
  between previously independent universes, coefficient categories, or index sizes.
- No characteristic or Noetherian restriction is introduced. The local finite type
  hypothesis is retained, as the source explicitly warns the equivalence fails without it.

Searches performed:

- msearch.py leanfinder, “Properness of closed subsets of algebraic spaces over a base
  is independent of closed structure and stable under finite unions and smaller closed
  subsets”: eight scheme results, including IsProper, universallyClosed locality,
  isProper_eq, and Scheme.Hom.isProperMap; no algebraic-space statement.
- msearch.py loogle, `AlgebraicGeometry.IsProper, IsClosed`: zero hits.
- msearch.py grep, `AlgebraicSpace|union.*[Ii]sProper|[Ii]sProper.*union|closed.*subset.*proper`
  in AlgebraicGeometry: zero hits.
- msearch.py leansearch, “Closed subsets of algebraic spaces proper over a base are
  independent of closed subspace structure and stable under finite unions”: eight hits
  on finite closed unions and scheme properness/base-change; no exact statement.
- rg in WeilConjectures and Sheaf for IsClosedSubsetProperOver, proper-support names,
  MapIsProper, ClosedSubspace, and reduced induced structures: found the shared notions
  above and the scheme-only ClosedSubsetProperOverBase family; the latter does not
  cover algebraic spaces. Searching the item's id in WeilConjectures found no declaration.
- Searched dag/lean_names_upstream.json and the DAG for the same names and concepts;
  inspected the existing definition nodes above. blueprint_refs.py search for
  “proper closed subset” provided no exact existing statement of this combined item.

Source checked directly: literature/stacks-project/spaces-perfect.tex,
lemma-closed-proper-over-base, definition-proper-over-base,
lemma-closed-closed-proper-over-base, and lemma-union-closed-proper-over-base.
The imported uniqueness theorem uses the reduced induced structure of Tag 047X.
No statement correction or STATEMENT-DISPUTED issue was found.

Validation: scompile.py compiled the sandbox file and its intended library module
successfully (3.3 seconds each), with no errors or unexpected warnings.

## Second reading by Q53

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
