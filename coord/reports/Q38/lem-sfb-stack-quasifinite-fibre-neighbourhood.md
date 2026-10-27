## Worker report

The module `Sheaf.AlgebraicGeometry.StackQuasiFiniteFibreNeighbourhood` states
`CategoryTheory.exists_open_locallyQuasiFinite_of_field_fibre_dimension_zero`, with
one `sorry` and no new definitions. It formalizes Stacks 06ME, read in
`literature/stacks-project/stacks-morphisms.tex`, lines 4034–4066. The node statement
is unchanged. There is no statement dispute or correction.

Hypothesis and conclusion correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}`. The explicit universes `u v w`
  retain the scheme universe and independent stack morphism/object universes. This
  realizes the size convention without imposing an equality of these universes.
- The algebraic stack is `X : BasedCategory.{v, w} (Over S)` with
  `hX : IsAlgebraicModuliStack X`. This is precisely the existing etale-stack,
  algebraic-space-diagonal, smooth-surjective-atlas predicate.
- The source algebraic space is `A : AlgebraicSpace S`. Its morphism to the stack
  is `h : BasedFunctor (discreteModuli A.obj.obj) X`, retaining the groupoid maps
  and automorphisms rather than using a coarse point set.
- Local finite type is `hft : ModuliSpaceTest @LocallyOfFiniteType h`. This existing
  predicate says every scheme 2-base change has an algebraic-space presentation,
  and every representable etale scheme chart of that presentation has a locally
  finite type composite to the test scheme. Representability here follows from
  the algebraic-stack diagonal and a space source, as in the node; it is not an
  added geometric hypothesis.
- The field is `(k : Type u) [Field k]`. Its specified base structure is
  `s : Spec (CommRingCat.of k) ⟶ S`, and the field-valued object is the based
  functor `a` from `discreteModuli (yoneda.obj (Over.mk s))` to `X`.
- The displayed fibre `F = A ×_X Spec k` and its projection are rendered by
  `F : AlgebraicSpace S`, `p : F.obj.obj ⟶ A.obj.obj`, and the based equivalence
  `e : discreteModuli F.obj.obj → moduliTwoFiberProduct h a`, with
  `he : e.toFunctor.IsEquivalence`. The hypothesis `hp` identifies the composite
  with `moduliTwoFiberFst h a` with `discreteModuliMap p` by a vertical 2-iso.
  Thus `p` is the actual source projection, not an arbitrary map. The other
  projection is retained by `e` through the second component of the 2-fibre
  product. Quantifying over presentations renders the given fibre diagram;
  every actual fibre has such an equivalence, and changing it changes no claim.
- The point is `z : Point F.obj.obj`, the existing common-field-extension quotient.
  The zero-dimensional hypothesis is `hz : etaleLocalDimension F.obj.obj z = 0`.
  This is the existing supremum of the common local dimensions on etale charts;
  each scheme local dimension is the infimum over open neighbourhoods. For an
  algebraic space all chart lifts agree, exactly as the node specifies.
- The required open subspace is `∃ V : OpenSubspace A`. This existing subtype
  consists of subfunctors whose inclusions are representable by scheme open
  immersions after every scheme base change.
- Containing the projected point is `mapPoint p z ∈ pointImage V.val.ι`, using the
  existing induced map on point classes and image of an inclusion.
- The restricted map is `(discreteModuliMap V.val.ι).comp h`; its local
  quasi-finiteness is `ModuliSpaceTest @Scheme.Hom.IsLocallyQuasiFinite` of that
  map. The scheme predicate is the recorded Stacks 01TD predicate, including
  local finite type, not Mathlib's weaker isolated-fibres-only predicate.
- No Noetherian or quasi-compactness assumption, atlas choice, surjectivity of
  `h`, separatedness, characteristic restriction or algebraic closure is added.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.discreteModuli`, `discreteModuliMap`, `moduliTwoFiberProduct`,
  `moduliTwoFiberFst`, `ModuliTwoIso`. Their complete generic signatures and
  docstrings were read. The unrelated stable-curve declarations are not used.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsEtale`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `Mathlib.Algebra.Field.Defs`: `Field`.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `Scheme.Hom.IsLocallyQuasiFinite`, `IsQuasiFiniteAtPoint`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion` (through the
  existing open-subspace predicate).
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`:
  `CategoryTheory.ModuliSpaceTest`. This predicate is generic in based categories
  and does not assume the stack is DM.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`:
  `AlgebraicGeometry.AlgebraicSpace.OpenSubspace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleDimension`:
  `AlgebraicGeometry.AlgebraicSpace.etaleLocalDimension`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`:
  `AlgebraicGeometry.AlgebraicSpace.mapPoint`, used only as the generic point map;
  no curve hypothesis is imported into the statement.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicGeometry.AlgebraicSpace.pointImage`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`:
  `AlgebraicGeometry.AlgebraicSpace.Point`; this is a direct statement dependency because
  the theorem binds `z : Point F.obj.obj` explicitly. The same declaration is also
  used by the existing dimension and point-topology constructions.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`,
  used by the existing etale local dimension.

The six already landed definition nodes owning the chartwise stack test, field-valued
point classes, open subspaces, etale dimension, point map, and point image are added
to `stmt_deps`. The point-class node is included directly because `Point` occurs in
the theorem signature, rather than relying on transitive reachability.
No missing notion or unusable dependency requires a new or repaired node.

All stated proof dependency modules are imported privately: chartwise stack
calculus; representable local-quasi-finite calculus; scheme etale source locality;
space fibre products and etale covers; relative-dimension-zero criterion;
Mathlib scheme coproducts; and local topological dimension. The still unstated
proof nodes (space-source representability, source-local locus descent, space
quasi-finite open locus, etale local dimension preservation) are named in the
proof docstring but have no module to import. They are proof prerequisites, not
notions needed to type this statement.

Edge cases checked before writing: if `A` or `F` is empty there is no `z`, so the
statement makes no false existence claim; empty opens remain available although
the containing-point condition excludes them here. If `h` is an identity or
already locally quasi-finite, the whole source is a possible answer. Positive-
and zero-characteristic fields, nonclosed field-valued points, nilpotents, and
non-Noetherian/non-quasi-compact sources are all allowed. Dimension zero is
local dimension at `z`, not zero global dimension of the entire fibre. Arbitrary
presentations of the fibre are retained, including the identity presentation.
The point containment is on `p(z)` and does not ask for a section of `p` or for a
rational lift to the chosen field. No classically chosen fibre map is introduced.

Searches for an existing statement and notions (2026-10-24):

- `msearch.py ... leanfinder "locally finite type algebraic stack morphism zero
  dimensional field fibre point locally quasi finite open neighbourhood"`:
  eight scheme-level hits, including Mathlib `LocallyQuasiFinite` and
  `LocallyOfFiniteType`; none states 06ME for algebraic stacks.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite,
  topologicalKrullDimAt"`: no hit; service does not index the project predicate.
- `msearch.py ... grep "quasi.*[Ff]inite.*(fibre|fiber|[Nn]eigh)|[Dd]im.*[Aa]t.*[Pp]oint"
  AlgebraicGeometry`: six hits in scheme QuasiFinite and ZariskisMainTheorem,
  none for algebraic stacks.
- `msearch.py ... leansearch "algebraic stack locally finite type zero dimensional
  fibre point quasi finite neighbourhood"`: eight scheme/ring-level hits; none
  is the item.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  quasi-finite fibre/neighbourhood patterns: related scheme and ring criteria,
  no existing item declaration. Name collision search in those trees, Mathlib,
  and `dag/lean_names_upstream.json`: no hit for the chosen theorem name.
- Concept/signature searches in `lean/Sheaf/AlgebraicGeometry` found all the
  existing point classes, point maps and images, open subspaces, chartwise
  predicates, and dimension definitions listed above; their owning DAG nodes
  were located and read rather than creating duplicate notions.

## Second reading by Q38

A separate self-audit reread the node, Stacks 06ME, and final signature clause by
clause. The current dispatcher explicitly prohibits starting other agents; this
section records a self-audit, not an independent second worker. The maintainer's
independent review remains required. The audit checked especially that the
source projection is fixed by `hp`, that the field need not be algebraically
closed, that `ModuliSpaceTest` imposes no DM assumption, that local dimension is
not replaced by global dimension, and that the conclusion is an open subspace
of `A` containing `p(z)`. No mismatch was found. No statement correction, new
definition, extra geometric hypothesis or weakening was made.

## Returned delivery repair

Repaired the H2 return of immutable head `24eff2b88362`: added the landed owner
`def-a1-algebraic-space-point-classes` directly to `stmt_deps`, since the statement
explicitly binds `z : AlgebraicGeometry.AlgebraicSpace.Point F.obj.obj`. Updated
the dependency explanation above. The Lean module and theorem signature are unchanged.
Compared the sandbox node with current main; only the authorized `lean` and
`stmt_deps` fields differ. The delivery wrapper refreshes its base before delivery.
