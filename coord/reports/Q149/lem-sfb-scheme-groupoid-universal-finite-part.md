## Worker report

The module `Sheaf.AlgebraicGeometry.SchemeGroupoidUniversalFinitePart` states
`AlgebraicGeometry.exists_schemeGroupoidUniversalFinitePart`. Its sole theorem
has proof `sorry`. No theorem was proved, no object was chosen from a postponed
existence theorem, and the item's statement and dependencies are unchanged.

The two auxiliary declarations belong to this theorem's own conclusion:
`SchemeGroupoidFinitePartContains` is explicit factorization through an open
subscheme of a fibre product, and `SchemeGroupoidUniversalFinitePart` packages
the quantified output data and properties. They do not introduce a second
notion of groupoid, open immersion, finite morphism, or finite locally free
morphism. All three declarations are listed in `lean.declarations`.

Hypotheses, individually:

- `S U R : Scheme.{u}` are the base, objects, and arrows in the chosen universe.
  `b : U ⟶ S` supplies the structure morphism; the arrow structure is `s ≫ b`.
- `s t e i c` have the node's exact domains, including `pullback s t` for
  composition. `hG : IsGroupoidScheme s t e i c` uses the recorded dependency
  definition, with the convention `c(a,b) = a ∘ b`.
- `hS : s ≫ b = t ≫ b` makes this a groupoid over S. Together with the
  groupoid identities, this says that all the displayed maps are S-maps;
  no separately supplied arrow-base map or compatibility assumption is needed.
- `[IsSeparated s] [IsSeparated t]` mean precisely closed-immersion diagonals.
- `[Flat s] [Flat t]` are the two flatness hypotheses.
- `[LocallyOfFinitePresentation s] [LocallyOfFinitePresentation t]` are the two
  local finite-presentation hypotheses. There is no affine, quasi-finite,
  finite-inertia, or pointed-stabilizer hypothesis.

Conclusions, clause by clause:

- The theorem quantifies existence of a structure with `M : Scheme.{u}` and
  `g : M ⟶ U`. Its base map is `g ≫ b`. `separated` and `etale` give exactly
  the two properties asserted of g.
- A family `(a,Z)` is represented literally by `a : T ⟶ U` and
  `Z : (pullback s a).Opens`. The premises of `represents` are finiteness of
  `Z.ι ≫ pullback.snd s a` and factorization of the unit section.
- `represents` gives a unique `m : T ⟶ M` with `m ≫ g = a` and equality of
  the selected open family with the pullback of W, tested on every scheme H
  and every pair `(r,h)`. This is the natural representing bijection, rather
  than arbitrary nonempty sets of correspondences. Conversely, pulling W
  back along any m gives such a finite family containing the unit, by
  stability of finite morphisms and factorization under base change. The
  uniqueness statement therefore is equivalent to the advertised bijection.
  The equivalence is natural since its comparison is stated after every
  precomposition h. Restricting these classifiers to S-maps gives
  `Mor_S(T,M)`; indeed `m ≫ g = a` gives the S-map equation for such a.
- `W` is the universal open, and `closed : IsClosed W.carrier` makes it
  closed as well. The arrow scheme Q is exactly `W.toScheme`. Its finiteness
  over M is included in `source_finiteLocallyFree`.
- `contains_unit` requires the section `(g ≫ e,1)` to factor through W.
  `SchemeGroupoidFinitePartContains` is an existential morphism into the
  open subscheme, with both projection equations, not merely pointwise
  topological membership. Thus Q-points are exactly the triples described
  in the node; uniqueness of the lift follows because an open inclusion is
  a monomorphism. The `represents` comparison states that its pullback at
  the classified pair is the given Z as an open subscheme.
- The source is exactly `W.ι ≫ pullback.snd s g`. `target_arrow` says its
  target's first coordinate is `t(z)`. `translated_target`, quantified over
  all further test changes H→T, identifies the source selected open with
  the target selected open by `r ↦ c(r,i(z))`. The morphism v encodes the
  compatible pair into `pullback s t`; its second projection is exactly
  `i(z)`. The original groupoid identities make this translation an
  isomorphism with inverse `r ↦ c(r,z)`. This supplies the whole translated
  subscheme, not just its geometric points.
- `unit`, `inv`, `comp` and `groupoid` give morphisms with the recorded
  groupoid laws on every test scheme. `unit_arrow`, `inv_arrow` and
  `comp_arrow` give their displayed arrow formulas; the groupoid identities
  fix their source objects as in the node. Thus the formulas also determine
  their triples, including the translated object for inversion.
- `over_base` makes the resulting groupoid an S-groupoid.
- `source_finiteLocallyFree` and `target_finiteLocallyFree` use the recorded
  `Scheme.Hom.IsFiniteLocallyFree`, with no fixed positive degree.
- The morphism of groupoids to (U,R) has object map g and arrow map
  `W.ι ≫ pullback.fst s g`. Source compatibility is the defining pullback
  equation; target, unit, inverse, and composition compatibility are the
  explicitly listed fields. The composition field permits every hR; it
  is nonvacuous because hQ, the source equation, and target_arrow imply hR.
- The restricted relation is written `(R ×[s,U,g] M) ×[t,U,g] M`, with
  arrow, source, target coordinates; permuting the coordinates identifies
  it with the node's `M ×[g,U,s] R ×[t,U,g] M`. `j_fst` and `j_snd` specify
  the induced map, and `openImmersion : IsOpenImmersion j` is its open
  immersion property. Its object map is the identity of M. Because the
  restricted operations retain endpoints and use the original arrow
  operations, the preceding identities also say precisely that j respects
  all groupoid operations. No independent restricted structure is chosen.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.GroupoidScheme`: `AlgebraicGeometry.IsGroupoidScheme`,
  including all eleven fields and its pointwise composition convention.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `IsSeparated` (closed diagonal).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, and `pullback.lift`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` (finite, flat, lfp).
- `def-weil-size-convention` is metatheoretic and represented by explicit u;
  there is no Lean object or required module for that node.

The proof-only module `Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties`
is imported privately; its recorded theorem was read. The etale composition,
base change, separated base change, open immersion base change, and section
clopen-immersion inputs are Mathlib matches in the imported morphism modules
and `Mathlib.AlgebraicGeometry.Morphisms.FlatMono`. The two proof prerequisites
`lem-sfb-section-marked-finite-parts-scheme` and
`lem-sfb-universal-finite-parts-groupoid` have no Lean records in the base and
are not imported: they are future proof inputs, not missing statement notions.
Their statements and source were read, and the four-step proof is retained in
the theorem's docstring. No dependency interface repair is necessary.

Edge cases checked before writing:

- Empty U and R: no nonempty assumption is present; the representing scheme
  and universal arrow scheme may be empty. Empty test schemes are included.
- A trivial groupoid has M=U and Q=U. The classifiers and formulas reduce to
  identity maps; no artificial extra family is introduced.
- The constant two-element group over a field has two finite parts containing
  the identity, giving two object components and three arrows. In particular
  neither M nor Q is incorrectly equated to U or R.
- For G_m over a field there are no nonempty finite open source fibres, so
  M and Q can be empty although U is not. No surjectivity of g is asserted.
- Nonreduced and disconnected test schemes are included. Subfunctor equality
  is checked on all schemes, avoiding an incorrect geometric-point-only test.
- Finite locally free allows degree zero on empty components; no degree or
  rank constraint is imposed. All schemes and every test scheme use the same
  explicit universe u; there is no smaller test universe or independent bound.

Searches for an existing declaration (2026-10-24):

- msearch leanfinder: “Universal finite parts of a scheme groupoid represented
  by a separated etale scheme with a finite locally free universal groupoid”:
  eight hits on Scheme.Etale and etale sites; none is this construction.
- msearch loogle: `"Scheme", "Groupoid"`: zero hits.
- msearch grep: `finite.part|finitePart|finite.*subgroupoid`, AlgebraicGeometry:
  zero Mathlib hits.
- msearch leansearch: “Universal finite open parts of a scheme groupoid with
  translation on source fibres”: eight hits on universally open maps, affine
  covers, manifold structure groupoids, and affine opens; no match.
- rg in lean/WeilConjectures and lean/Sheaf for `FiniteParts`, `finitePart`,
  `SectionMarked`, and `UniversalFinite`: only unrelated finite-parts trace
  presentations, quasi-finite splitting, finite-open sheaf comparison maps,
  and rank-one character constructions. rg for the exact node id in
  lean/WeilConjectures found no declaration.
- `tools/blueprint_refs.py search 'finite part'` returned fourteen unrelated
  finite-partition blueprint nodes. DAG search found the item's two existing
  proof prerequisites but no separate definition node for the output package.
  The helpers here merely spell out this item's own statement, as permitted
  by the missing-helper rule; no independent new definition node is needed.

Source read: `literature/stacks-project/spaces-more-groupoids.tex`, Tags 04RI,
04RR, the entire finite-part-groupoid construction and Tag 04RU, and the first
paragraph of the proof of Tag 0DTC. No statement fault or correction was found.
No STATEMENT-DISPUTED flag is raised. The inherited null blueprint ancestor is
an existing metadata fault noted by the stage-1 reviewer, unchanged here.

Validation: scompile.py compiled both its sandbox form and library module
successfully. A first compile required replacing an ambiguous scheme-to-type
coercion by `W.carrier`; the final compile has no errors or warnings. All Lean
lines have at most 98 characters. All variables and the universe are explicit.

## Second reading by Q149

The dispatcher explicitly prohibits starting other agents and supplies no
second reader. This section records a second verification pass by the same
worker, not an independent review; the maintainer supplies the independent
reading requested in the assignment.

Re-read the source, node, and final declaration against the mapping above.
Checked composition order, source versus target endpoints, the inverse in the
translation formula, and the all-test-scheme factorization in represents and
translated_target. Checked that the classifier supplies all finite open
families, that it is unique, and that every pullback of W is finite and contains
the unit. Checked that the inverse and unit formulas are fixed by their arrow
formulas and groupoid source identities, rather than unconstrained maps.
Checked that j retains both endpoint objects, that its target is the whole
restricted relation, and that the asserted open immersion is on that map.
No mathematical mismatch was found. The only edit from compilation was the
explicit carrier coercion in the closedness field. No additional theorem or
helper data uses sorry; only the named existence theorem is postponed.
