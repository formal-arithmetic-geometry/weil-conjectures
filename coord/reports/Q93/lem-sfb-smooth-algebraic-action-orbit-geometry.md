## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothAlgebraicActionOrbitGeometry` states
`AlgebraicGeometry.smooth_algebraic_action_orbit_geometry`. Its sole postponed theorem
has the twelve-step natural-language DAG proof in its docstring. The two concrete helpers
`SmoothActionOrbit.orbitArrow` and `SmoothActionOrbit.support` are respectively the composite
of the pairing `(id_G, x)` with the given action and the range of its underlying point map.
They belong to this node's own orbit construction. No definition has postponed data.

The node is unchanged except for `lean`. There are no new nodes or dependency repairs.
The hypotheses and conclusions are rendered as follows.

| Node text | Lean rendering |
| --- | --- |
| Algebraically closed field F | `{F : Type u} [Field F] [IsAlgClosed F]` |
| G is a group scheme over F | `G : Over (Spec (.of F))`, `[GrpObj G]` |
| G is smooth and of finite type | `[Smooth G.hom]`, `[LocallyOfFiniteType G.hom]`, `[QuasiCompact G.hom]` |
| X is a finite-type F-scheme | `X : Over (Spec (.of F))`, `[LocallyOfFiniteType X.hom]`, `[QuasiCompact X.hom]` |
| Action with its unit and multiplication identities | `[ModObj G X]`; its `smul`, `one_smul`, `mul_smul` are exactly those data and identities |
| x ranges over X(F) | `x : 𝟙_ (Over (Spec (.of F))) ⟶ X`; this tensor unit is `Spec F` over itself |
| b_x(g)=gx | `SmoothActionOrbit.orbitArrow x` |
| Scheme-theoretic stabilizer G_x | The family `H`, inclusion `j`, and `IsPullback (j x).left (H x).hom (orbitArrow x).left x.left` specify exactly the fibre over x, uniquely up to the unique isomorphism commuting with the projections |
| Closed finite-type subgroup | `∃ (_ : GrpObj (H x)), IsMonHom (j x) ∧ IsClosedImmersion (j x).left` (reviewer fix) and the locally-finite-type/quasi-compact structure map clauses |
| Locally closed image | `IsLocallyClosed (support x)` |
| Reduced induced orbit scheme | `IsImmersion (i x).left`, `IsReduced (O x).left`, and `Set.range (i x).left = support x` |
| Canonical in every suitable open | For every open `U` containing the support and closed inverse image, there is `f : (O x).left ⟶ U.toScheme` over X, with `IsClosedImmersion f`, kernel exactly `Scheme.IdealSheafData.vanishingIdeal` of that closed subset, and the unique isomorphism with its existing reduced induced closed subscheme |
| Smooth finite-type orbit | `Smooth (O x).hom`, `LocallyOfFiniteType (O x).hom`, `QuasiCompact (O x).hom` |
| G-stability as a subscheme | `∃ (_ : ModObj G (O x)), IsModHom G (i x)`; this supplies the actual restricted algebraic action and equivariance |
| Orbit map factors | `β x ≫ i x = orbitArrow x` |
| Flat surjective locally finitely presented orbit map | `Flat (β x).left`, `Surjective (β x).left`, `LocallyOfFinitePresentation (β x).left` |
| Geometric fibres are translates of the base-changed stabilizer | For every algebraically closed extension E and E-point y of O, there is a lift h with `h ≫ β x = y`, and a scheme isomorphism from `(H x) ×_F Spec E` to the fibre `pullback (β x).left y.left`. The first projection of its hom is explicitly the multiplication `h s`; the second projection is the projection to Spec E. This is a translation, not merely an abstract isomorphism of schemes |
| G(E) is transitive on O_x(E) | For all E and all `y z` over E, there is `g` with `g • (y ≫ i x) = z ≫ i x`; the immersion identifies this with equality on the orbit |
| O_x(F) is the rational orbit | The displayed equivalence between factoring through `i x` and having the form `g • x` |
| Rational orbits partition X(F) | Every y factors through some `i x`, and the ranges of the induced maps on F-points are equal or disjoint |
| Supports coincide or are disjoint | The final `support x = support y ∨ Disjoint (support x) (support y)` |
| Equidimensionality | Every `C ∈ irreducibleComponents (O x).left` has `topologicalKrullDim C = topologicalKrullDim (O x).left` |
| Dimension formula | Natural numbers d,e give `dim O = d`, `dim H = e`, `dim G = d+e`. For these nonempty finite-dimensional schemes this is equivalent to `dim O = dim G - dim H`. Using this additive form avoids any convention about subtraction at minus infinity |
| Closure and boundary invariant | Reduced closed immersions `iz : Z ⟶ X`, `ib : B ⟶ X` have exactly the closure and closure-minus-support as ranges, and each has an actual `ModObj` action making its inclusion equivariant. Reduced closed immersions with these supports are the canonical reduced induced subschemes |
| Strictly smaller boundary orbits | `support y ⊆ closure (support x) \\ support x → topologicalKrullDim (O y).left < topologicalKrullDim (O x).left` |
| Connected G gives irreducible orbit | `ConnectedSpace G.left → IrreducibleSpace (O x).left` |
| No affine/connected/separated/reduced restrictions | No such binder is present; connectedness occurs only in the final implication. In particular no reducedness of H is imposed |

Dependency declarations used, with their actual defining modules:

- `Field`, `Mathlib.Algebra.Field.Defs`; `IsAlgClosed`, `Mathlib.FieldTheory.IsAlgClosed.Basic`
  (the algebraic-closure node's recorded match explicitly includes this notion).
- `CategoryTheory.GrpObj`, `Mathlib.CategoryTheory.Monoidal.Grp`, specialized to
  `Over (Spec (.of F))` as prescribed by `def-sc-group-scheme`.
  The stabilizer is a closed subgroup scheme through a homomorphism (`IsMonHom`, recorded
  by `def-sc-group-scheme`) which is a closed immersion; the class
  `AlgebraicGeometry.IsClosedSubgroupScheme` belongs to the uncited node
  `def-sc-group-scheme-subgroup` and is not used (reviewer fix).
- `AlgebraicGeometry.Smooth`, `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`; finite type is their
  conjunction, as the recorded dependency explains.
- `AlgebraicGeometry.Scheme`, `Mathlib.AlgebraicGeometry.Scheme`.
- `CategoryTheory.Limits.pullback`, `.fst`, `.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; `IsPullback` specifies
  the universal property independently of a choice of pullback.
- `AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`,
  `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`; its actual construction is
  the existing `vanishingIdeal` and `.subscheme`, reused in the canonical-open clause.
- `AlgebraicGeometry.Flat`, `Mathlib.AlgebraicGeometry.Morphisms.Flat`.
- `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `topologicalKrullDim`, `Mathlib.Topology.KrullDimension`.
- `ConnectedSpace`, `Mathlib.Topology.Connected.Basic`.
- `CategoryTheory.ModObj`, `Mathlib.CategoryTheory.Monoidal.Mod`, with the existing
  Cartesian action on hom types from `.Cartesian.Mod`; `.Cartesian.Grp` gives multiplication
  of G-valued test points. No second definition of scheme actions or stabilizers is introduced.

All recorded proof-dependency modules are imported privately; statement dependencies are
public imports. The proof leaf `lem-wf-affine-constructible-open` currently has no recorded
module, so no proof import can yet be supplied for that node. No import cycle was introduced.

Edge cases checked before writing and again in the second pass:

- Empty X: the type of F-points is empty, all indexed families and clauses are vacuous;
  no nonemptiness assumption is added. G itself always has its identity.
- The trivial group, zero-dimensional orbits, and empty boundary: the dimension formula
  admits d=0; the boundary-orbit implication has no witness when the boundary is empty.
- Disconnected G: equidimensionality concerns all components, not irreducibility;
  irreducibility is conditional on connectedness.
- Nonaffine G and nonseparated/nonreduced X: `Over`, `GrpObj`, `ModObj`, immersion and
  finite-type predicates do not impose any of those excluded assumptions.
- In positive characteristic, the translation fibre retains the full stabilizer scheme,
  including nilpotents. Neither `Smooth β` nor `IsReduced H` is asserted. The Frobenius
  action of G_m on G_m, with stabilizer μ_p, is therefore included.
- E=F and arbitrary algebraically closed extensions are quantified with their algebra maps.
  Test fields live in the ambient scheme universe u, as do all schemes and the base field;
  no separate smaller test universe or condition excluding the identity extension is used.
- Stabilizer and orbit witnesses are universally characterized, not definitions extracting
  arbitrary data from a `sorry` existence theorem. All actual definitions are composites/ranges.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Smooth group scheme acts on finite type scheme locally closed smooth orbits flat orbit map stabilizer dimension"`:
  eight hits, all about smooth morphisms/loci; no orbit-geometry statement.
- `msearch.py ... loogle "CategoryTheory.GrpObj, AlgebraicGeometry.SchemeAction"`:
  zero hits; unknown identifier `AlgebraicGeometry.SchemeAction` (that is a project namespace,
  not a Mathlib declaration).
- `msearch.py ... grep "SchemeAction|orbitMap|stabilizer" AlgebraicGeometry`:
  zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for group actions, orbit maps and
  stabilizers found `SchemeActionTorsorGroupoids`, `GroupSchemeLinearization` and
  `AffinePGLQuotientOrbitTopology`. Read those interfaces: they supply action groupoids,
  linearizations/stability and affine PGL quotient geometry, not this theorem. In particular
  the linearization stabilizer is an equalizer description of the same geometric notion;
  this delivery does not create a competing stabilizer definition.
- `rg` for the item's exact id in both Lean roots found no declaration.
- `rg` for `orbitArrow|SmoothActionOrbit|smooth_algebraic_action_orbit_geometry` in Mathlib,
  both project Lean roots, and `dag/lean_names_upstream.json` found no name collision.
- Read the node, every statement dependency's full statement and binding, and the defining
  source declarations/docstrings. Read Milne pp.27 and 139–140 via `pdftotext`, and the current
  blueprint unit `_section.md`: this item is a supporting orbit lemma, not the unit statement.

No statement fault or STATEMENT-DISPUTED issue was found.

## Second reading by Q93

A separate clause-by-clause reread of the node and the completed Lean file checked every row
above. This is a self-review; the dispatcher explicitly forbids starting another agent, and
the maintainer supplies the independent review after delivery. No independent worker review
is claimed here.

The second pass checked in particular the order of the stabilizer pullback square, the actual
left-translation formula on the entire stabilizer (including nilpotents), and the second
projection fixing Spec E. It checked that the open-subscheme clause uses the vanishing ideal
and its unique isomorphism, and that invariance is an internal scheme action with equivariant
inclusion, rather than invariance of rational points alone. The rational partition includes
coverage and equal-or-disjoint images, and the corresponding support statement is separate.
The finite additive dimension equation is equivalent to the requested subtraction formula.
No mathematical statement changed. Compiler feedback required explicit arguments on
`ModObj.smul` and the Cartesian group import plus its existing `MonObj` scope for multiplication on test points.

## Maintainer review fix (independent reader, 2026-10-25)

The stabilizer clause used `AlgebraicGeometry.IsClosedSubgroupScheme`, the declaration of the
DAG node `def-sc-group-scheme-subgroup`, which is not in the item's `stmt_deps` (H2). It is
replaced by the equivalent inline `IsMonHom (j x) ∧ IsClosedImmersion (j x).left` (a closed
immersion is a monomorphism, so the maps on points are injective, which is the remaining field
of `IsSubgroupScheme`), and the import `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`,
then unused, is removed. No other change.
