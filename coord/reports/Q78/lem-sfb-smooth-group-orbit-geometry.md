## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SmoothGroupOrbitGeometry` states
`AlgebraicGeometry.exists_smooth_group_orbit_geometry`. Its only postponed proof is
this theorem, matching the assigned DAG node; no definition or additional theorem is added.
The original statement and all dependency lists are unchanged.

Source checked: [Milne, Algebraic Groups, 2022 corrected text](https://www.jmilne.org/math/Books/iAG2022.pdf),
printed pp.139–140, Propositions 7.4–7.6 and the preceding orbit/stabilizer definitions;
printed p.104, Proposition 5.23; pp.141–142, Propositions 7.11–7.12.

Clause-by-clause rendering:

- The field is `{k : Type u} [Field k] [IsAlgClosed k]`. Mathlib's `IsAlgClosed`
  says every polynomial splits; its docstring and `IsAlgClosed.exists_root` identify this
  with the node's nonconstant-polynomial-root formulation.
- The group over k is `G : Over (Spec (.of k))` with `[GrpObj G]`. Its affineness,
  smoothness, connectedness and finite type are `[IsAffine G.left]`, `[Smooth G.hom]`,
  `[ConnectedSpace G.left]`, and `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`.
  `IsAffine` is Mathlib's affine scheme notion, hence a spectrum of a commutative algebra.
- The scheme over k and its separatedness and finite type are `X : Over (Spec (.of k))`
  with `[IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]`.
- The scheme action and its two identities are `[ModObj G X]`: its `smul` is a morphism
  of k-schemes on the fibre product, with `one_smul` and `mul_smul` as the unit and
  multiplication laws. This is the existing Mathlib notion, with no duplicate action def.
- The rational point is `x : 𝟙_ (Over (Spec (.of k))) ⟶ X`. The tensor unit of this
  slice category is Spec k with its identity structure map.
- The closed stabilizer is the existential group object `K` and inclusion `i`, with
  `IsClosedSubgroupScheme i`. The universal condition for every `T` and `g : T ⟶ G`
  says exactly that factoring through i is equivalent to fixing `toUnit T ≫ x`.
  Factorizations are automatically unique because a closed immersion is mono. This
  characterizes the full scheme-theoretic stabilizer, including infinitesimal test points.
- The orbit O and immersion j are existentially specified by `IsReduced O.left`,
  `IsImmersion j.left` and equality of its underlying range to that of
  `lift (𝟙 G) (toUnit G ≫ x) ≫ γ[G, X]`. In Mathlib an immersion has locally closed
  range and is an embedding with surjective stalk maps. A reduced immersion with this
  prescribed range specifies exactly the induced reduced locally closed subscheme.
  `Smooth O.hom` is the asserted smoothness.
- The canonical orbit factorization is `q ≫ j = lift (𝟙 G) (toUnit G ≫ x) ≫ γ[G, X]`.
  Because j is mono this specifies q uniquely. `Flat q.left ∧ Surjective q.left`
  is faithful flatness of the morphism of schemes.
- The dimension formula uses `topologicalKrullDim G.left = topologicalKrullDim K.X.left +
  topologicalKrullDim O.left`, precisely the additive formula printed in Milne 5.23.
  All three schemes here are nonempty and finite type over k: K contains the identity
  and is closed in G, O is the nonempty locally closed image of G. Thus their dimensions
  are finite natural dimensions, and this is equivalent to dim O = dim G - dim K.
  It avoids inventing subtraction on `WithBot ℕ∞` while retaining the full equality.
- The reduced closure Z is specified by `IsReduced Z.left`, `IsClosedImmersion z.left`
  and `Set.range z.left = closure (Set.range j.left)`.
- The reduced boundary B is specified by `IsReduced B.left`, `IsClosedImmersion b.left`
  and range equal to `closure (Set.range j.left) \ Set.range j.left`.
  Because the orbit is open in its closure, this boundary is closed in X.
- Invariance of Z and B is scheme-theoretic: `aZ` and `aB` factor the original action
  after tensoring their respective inclusions with the identity of G. These maps are
  unique because the inclusions are mono. Cancelling the inclusions gives their unit
  and multiplication identities, so this is precisely restriction of the action.
- Every boundary rational point is quantified by `∀ y : 𝟙_ ... ⟶ X` with
  `y.left (IsLocalRing.closedPoint k) ∈ Set.range b.left`. The last inequality is the
  Krull dimension of the range of its orbit map, as a subspace, strictly less than
  `topologicalKrullDim O.left`. This is exactly dim O_y: a reduced locally closed
  orbit has the same topological space as that range. Applying the same universally
  quantified theorem to y supplies its reduced orbit; no separate weaker orbit notion
  or geometric-point-only stabilizer is used.
- All dimensions are Mathlib's `topologicalKrullDim : WithBot ℕ∞`, including dimensions
  of subsets with their induced topology. No reducedness of X or K is assumed.

Dependency declarations read and used:

- `Field` (`Mathlib.Algebra.Field.Defs`), `AlgebraicGeometry.Spec` and `Spec.map`,
  `AlgebraicGeometry.Scheme` and `Scheme.Hom` (`Mathlib.AlgebraicGeometry.Scheme`).
- `CategoryTheory.GrpObj`, with its `MonObj` unit and multiplication and its inverse,
  (`Mathlib.CategoryTheory.Monoidal.Grp`); the assigned group-scheme node's closed
  upstream declarations `CategoryTheory.GrpObj.ker`
  (`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`) and
  `AlgebraicGeometry.Scheme.Hom.finrankΓ`
  (`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`) were read. This statement
  uses the group-object interface itself, via
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, which also supplies
  `AlgebraicGeometry.IsClosedSubgroupScheme`.
- `AlgebraicGeometry.Smooth` (`Mathlib.AlgebraicGeometry.Morphisms.Smooth`).
- `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact`
  (`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `...QuasiCompact`).
- `AlgebraicGeometry.IsSeparated` from the proper-morphism node
  (`Mathlib.AlgebraicGeometry.Morphisms.Proper`, declaration defined in `...Separated`).
- `topologicalKrullDim` (`Mathlib.Topology.KrullDimension`).
- Existing action declaration `CategoryTheory.ModObj` and its functor-of-points action
  (`Mathlib.CategoryTheory.Monoidal.Cartesian.Mod`, core structure in `...Monoidal.Mod`).
- The recorded modules of all available proof dependencies are imported without public
  export. `lem-wf-affine-constructible-open` currently has no recorded declaration or
  Mathlib match, so no proof import can be added for it. It is a proof input, not needed
  to type this statement. No import of the downstream homogeneous orbit quotient theorem
  is used, avoiding a mathematical dependency cycle.

Edge cases checked before drafting and on rereading:

- Empty X has no possible rational point x; it is not excluded by an extra nonempty binder.
- A trivial action has a reduced point orbit, K = G and empty boundary, satisfying the
  dimension formula. The boundary quantification is vacuous when the boundary is empty.
- A smooth connected zero-dimensional G is the trivial group; all its orbits have
  dimension zero and no smaller boundary orbit is forced to exist.
- A nonreduced X is permitted. The orbit and its closure/boundary are reduced induced
  subschemes, not X itself. The theorem has no `[IsReduced X.left]` binder.
- In characteristic p, the p-th-power action of G_m on G_m has stabilizer μ_p and a
  flat surjective orbit map which need not be smooth. No smoothness or reducedness of
  K, or smoothness of q, is asserted or assumed.
- The test schemes T have the same scheme universe u as the ambient slice category;
  this quantifies over every test object of that category, rather than an independent
  universe below k. All universes and variables are explicitly bound, and both forms
  of auto-implicit binding are disabled.

Searches for an existing statement:

- `msearch.py ... leanfinder`: query “A smooth connected algebraic group acting on a
  scheme has smooth locally closed orbits with dimension group minus stabilizer and
  smaller boundary orbits”; eight hits, all unrelated topological covering/action
  results, with no scheme orbit dimension theorem.
- `msearch.py ... loogle`: `GrpObj, AlgebraicGeometry.Smooth, topologicalKrullDim`;
  zero hits, with service diagnostic `unknown identifier 'GrpObj'`. Local source reads
  resolved that identifier and its exact categorical signature.
- `msearch.py ... grep`: `orbit|stabilizer|class ModObj` in
  `CategoryTheory/Monoidal/Cartesian`; zero hits reported by that wrapper.
- Direct `rg` in Mathlib's algebraic geometry and categorical monoidal sources found
  `ModObj`, `GrpObj`, `IsImmersion`, `IsAlgClosed` and the dimension definition; no
  theorem matching the assigned statement.
- Direct `rg` over `lean/WeilConjectures/AlgebraicGeometry`,
  `lean/Sheaf/AlgebraicGeometry` and `dag/lean_names_upstream.json` searched
  orbit/stabilizer and smooth-orbit names. The upstream node-id search returned none.
  `HomogeneousOrbitQuotientGeometry.lean` was read in full: its orbit theorem characterizes
  an fppf quotient and cites this item as an unproved prerequisite; it supplies neither
  the dimension formula nor invariant closure/boundary geometry. The torus filtration
  module was also read to confirm the established `ModObj` action convention.

No node fault, statement correction, new definition node or dependency repair is needed.
No STATEMENT-DISPUTED flag applies.

## Second reading by Q78

A fresh clause-by-clause reread of the node and completed module checked the field,
all five group properties, all three scheme properties, the action laws and rational
point, the full stabilizer test-scheme criterion, reduced locally closed orbit,
smoothness, canonical factorization, flatness and surjectivity, dimension equality,
reduced closure and boundary, both scheme-action factorizations, and every boundary
orbit's strict dimension inequality. The additive formula and subspace representation
of dim O_y are equivalent renderings, justified above; no clause is dropped. No
reducedness of X or K or smoothness of q slipped in. No signature change was necessary.
This is a second pass by the assigned worker; no additional agent was started, as the
explicit dispatcher brief requires. The maintainer's independent review remains separate.

## Validation

The prescribed `scompile.py Q78 lem-sfb-smooth-group-orbit-geometry <module>` compiled
both its isolated sandbox form (20.9 s) and final library module (6.4 s), cleanly,
with no warnings or errors. The declaration proof is exactly `by sorry`.
