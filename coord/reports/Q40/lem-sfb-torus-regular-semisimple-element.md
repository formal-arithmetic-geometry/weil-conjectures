## Worker report

This stage-2 delivery states Milne's regular torus element lemma as
`AlgebraicGeometry.torus_exists_semisimplePoint_centralizer` in
`Sheaf.AlgebraicGeometry.TorusRegularSemisimpleElement`. Its only theorem proof is
`sorry`. Its docstring contains all five steps of the accepted split, including
the invertible scalar block calculation over arbitrary algebras. The new module
`Sheaf.AlgebraicGeometry.SemisimpleGroupSchemePoint` supplies the missing predicate
`AlgebraicGeometry.IsSemisimpleGroupSchemePoint` with an actual Prop-valued definition.
No proof or data construction is replaced by a hypothesis.

The inherited ending referred to a stage-1 refusal to re-split an accepted node.
The current brief-stage2.md §0 explicitly distinguishes that refusal from stage 2.
The current item has no Lean record and its queue entry is stage 2. I preserve its
accepted statement and proof, adding only its Lean attachment and three statement
dependencies: the two already landed terminology nodes and the new definition.
No released repair note for this item was present.

Hypotheses and conclusions, clause by clause:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- `G T : Grp (Over (Spec (.of k)))` supplies the two group schemes, with their
  multiplication, inverse and unit and the corresponding groups of points.
- Each group's affineness is `[IsAffine ...X.left]`. Finite type is
  `[LocallyOfFiniteType ...X.hom] [QuasiCompact ...X.hom]` for both G and T.
  These retain exactly the node's standing affine finite-type convention.
- Smoothness and connectedness of G are `[Smooth G.X.hom]` and
  `[ConnectedSpace G.X.left]`. There is no characteristic restriction.
- `i : T ⟶ G` is a bundled group-scheme homomorphism;
  `hi : IsClosedSubgroupScheme i.hom.hom` gives the closed subgroup inclusion.
- `hT : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus k r)` says that T
  is isomorphic over k, as a group scheme, to the rank-r product of G_m.
  It uses the existing splitTorus construction, including its rank-zero clause.
  This is precisely the item's definition of torus, without replacing it by a
  separate geometrically split predicate or fixing an isomorphism as extra data.
- `∃ s : StandardGroupSchemes.affine k k ⟶ T.X` is the single T(k)-point chosen
  before the test algebras. Its image in G(k) is `s ≫ i.hom.hom`.
- `IsSemisimpleGroupSchemePoint G.X (s ≫ i.hom.hom)` is the semisimplicity clause.
  Its definition tests every finite index type `ι : Type u`, every rational
  representation `GeneralLinearGroup.RationalHom G ι`, and its `IsMonHom`
  instance. It asserts `P⁻¹ * ρ_k(s) * P = Matrix.diagonal d` for an invertible
  matrix P and diagonal entries d. `GeneralLinearGroup.homMulEquiv` reads the
  representation's point as its matrix. Choosing a basis identifies every
  finite-dimensional vector space with k^ι, so this tests exactly the algebraic
  representations in the item, rather than arbitrary abstract group actions.
  The empty finite index type is included. Larger presentations of finite
  vector spaces give the same predicate by transport along a finite basis.
- `∀ (A : Type u) [CommRing A] [Algebra k A] (g : affine k A ⟶ G.X)` quantifies
  over every commutative test algebra and every point. No nontriviality,
  reducedness, finite generation, or field hypothesis is imposed on A.
- `StandardGroupSchemes.map k (Algebra.ofId k A) ≫ s ≫ i.hom.hom` is s_A,
  using the canonical structural map k → A. `Commute g ...` is gs_A = s_Ag.
- `g ∈ ReductiveTorusCentralizer.centralizerPoints i A` is exactly the other
  side of the equivalence. Expanding the already landed definition gives, for
  every commutative k-algebra B, every k-algebra map f : A → B, and t ∈ T(B),
  `Commute (StandardGroupSchemes.map k f ≫ g) (t ≫ i.hom.hom)`. These are
  precisely all commutative A-algebra extensions with their induced k-algebra
  structure. The identity map A → A is included. B is not assumed reduced or
  nonzero. The displayed `↔` therefore identifies the centralizer functors on
  all algebras, not merely field-valued or rational points.

Dependency declarations used (sources and full interfaces were read):

- `Mathlib.Algebra.Field.Defs`: `Field`; and
  `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, selected by the
  algebraic-closure node's mathlib_match. A chosen algebraic closure is not
  needed, since k itself is algebraically closed.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `Grp`, and
  group-valued Hom; bundled Grp morphisms encode the required homomorphisms.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsClosedSubgroupScheme`, extending `IsSubgroupScheme`
  (which includes `IsMonHom` and injectivity on algebra-valued points).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`;
  `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` (nonempty included).
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`:
  `AlgebraicGeometry.StandardGroupSchemes.affine`, `.map`, `.multiplicative`,
  and its canonical group structure. The first two provide canonical Spec and
  scalar extension, not a replacement definition of group schemes.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `AlgebraicGeometry.MultiplicativeType.splitTorus`.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `AlgebraicGeometry.ReductiveTorusCentralizer.centralizerPoints`.
  Its reductivity and maximal-torus predicates are not imposed here.
- The algebraic-representation node records
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Lie`
  and `GeneralLinearGroup.RationalHom.representation`. That recorded module is
  publicly imported in the new definition module. The general, existing
  `GeneralLinearGroup.RationalHom` and `.homMulEquiv`, publicly provided through
  its imports, give representations and their matrices over every field and
  algebra, without its unrelated characteristic-zero semisimple-module API.
  I read `standardRepresentation`, `RationalHom.representation`, `RationalHom`,
  `RationalHom.points`, `GeneralLinearGroup` and `homMulEquiv` and their docstrings.
- The stated proof dependency `lem-sc-kernel-subgroup` is imported with a plain
  import of `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`.
  The other proof dependencies currently lack Lean records; their proofs remain
  in the theorem's docstring. They are not required for elaborating this statement.
  In particular the existing upstream general-linear construction is reused;
  this delivery does not duplicate the not-yet-attached GL/SL definition node.

Edge cases checked against the statement and the five-step proof:
rank-zero T has s = 1 and the universal centralizer is all G; repeated weights
are collected into a single block; the empty representation has its unique
empty invertible matrix and empty diagonal; the trivial G is included. No
CharZero or perfectness condition is introduced. Distinct character values
have differences in k^×, hence remain units even in nonreduced A and B.
The zero ring is permitted for A and B, where the equalities remain valid.
The point s is fixed before A and g. The coefficient, group and algebra
universes are the same ambient u, never an independent smaller test universe.
An initial compile exposed that `Fin n : Type 0` does not fit an API with
index universe equal to u; quantifying over finite `ι : Type u` repairs this
without restricting k (use `ULift.{u} (Fin n)` for any desired dimension).

Searches (all msearch responses are preserved in searches.jsonl):

- LeanFinder: "A torus subgroup of a smooth connected affine algebraic group
  has a semisimple element whose centralizer functor equals the torus centralizer
  on all algebras" returned eight Lie-algebra/endomorphism results, no match.
- Loogle: `"centralizer", "exists"` returned zero hits. Mathlib grep
  `torus|regularSemisimple|semisimple` under AlgebraicGeometry returned zero hits.
- LeanSearch: "A torus contains an element with centralizer equal to the
  centralizer of the torus" returned eight abstract-centralizer results;
  none is a result about scheme-valued centralizers.
- LeanFinder for a point diagonalizable in every algebraic representation
  returned eight semisimple-endomorphism/module results. LeanSearch for the
  same notion returned Lie-algebra, module and diagonal-representation results.
  Loogle `"semisimple"` returned twelve ring/module results; no point predicate.
- Mathlib AlgebraicGeometry grep `IsSemisimplePoint|semisimple point|semisimple
  element` returned zero hits. Direct rg of WeilConjectures and Sheaf for
  `IsSemisimpleGroupSchemePoint|semisimple point|semisimple element` returned
  no declaration. Searches for torus and centralizer found the two landed
  terminology modules now reused. Direct search for the item's id in
  WeilConjectures and Sheaf found no implementation.
- Definition-node grep and `tools/blueprint_refs.py search "semisimple point"`
  found no existing definition node (zero blueprint matches). A broader
  blueprint "semisimple" search concerned modules, Lie algebras or Weil
  representations, not semisimple rational points.

Source read: Milne PDF page 351, printed p.339, including the complete proof
of Lemma 16.42. The accepted split's arbitrary-algebra block calculation is
retained. No statement dispute or source-based correction is required.

## New nodes

`def-sfb-semisimple-group-scheme-point` defines the item's missing semisimple
point notion over an algebraically closed field, by diagonalizability in every
finite-dimensional algebraic representation. Its module contains only the
actual predicate, no postponed construction or theorem. It uses the recorded
algebraic-representation interface, the original field/group-scheme notions,
and the canonical affine Spec construction. The finite-index formulation is
basis-independent and includes dimension zero. Sources are Milne Lemma 16.42
and Theorem 12.12. Its mathlib_searches include the actual semantic search
responses and the negative Mathlib/project/DAG searches; module, Lie-algebra
and endomorphism semisimplicity are different notions. The ancestor tool has
no named blueprint ancestor for this item; the null ancestor and its existing
provenance chain are preserved, with the item prepended to via.

## Second reading by Q40

I reread both node records and both Lean modules together after compilation.
This is a second pass by the assigned worker, not a claim of an independent
agent review: the dispatcher explicitly forbids starting other agents and
assigns independent review to the maintainer. The clause correspondence above
was checked against the final source. I found and fixed the finite-index
universe issue; no field-universe equality was imposed. I also made the new
point predicate explicitly require an algebraically closed field, matching
its intended context (over a general field, semisimple need not mean split
diagonalizable over that field). The final main theorem retains both groups'
standing affine finite-type assumptions, G's smoothness and nonempty
connectedness, the closed inclusion, an actual split-torus isomorphism, the
single existential point, its semisimplicity, and the equivalence over all
algebras and all extensions. There is no arbitrary substitute map, extra
faithful representation hypothesis, field-only test, or characteristic-zero
restriction. The accepted item statement and proof are unchanged.
