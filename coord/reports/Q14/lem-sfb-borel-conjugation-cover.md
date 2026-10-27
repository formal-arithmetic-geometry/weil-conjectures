## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.BorelConjugationCover` states
`AlgebraicGeometry.exists_borelGroupScheme_and_conjugation_surjective` with proof
`sorry`. It introduces no definition and proves nothing. The node's statement,
source, proof and proof dependencies are unchanged. Its statement dependencies gain
only the already landed `def-sfb-borel-subgroup-scheme`, whose exact definition is
used rather than duplicated. There are no new nodes or dependency repairs.

Source read: `literature/milne-algebraic-groups_iAG2017.pdf`, printed pp.353–354,
Definition 17.6 and its following sentence (PDF pages 365–366), and printed p.362,
Theorem 17.33, its proof and Corollary 17.34 (PDF page 374). The section assumes a
connected group variety over an algebraically closed field. The node's smooth
connected affine finite-type scheme formulation matches that setting. In particular,
the proof of 17.33(b) fixes any Borel B before choosing T inside it, so the assertion
really concerns every prescribed Borel, rather than merely the existence of one.

Hypotheses and clauses, individually:

- Algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
  No characteristic hypothesis is imposed.
- k-group scheme G: `(G : Over (Spec (.of k))) [GrpObj G]`; the multiplication,
  inverse and identity are the internal group structure already used upstream.
- Affine: `[IsAffine G.left]`.
- Finite type over k: `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, precisely
  the recorded conjunction from `def-weil-finite-type-morphism`.
- Smooth: `[Smooth G.hom]`.
- Connected, including nonempty: `[ConnectedSpace G.left]`.
- Subgroups are closed subgroup schemes, and a Borel is maximal smooth connected
  solvable: `IsBorelGroupScheme i`. Its definition includes
  `IsClosedSubgroupScheme i`, `Smooth B.hom`, `ConnectedSpace B.left`, and
  `IsSolvableGroupScheme B`. Its final quantified factorization condition is
  maximality among these closed subgroups. The real definition
  `IsSolvableGroupScheme` uses `GroupSchemeDerivedLength`; successors use the
  smallest closed subgroup through which `groupSchemeCommutator` factors and
  the zero case is terminality over k. Thus it retains scheme structure, rather
  than testing solvability only on rational points.
- Borel existence is the first conjunct:
  `∃ (B : Over (Spec (.of k))) (_ : GrpObj B) (i : B ⟶ G), IsBorelGroupScheme i`.
- Any prescribed Borel is covered by the second conjunct's universal B and i
  followed by `IsBorelGroupScheme i →`.
- Rational points G(k) and B(k) are respectively
  `𝟙_ (Over (Spec (.of k))) ⟶ G` and `𝟙_ (Over (Spec (.of k))) ⟶ B`.
  The monoidal unit of the over-category is the base spectrum with its identity
  structure map, so these are exactly k-rational points.
- The map G(k) × B(k) → G(k) is the displayed product-domain function
  `fun p ↦ p.1 * (p.2 ≫ i) * p.1⁻¹`; composition includes b in G before multiplication.
  `Function.Surjective` is exactly the requested conclusion. Its meaning also
  gives the node's final sentence that every element is conjugate into B.
- There is no reductivity or semisimplicity assumption, nor any implicit
  finiteness, smoothness or connectedness assumption on G beyond those listed.

Dependency declarations inspected and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (line 180).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (line 62 and docstring).
  The dependency's `AlgebraicClosure` entry also explicitly points to this
  predicate for its algebraically-closed clause; no chosen algebraic closure is needed.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` (line 43).
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: `CategoryTheory.Hom.group`
  (line 63), the group on morphisms into a group object, enabled by `open scoped MonObj`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsSubgroupScheme` and `IsClosedSubgroupScheme` (lines 76, 96),
  read with their full class fields and functor-of-points docstrings.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` (line 43),
  and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact` (line 43).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth` (line 62).
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` (line 705).
- Added landed dependency `Sheaf.AlgebraicGeometry.GroupScheme.Borel`:
  `AlgebraicGeometry.IsBorelGroupScheme`, including every maximality binder.
  Its imported `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple` supplies
  `groupSchemeCommutator`, `IsDerivedGroupScheme`, `GroupSchemeDerivedLength`
  and `IsSolvableGroupScheme`; all definitions were read in full.

The statement dependency module is a public import. Plain imports retain the
available proof plan: `Sheaf.AlgebraicGeometry.TorusRegularSemisimpleElement`,
`Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry`,
`Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates`, and the Mathlib
finite-type/Jacobson and algebraically-closed-point modules. The other proof nodes
currently have neither a recorded Lean declaration nor a Mathlib match; they are
not required to type this statement and are not restated here. The theorem
docstring gives all six DAG proof steps, including the finite-normalizer quotient
argument and the closed-point contradiction at the end.

Edge cases checked before writing: for G = 1 both clauses reduce to the trivial
Borel and singleton surjectivity. For a smooth connected solvable G (including
G_a and G_m), G itself is its Borel and choosing g = 1 realizes every point.
For GL₂ the assertion is triangularization into any prescribed flag stabilizer,
without excluding nondiagonalizable matrices. Positive characteristic, including
2, is retained. The empty scheme cannot be a group scheme over the nonzero field
because of the identity section; ConnectedSpace also explicitly enforces nonemptiness.
No torus rank or nontrivial dimension is assumed. One explicit universe u covers
the field, its schemes and all rational-point morphisms, as in the dependency APIs.

Searches actually run through `msearch.py Q14 lem-sfb-borel-conjugation-cover`:

- leanfinder: `Borel subgroups exist and conjugates of any Borel cover a connected affine algebraic group`.
  Eight hits, including Iwasawa structures and topological connected components;
  none is this algebraic-group theorem.
- loogle: `"Borel"`. Twelve hits on Lie-algebra Borel submodules and measurable
  Borel spaces; none is this theorem.
- grep: `BorelSubgroup|IsBorelGroupScheme|conjugation.*surjective|surjective.*conjugation`.
  Zero Mathlib hits.
- leansearch: `Conjugates of any Borel subgroup cover a smooth connected affine algebraic group over an algebraically closed field`.
  Eight abstract conjugacy hits. `Group.conjugatesOfSet` and its membership and
  inclusion lemmas were inspected in `Mathlib/Algebra/Group/Subgroup/Basic.lean`,
  lines 561–575; they define conjugation saturation without proving its coverage.

Local searches: `rg` for Borel/IsBorelGroupScheme/solvable/commutator terminology
in `lean/Sheaf`, `lean/WeilConjectures` and `dag/nodes` found the landed Borel and
scheme-derived-series definitions above. The general Borel flag-variety theorem
was read: it constructs a variety of Borels and does not assert this conjugation
surjectivity theorem. The common-Borel theorem for a torus and a commuting point
was read: it is a downstream user of this item, not a reusable proof dependency.
The item-id search in `lean/WeilConjectures` and the fresh declaration-name search
in both source trees and `dag/lean_names_upstream.json` returned no match.
No duplicate theorem or private notion was introduced.

Validation: `scompile.py Q14 lem-sfb-borel-conjugation-cover` compiled the delivered
file in sandbox mode (4.4 s) and under its library module name (2.3 s), both clean.
All variables and the single universe are explicit; `autoImplicit` is disabled.
No statement dispute or source error was found.

## Second reading by Q14

This is the dispatched worker's separate second pass, not a claim to an independent
agent review; the brief prohibits starting other agents. The maintainer supplies
the independent review after delivery.

Reopened the node and final Lean file and checked the first conjunct separately
from the second. Existence does not depend on a supplied Borel. The second part
quantifies over each B and embedding i, so it does not accidentally restrict to
the existential witness. B's group structure is bound explicitly in both parts.
The rational point product has G first and B second; `p.2 ≫ i` lands in G(k), and
the final inverse is of p.1. Thus the formula is g b g⁻¹ with the correct inclusion.
The codomain inferred by Function.Surjective is G(k).

Reopened the Borel definition: closedness, smoothness, connectedness, derived-series
solvability and maximality are all present, with no reductivity condition.
Rechecked G's five geometric binders: affine, locally finite type, quasi-compact,
smooth and connected, exactly as the node says. Read IsAlgClosed and ConnectedSpace
rather than treating their names as sufficient. No characteristic, dimension,
nontriviality, or independently smaller test universe is introduced.

The only metadata adjustment is adding the existing Borel definition node to
stmt_deps, as authorized for landed notions. No mismatch requiring a mathematical
statement correction was found; the natural-language statement remains verbatim.
The sole theorem has the whole proof `by sorry`, and its source and six-step proof
are in its docstring. The record signature was extracted directly from the file,
and every Lean line is at most 100 characters.
