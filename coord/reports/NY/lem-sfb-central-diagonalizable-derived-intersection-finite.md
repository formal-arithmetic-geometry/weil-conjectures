## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.CentralDiagonalizableDerivedIntersection`
states `AlgebraicGeometry.central_diagonalizable_derived_intersection_finite` with one
`sorry`, and introduces no definitions. The natural-language statement and proof are
unchanged. The only added statement dependency is the already landed definition node
`def-sfb-diagonalizable-group`; its canonical Hopf-spectrum construction is reused.

Source read: Milne, Algebraic Groups (2017), Theorem 12.12 and Remark 12.13, printed
pp.234--235, and Proposition 12.46(a) and its proof, printed pp.245--246. The latter
states the torus case. The node explicitly extends its weight-block determinant argument
to diagonalizable subgroups; Theorem 12.12 and Remark 12.13 provide that decomposition
even for characteristic torsion. The module docstring includes all four node proof steps
and the coordinate quotient argument establishing scheme-theoretic finiteness.

Clause-by-clause correspondence:

- An algebraically closed field F is `{F : Type u} [Field F] [IsAlgClosed F]`.
- The group schemes G, C and the derived group D are `Grp (Over (Spec (.of F)))`.
  This records the structural maps, group laws and base field.
- Smoothness is `[Smooth G.X.hom]`; connectedness is `[ConnectedSpace G.X.left]`;
  affineness is `[IsAffine G.X.left]`. Finite type is the pair
  `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`, exactly as its dependency
  records it.
- The central closed subgroup is `i : C ⟶ G` with
  `hi : IsClosedSubgroupScheme i.hom.hom`. The bundled arrow supplies a group
  homomorphism and `hi` supplies the closed inclusion, retaining scheme structure.
- Centrality after every commutative F-algebra extension is `hcentral`: for each
  `R : Type u`, `[CommRing R] [Algebra F R]`, each C(R)-point c and G(R)-point g,
  `Commute (c ≫ i.hom.hom) g`. The test object is explicitly
  `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F R)))`. This is an equality in
  the group of algebra-valued points, with the standard `MonObj` scope opened.
  It quantifies over nonreduced test algebras as well as fields.
- Diagonalizability is `hdiag : ∃ (M : Type u) (_ : AddCommGroup M)
  (_ : AddGroup.FG M), Nonempty (C ≅ diagonalizableGroup F M)`.
  The isomorphism is of group schemes. The reused definition is literally the spectrum
  of `AddMonoidAlgebra F M` with its canonical Hopf structure, whose basis elements have
  precisely the multiplication, coproduct, counit and antipode listed in the node.
- The phrase “let G^der be the smallest closed subgroup through which the commutator
  factors” is `j : D ⟶ G` and `hderived : IsDerivedGroupScheme j.hom.hom`.
  This predicate explicitly gives closedness, factorization of `xyx⁻¹y⁻¹`, and minimality
  among such closed subgroups. Quantifying over a representative of this subgroup
  avoids an arbitrary choice and applies to every representative; the recorded
  `exists_smooth_connected_derived_subgroup` guarantees existence under exactly G's
  hypotheses.
- The scheme-theoretic intersection is `pullback i.hom.hom j.hom.hom` in the category
  over Spec F. Its structure morphism is `.hom`, and the conclusion is
  `IsFinite (pullback i.hom.hom j.hom.hom).hom`. Mathlib's `IsFinite` means affine
  with finite coordinate ring map; over the field F this is exactly finite dimensionality
  of the coordinate F-algebra. No statement about just the set of F-points is substituted.
- No reductivity of G, smoothness or connectedness of C, reducedness of C or of the
  intersection, characteristic restriction, or condition on D beyond being the derived
  subgroup is imposed.

Dependency declarations read and used:

- `Field`, `Mathlib.Algebra.Field.Defs`; `IsAlgClosed`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic`. The algebraic-closure node's recorded
  `AlgebraicClosure` and `IsAlgClosure` were also read; the present statement needs
  the algebraically-closed predicate, rather than a chosen closure extension.
- `CategoryTheory.GrpObj`, `Grp`, and group-valued representable homs,
  `Mathlib.CategoryTheory.Monoidal.Grp` (also supplied through group-scheme dependencies).
- `AlgebraicGeometry.Spec` and `Spec.map`, `Mathlib.AlgebraicGeometry.Scheme`.
- `AlgebraicGeometry.IsClosedSubgroupScheme`,
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: extends the recorded
  `IsSubgroupScheme` and requires a closed immersion. Its injectivity on each
  algebra's points and its group-homomorphism condition are not redefined.
- `AlgebraicGeometry.Smooth`, `Mathlib.AlgebraicGeometry.Morphisms.Smooth`;
  `ConnectedSpace`, `Mathlib.Topology.Connected.Basic`;
  `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`; `AlgebraicGeometry.QuasiCompact`,
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` (imported through finite type).
- `AlgebraicGeometry.exists_smooth_connected_derived_subgroup`,
  `Sheaf.AlgebraicGeometry.GroupScheme.SmoothConnectedDerivedSubgroup`;
  `AlgebraicGeometry.IsDerivedGroupScheme` and `groupSchemeCommutator`,
  `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple` (publicly imported there).
- `AlgebraicGeometry.diagonalizableGroup`,
  `Sheaf.AlgebraicGeometry.DiagonalizableGroup`, with Mathlib's `hopfSpec` and
  canonical `AddMonoidAlgebra` Hopf operations. Its already landed node is added to
  `stmt_deps`; no additional definition node or repair module is needed.
- `AlgebraicGeometry.IsFinite`, `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  supplied by the recorded group-scheme definitions.
- Stated proof inputs are imported: `Sheaf.AlgebraicGeometry.LinearGroupSchemes`
  (the GL/SL/determinant node), the derived-subgroup module already publicly imported,
  the subgroup definitions, and `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
  At writing time the faithful-weight-block and diagonalizable-weight-grading nodes
  have no Lean record, so they have no module to import. Their node identifiers and
  their precise roles remain in the proof docstring.

Edge cases checked before writing:

- G trivial and C trivial give a trivial, finite intersection. The trivial character
  group M is allowed; there is no nonzero-rank condition.
- If G is commutative, D is trivial, even when C is a positive-dimensional torus.
- For G = GL_n and central C = G_m, the intersection is mu_n. In characteristic p
  dividing n this is nonreduced; neither the theorem nor its canonical pullback takes
  a reduction or replaces the group scheme by its rational points.
- Finite diagonalizable groups, disconnected diagonalizable groups and torsion character
  groups are included by `AddCommGroup` and `AddGroup.FG`, without torsion-freeness.
- The empty ambient scheme is correctly excluded by `ConnectedSpace`, as required
  by the recorded definition (a group scheme already has an identity section).
- F, character groups, schemes and test algebras use the standard common universe u
  of the existing group-scheme interfaces. The test-algebra universe is not independent
  or smaller than F's, and includes all coordinate algebras needed to detect identities.
  Finite generation permits character groups of any initial size to have representatives
  in this universe. All variables and universes are explicit; auto-implicits are disabled.

Searches actually run:

- `msearch.py ... leanfinder`: “A central diagonalizable closed subgroup of a smooth
  connected affine algebraic group has finite scheme theoretic intersection with the
  derived subgroup”. Eight hits, including `Subgroup.finiteIndex_center`,
  `Subgroup.index_center_le_pow` and abstract commutator/centralizer results; none
  states this scheme-theoretic intersection theorem.
- `msearch.py ... loogle`: `"IsFinite", "pullback"`. Zero hits.
- `msearch.py ... grep`: `diagonalizable.*(derived|commutator)|(derived|commutator).*diagonalizable`.
  Zero Mathlib hits.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for central/derived/
  intersection combinations: no matching theorem; related torus-centralizer intersection
  and unrelated derived-category central actions do not assert this result.
- Direct node-id grep in `lean/WeilConjectures`: no match. Direct full-name search
  in Mathlib, WeilConjectures, Sheaf and `dag/lean_names_upstream.json`: no collision.
- Direct `rg` for `Diagonalizable`, `diagonalizableGroup` and `IsDerivedGroupScheme`
  found the existing diagonalizable construction and the Semisimple/derived-subgroup
  interfaces, which are imported instead of duplicated.

No disputed mathematical statement or source-based correction was needed. The example
`CompactObject.lean` is currently withdrawn and contains no declarations; the live
derived-subgroup module supplies the module/header conventions used here.

Validation uses only the prescribed `scompile.py` and `deliver2.py` wrappers.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
