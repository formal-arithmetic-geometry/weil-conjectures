## Worker report

The theorem is `AlgebraicGeometry.PGLTwoTriangular.triangular_maximal_torus_conjugacy`
in `Sheaf.AlgebraicGeometry.GroupScheme.TriangularMaximalTorusConjugacy`.
Its only postponed proof is the named theorem with `sorry`; the proof docstring
contains every step of the node's seven-step proof, including the nonreduced
normalizer calculation and the character-lattice justification of equality.
The auxiliary `Conjugates` is a real Prop definition, not postponed data.

Hypotheses, clause by clause:

- The nonzero commutative Noetherian ring is `(A : Type u) [CommRing A]
  [Nontrivial A] [IsNoetherianRing A]`; S is always `Spec (.of A)`.
- Group diagrams are the instances in `G B D T : Grp (Over (Spec (.of A)))`.
  `iB : B ⟶ G`, `iD : D ⟶ B`, and the `Presentation G B D iB iD` specify exactly
  PGL2 as represented fppf scalar quotient, and its triangular/diagonal subgroup
  images. Its q maps are injective, natural group homomorphisms; local surjectivity
  is a covering-sieve condition, not a global lift hypothesis. Upper triangular
  means matrix entry (1,0) zero; diagonal means both off-diagonal entries zero.
  Closedness of these two subgroup maps is recorded in the presentation.
- T is included by `iT : T ⟶ B` and `[IsClosedImmersion iT.hom.hom.left]`.
  `IsRelativeTorus T.X` is precisely fppf local finite products of units, allowing
  varying covering ranks. `hmax` tests every algebraically closed field and every
  `A →+* Ω`; the pullback of `iT ≫ iB` is `IsMaximalTorus`. This uses the existing
  maximality-under-inclusion predicate, not pointwise maximality of abstract groups.
- `Conjugates iD iT V b` tests all `h : W ⟶ V` and all `z : W ⟶ B.X` and states an
  iff between the D-image and the conjugated T-image. Thus it is equality of subgroup
  functors over V; it detects nilpotents and is not equality just on geometric points.

Conclusions, clause by clause:

- `Nonempty (D ≅ relativeSplitTorus (Spec (.of A)) 1)` renders D ≃ G_m,S as groups.
- `∃ Y j act, Mono j ∧ ...` together with the iff for every test scheme is
  representability of the indicated subfunctor. The map y ↦ y ≫ j is injective
  by `Mono j` and its image is exactly `Conjugates`; composition makes these
  bijections natural. The resulting functor is automatically an fppf sheaf because
  it is represented. No new arbitrary functor or choice of representing scheme is defined.
- `Smooth Y.hom ∧ Surjective Y.hom` is the claimed smooth surjection.
- The identity `lift d y ≫ act ≫ j = (d ≫ iD.hom.hom) * (y ≫ j)` specifies the
  action as actual left multiplication, not an unspecified action. Monicity of j
  and the group laws imply its identity and associativity diagrams.
- `IsIso (lift act (snd D.X Y))` is the specified D ×_S Y → Y ×_S Y map. Products
  in `Over S` are precisely scheme fibre products over S, and the two components
  are multiplication and y, in that order.
- A family `U : I → Over S` whose underlying arrows belong to
  `Scheme.etalePrecoverage S`, with `Nonempty (U i ⟶ Y)`, gives etale local sections.
- A family belonging to `Scheme.zariskiPrecoverage S` and `b : ∀ i, U i ⟶ B.X`
  gives the open cover and actual triangular conjugating sections. The first
  Conjugates clause gives their membership in Y; representability gives the
  corresponding Y sections. The last universal Conjugates clause is exactly
  persistence along every base change `h : V ⟶ U i` (and all further extensions).

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, all ideals finitely generated.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`, their full defining signatures.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, multiplication/unit/inverse diagrams;
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: group laws on test-scheme Hom sets.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`, exposed by Sites.Etale.
- `Sheaf.AlgebraicGeometry.RelativeTorus`: `IsRelativeTorus`, `relativeSplitTorusFunctor`.
- `Sheaf.AlgebraicGeometry.RelativeSplitTorus`: `relativeSplitTorus` with its explicit Hopf data.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `ReductiveTorusCentralizer.IsMaximalTorus`, including its larger-torus factorization test.
- `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective`:
  `Matrix.ProjGenLinGroup`, `.mk`, `.map`, `.mk_eq_mk_iff`; the quotient is by scalars,
  but is used only as the quotient presheaf, never mistaken for its sheafification.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology`, `fppfPrecoverage`;
  `Mathlib.CategoryTheory.Sites.Over`: the induced topology on `Over S`.

Plain proof imports are all available recorded proof dependencies:
`Sheaf.AlgebraicGeometry.GroupScheme.BorelMaximalTorusConjugacy`
(`borel_contains_maximal_torus_and_conjugacy`),
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`
(`AffineSpace.smoothOfRelativeDimension_over`, accepts any finite coordinate type),
`WeilConjectures.AlgebraicGeometry.Sites.GmPicard`
(`Scheme.nonempty_equiv_quotient_torsor`, etale and Zariski clauses),
and `WeilConjectures.AlgebraicGeometry.Modules.Invertible`
(`Scheme.Modules.IsInvertible`, local unit-module trivializations).
The recorded smooth-restriction Mathlib match is already exposed by the public Smooth
import (`instSmoothResLE`, `smooth_comp`, and smoothness of open immersions).
The other proof nodes have no recorded usable Lean declaration and introduce no new
notion required to type this statement, so no speculative proof-dependency imports are added.

Edge cases checked: all characteristics including 2; arbitrary nilpotents and
nonconnected Noetherian bases; geometric maximality is not replaced by global splitting.
The base is nonempty as required by Nontrivial A, while test schemes and base changes
may be empty. The rank-zero case is allowed by IsRelativeTorus and excluded only where
geometric maximality in PGL2 forces rank one. No PID, domain, reducedness, algebraically
closed base, chosen global generator, or trivial Picard group is assumed. A nontrivial
line bundle on an affine base is compatible with the local, rather than global, sections.
One universe u accommodates rings, schemes, covers, and all geometric field tests.

Searches actually run through msearch.py:

- LeanFinder: “The transporter of a triangular maximal torus in PGL2 to the diagonal
  torus is a smooth surjective Gm torsor with Zariski local sections”: 8 unrelated
  modular-group/projective-line action hits, no relative theorem.
- Loogle: `"torus", "conj"`: no hits.
- Mathlib grep under AlgebraicGeometry: `PGL|[Tt]orus|[Tt]ransporter|[Tt]riangular`:
  no hits. A second grep `ProjGenLinGroup|IsProjectiveLinearQuotient|triangular|transporter`
  under AlgebraicGeometry also has no hits.
- LeanSearch and LeanFinder: “PGL2 as fppf scalar quotient of invertible matrices with
  upper triangular and diagonal subgroup functors”: 8 hits each, ordinary matrix
  quotient and projective actions, no relative configuration.
- Loogle `Matrix.ProjGenLinGroup`: 12 hits including the existing quotient, mk, and map;
  these are reused.
- rg of WeilConjectures and Sheaf for PGL, torus, transporter, scalar quotient;
  item-id search in WeilConjectures: no theorem matching the item. Read the field-only
  `IsProjectiveLinearQuotient` and `ProjectiveMatrixCentralCover.Presentation` interfaces.
- DAG title/statement searches and `tools/blueprint_refs.py search PGL` / `search transporter`:
  existing quotient node is field-only, no relative triangular configuration node;
  the two blueprint searches return zero. Ancestor command returns None.

No statement correction and no STATEMENT-DISPUTED flag. The item statement is unchanged.

## New nodes

`def-sfb-pgl-two-triangular-presentation` supplies the missing relative triangular
PGL2 configuration. Its module contains the real definition `LocallyMatrix` and the
structure `Presentation`. The source is Conrad, Proposition 4.2.7, pp.123--124; the
structure spells out exactly the groups and subgroup images used there. Search records
are the actual logged LeanSearch, LeanFinder, Loogle and grep results, supplemented by
DAG, upstream, and project searches. It reuses the existing Mathlib matrix quotient.
It differs from `def-sfb-projective-linear-quotient` by allowing arbitrary scheme bases
and retaining the quotient maps needed to specify B and D; that older field predicate
forgets its quotient maps existentially and cannot specify these subgroup images.
The item also gains the existing relative-torus, relative-split-torus and maximal-torus
terminology nodes in stmt_deps, using their landed modules with no redefinition.

## Self-check by Q95

I reread the node and both modules against each clause. The first compile found that
fppfTopology.over needed the explicit Sites.Over import; that import was added.
The represented-subfunctor encoding retains naturality via composition with j and
injectivity via Mono j. The torsor map has the source D × Y, target Y × Y and correct
component order. Fppf sheaf images use local matrices, not global matrix lifts.
This is the author's self-check; the maintainer supplies the independent reading.

## Second reading by Q95

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
