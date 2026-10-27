## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.BorelSchemeNormalizer` states
`AlgebraicGeometry.borelGroupScheme_normalizer_iff`, with `sorry` as its entire proof.
There are no new definitions, dependency repairs, or statement corrections.
The existing, landed definition node `def-sfb-borel-subgroup-scheme` is added to
`stmt_deps`, as permitted by brief-stage2 §5, to record the Borel predicate already
spelled out inline in the item's statement. No other existing field changes except
`lean`. The source read was Milne, Algebraic Groups (2017), printed pp.366--367
(PDF pages 378--379), Lemma 17.47 and Theorem 17.48, including the surrounding
connected-group-variety convention. The theorem is scheme-theoretic there: the
normalizer is smooth, and the proof reduces to rational points only after that fact.

Hypotheses and clauses:

- The algebraically closed base field is `{F : Type u} [Field F] [IsAlgClosed F]`.
  No characteristic restriction is imposed.
- `G B : Over (Spec (.of F))`, with `[GrpObj G] [GrpObj B]`, are group schemes
  over this same field, with the actual group laws on their functors of points.
- Affineness of the ambient group is `[IsAffine G.left]`; finite type is
  `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`.
- Smoothness and connectedness of G are `[Smooth G.hom] [ConnectedSpace G.left]`.
- `i : B ⟶ G` and `hB : IsBorelGroupScheme i` say precisely that B is a closed
  subgroup, smooth, connected, and solvable by its scheme-theoretic derived series,
  maximal among smooth connected solvable closed subgroups. This is the existing
  Borel predicate, not abstract solvability of B(F). Its closed immersion into the
  affine finite-type G also makes B affine and finite type, so separate assumptions
  for these consequences are unnecessary. The predicate includes the required
  homomorphism property and injectivity on algebra points.
- An arbitrary commutative F-algebra is `A : CommAlgCat.{u} F`; the point is
  `g : (algSpec (.of F)).obj (op A) ⟶ G`, i.e. a morphism Spec A → G over F.
- Every A-algebra A' is represented by `A' : CommAlgCat.{u} F` together with
  `f : A ⟶ A'`. This is exactly an F-compatible algebra extension; equivalently
  any A-algebra is given its induced F-algebra structure. No injectivity, flatness,
  finite generation, reducedness or nontriviality of A or A' is assumed.
- `(algSpec (.of F)).map f.op ≫ g` is the scalar extension g_A'. Contravariance
  gives Spec A' → Spec A, in the required direction.
- The first `Set.range` consists of `g_A' * (b ≫ i) * g_A'⁻¹` for every B-point b.
  The second is exactly the image B(A') in G(A'). Their equality expresses the
  full equality g_A' B(A') g_A'⁻¹ = B(A'), rather than one-sided preservation.
- `∃ b : (algSpec (.of F)).obj (op A) ⟶ B, b ≫ i = g` is g ∈ B(A).
- The equivalence states equality of the normalizer and B on every test algebra.
  The reverse implication is the automatic converse noted in proof step 10 of the
  node: elements of a subgroup normalize it after every extension. Thus the `↔`
  retains the node's final functor-equality clause as well as its stated implication.
- There is no reductivity assumption and no chosen normalizer scheme or arbitrary map.
  All objects, variables and universes are explicitly bound; autoImplicit is false.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs, line 180; and `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic, line 62 (the definition's splitting condition
  is equivalent to the node's root condition by `IsAlgClosed.exists_root` and
  `IsAlgClosed.of_exists_root`). The algebraic-closure dependency's own match
  explicitly lists IsAlgClosed for this clause; no chosen closure is required.
- `CategoryTheory.GrpObj`, Mathlib.CategoryTheory.Monoidal.Grp, line 43, gives the
  group-scheme structure in Over. `GrpObj.Hom.group`,
  Mathlib.CategoryTheory.Monoidal.Cartesian.Grp, supplies multiplication and inverse
  on points (enabled by `open scoped MonObj`).
- `IsSubgroupScheme`, `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs, lines 74--105: the Borel
  predicate uses the recorded closed-subgroup notion, with its IsMonHom and
  point-injectivity properties, not a private copy.
- `LocallyOfFiniteType`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType, line 43;
  `QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact, line 43, encode
  finite type as specified by the dependency's lean.note.
- `Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth, line 62; `ConnectedSpace`,
  Mathlib.Topology.Connected.Basic, line 705.
- `IsBorelGroupScheme`, Sheaf.AlgebraicGeometry.GroupScheme.Borel, line 31;
  its import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple gives
  `groupSchemeCommutator`, `IsDerivedGroupScheme`, `GroupSchemeDerivedLength`,
  `IsSolvableGroupScheme`. Their real definitions express the commutator morphism,
  smallest closed subgroup through which it factors, and eventual terminality.
- `algSpec`, Mathlib.AlgebraicGeometry.Group.Affine, line 73, is the existing
  contravariant Spec on algebras over F. `algSpec_obj_hom` and `algSpec_map_left`
  confirm the structure and scalar-extension maps. No second affine-test-scheme
  definition is introduced.

Plain proof imports retain every recorded proof dependency's available module:
TorusCentralizerBorelIntersection, AffineNormalQuotientGeometry,
SmoothGroupOrbitGeometry, PerfectSolvableUnipotentTorus, HomogeneousQuotient,
ProperReducedGlobalSectionsProduct; upstream Spectrum.Prime.Topology and
Geometrically.Reduced; Mathlib Sites.Fpqc for the recorded representable descent
match; and upstream RingTheory.Nullstellensatz for the recorded three vanishing
declarations. The other proof dependencies have no recorded module yet. They are
named individually in the ten-step proof docstring, which carries the full node
argument, including both strict dimension decreases, descent, and the final
reduced-normalizer Nullstellensatz step. No theorem from these proof imports is
used as definition data.

Edge cases checked before writing: G = B (in particular smooth connected solvable
groups, tori, Ga and the trivial group); dimension zero; arbitrary characteristic;
A' = A with the identity map; the zero algebra (empty Spec); nonreduced algebras
such as F[ε]/(ε²); and noninjective algebra maps. The universal hypothesis includes
the identity extension and all nilpotent extensions. No field-points-only shortcut
is used. Empty G is already excluded by its identity and ConnectedSpace, as in the
source. All algebras and schemes share universe u, so the algebra quantification
is not in an independent possibly smaller universe. The theorem is polymorphic
in u and imposes no additional size hypothesis.

Searches actually run through msearch.py for this group and item:

- leanfinder: “The scheme theoretic normalizer of a Borel subgroup of a smooth
  connected affine algebraic group equals that Borel subgroup”: eight hits, on
  Cartan Lie subalgebras, zero-root subalgebras, Sylow normalizers and abstract
  subgroup normalizers; none is the scheme-theoretic Borel theorem.
- loogle: `"Borel", "normalizer"`: zero hits.
- grep: `BorelSubgroup|borel.*normalizer|normalizer.*borel`: zero Mathlib hits.
- leansearch: “The normalizer of a Borel subgroup scheme of a smooth connected
  affine algebraic group is the Borel subgroup”: eight hits, including
  Subgroup.normalizer, Subgroup.setNormalizer, AddSubgroup.setNormalizer,
  Subgroup.normalizer_eq_top, Subgroup.mem_normalizer_iff', AddSubgroup.normalizer,
  LieSubalgebra.normalizer and Subgroup.mem_normalizer_iff; none states this
  algebraic-group scheme theorem.
- Direct rg of lean/WeilConjectures and lean/Sheaf for Borel, normalizer,
  IsBorelGroupScheme, derived and solvable found the existing Borel and Semisimple
  definitions and a citation of this lemma in GeneralBorelFlagVariety, but no
  declaration of the theorem. The existing RankOneRoots.normalizer only defines
  rational normalizer points after scalar extensions and is not this theorem.
- A declaration-name search of Mathlib, lean/WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json found no existing borelGroupScheme_normalizer_iff.
  A DAG search located the landed def-sfb-borel-subgroup-scheme, which is reused.

Validation: prescribed scompile.py compiled the sandbox module and its library
module name cleanly, with no errors or unexpected warnings (2.5 s and 4.1 s).
No live files were changed and no local or global Lean build was run.
No STATEMENT-DISPUTED issue was found.

## Second reading by Q25

The dispatcher assigns the independent review after delivery; no second agent
was started. This is a second pass by the same worker, not a claim of independent
review. I reread the node against the final signature and the definitions it uses.
The base, group structures, affine finite-type condition and smooth connected
condition appear explicitly. The Borel predicate's four initial conjuncts and
maximality quantifier match the node's inline definition, including its genuine
scheme-derived solvability. The normalizer hypothesis quantifies over every
F-algebra map out of A; it does not replace scheme normalization by normalization
of just B(A) or B(F). Both images live in the same G(A') point group, the
conjugating element is the scalar extension of the given g, and the conclusion
lifts that very g through the Borel inclusion. The converse renders the final
functor equality. No reductivity, separability or reduced-test-algebra hypothesis
entered. Affine finite type for B is a consequence of being closed in G, rather
than a dropped condition. No mismatch or statement correction was necessary.
