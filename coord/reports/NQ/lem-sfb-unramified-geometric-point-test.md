## Worker report

The module `Sheaf.AlgebraicGeometry.UnramifiedGeometricPointTest` states
`AlgebraicGeometry.unramified_iff_geometricPoint_test`. It contains one theorem,
with its whole proof `sorry`, and no definitions or instances. No statement or
DAG dependency is changed. No new nodes or dependency repairs are needed.

The source was read in the local Stacks files: morphisms.tex, the full lemma and
proof labelled lemma-set-points-where-fibres-unramified (Tag 0475), and
schemes.tex, the discussion preceding and the statement of lemma-characterize-points
(Tag 01J9). The former provides arbitrary-base-change equality of the unramified
locus under precisely locally finite type; the latter identifies field-valued
points with residue-field embeddings. The theorem docstring carries all four
steps of the node's proof, including the lifting construction and the empty cover.

Hypotheses and clauses, matched individually:

- Schemes X and S and their morphism f are `{X S : Scheme.{u}} (f : X ⟶ S)`.
- The sole geometric hypothesis is `[LocallyOfFiniteType f]`.
- Unramifiedness is the dependency's `IsUnramified f`, literally locally finite
  type and open-immersion diagonal. It is the left side of the first conjunct's iff.
- Every algebraically closed field is quantified by
  `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]`. The universe is the scheme's ring
  universe, as for the recorded geometric-point interface; it is not an independent,
  possibly too-small test universe. In particular it contains every source residue
  field and its algebraic closure. There is no algebraicity condition over any
  base residue field, so transcendental extensions are allowed.
- A geometric point s is `(s : Spec (.of Ω) ⟶ S)`.
- Its geometric fibre is exactly `pullback f s`, not the set-valued geometric fibre.
  Its p_s and g_s are respectively `pullback.snd f s` and `pullback.fst f s`.
- A rational test point is `(x : Spec (.of Ω) ⟶ pullback f s)`, with the explicit
  section hypothesis `x ≫ pullback.snd f s = 𝟙 (Spec (.of Ω))`.
- The image point is `x (IsLocalRing.closedPoint Ω)`; Spec of a field has one point.
- Being unramified there on some open neighbourhood is stated literally as
  `∃ U : (pullback f s).Opens, x (IsLocalRing.closedPoint Ω) ∈ U ∧
  IsUnramified (U.ι ≫ pullback.snd f s)`.
- The words "if and only if" are the `↔`, encompassing both directions.
- The second outer conjunct is the source-point lifting assertion, independently
  of whether f is unramified: `∀ z : X, ∃ s ... x ..., ...`.
- For that lifting clause Omega is Mathlib's chosen
  `AlgebraicClosure (X.residueField z)`. Its Field, IsAlgClosed, canonical embedding
  and IsAlgClosure instances supply exactly the algebraic closure requested.
  Fixing this standard chosen closure introduces no condition on f or z.
- The existential s and x use that very field; the first inner conjunct again
  asserts the section equation. The second says exactly
  `pullback.fst f s (x (IsLocalRing.closedPoint ...)) = z`.
- There are no flatness, locally finite presentation, quasi-compactness, or
  Noetherian binders.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` and
  `locallyOfFiniteType_isStableUnderBaseChange`, including the pullback.snd instance.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, `IsAlgClosure`.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`, its
  `IsAlgClosure` and `isAlgClosed` instances.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.lift`. Scheme pullbacks are provided
  transitively by the unramified-morphism dependency, as in the existing modules.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.fromSpecResidueField`,
  `Scheme.fromSpecResidueField_apply`, `Scheme.SpecToEquivOfField`, and
  `Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`.
- `Sheaf.AlgebraicGeometry.UnramifiedLocusBaseChange`: `unramifiedLocus` and
  `unramifiedLocus_baseChange`. This is a plain proof import. The other direct
  imports expose the statement notions; they transitively expose the scheme,
  finite-type, and pullback modules already, so no duplicate imports are needed.

Edge cases checked before writing: the empty source has no test sections and no
source points, and its diagonal is an open immersion; an empty individual fibre
has no rational test points. Identity and open-immersion morphisms satisfy the
criterion. Nonreduced zero-dimensional fibres are not silently accepted: the
neighbourhood morphism must be unramified, not merely have a singleton underlying
space. No characteristic restriction or assumption of rationality of the original
source point is present. Using the algebraic closure of kappa(z), rather than
only algebraic closures of base residue fields, retains generic points with
transcendental residue extensions. All universes and variables are explicit,
with `set_option autoImplicit false`; the statement has no lets or local notation.

Searches for an existing exact statement (2026-10-24):

- msearch.py leanfinder: "A locally finite type morphism is unramified iff every
  rational point of each geometric fibre has an unramified open neighborhood".
  Eight hits, including Algebra.isOpen_unramifiedLocus, FormallyUnramified,
  formallyUnramified_iff, and etale permanence; none states this criterion or
  the source-point lifting clause.
- msearch.py loogle: "AlgebraicGeometry.IsUnramified,
  CategoryTheory.Limits.pullback.snd". Zero hits; unknown identifier
  AlgebraicGeometry.IsUnramified in that service's Mathlib environment (the
  project's definition is instead read and used directly).
- msearch.py leansearch: "Unramified morphisms of schemes detected at rational
  points of geometric fibres". Eight hits on formal unramifiedness and ring
  unramifiedness, none this geometric-point theorem.
- msearch.py grep in AlgebraicGeometry:
  `unramified.*[Gg]eometric|[Gg]eometric.*unramified|unramifiedLocus`: zero hits.
  A direct rg with that expression in the pinned Mathlib AlgebraicGeometry
  source also found no exact statement.
- Direct rg with the same expression and this node id in lean/WeilConjectures
  and lean/Sheaf found the shared unramified locus definition and the related
  GeometricTangentUnramified and GeometricFibreUnramifiedCriterion modules.
  Both related theorem signatures and docstrings were opened: the former tests
  tangent spaces and dual-number maps, and the latter tests entire canonical
  geometric fibres, without this theorem's rational-section/neighbourhood test
  and lifting assertion. Neither is an exact existing declaration for this node.
- The exact name and geometric/unramified name patterns were searched in
  dag/lean_names_upstream.json and both Lean roots; the new name is unused.
  The exact node-id search in lean/WeilConjectures found no declaration.

Validation: the prescribed scompile.py invocation completed successfully against
current server sources (1.9 seconds), with no compiler errors or warnings. Its
initial local attempt reported OSError(28), no space left on device; the wrapper's
normal server confirmation succeeded. No live file, build artifact, launcher
script or shared-repository Git state was edited directly.

There are no STATEMENT-DISPUTED flags, statement corrections, dependency repairs,
or omitted proof-dependency imports.

## Second reading by NQ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
