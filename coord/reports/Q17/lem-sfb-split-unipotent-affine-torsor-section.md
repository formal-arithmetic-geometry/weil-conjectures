## Worker report

The module states `AlgebraicGeometry.split_unipotent_affine_torsor_section` with
one `sorry` and no new definitions. It renders the unchanged node statement.
The source was read in Milne, Algebraic Groups (2017), Proposition 16.55(b),
printed p.344; the adjacent proof reduces to Example 2.72, printed p.61.
Definition 14.61 and paragraph 14.62, printed p.299, specify the additive series.

Hypothesis and clause correspondence:

- The field is `{k : Type u} [Field k]`.
- The k-group is `U : Grp (Over (Spec (.of k)))`, using the recorded group-object
  definition. Its affineness is `IsAffine U.X.left`; finite type is
  `LocallyOfFiniteType U.X.hom` and `QuasiCompact U.X.hom`.
- The finite split additive series is `(m : ℕ) (hseries : SplitUnipotentLength U m)`.
  Its recursive definition includes `Smooth U.X.hom` and `ConnectedSpace U.X.left`
  at every stage. At zero it requires `Nonempty (U ≅ Grp.trivial _)`. At a successor
  it supplies a closed normal homomorphism `i : N ⟶ U`, and a homomorphism from U
  to the canonical `Grp.mk (StandardGroupSchemes.additive k)`, representing the
  fppf quotient by N through `SolvableGroupStructure.IsFppfQuotient`. The recursion
  supplies exactly the tail series. Thus no multiplicative quotients are allowed.
  A quotient isomorphic to G_a can be transported along that isomorphism to this
  quotient map with target G_a, and conversely this map gives such a quotient.
  Affineness and finite type of the closed subgroup terms follow from those of U.
- The base k-scheme is `S : Over (Spec (.of k))`; its affine finite-type hypotheses
  are `IsAffine S.left`, `LocallyOfFiniteType S.hom`, and `QuasiCompact S.hom`.
- `P : RepresentedRightTorsor U S` supplies `space`, `projection`, and the actual
  right action `space ⊗ U.X ⟶ space`. Its fields `flat`, `surjective`, `lfp`, `qc`,
  `qs` give flatness, surjectivity, and finite presentation. `one_action` and
  `mul_action` are the right-action laws on all test k-schemes. Its `torsor` field
  is the cartesian square with top maps first projection and action, and bottom
  maps both `projection`: this is exactly the specified torsor isomorphism.
- The conclusion `∃ s : S ⟶ P.space, s ≫ P.projection = 𝟙 S` is the section and
  its required equation. Composition in Lean is left to right. Morphisms live in
  Over Spec k, so the section is a k-morphism. An underlying scheme section is
  automatically over k because the projection is over k, so this adds no condition.
- There are no perfectness, reducedness, commutativity, or centrality assumptions.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` and its bundled
  `CategoryTheory.Grp`, used for groups over Spec k.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`, inside
  the split-series definition.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, inside the split series.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions`:
  `AlgebraicGeometry.RepresentedRightTorsor`; the module's `SplitSolvableLength`
  allows G_m and is therefore insufficient for the additive-only series.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`:
  `AlgebraicGeometry.StandardGroupSchemes.additive` and `additiveGroup` specify
  Spec k[y], with y mapping to y⊗1+1⊗y, 0, and -y in its Hopf maps.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd` and `pullback.lift`;
  the torsor's cartesian square expresses the same fibre product without naming
  the chosen model.
- Newly cited LANDED node `def-sfb-split-unipotent-series`, already carrying
  `AlgebraicGeometry.SplitUnipotentLength` in
  `Sheaf.AlgebraicGeometry.GroupScheme.SplitUnipotentSeries`, is added to stmt_deps
  under the rule permitting additional landed notions. This is not a new node.

Proof imports are `Mathlib.AlgebraicGeometry.Morphisms.FlatMono`
(`IsOpenImmersion.of_flat_of_mono`),
`Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`, and
`Sheaf.AlgebraicGeometry.AdditiveAffineTorsorSection`. The fourth proof dependency,
`lem-sfb-normal-extension-torsor-reduction`, has no Lean record, Mathlib match, or
closed upstream audit in the read clone, so no module can yet be imported for it.
It is used only in the proof plan and is not needed to state this theorem.
The docstring carries all three node proof steps with their dependency identifiers.

Edge cases checked: m=0 unfolds to the smooth connected trivial group, with no
successor quotient required; m=1 includes G_a; the empty affine base is permitted,
as the statement does not assume connectedness or nonemptiness of S. Nonreduced
finite-type bases such as Spec k[ε]/(ε²) are permitted. Imperfect fields of positive
characteristic are permitted. A noncommutative split unipotent group such as the
upper unitriangular 3-by-3 group is permitted: the normal inclusions are only
required to be normal in their predecessors, never central. No unipotence-as-matrix
hypothesis has been added to the supplied additive series. The explicit universe u
can be chosen large enough for the field and all schemes; there is no independent
smaller test universe. `set_option autoImplicit false` enforces bound variables.

Searches actually run:

- msearch.py leanfinder: "Every represented torsor under a split unipotent algebraic
  group over an affine scheme has a section"; eight hits, concerning affine space
  and transition-limit constructions, none asserting this theorem.
- msearch.py leansearch: "Every torsor under a split unipotent group over an affine
  scheme is trivial"; eight hits on AddTorsor and affine subspaces, no scheme result.
- msearch.py loogle: "AlgebraicGeometry.RepresentedRightTorsor,
  AlgebraicGeometry.SplitSolvableLength"; unknown identifier RepresentedRightTorsor,
  no hits (the remote Mathlib index does not contain project declarations).
- msearch.py grep: `torsor|Torsor|[Uu]nipotent`, subdirectory AlgebraicGeometry;
  zero Mathlib hits.
- rg on lean/WeilConjectures and lean/Sheaf for unipotent, SplitSolvableLength,
  split_unipotent, splitUnipotent, and additive-series variants found the existing
  torsor module, additive affine theorem, and the landed SplitUnipotentSeries
  definition, but no statement of this theorem. The upstream node-id grep returned
  no hit. The upstream names index was also searched. The reductive quotient module
  mentions the lemma only in its proof plan; it does not declare it.

No disputed statement, source error, dependency repair, or new node is needed.

## Second reading by Q17

Author's separate clause-by-clause rereading, with the source node and final Lean
module open; independent mathematical review remains with the maintainer.
The source statement requires a smooth connected affine finite-type U, an additive
series, an affine finite-type S, and a represented right torsor. The final signature
contains exactly these: smoothness and connectedness occur in hseries rather than
as duplicate instance binders. The series uses the landed additive-only predicate,
not IsSplitSolvable, which would allow G_m and make the theorem false for a base
with nonzero Picard group. The torsor is the dependency's original structure,
including finite presentation and action laws. The conclusion is a section over k
with the projection equation, not merely existence of a rational point or a local
section. Zero length and empty base remain included. The only DAG adjustment is
adding the already landed additive-series definition to stmt_deps. No mismatch
requiring a statement change was found.

Validation: scompile.py compiled the delivered file as both sandbox and library
module on the live server, with no errors or unexpected warnings (29.5 s and
5.4 s respectively). The only theorem proof is `sorry`.
