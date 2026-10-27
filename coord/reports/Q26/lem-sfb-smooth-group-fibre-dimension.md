## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothGroupFibreDimension` states
`AlgebraicGeometry.AlgebraicSpace.exists_locallyConstant_geometricFibreDimension`.
Its only theorem proof is `sorry`. The helper `groupGeometricFibre` constructs the
actual presheaf pullback of the structural map with a field-spectrum map; it has
real data, no choice and no postponed proof. It belongs to this node's geometric
fibre construction and is listed in `lean.declarations`.

Hypothesis and clause correspondence:

- The arbitrary scheme base is `{B : Scheme.{u}}`; the group space is
  `H : AlgebraicSpace B`. No representability of H by a scheme is assumed.
- The group law is `F : (Over B)ᵒᵖ ⥤ GrpCat.{u}` together with
  `e : F ⋙ forget GrpCat ≅ H.obj.obj`. Transport along this natural isomorphism
  gives actual multiplication, identity and inverse on H, natural in every test
  scheme. The ordinary group axioms include associativity, both unit identities
  and both inverse identities. `GrpCat` imposes no commutativity. This is the
  same group-law encoding used in the existing locally separated group-space
  and separated geometric group-space modules, not a second group-space notion.
- The structural morphism p is a natural transformation to the represented base
  `yoneda.obj (Over.mk (𝟙 B))`. This target is terminal; thus p is precisely the
  structure map already specified by H over B and needs no extra compatibility
  axiom with the group law.
- Smoothness is `hsm : MapToSchemeIsLocally (@Smooth) H (Over.mk (𝟙 B)) p`.
  This tests the scheme composite on every representable etale source chart.
- Separatedness is `hsep : MapToSchemeIsSeparated H (Over.mk (𝟙 B)) p`:
  the relative representable diagonal is a closed immersion on every scheme test.
- Finite presentation is exactly the three binders `hlfp`, `hqc`, `hqs`:
  `MapToSchemeIsLocally (@LocallyOfFinitePresentation) ... p`,
  `MapIsQuasiCompact p`, and `MapIsQuasiCompact (pullback.diagonal p)`.
  The latter two are the affine-test quasi-compactness and quasi-separatedness
  specified in the node, not quasi-compactness of an arbitrary chosen atlas.
- The dimension function is `∃ d : B → ℕ, IsLocallyConstant d ∧ ...`.
  Its natural-number codomain gives finite, nonnegative dimensions.
- An arbitrary scheme map to B is `T : Over B`, with domain `T.left` and map
  `T.hom`. The point is `t : T.left`. Every choice of algebraic closure is
  quantified by `Ω : Type u`, `[Field Ω]`, `[Algebra (T.left.residueField t) Ω]`
  and `[IsAlgClosure (T.left.residueField t) Ω]`.
- The actual field-spectrum map to B is
  `Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) Ω)) ≫
  T.left.fromSpecResidueField t ≫ T.hom`. Its fibre is `groupGeometricFibre p`
  applied to this composite. `Point` and its topology are the recorded point
  classes and atlas topology, applied to this actual sheaf/presheaf pullback.
- Nonemptiness is `Nonempty (Point (...))`. Purity is the assertion for EVERY
  `Z ∈ irreducibleComponents (Point (...))` that
  `topologicalKrullDim Z = (d (T.hom t) : WithBot ℕ∞)`; Z has its subspace topology.
- Taking `T = Over.mk (𝟙 B)` gives exactly the original geometric fibre at every
  b, for every algebraic closure of its residue field. For arbitrary T, the same
  conclusion says that the dimension of every geometric fibre of the base-changed
  group is `d (T.hom t)`. Associativity of sheaf fibre products identifies that
  fibre with the displayed pullback. Thus its dimension function is `d ∘ T.hom`,
  precisely the requested equality `d_(p_T) = d_p ∘ h`. No independent choice of
  dimension functions or arbitrary comparison maps is introduced. Nonemptiness
  and purity determine the natural-number dimension uniquely, since an inhabited
  space has an irreducible component. Every algebraic closure is quantified, so
  the conclusion is independent of the choice of closure.
- No integrality, connectedness, properness, Noetherian, commutativity, flatness
  of the base map, or nonempty-base hypothesis occurs.

Dependencies used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme
  morphisms, `Spec`, `Spec.map` (def-pc-scheme, def-weil-affine-spectrum).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale` and
  `IsRepresentableWith` (def-trf-algebraic-space).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`; and
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation` (the recorded scheme chart notions).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme` provide the sheaf fibre products used here.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.fromSpecResidueField`; `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`:
  `AlgebraicClosure` and `IsAlgClosure`. The statement permits every closure.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`;
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `Point` and its
  `pointTopologicalSpace` final/atlas topology, transitively imported through the
  direct statement dependency below.
- Added the already-landed node `def-sfb-proper-curve-moduli` to `stmt_deps`,
  solely to cite its shared `MapToSchemeIsLocally`, `MapToSchemeIsSeparated`,
  and `MapIsQuasiCompact` helpers in `Sheaf.AlgebraicGeometry.ProperCurveModuli`.
  Their full definitions and source docstrings were read; no duplicate predicates
  were written. The proper-curve condition itself is not used or assumed.
- Proof-only imports: `Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus`
  (`point_open_calculus`) and `WeilConjectures.AlgebraicGeometry.DensePoints`
  (`Scheme.Hom.denseRange_fieldPoints`, `Scheme.Hom.nonempty_fieldPoints`).
  The proof dependency `lem-sfb-smooth-space-dimension-strata` currently has no
  Lean record/module, so its import is omitted and the proof plan names it.
  It is not needed to type the statement. No import cycle is introduced.

Edge cases checked before writing: the empty base is allowed (the function and
all pointwise assertions are vacuous); over a nonempty base the identity excludes
an empty geometric fibre. Dimension zero and disconnected smooth groups are
included: purity quantifies all components and never assumes irreducibility.
The field characteristic is unrestricted. Non-Noetherian and disconnected bases
are included, allowing d to vary between clopen base pieces. The arbitrary T
includes identity maps, empty T, nonflat maps, and nonreduced schemes. The universe
is the existing algebraic-space convention (schemes and test fields in u,
point classes in u+1); no independent smaller test-field universe is imposed.

Searches for existing declarations:

1. `msearch.py leanfinder`, query: "For a smooth separated group algebraic space
   of finite presentation the geometric fibre dimensions are locally constant and
   invariant under base change". Eight hits: scheme smooth-relative-dimension
   base-change results and standard-smooth algebra dimension definitions. None
   states this assertion for group algebraic spaces.
2. `msearch.py loogle`, query: "GrpObj, IsLocallyConstant, topologicalKrullDim".
   Zero hits; the service reported unknown identifier `GrpObj`. Local source
   inspection instead found and reused `GrpCat` and the project group-functor
   encoding rather than creating a group-space definition.
3. `msearch.py grep`, query: "group.*dimension|GroupAlgebraicSpace|smooth.*group"
   in Mathlib AlgebraicGeometry. Two hits, scheme smoothness and an elliptic-curve
   comment; neither gives the required statement.
4. `rg` in `lean/WeilConjectures` for smooth/group/dimension combinations found
   scheme-only group smoothness, Lie dimension, and group-field results; searching
   the item id found no declaration. `rg` in `lean/Sheaf` found the existing
   `LocallySeparatedGroupSpaceScheme`, `SeparatedGroupSpaceGeometricScheme`,
   `RegularGroupSpace`, `AlgebraicSpaceMorphismProperties`, `ProperCurveModuli`,
   and algebraic-space fibre/topology/dimension modules. These supplied the group
   encoding and shared morphism predicates, but none states this theorem.
5. `rg` of Mathlib, WeilConjectures, Sheaf and `dag/lean_names_upstream.json` for
   the two proposed declaration names found no existing declaration.

Source checks: read the actual Stacks `morphisms.tex` lemma
`lemma-smooth-omega-finite-locally-free` (02G1), giving differential rank equal to
fibre dimension, and `groupoids.tex`
`lemma-group-scheme-field-geometrically-irreducible` (047M), whose proof explicitly
uses translation to identify local geometry at a rational point with the identity.
The theorem docstring carries all five steps of the accepted node's proof,
including the arbitrary-algebraically-closed-field argument in its final step.
No statement correction, disputed statement, new node, or dependency repair is needed.

Validation: the prescribed `scompile.py` compiled the file in sandbox and library
mode successfully (2.1 s and 2.0 s), with no errors or unexpected warnings.

## Second reading by Q26

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
