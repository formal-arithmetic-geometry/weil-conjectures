## Worker report

The module `Sheaf.AlgebraicGeometry.PointedGenericIntegralActionSquarePower` states
`AlgebraicGeometry.exists_tensorPow_square_of_pointed_generic_integral` with `sorry`.
No definition, auxiliary theorem, new node, or dependency repair is needed. The existing
normal-group square theorem is not this statement: it treats left multiplication on H,
whereas this item concerns a separate pointed integral S-scheme Y with an arbitrary action.
The node is unchanged except for its `lean` field.

Hypothesis and conclusion correspondence:

- The base scheme is `S : Scheme.{u}`. `IsAffine S` and `IsLocallyNoetherian S` express
  an affine Noetherian scheme: affineness supplies quasi-compactness, so local
  Noetherianness is equivalent here to Noetherianness. `IsIntegral S` includes
  nonemptiness, reducedness, and irreducibility. There is no empty-base case in this node.
- Normality is precisely `hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
  IsIntegrallyClosed (S.presheaf.stalk s)`, the stated condition on every local ring.
- The generic point is `genericPoint S`, with `genericPoint_spec S` giving
  `IsGenericPoint (genericPoint S) Set.univ`. The generic base morphism is
  `S.fromSpecStalk (genericPoint S)`. Its source is `Spec S.functionField`, since
  `Scheme.functionField` is definitionally the stalk at that point; Mathlib's integral
  scheme instance makes it a field. Thus no arbitrary generic map or field is supplied.
- `H : Over S` is H with its structure morphism. `GrpObj H` supplies multiplication,
  identity, inverse and their identities in the category of S-schemes. `Smooth H.hom`,
  `IsSeparated H.hom`, `LocallyOfFiniteType H.hom` and `QuasiCompact H.hom` express smooth,
  separated and finite type. Separatedness means its diagonal is a closed immersion.
- `GeometricallyConnected H.hom` says all field-valued geometric fibres are nonempty
  connected spaces. This is the node's geometrically connected fibre hypothesis;
  equivalently it can be tested on algebraic closures of the residue fields. It does
  not impose commutativity or properness on H.
- `Y : Over S` provides p. `Smooth Y.hom`, `IsSeparated Y.hom`,
  `LocallyOfFiniteType Y.hom`, `QuasiCompact Y.hom`, and `IsIntegral Y.left` render each
  stated property of p and Y. In particular these do not assert integral special fibres.
- `e : Over.mk (𝟙 S) ⟶ Y` is the S-section: its underlying morphism S → Y satisfies
  `e.left ≫ Y.hom = 𝟙 S` by being a morphism in Over S. It is not an equivariant map.
- `ModObj H Y` is Mathlib's action object: its `smul : H ⊗ Y ⟶ Y`, `one_smul`, and
  `mul_smul` are exactly the specified S-action and its two axioms. These are existing
  Mathlib definitions, not an arbitrary family of translations or new private copies.
- `GeometricallyIntegral (pullback.snd Y.hom
  (S.fromSpecStalk (genericPoint S)))` applies precisely to the generic fibre structure
  map Y_eta → Spec k(S). The geometric-integrality class requires integral base change
  along every field extension, including nonemptiness. There is no condition on the
  special fibres of Y beyond the hypotheses already stated.
- `L : Y.left.Modules` and `[L.IsInvertible]` render the arbitrary invertible O_Y-module.
- `∃ r : ℕ, 1 ≤ r ∧ ∀ (B : Over S) (g h : B ⟶ H), ...` renders a positive integer
  chosen before every test S-scheme and both group-valued points. Positive natural
  numbers and positive integers parameterize exactly the same tensor powers.
- In Over S, `Y ⊗ B` is Y_B. `fst Y B` is its map to Y, and `snd Y B` is q_B.
  For k = g,h,g*h the morphism `((snd Y B ≫ k) • fst Y B).left` is the composite
  Y_B → Y_B → Y sending (y,b) to k(b)y. Its tensor pullback of `L.tensorPow r`
  is canonically τ_k^* M_B by `tensorPullbackSectionComp`. Thus the three displayed
  translated terms are exactly the node's translated base-changed modules.
- The first factor on the left is the gh-translation, the second is M_B. On the right
  the factors are the g-translation, h-translation, and `(tensorPullback (snd Y B).left).obj N`.
  These are the stated sheaf tensor products; parentheses only select the associator.
- `∃ N : B.left.Modules, N.IsInvertible ∧ Nonempty (...)` gives precisely an invertible
  base module and existence of the displayed isomorphism, without an extra coherence
  condition or a chosen canonical trivialization.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, used through affineness of S;
  `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, with
  `IsDomain` in the node's prescribed inline normality condition.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`, through
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`'s `IsSeparated` definition.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, also the fibre products underlying products in Over S.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`, used in the geometric-fibre interpretation.
- `Mathlib.Topology.Sober`: `IsGenericPoint`, `genericPoint`, `genericPoint_spec`;
  `WeilConjectures.AlgebraicGeometry.FunctionField` publicly imports Mathlib's
  `Scheme.functionField`, the dependency node's arbitrary-integral-scheme clause.
  The component-product definition is intentionally not used for an integral S.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral`;
  `Mathlib.AlgebraicGeometry.Geometrically.Connected`: `GeometricallyConnected`, based
  on `ConnectedSpace` from `Mathlib.Topology.Connected.Basic` (including nonemptiness).
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`
  and `Scheme.Modules.tensorPow`, using the existing sheaf monoidal tensor.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: `Scheme.Modules.tensorPullback`
  by public import, and its canonical composition comparison `tensorPullbackSectionComp`.
  The underlying tensor formula was read in `WeilConjectures.AlgebraicGeometry.TensorPullback`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, the existing localization sheaf tensor.
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: `GrpObj` and its group structure
  on `B ⟶ H`; `Mathlib.CategoryTheory.Monoidal.Cartesian.Mod`: `ModObj`, `Hom.smul`,
  and `Hom.mulAction`. These introduce no new notion beyond the node's explicit data.

The module also imports each recorded available proof dependency, privately, including
Slicing, SmoothFiber, geometric reducedness, smooth/finite-presentation/proper/flat
permanence, torsion-freeness, affine pullbacks, GeometricallyIrreducibleProduct and
FieldProductSquarePower. The two still unstated proof nodes
`lem-sfb-smooth-normal-ascent` and `lem-sfb-normal-noetherian-generic-line-pullback`
have no module to import; neither is a statement prerequisite. The docstring retains
all eight proof steps and their named dependencies for stage 3.

Source checked: the author PDF at
https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf, Proposition 5.9
final assertion (1) and Lemma 5.7, printed pages 14–15. The reordered-factor argument
is expressly in the source proof of case (1); it does not require special fibres of Y
integral. No statement correction or STATEMENT-DISPUTED flag is needed.

Edge cases checked: positive exponent excludes zero; trivial group and trivial action
are allowed; no commutativity is assumed, and gh stays in that order; a section not
fixed by the group is allowed; Y special fibres may be disconnected; B may be empty,
nonreduced, or non-Noetherian; no properness, algebraic-closedness, characteristic, or
Noetherian hypothesis is imposed on B. S and Y cannot be empty by integrality.
All schemes lie in an explicitly arbitrary universe u, as in Mathlib's scheme category;
there is no independent lower test universe, unbound universe, or auto-implicit binder.

Searches actually run with `batch2/msearch.py`:

- LeanFinder: `A positive tensor power of a line bundle on a pointed smooth integral
  scheme satisfies the theorem of the square under a connected group scheme action`.
  Eight hits, including `CommRing.Pic.mul_eq_tensor`, `Scheme.basicOpen_pow`, and
  pullback triplet constructions; none states this result.
- Loogle: `"Pic", "tensor"`. Two hits, `CommRing.Pic.mk_tensor` and
  `CommRing.Pic.mul_eq_tensor`; both concern tensor multiplication of ring Picard classes.
- Mathlib grep: `squarePower|square_power|theorem.of.the.square`, AlgebraicGeometry.
  Zero hits.
- LeanSearch: `theorem of the square for a line bundle on a scheme with a group action`.
  Returned ordinary group-action and projectivization results, not this scheme theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for square power, square theorem,
  group action and the exact item id. The NormalGroupSquarePower theorem is the distinct
  group-only case, and FieldProductSquarePower is a proof dependency. No exact theorem.
- Read Mathlib Cartesian/Mod and Cartesian/Grp to locate the existing action and group
  data; no replacement definition is introduced. The read-only CompactObject example
  is withdrawn in this checkout, so its node record and current module-mode sibling
  NormalGroupSquarePower were used for conventions instead.

## Second reading by NJ

This is a second pass by the dispatched worker; no independent second reader was
started, as the dispatch explicitly prohibits agents. The maintainer's independent
review remains responsible for independent statement review.

Reopened the node and module together. Checked each base property, the two finite-type
conjunctions, the separate integral-Y hypothesis, the section in Over S, the group and
action axioms, the generic-only geometric-integrality hypothesis, and the arbitrary line.
Checked the quantifier order r before B,g,h, the exact gh,g,h order of the three
translations, unshifted M_B, existence and invertibility of N, and the q_B pullback.
The composite-to-Y pullbacks express τ_k^* M_B using the existing canonical pullback
composition isomorphism, so no clause is lost. The geometric connectedness class retains
nonemptiness. No mismatch or correction was found on this pass. All declarations use
explicit universes and disabled auto-implicits; all theorem proofs are `sorry`.
