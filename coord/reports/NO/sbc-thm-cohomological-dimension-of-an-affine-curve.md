## Worker report

The module states the two clauses of the node using the recorded ordinary derived-section
cohomology, with a real-data helper defining the canonical constant-section map. Nothing
is proved: the sole postponed theorem is
`AlgebraicGeometry.affineCurve_constantZMod_cohomology`, with the node's six-step proof in
its docstring. There is no statement correction and no disputed statement.

Hypothesis and conclusion correspondence:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The scheme and its map to the field are `(C : Scheme.{u}) (f : C ⟶ Spec (.of k))`.
  `[IsCurve f]` is precisely separated, finite type, and dimension at most one.
  Its class extends `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` and has
  `krullDim_le_one`. It does not require nonemptiness, connectedness, or pure dimension.
- Smooth and affine are `[Smooth f] [IsAffine C]`.
- The integer condition is `(d : ℕ) (hd : 1 ≤ d)` and prime-to-characteristic is
  `(hchar : IsUnit (d : k))`. Both hypotheses are retained, even though
  the more general affine torsion bound would not require prime-to-characteristic.
- The coefficient sheaf is the recorded `C.constantZMod d`, the constant sheaf with value
  `AddCommGrpCat.of (ULift.{u + 1} (ZMod d))`. The lift is a canonical additive copy of Z/d.
- For every nonnegative degree `q` with `1 < q`, the first conjunct asserts `Subsingleton`
  of `(Etale.cohomology AddCommGrpCat.{u + 1} C q).obj
  ((DerivedCategory.singleFunctor _ 0).obj (C.constantZMod d))`.
  A subsingleton abelian group is the zero group. This uses the recorded cohomology
  functor itself, without switching to the Ext presentation `Sheaf.H`.
- The second conjunct is `ConnectedSpace C → IsIso
  (C.constantZModToDerivedCohomologyZero d)`. Mathlib's `ConnectedSpace` includes
  nonemptiness, so this condition is precisely the node's nonempty-connected condition.
  The direction of the isomorphism is Z/d to H0; its inverse gives the displayed H0 to Z/d.
- The requirement "induced by constant sections" is part of the map's construction,
  not merely a comment on a bare existential isomorphism. The helper first applies
  `(constantSheafΓAdj ...).unit.app` to the coefficient group. This is the canonical
  constant-section map into Γ. It then applies the inverse single-complex H0
  identification, the inverse of `HomologicalComplex.singleMapHomologicalComplex`
  mapped through `DerivedCategory.Q`, and H0 of `Functor.rightDerivedFunctorUnit`
  evaluated on the sheaf in degree zero. This is the canonical map Γ(F) to H0(RΓ(F)).
  Every component is supplied by Mathlib/upstream and the helper contains no `sorry`,
  chosen arbitrary map, or extra assumption. It belongs to the canonical arrow specified
  in this theorem's own node; it is not a new independent notion.

Dependency declarations inspected and used:

- `WeilConjectures.AlgebraicGeometry.Curve`: `AlgebraicGeometry.IsCurve` and its full
  class signature/docstring. We use the general class, not `IsConnectedCurve`.
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`:
  `AlgebraicGeometry.Scheme.constantZMod` (full definition with lifted ZMod coefficient).
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.cohomology` and `rightDerivedGlobalSections`, with their
  full signatures and definitions: RΓ followed by derived homology.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, including `toNonempty`.
- `Mathlib.CategoryTheory.Sites.GlobalSections`: `constantSheafΓAdj` and `Sheaf.Γ`;
  `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`:
  `DerivedCategory.singleFunctorCompHomologyFunctorIso`;
  `Mathlib.Algebra.Homology.Additive`: `HomologicalComplex.singleMapHomologicalComplex`;
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`:
  `Functor.rightDerivedFunctorUnit`. These construct the required canonical map.

All recorded proof-dependency modules are imported, including the affine connected-curve
calculation, torsion cohomological dimension, the separably closed field bound, the
constant-section theorem, enough injectives, right derived degree zero, and bounded-below
K-injectivity. `thm-sc-affine-torsion-cd` has no Lean record and hence no import yet; it is
a future proof input, not a prerequisite for typing this statement. The empty case does
not use a vacuous connectedness hypothesis.

Edge cases checked: the empty affine curve is included in the first conjunct and excluded
from the second by ConnectedSpace; disconnected and mixed zero/one-dimensional schemes
are included; Spec k is allowed as a connected zero-dimensional curve; d = 1 gives zero
coefficients; d = 0 is excluded by hd; characteristic zero allows every positive d, since its image in k is a unit. In
positive characteristic p, IsUnit (d : k) says precisely that p does not divide d. No degree-one vanishing
is claimed. Every variable and the sole universe u are explicitly bound.

Searches made:

- msearch LeanFinder: "Etale cohomology of a smooth affine curve over an algebraically
  closed field vanishes above degree one and constant coefficients degree zero on a
  connected curve". Eight unrelated cotangent/singular-homology hits; no match.
- msearch Loogle: `AlgebraicGeometry.IsCurve, Subsingleton`. No hits; IsCurve is unknown
  to the Mathlib search service (it is an upstream project declaration).
- msearch grep: `constantZMod|subsingleton_sheafH_constantZMod`. Zero Mathlib hits.
- msearch LeanSearch: "Canonical map from constant sections to degree zero derived etale
  cohomology and affine curve cohomology vanishing". Service unavailable (Internal Server
  Error); other search kinds and source inspection were used.
- rg in upstream WeilConjectures and project lean/Sheaf for affine/cohomology and
  constantZMod found the upstream affine-curve theorem. Its full signature requires
  `[SmoothOfRelativeDimension 1 f]`, which excludes zero-dimensional components. It also
  states only a bare `Nonempty` additive equivalence in the Ext cohomology presentation.
  It is therefore not an exact existing match for this node.
- rg for the item id in upstream found its theorem docstring and two uses in
  FourierTransform/ArtinSchreierCohomology and SixFunctors/Etale/SmoothBaseChange/Vanishing.
- rg of both proposed declaration names in Mathlib, upstream, project lean/Sheaf and
  dag/lean_names_upstream.json gave zero matches.

Source checked: the blueprint item's text and proof and Stacks etale-cohomology.tex,
`theorem-vanishing-affine-curves` (Tag 03SC), particularly clause (2). The already-reviewed
node's conditional degree-zero assertion correctly repairs the blueprint's unconditional
H0 wording; no additional node change is made here.

Validation: the entire delivered module compiled on the server through scompile.py,
with no errors or warnings. The module's library-path compile took 5.7 seconds.

## Second reading by NO

Independent verdict: the Lean states exactly the reviewed DAG node. No mathematical or
Lean mismatch was found; the only change in this second reading is this review report.
The node has no stage-2 `statement_change`, new definition nodes, or dependency modules.
The stage-1 repair of the blueprint's unconditional H0 assertion is already in the base.
I checked the source first: etale-cohomology.tex, theorem-vanishing-affine-curves
(Tag 03SC), explicitly assumes an algebraically closed field and a separated finite-type
scheme of dimension at most one; clause (2) requires affineness, with no connectedness
or pure-dimension assumption. The constant-section identification follows from
remark-constant-locally-constant-maps (Tag 03P5). The Lean follows this reviewed node,
including its positive prime-to-characteristic coefficient restriction.

Object/hypothesis/conclusion checklist, with the node and Lean open:

- Field k, algebraically closed: `(k : Type u) [Field k] [IsAlgClosed k]`. Pass.
- Scheme C over k: `(C : Scheme.{u}) (f : C ⟶ Spec (.of k))`. The explicit map is
  permitted because the recorded curve definition takes f. Pass.
- Curve: `[IsCurve f]`. I opened Curve.lean: this extends `IsSeparated f`,
  `LocallyOfFiniteType f`, `QuasiCompact f`, and has `topologicalKrullDim C ≤ 1`.
  Finite type is locally finite type plus quasi-compact; no dimension-one, nonempty,
  connected, or integral condition is introduced. Pass.
- Smooth and affine: `[Smooth f] [IsAffine C]`. These are precisely the two additional
  geometric assumptions, with no properness or relative-pure-dimension condition. Pass.
- Positive integer d: `(d : ℕ) (hd : 1 ≤ d)`. Pass.
- Prime to char k: `(hchar : IsUnit (d : k))`; in a field this is equivalent to its
  image being nonzero, hence the required characteristic condition. Pass.
- Constant etale sheaf: `C.constantZMod d`. I read Kummer.lean's actual definition:
  constantSheaf at `AddCommGrpCat.of (ULift.{u + 1} (ZMod d))`, the canonical lifted
  copy of Z/d, with no additional scheme or integer hypotheses. Pass.
- Etale cohomology: `(Etale.cohomology AddCommGrpCat.{u + 1} C q).obj
  ((DerivedCategory.singleFunctor _ 0).obj (C.constantZMod d))`. I read LowerShriek.lean:
  cohomology is RΓ followed by derived homology; RΓ is the total right derived functor
  of `Sheaf.Γ`. Thus this is the recorded ordinary cohomology, for a sheaf in degree zero.
  It is not compactly supported cohomology or the different Ext presentation. Pass.
- Higher vanishing: `∀ (q : ℕ), 1 < q → Subsingleton (...)`. Nonnegative degrees and
  q > 1 are exactly the quantifiers; a subsingleton abelian group is zero. Pass.
- Conditional H0: the second conjunct is `ConnectedSpace C → IsIso
  (C.constantZModToDerivedCohomologyZero d)`. I opened Connected.Basic: ConnectedSpace
  extends preconnectedness and includes Nonempty. This condition therefore applies
  precisely to the node's nonempty connected schemes, without restricting vanishing.
  An isomorphism from the lifted coefficient group to H0 gives the displayed reverse
  identification by inversion. Pass.
- Induced by constant sections: the helper is real data. I read Sites.GlobalSections,
  DerivedCategory.FullyFaithful, Homology.Additive and RightDerivedFunctor.Defs.
  The map starts with the unit of `constantSheafΓAdj`, hence constant sections into Γ.
  The inverse single/homology comparison sends Γ(F) into H0(single Γ(F)); the inverse
  `singleMapHomologicalComplex` identifies that single complex with Γ(single F).
  Finally H0 of `rightDerivedFunctorUnit` gives H0(RΓ(single F)). Each arrow has the
  canonical orientation and normalization; no arbitrary isomorphism, existence choice,
  or extra hypothesis replaces the prescribed map. Pass.

Edge cases: empty C satisfies the geometric hypotheses and remains in the vanishing
conjunct; ConnectedSpace excludes it only from H0. Disconnected schemes and mixtures of
zero- and one-dimensional components are included. Spec k is an allowed connected
zero-dimensional case. d = 1 gives zero coefficients; d = 0 is excluded explicitly.
Degree zero and degree one are excluded only from the higher-vanishing assertion;
H0 has its separate clause, and no H1 vanishing is claimed. Characteristic zero admits
all positive d, and characteristic p excludes precisely multiples of p. The single
universe u is bound explicitly; schemes and their base fields can be lifted to a common
universe, and the coefficient lift u+1 matches the recorded small-etale-site interface.
There is no extra independent universe equality assumption.

Independent duplicate searches (2026-10-15):

- msearch LeanFinder: `constant coefficient etale cohomology affine algebraic curve
  higher vanishing canonical degree zero sections`. Eight cotangent/etale-algebra or
  affine elliptic-coordinate hits; no matching theorem.
- msearch Loogle: `"constantSheaf", "IsIso"`. One hit for an adjunction counit on a
  constant sheaf; it is not the scheme-cohomology statement or this constant-section map.
- msearch grep: `rightDerivedFunctorUnit|constantSheafΓAdj|cohomological.*curve`.
  Six Mathlib hits concerning the general global-sections adjunction, no full match.
- Independent rg in upstream WeilConjectures, Mathlib homology and algebraic geometry,
  and project lean/Sheaf found the general single-complex comparisons, the existing
  curve bounds, and the upstream theorem
  `subsingleton_sheafH_constantZMod_and_nonempty_addEquiv_sheafH_zero`. I opened its
  full signature: it requires `[SmoothOfRelativeDimension 1 f]`, omits zero-dimensional
  cases and uses Sheaf.H with a bare Nonempty additive equivalence. It is not an exact
  existing declaration for this node. No matching combined theorem or specialized
  canonical map already exists. Related derived-plus single-unit helpers use a different
  bounded-below interface and do not duplicate this composite with constant sections.

The two declarations have source/blueprint docstrings, and the theorem docstring gives
all six proof steps in order, including the general affine bound and empty-scheme case.
The only sorry is the named theorem; nothing is proved in this delivery. The helper
contains no sorry or hollow data. The recorded `lean.statement` is byte-for-byte the
file signature before `:=`, all binders and universes are explicit, and every line is
within 100 columns. The stated proof dependencies are imported; thm-sc-affine-torsion-cd
has no recorded Lean declaration and is not needed to type this statement.

Validation: reran scompile.py NO sbc-thm-cohomological-dimension-of-an-affine-curve on
lean/Sheaf/AlgebraicGeometry/AffineCurveCohomologicalDimension.lean. Both sandbox and
library-path server compiles passed without errors or warnings (5.4 s and 6.0 s).
