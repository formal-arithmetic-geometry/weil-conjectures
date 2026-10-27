## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricNodalPinchingCriterion` states
`AlgebraicGeometry.geometric_nodal_pinching_criterion`, with `sorry` as its sole proof.
It introduces no definitions and proves nothing. The source statement is unchanged.
The only added statement dependency is the already landed definition node
`def-sfb-nodal-geometric-fibre-local-rings`, whose completion and node-ring definitions
are reused directly.

Hypotheses, matched individually:

- The base scheme is `S : Scheme.{u}`. The four schemes with their structure maps are
  `X Z T P : Over S`. Morphisms in `Over S` include precisely the required base compatibility.
- Properness, flatness and finite presentation of X/S are `[IsProper X.hom]`,
  `[Flat X.hom]`, and `[LocallyOfFinitePresentation X.hom]`. Properness already supplies
  quasi-compactness and quasi-separatedness, so these express finite presentation.
- Z/S and T/S are finite étale: the separate `IsFinite` and `Etale` instances on each
  structure map. No splitting over S is imposed.
- The branch inclusion is `i : Z ⟶ X` with `[IsClosedImmersion i.left]`.
  `hi` puts every image point in `X.hom.smoothLocus`, exactly the relative smooth locus.
- `j : Z ⟶ T` has `[Etale j.left]` and `[j.left.IsFiniteLocallyFreeOfDegree 2]`.
  The latter extends finite locally free and requires the fibre degree to be two;
  its inherited `IsFinite` is the required finiteness of j.
- P/S is proper and finitely presented via `[IsProper P.hom]` and
  `[LocallyOfFinitePresentation P.hom]`; no `Flat P.hom` appears.
- `a : X ⟶ P` and `b : T ⟶ P` are S-maps, and `hab : i ≫ a = j ≫ b`
  expresses compatibility on Z.
- `hpushout` quantifies over every `Ω : Type u` with `[Field Ω] [IsAlgClosed Ω]` and
  every `g : Spec (.of Ω) ⟶ S`. `IsPushout` is taken in `Scheme`, with the four actual
  maps obtained by `(Over.pullback g).map`. This is a pushout in all schemes, not merely
  in affine schemes or in a subcategory of proper schemes.
- `hX` gives, separately, nonemptiness (`Nonempty`), reducedness (`IsReduced`), pure
  dimension one (`Scheme.IsPureDimension 1`), and the completed-local-ring condition
  at every nonsmooth closed point (`closedPoints` followed by nonmembership in the
  fibre projection's `smoothLocus`). The condition is `Nonempty` of a ring equivalence
  from the maximal-ideal completion to `NodalFiber.powerSeriesQuotient Ω`.
  No connectedness, normalization or smoothness of every point is assumed.

Conclusions, matched individually, under the same universal quantifier over Ω and g:

- The first three conjuncts give nonemptiness, reducedness and pure dimension one of
  `pullback P.hom g`.
- The next conjunct gives the identical completed-local-ring condition for its
  nonsmooth closed points.
- The next two conjuncts state that every nonclosed point of X's fibre and of P's
  fibre is smooth, respectively.
- The two existential cofans express that Z's and T's fibres are finite disjoint
  unions of `Spec Ω`, over Ω. Their legs come from morphisms in `Over (Spec Ω)`, and
  their underlying scheme cofans are colimits. Natural numbers m and n include zero.
- For every `t : pullback T.hom g`, the map `z : Fin 2 → pullback Z.hom g` lists exactly
  its inverse image under the base change of j, by the displayed biconditional.
  Injectivity of its composite with the base change of i asserts two distinct branch
  points in X's fibre; the final clause puts both in that fibre's smooth locus.
- The existential opens U and V are precisely the complements of the images of the
  base changes of i and b. Their isomorphism e commutes with the base change of a and
  with their maps to `Spec Ω`. Thus the specified map identifies the complements as
  Ω-schemes, carrying their local rings, smooth loci and old singularities to each
  other. This records preservation by the actual map, not an unrelated isomorphism.
- For every t the first ring equivalence identifies the completion at the actual image
  `((Over.pullback g).map b).left t` with the `CommRingCat` pullback of the two
  `PowerSeries.constantCoeff` maps. The second identifies that ring with
  `NodalFiber.powerSeriesQuotient Ω`, giving precisely the stated chain
  Ω[[u]] ×_Ω Ω[[v]] ≅ Ω[[u,v]]/(uv).

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  its morphisms. The full structure extends locally ringed spaces with affine charts.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper` (separated, universally closed and locally finite type).
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat` (the affine-local condition equivalent to flat stalk maps).
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite` (affine with finite ring maps).
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion` (closed embedding and surjective stalk maps).
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`, through `Scheme.Hom.smoothLocus`.
- `def-pc-finite-locally-free`:
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`,
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree`; read its full signature
  and its `fiberDegree_eq` field and inherited structures.
- `def-weil-geometric-fibre`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`; applied to a structure map and g.
- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.Limits.IsColimit`; the pushout uses `CategoryTheory.IsPushout`.
- `def-pc-reduced-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsReduced`, meaning all section rings are reduced.
- `def-weil-pure-dimension`: `Sheaf.AlgebraicGeometry.PureDimension`,
  `AlgebraicGeometry.Scheme.IsPureDimension`; all irreducible components have dimension 1.
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `AdicCompletion`, used by the existing completed-local-ring helper. Its ring structure
  is supplied by `Mathlib.RingTheory.AdicCompletion.Algebra`.
- `def-weil-pbc-multivariate-power-series`: `Mathlib.RingTheory.MvPowerSeries.Basic`,
  `MvPowerSeries`, used by the existing split-node-ring helper with variable type `Fin 2`.
- `def-weil-geometric-point`: the recorded inline encoding with `IsAlgClosed` and a
  morphism `Spec Ω ⟶ S`. Read `Scheme.SpecToEquivOfField` in
  `Mathlib.AlgebraicGeometry.ResidueField`: arbitrary such maps encode a point and a
  residue-field embedding, not just one chosen algebraic closure per point.
- `def-weil-algebraic-closure`: `Mathlib.FieldTheory.IsAlgClosed.Basic`, `IsAlgClosed`;
  the dependency's mathlib_match also records `AlgebraicClosure`, needed only by the proof.
- `def-weil-closed-points`: `Mathlib.Topology.JacobsonSpace`, `closedPoints`.
- Added landed dependency `def-sfb-nodal-geometric-fibre-local-rings`:
  `Sheaf.AlgebraicGeometry.NodalGeometricFibreLocalRings`,
  `AlgebraicGeometry.NodalFiber.completedLocalRing` and `powerSeriesQuotient`, including
  their real ring structures. No copy of either definition is introduced.

The canonical base-change functor is Mathlib's `CategoryTheory.Over.pullback`, whose
source explicitly constructs the underlying maps with `pullback.lift`. The one-variable
rings and residue maps are `PowerSeries` and `PowerSeries.constantCoeff`. The ring
pullback is the existing `CommRingCat` categorical pullback, not an arbitrary ring.
All recorded proof modules, including the field pinching theorem and Ferrand theorem,
are imported without `public` when not already public statement dependencies. The
seven-step natural-language proof is carried in the theorem's docstring.

Sources opened: `literature/stacks-project/curves.tex`, `lemma-complete-local-ring-pushout`
(Tag 0E36), and `example-glue-points` (Tag 0C1J), together with the recorded field
pinching and Ferrand theorem signatures and their complete proof docstrings.

Edge cases checked before drafting:

- Empty S: the geometric-point hypotheses and conclusions are vacuous, as they should be.
- Empty Z=T: degree two has no target point at which to impose a condition; the empty
  cofans use m=n=0, the branch assertions are vacuous, and the complement isomorphism
  gives exactly the whole-fibre isomorphism PΩ ≅ XΩ. No nonempty branch binder is used.
- Disconnected S and geometric fibres: no connectedness or integrality assumption occurs.
- Two points on the same component are permitted: injectivity only distinguishes the
  two image points and says nothing about their irreducible components.
- Smooth fibres and old nodes away from Z: the nonsmooth closed-point hypothesis is
  respectively vacuous or retained via the complement isomorphism. Nonclosed points
  receive their own smoothness conclusion, not an assumption.
- Characteristic two: no sign, separability degree restriction, or division by two is
  used. The node ring is the quotient by uv in every characteristic.
- Pure dimension is not replaced by mere total dimension. Nonemptiness is separate,
  because pure dimension alone holds for the empty scheme.
- All schemes and testing fields use the same arbitrary universe u, in the project's
  geometric-point convention. There is no smaller independent test universe.

Searches for an existing exact statement, performed through the required msearch.py:

- LeanFinder: `Geometric fibres of pinching two smooth points of a reduced nodal curve
  are reduced nodal curves` returned eight Weierstrass-curve facts, no pinching theorem.
- Loogle: `"AlgebraicGeometry", "pinching"` returned zero hits.
- Mathlib grep: `nodal|ordinaryDouble|pinch` under `AlgebraicGeometry` returned zero hits.
- LeanSearch: `Pushout of a reduced curve identifying two smooth points has nodal
  completed local rings` returned eight categorical/ring pushout and pullback facts,
  no exact scheme statement.
- Project rg searches for the item id and the proposed theorem name returned no match
  in `lean/WeilConjectures` or `lean/Sheaf`. Concept searches for `nodal`, `pinching`,
  `ordinaryDouble`, and the completion helpers found `RelativeNodalPointPinching`,
  `TraitEtaleBranchPinching` and `NodalGeometricFibreLocalRings`. The first is an
  existence theorem for a semistable curve over a field; the second imposes trait and
  projectivity hypotheses. Neither states this theorem about a given P over arbitrary S.
  The third supplies the existing notions reused here. The proposed name also has no
  match in `dag/lean_names_upstream.json`.

No disputed statement, source correction, new definition node, or dependency repair.
The initial compile required explicit `C := Scheme.{u}` in scheme pullbacks occurring
in type positions and parentheses around the hom type of each cofan leg. These were
elaboration fixes, with no change in mathematical statement. Overlong lines were wrapped.

## Second reading by Q07

Author's final rereading; the independent delivery review is left to the maintainer as
specified by this dispatcher brief. Compared the unchanged node statement against every
binder and conjunct above. Checked especially that the pushout is in Scheme, that the
fibres and their maps are canonical, that the split coproducts are over Ω, that the two
branches exhaust each fibre of j, and that no condition places them on different
components. Both source and output nonclosed-point clauses are present, and old
singularities are preserved by an isomorphism of the actual complements over Ω.
The branch completion is at bΩ(t), and its intermediate pullback uses exactly the
constant-coefficient maps. Checked each listed dependency declaration against its
source, including the landed local-ring helpers. No mathematical mismatch was found.
