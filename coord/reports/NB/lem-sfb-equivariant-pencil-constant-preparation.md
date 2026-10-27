## Worker report

The module `Sheaf.AlgebraicGeometry.EquivariantPencilConstantPreparation` states
`AlgebraicGeometry.exists_equivariant_pencil_constant_preparation`, with its proof `sorry`.
The helper `EquivariantPencilConstantPreparation` is a fully expanded existential
proposition for its conclusion, not an existence axiom or a choice of model. All of its
data and conditions are written out; it has no postponed proof. There are no new DAG
nodes, dependency repairs, or changes to the mathematical node statement.

Source read: the publisher PDF of de Jong, *Families of curves and alterations*,
§§3.2–3.5, printed pp.605–606 (PDF pages 7–8), including its compatible-pair group,
local finite pencils, avoidance of 0,1,infinity, and constant base change. Also read the
current blueprint `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, clause (3).
This node is an auxiliary preparation, not that unit's own statement.

Hypotheses:

- `k`, `[Field k]`, `S`, `X`, and `[IsIntegral S]`, `[IsIntegral X]` introduce the original
  objects. `pS` is the base structure morphism; the structure morphism of X is `f ≫ pS`.
- `[IsHProjective pS]`, `[LocallyOfFiniteType pS]`, `[QuasiCompact pS]` express the base
  projectivity and finite type; `hnormal` asks that every local ring be an integrally
  closed domain, exactly the node's normality convention.
- `f`, `[IsHProjective f]`, `[LocallyOfFiniteType (f ≫ pS)]`, and
  `[QuasiCompact (f ≫ pS)]` express the relative projectivity and finite type of X.
- `hpure` states pure dimension one on every algebraically closed geometric fibre.
  The smoothness and geometric-integrality instances on `pullback.snd f
  S.fromSpecFunctionField` express the properties of C. The site and scheme universe is
  consistently `u`; the group universe `v` is independent.
- `M` is a closed subset carrying its canonical reduced closed subscheme via
  `Scheme.IdealSheafData.vanishingIdeal M`; `hMfinite`, `hMetale` say this subscheme is
  finite etale over K. A reduced closed subscheme is uniquely determined by this support.
- `H`, `[Group H]`, `[Finite H]`, `ρk`, `ρX`, `ρS`, `hk`, `hX` give the compatible scheme
  actions. The k-action is an action on Spec k, so it permits semilinearity.
  `hMstable` expresses stability of the generic closed marking, without constructing a
  second generic action or assuming faithfulness.
- `ell`, `hell`, `hell5`, `hellchar` render exactly the prime, lower bound and unequal
  characteristic conditions.
- The existential algebra in the theorem is fixed by its Spec/generic-point equation;
  `aK`, `aF` are fixed by inverse pullback of the given scheme automorphisms. These are
  conclusions supplying canonical interfaces, not additional hypotheses.

Conclusions, in the helper's written order:

- `B`, `_fixedBase` give exactly K^H, as a subfield with its usual inclusion.
  `E₀`, `K₀`, their algebra, finite-dimensional and separability witnesses, and the
  scalar-tower witnesses give the required finite tower. The B/K₀ finite-dimensional
  and `IsGalois` witnesses express finite normal separability. `commonClosureE`,
  `commonClosureK`, `_commonClosure` embed the tower in the actual `AlgebraicClosure K`.
  `root` and `_primitiveRoot` give the primitive ell-th root in K₀.
- `_positiveDimension` expresses E₀=K as bijectivity of the specified field inclusion,
  which does not impose a literal equality of unrelated Lean carrier types.
- `H₀`, `projection`, `fieldAction` and the injectivity, compatibility, and exhaustiveness
  assertions identify H₀ with precisely the pairs (h,sigma) in the node, with the
  componentwise law supplied by both monoid homomorphisms. This is not an arbitrary
  group extension. `projection_surjective` and `kernel_constants` give surjectivity
  and K₀^A₀=K; A₀ is directly `projection.ker`, not a freely chosen subgroup.
- The domain witness and `tensorField` assert the tensor algebra is a field with its
  original ring operations. `FractionRing (F ⊗[K] K₀)` represents that same field through
  the canonical localization, avoiding an unrelated field instance. `finiteTensor` and
  `separableTensor` express F₀/F finite separable. This is the same presentation used
  by the already stated invariant-pencil theorem. `tensorAction_pure` is precisely
  (h,sigma)(z tensor c)=h(z) tensor sigma(c), through this canonical localization.
  `kernel_functionField` says that the fixed elements are exactly the image of F.
- S₀ and X₀ are literally `S.normalizationIn K₀` and `X.normalizationIn
  (FractionRing (F ⊗[K] K₀))`. Their integral witnesses, normal stalk assertions,
  projectivity and finite-type assertions, `finiteS`, and `surjectiveS` render all
  model conditions. `q`, `q_over`, `q_generic` specify the map between the models on
  the schemes and generic fields. `projectiveX`, `pureFibres` give its projectivity
  and pure geometric fibres.
- `modelComparison`, its two projection equations, `finiteComparison` and
  `surjectiveComparison` give the required finite surjection onto the full fibre
  product. `genericComparison`, with both base and original-X equations, is an actual
  isomorphism with C ×_K K₀, not an arbitrary identification of abstract curves.
- `actionX`, `actionS`, their equations on original models and field spectra, `action_q`,
  `actionComparison` with both projection equations, and `action_modelComparison`
  render equivariance of each of the four displayed morphisms. `uniqueActions` says
  that any extensions inducing the same prescribed generic field actions equal these.
  The inverse in `Spec.map` converts the left field action to the left scheme action.
- `qE`, `qE_over`, `qE_generic` specify the intermediate normalized relative model.
  `sE`, `xE`, their generic/base/original-model equations, and `finiteXE` give the finite
  map to X_E₀ over S₀→S_E₀. The comparison on S_E₀ is fixed on Spec K₀ by `sE_generic`.
- `r`, `V`, `coverE`, `affineE` give the finite affine cover. `pencilE` with its over-base,
  finite and surjective assertions gives each psi_i. `oneOpen` gives r=1 in dimension
  zero. The preimages `sE ⁻¹ᵁ V i` are exactly the opens U_i; `coverK`, `affineK` express
  their covering and affineness.
- `localComparison` with both projections is the induced restricted X₀→X_E₀ map;
  `pencilK`, `pencilK_over`, `inducedPencil` express the induced pencils via the
  projective-space base-change map. `pencilK_finite`, `pencilK_surjective` give finite
  surjectivity, without requiring any invariance of individual pencils.
- `M₀`, `markingPreimage` specify the reduced inverse image of M under the canonical
  generic comparison. `markingFinite`, `markingEtale`, `markingStable` give the finite
  etale and H₀-stable assertions.
- `genericPencils` supplies each generic-point lift, the actual generic pencil, and its
  comparison to the global pencil via the projective-space map. The two equations for c
  determine its canonical map to the generic curve. It is etale above a nonempty target
  open; this is dense since the projective line over K₀ is irreducible (the node's
  definition of generically etale). Each of its three inverse fibres
  is explicitly finite, etale and reduced; the last pointwise implication expresses
  disjointness from M₀.

Dependency declarations used, after opening their definitions/signatures/docstrings:

- `Field` and `Algebra` from Mathlib, for fields and extensions.
- `AlgebraicGeometry.IsIntegral` (`Mathlib.AlgebraicGeometry.Properties`),
  `LocallyOfFiniteType` and `QuasiCompact` from Mathlib's morphism modules.
- `AlgebraicGeometry.IsHProjective` from
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`.
- `Scheme.functionField` and `Scheme.fromSpecFunctionField`, the generic stalk and map,
  through `WeilConjectures.AlgebraicGeometry.FunctionField` and its Mathlib complement;
  the component-product generalization is not needed for integral schemes.
- `Scheme.IsPureDimension` from `Sheaf.AlgebraicGeometry.PureDimension`.
- `pullback`, `pullback.fst`, `pullback.snd` from Mathlib's pullback module, for both
  geometric fibres and all the other fibre products.
- `Smooth`, `GeometricallyIntegral`, `IsFinite`, `Surjective`, `Etale` from the
  dependency-recorded Mathlib modules.
- `Scheme.normalizationIn`, `Scheme.fromNormalizationIn`, and
  `Scheme.fromSpecOfAlgebraFunctionField` from
  `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`.
- `ProjectiveSpace`, its `map`, and the existing `ProjectiveLine` specialization from
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace` and `.ProjectiveSpace.Line`.
- `AlgebraicClosure` from `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`.
- `invariantPencilConstantMap`, `invariantPencilSpecialPoint` and the already stated
  local-pencil interface from `Sheaf.AlgebraicGeometry.InvariantLocalCurvePencils`.
- `Scheme.functionFieldAut` from `WeilConjectures.AlgebraicGeometry.StalkAut`.
  The recorded relative-model module and the stated finite/etale base-change proof
  dependencies are imported for the later proof. Unstated proof dependencies are not
  copied or assumed as hypotheses.

Searches actually run:

- msearch leanfinder: “Equivariant constant extension of a relative curve preserving
  finite local pencils and adjoining roots of unity”: eight unrelated Weierstrass-curve
  hits; no exact statement.
- msearch loogle: `IsGalois, IsPrimitiveRoot`: zero hits.
- msearch grep: `equivariant.*pencil|constant.*preparation`: zero hits.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for pencil/constant preparation and the
  exact node id: the invariant-local-pencil theorem and high-genus consumer were found,
  neither states this whole preparation. No existing declaration of this item exists.
- Searched the DAG and the source modules for compatible-pair and semilinear-envelope
  interfaces. The envelope is an unstated proof dependency, not a definition prerequisite;
  its conclusions are stated explicitly here rather than assumed.

Edge cases checked: the empty marking, trivial group, nonfaithful group action, moving
k-action, finite ground field and zero-dimensional S, positive-dimensional S with identity
E₀/K, ell=5 and characteristic 2 or 3. No faithfulness or pencil invariance is imposed.
Empty S and X are excluded exactly by the original integrality hypotheses. A finite cover
is chosen with all generic-point lifts, so no unnecessary empty chart is required.
The auxiliary compatible-pair group lives in `Type (max u v)`, allowing arbitrary original
group universe v and the automorphism group of a field in universe u.

Compilation: scompile.py compiled both sandbox and library module cleanly, with no warnings
(the theorem's intended sorry warning is not counted). The large witness structure was
replaced by an explicit existential proposition to avoid generated structure-projection
elaboration exceeding the 60-second limit; no mathematical clause was removed. The helper
uses `maxRecDepth 2048` for the long nested binder list, not a larger compile timeout.
No statement dispute or known node fault remains.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
