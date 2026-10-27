## Worker report

The delivery states `AlgebraicGeometry.CubicalAntisymmetric.cubical_antisymmetric_frame_extension`
in `Sheaf.AlgebraicGeometry.CubicalAntisymmetricFrameExtension`. Its only theorem proof is
`sorry`. `Extension H L` is a conclusion record, not an input assumption. All helper definitions
have real data. The existing `SplitTorusFrames.FrameModel` supplies the actual representing
scheme and universal frame; no scheme is selected from a mere existence assertion.

Hypothesis-by-hypothesis correspondence:

- The base scheme is `{S : Scheme.{u}}`; `[IsAffine S]`, `[IsIntegral S]`, and
  `[IsNoetherian S]` express affine, integral, and Noetherian. The last class extends local
  Noetherianity and compactness. `hnormal` says at every point that its stalk is a domain and
  integrally closed. This is exactly the statement's local-ring meaning of normality.
- `H : Over S` is the supplied structure morphism `H.hom`. `[CommGrpObj H]` supplies actual
  scheme morphisms for multiplication, inverse, and identity and their diagrams.
  `[Smooth H.hom]`, `[IsSeparated H.hom]`, `[LocallyOfFinitePresentation H.hom]`, and
  `[QuasiCompact H.hom]` give the stated geometric conditions. Quasi-separatedness follows
  from separatedness; an additional redundant instance binder was removed on second reading.
  `IsSeparated` is the closed-diagonal condition, not a pointwise separation condition.
- `hsemiabelian : HasSemiabelianGeometricFibres (Grp.mk H)` uses the recorded definition,
  including all algebraically closed fields in the chosen scheme universe and rank zero.
- `L : CubicalRigidifiedLine H` supplies the actual invertible module, rigidification,
  eight-factor cube section and all symmetry/identity/cocycle laws. It is not replaced by
  an unstructured line or by the conclusion that a multiplication exists.

Clause-by-clause correspondence of the conclusion:

- `line L` is literally `L.line ⊗ dual ((tensorPullback inv).obj L.line)`. The dual is the
  recorded internal Hom into the structure module. The inverse is the supplied inverse of H.
- `Extension.frames : FrameModel (line L)` is the actual scheme `q = frames.space.hom`
  over H with a universal frame and the bijection on every H-scheme. Its bijection is
  induced by tensor pullback of its universal frame, so includes naturality. This is the
  actual frame functor specified in the statement, not an arbitrary torsor.
- `group` and `commutative` give the commutative group object on that SAME scheme, viewed
  over S by `Over.map H.hom`. `projectionHom` makes the actual q a group homomorphism.
- `multiplication` is the sheaf isomorphism from the two projection pullbacks of D to the
  multiplication pullback of D. `multiplicationAt` is its explicit tensor/composition
  pullback along a pair of generalized points, using the recorded normalized comparisons.
- `cube_formula` fixes this isomorphism to the inverse of the cube Hom frame at
  `![x,y,(x*y)⁻¹]`. In valid frames its coefficient times the cube coefficient is one:
  `mu.hom ≫ frameMap(x*y) ≫ CubicalLine.value tau = (frameMap x ⊗ₘ frameMap y) ≫ lambda`.
  Thus it selects exactly the isomorphism specified by the node, including its direction,
  and rules out multiplication rescaled by an arbitrary unit. The local tests require only
  the finitely many frames already present in the supplied eight-factor cube. Every such
  finite set is locally trivializable. Frame-map equality is equality of module sheaf maps.
- `frame_product` says that the group product of two universal frames is their tensor
  product followed by that same multiplication isomorphism. It quantifies over every
  S-scheme, including the universal product and nonreduced schemes. The group diagrams,
  the frame bijection, and this equality give the associative, commutative and unit
  identities of the sheaf multiplication. `HEq` identifies the targets along the
  already-required equality supplied by `projectionHom`; it does not quotient scalars
  or test just geometric points. It replaces expensive explicit `eqToHom` transports.
- `identity_frame` identifies the group identity frame with the evaluation frame at e.
  At the identity, D is `e*L ⊗ (e*L)ᵛ`; evaluation in any valid frame is the identity.
  Applying the supplied rigidification to its two factors scales them inversely, so this
  is precisely the frame induced by r and is independent of rescaling r. Inverse/identity
  compatibility of H identifies the two appearances of e; both frame-validity assumptions
  merely express local frames of these factors, not extra theorem hypotheses.
- `inclusion`, `inclusionHom`, `kernel`, and `locally_surjective` give the homomorphism
  from the actual relative Gm, its scheme-theoretic kernel square in `Over S`, and the
  local epimorphism for `Scheme.fppfTopology.over S`. These are exactly the exactness
  conditions as fppf sheaves.
- `scaling` identifies translation by a kernel element with multiplication of the frame
  by its scalar. That scalar is the pullback of the EXISTING tautological unit coordinate
  on `Etale.multiplicativeGroup S`. The normalization of the kernel inclusion is thereby
  fixed: at the group identity it sends a to a times the identity frame.
- `smooth`, `separated`, and `finitePresentation` assert the properties of the composite
  `q ≫ H.hom`. Finite presentation is written out as local finite presentation,
  quasi-compactness, and quasi-separatedness. `semiabelian` applies the existing predicate
  to the very group law in the record, not an unrelated structure on the same scheme.
- `affine`, `faithfullyFlat`, and `projectionFinitePresentation` assert affineness,
  flatness plus surjectivity, and all three finite-presentation properties of q itself.
- `frames.frame.symm` is the requested trivialization `q*D ≅ O_E`, and
  `frames.frame` its tautological inverse. It is already part of `FrameModel`, not a
  separately assumed existence of a trivialization.
- There is no ampleness hypothesis, field/characteristic restriction or ampleness conclusion.

Recorded dependencies actually used (declarations were read with their docstrings and signatures):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, together
  with `IsDomain` on every structure-sheaf stalk (the normal-ring node's inline convention).
- `Mathlib.CategoryTheory.Monoidal.Grp` and the Cartesian group modules: `GrpObj`,
  `IsCommMonObj`, `IsMonHom`, `Grp.mk`, `GrpObj.inv`, and the supplied `eta` and `mu`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its projections
  and `IsPullback`, including kernel and Laurent-model fibre products.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` and `Separated`:
  `IsClosedImmersion` and `IsSeparated` (closed diagonal).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth` and `FinitePresentation`: `Smooth`,
  `LocallyOfFinitePresentation`; finite presentation includes quasi-compact/separated data.
- `Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres`:
  `HasSemiabelianGeometricFibres` and its exact kernel/local-surjectivity definition.
- `Sheaf.AlgebraicGeometry.CubicalRigidifiedLine`: `CubicalRigidifiedLine`,
  `CubicalLine.Word.frameMap`, `Frame.valid`, `Framed`, `value`, and `pullbackUnit`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible` and `Modules.Dual`:
  `Scheme.Modules.IsInvertible`, `dual`, `dualEvaluation`, the existing sheaf tensor.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `tensorPullback`, `tensorPullbackSectionComp`;
  `WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons`:
  `boundaryPullbackTensorIso`. No private pullback or tensor product is introduced.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` is publicly imported by
  the cubical-line dependency and supplies the recorded general-site tensor interface.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes.multiplicative` is field-only. The new
  relative-group module uses Mathlib's same Laurent Hopf scheme for a general coefficient
  ring and its pullback to S, then normalizes its comparison to the existing punctured line.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`, `Mathlib.CategoryTheory.Sites.Over` and
  `Sites.LocallySurjective`: `fppfTopology.over S`, `Presheaf.IsLocallySurjective`.
- The landed `def-sfb-split-torus-frame-model` was added to `stmt_deps`, using its unchanged
  `Sheaf.AlgebraicGeometry.SplitTorusTorsorFrameGeometry` definitions `FrameModel`,
  `pullFrame`, and `unitComparison`. This registers an actual dependency, no duplicate node.

The recorded proof modules with Lean interfaces are imported as proof-only imports, including
invertible-pullback-tensor, semiabelian-power-integrality, relative-unit-axis-factorization,
geometrically-connected-algebraic-closure, connected-group-extension, commutative
multiplicative-type-extension, largest-subtorus, and the smooth/proper/affine/flat/gluing
Mathlib leaves. Proof nodes still without Lean interfaces (frame-product-Laurent-algebra,
space-separated-fp-composition, diagonalizable-group-geometric-criteria) are not invented as
statement assumptions. The main theorem docstring includes all ten original proof steps.

Searches:

- `msearch.py leanfinder`: theorem of the cube gives a commutative group extension on
  frames of L tensor dual inversion pullback. Eight hits on algebraic tensor inverse maps;
  none states the theorem.
- `msearch.py loogle`: `AlgebraicGeometry.CubicalRigidifiedLine, CategoryTheory.GrpObj`.
  Unknown cubical identifier in the search index; no hit.
- `msearch.py leansearch`: cubical line bundle antisymmetric part multiplicative frame
  torsor extension. Eight hits on additive torsors, exterior powers and differential
  geometry; none is this statement.
- `msearch.py grep`: `[Cc]ubical|[Bb]iextension|[Aa]ntisymmetric.*[Ff]rame` under
  AlgebraicGeometry: no hit.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/nodes`, including the exact item
  id, found the recorded cubical-line module and the existing `SplitTorusFrames.FrameModel`.
  No existing theorem states the antisymmetric extension. A broader name search also
  found the relative punctured line `Etale.multiplicativeGroup`, which is reused.
- Relative-group searches and their exact outputs are recorded in the new node's
  `mathlib_searches`. The new node was checked against DAG and blueprint name searches.

Edge cases checked before completing the statement: H=S (the trivial group), trivial L,
rescaling the rigidification, torus rank zero, pure torus geometric fibres, arbitrary
characteristic including 2, and nonreduced test schemes. For trivial L and cube the product
is ordinary multiplication of frame scalars. Rescaling r cancels against the dual, so the
identity clause is correct. Rank zero is admitted by the recorded semiabelian definition.
The main base is integral and therefore nonempty, exactly as the node requires; the new
relative-group definition additionally works on empty bases and zero global-section rings.
No assumption restricts tests to affine, reduced, integral or geometric schemes.

Validation: all compilation uses the prescribed `scompile.py`, one module at a time in
its private overlay. Both modules compiled cleanly within 60 seconds, with only the two
expected sorry-bearing theorem declarations. No proof is supplied in this stage.

No statement correction or mathematical dispute is needed.

## New nodes

`def-sfb-relative-multiplicative-group` defines the missing canonical group-structure
interface over an arbitrary base scheme. It reuses the existing punctured affine line and
its existing unit coordinate from
`WeilConjectures.EtaleCohomology.TateTwist.AffineLineDatum`. The Laurent Hopf spectrum over
Gamma(S,O_S), and its base change along `S.toSpecΓ`, provide an explicit comparison model.
The named theorem `comparison_existsUnique` specifies the unique isomorphism pulling the
existing coordinate back to the Laurent coordinate; its local Laurent-chart proof is
fully written in its docstring and in the new node's statement. Thus `comparison` is
chosen only from uniqueness, and the transported `GrpObj` has real, specified operations.
`scalar` is the pullback of the existing unit coordinate. This supplies what the field-only
`def-sc-gm-ga` cannot supply without modifying that dependency's meaning. Source: Stacks
Tag 022U, read directly in `literature/stacks-project/groupoids.tex`. Searches found the
underlying punctured-line scheme, which is reused, but no group law or coordinate-normalized
comparison interface on it. The relative-torus node defines a units-valued functor and a
local splitting predicate, not this representing group object. The new node uses the
inherited null blueprint ancestor returned by `blueprint_refs.py ancestor` and retains the
item's via chain with this item prepended.

## Second reading by ND

A separate reading pass in this worker session reopened the node and both final modules;
the dispatcher explicitly prohibits starting another agent, so this is a second pass rather
than a claim of another reader. The maintainer supplies the independent delivery review.

The pass checked each base and group hypothesis against the theorem signature, the exact
line/dual order against `line`, and the direction of the cube cancellation against
`cube_formula`: the pulled-back cube is a frame of Hom(D_(x+y),D_x tensor D_y), so mu is
its inverse. This direction was retained. It checked the universal frame bijection,
frame-product formula, identity evaluation, kernel square, fppf local epimorphy and
scalar action separately. The action uses the positive coordinate, not its inverse.
It checked each of the three finite-presentation conjuncts and both smooth/separated
conclusions, and confirmed that semiabelianity uses the chosen extension group law.
The tautological frame was found already in the reused frame model, so no extra
noncanonical trivialization was introduced.

Two changes resulted: a redundant quasi-separatedness hypothesis was removed (it follows
from separatedness), and the newly found upstream relative punctured-line scheme replaced
the initially proposed separate relative-Gm object. Its Hopf group structure is now
transported through a unique coordinate-preserving isomorphism, so the definition neither
duplicates the underlying scheme nor chooses an arbitrary group law. The second pass also
replaced expensive equality transports in the product and scaling clauses with `HEq`,
with exactly the same module maps and target identifications, and checked both are
universally quantified over schemes. All diagnostic `#check` commands were removed.
