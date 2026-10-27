## Worker report

The module `Sheaf.AlgebraicGeometry.PositiveWeightAffineSpaceArbitraryField` states
`AlgebraicGeometry.positive_weight_affine_space_arbitrary_field`, with proof `sorry`.
Its two fully defined helpers, `tangentLaurentUnit` and `IsPositiveTangentCharacter`,
spell out the universal character test belonging to this statement. They are listed
in `lean.declarations`. There are no new nodes or dependency repairs, and no change
to the node statement or its dependencies.

Hypothesis and clause correspondence:

- Any field k: `(k : Type u) [Field k]`, with no algebraic-closure, perfection,
  characteristic, infinitude or nontrivial-character restriction.
- A k-scheme: `X : Over (Spec (.of k))`, with the recorded Mathlib scheme and morphism.
- Affine: `[IsAffine X.left]`.
- Smooth: `[Smooth X.hom]`.
- Geometrically connected: `[GeometricallyConnected X.hom]`. This Mathlib predicate
  tests connectedness, including nonemptiness, after all field-valued base changes;
  it uses precisely `ConnectedSpace`, the match for def-weil-connected-scheme.
- Finite type: `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]`, the two recorded
  constituents of def-weil-finite-type-morphism.
- The algebraic G_m action: `a : ModObj (StandardGroupSchemes.multiplicative k) X`.
  `ModObj.smul` is an actual morphism over k and its fields `one_smul` and `mul_smul`
  are the identity and associativity equations. The multiplicative group is the
  dependency's Laurent Hopf group scheme, with its recorded group structure.
- Rational fixed point: `s : Over.mk (𝟙 (Spec (.of k))) ⟶ X` is a section; its point
  is `s.left (IsLocalRing.closedPoint k)`. The binder `hs` says the action fixes
  this section on every test scheme W and every W-point t of G_m. In particular
  it holds on every commutative k-algebra extension, including nonreduced ones.
  Conversely the affine-test formulation of fixedness implies this formulation
  by the affine open cover of W, so no hypothesis has been strengthened.
- The tangent space is exactly `schemeTangentSpace k X.left X.hom (...)`, the
  recorded dual-number space. The supplied `Module.Basis (Fin d)` is over its
  existing residue-field module structure. The residue field of the point of a
  k-rational section is canonically k, so this is a k-basis and d is exactly the
  node's tangent dimension, without assuming or choosing another module structure.
- The positive character decomposition: `n : Fin d → ℤ` and `hn` require the
  displayed basis vectors to satisfy `IsPositiveTangentCharacter ... (n i)`.
  This contains `0 < n i` and the actual action equation after scalar extension
  to K[z,z⁻¹][ε], where K is the residue field of the rational point. The first
  projection of q evaluates the Laurent coordinate at the universal unit z,
  with coefficient map k → K → K[z,z⁻¹] → K[z,z⁻¹][ε]. Its second projection is
  v extended along K → K[z,z⁻¹]. The output is v after ε is scaled by z^(n i).
  The two projections determine q uniquely by the product universal property.
  Thus q is not an arbitrary map, and no arbitrary differential is assumed.
  This is exactly the character equation d(a_z)(v)=z^(n i)v; all characters are
  detected universally rather than only on k× or through their Lie differentials.
  Choosing a basis of each character space gives this eigenbasis formulation and
  conversely an eigenbasis gives the direct sum in the node.
- The conclusion `∃ e : X.left ≅ AffineSpace (ULift.{u} (Fin d)) (Spec (.of k)), ...`
  gives the affine-space isomorphism with exactly d coordinates. `ULift` puts the
  finite coordinate type in the scheme universe without limiting k or d.
- `e.hom ≫ ... ↘ Spec (.of k) = X.hom` says it is defined over k. Inverses of an
  isomorphism over the base also commute with the structure morphisms.
- `s.left ≫ e.hom = AffineSpace.homOfVector (𝟙 ...) (fun _ ↦ 0)` is equality of
  the rational section with the canonical zero section, not just equality of points.
- For d=0 the basis and weight family are empty. Mathlib's affine space with empty
  coordinate type has its projection a canonical isomorphism, so the same conclusion
  is precisely X ≅ Spec k. This clause needs no extra nonempty-basis hypothesis.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs; `AlgebraicGeometry.Scheme` and `Spec`,
  Mathlib.AlgebraicGeometry.Scheme.
- `AlgebraicGeometry.Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- `ConnectedSpace`, Mathlib.Topology.Connected.Basic, via
  `AlgebraicGeometry.GeometricallyConnected`, Mathlib.AlgebraicGeometry.Geometrically.Connected.
- `AlgebraicGeometry.LocallyOfFiniteType`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  and `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `AlgebraicGeometry.StandardGroupSchemes.multiplicative` and its `multiplicativeGroup`,
  Sheaf.AlgebraicGeometry.StandardGroupSchemes. Their definitions were read in full:
  the spectrum of Laurent polynomials and the Laurent Hopf group structure.
- `AlgebraicGeometry.schemeTangentSpace`, its additive group and residue-field module,
  WeilConjectures.AlgebraicGeometry.SchemeTangentSpace; the postcomposition description
  of `schemeTangentMap` was also read. The character condition writes that canonical
  postcomposition directly, avoiding point-equality transports in an action family.
- `AlgebraicGeometry.AffineSpace`, `AffineSpace.homOfVector`,
  `AffineSpace.SpecIso` and the empty-coordinate projection instance,
  Mathlib.AlgebraicGeometry.AffineSpace. These identify the conclusion with Spec k[T].

Proof-only imports retain the recorded finite-type coordinate-algebra theorem,
regularity and integrality results, rational tangent/cotangent duality, and Krull
intersection. The two proof prerequisites `lem-sfb-gm-affine-action-grading` and
`lem-sfb-positive-graded-regular-polynomial` have no Lean record at this reading,
so there is no module to import for them. They are not statement prerequisites.
The docstring contains all seven proof steps, naming every mathematical input.

Source and edge cases checked:

Read Milne, Algebraic Groups (2017), printed pp.269--270 (PDF pp.281--282),
Definition 13.40 and Theorem 13.41, and the current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`.
The smooth hypothesis makes X regular; connected nonempty regular X is integral,
so the strengthened smooth-everywhere setting avoids the reducible-case issue.
Checked Spec k with empty tangent basis; A¹ of weight 2; affine space with weights
(2,5); a finite field where distinct characters can agree on k×; and weight p in
characteristic p. The universal z^p equation remains nontrivial even though the
character's Lie differential vanishes. Negative or zero weights fail `0 < n`.
No field cases or zero-dimensional cases are excluded. No statement fault or
STATEMENT-DISPUTED flag was found.

Searches for an existing statement or notion (2026-10-24):

- msearch.py leanfinder: "A smooth geometrically connected affine scheme over an
  arbitrary field with a multiplicative group action fixing a rational point and
  strictly positive tangent weights is affine space". Eight hits, all on affine
  space itself, its relative structure and basic properties; no matching theorem.
- msearch.py loogle: "AlgebraicGeometry.AffineSpace,
  AlgebraicGeometry.schemeTangentSpace". No hits; the service does not index the
  project-specific tangent declaration. That declaration was read locally instead.
- msearch.py grep, AlgebraicGeometry: "positive.*weight|GmAction|Luna". No hits.
- msearch.py leansearch: "smooth connected affine variety multiplicative group
  strictly positive tangent weights is affine space". Eight hits on affine space,
  formally smooth polynomial rings and unrelated manifold/affine-space results;
  none is this theorem.
- rg on `lean/WeilConjectures` and `lean/Sheaf` for
  `Luna|luna|positive.*[Ww]eight|[Pp]ositive.*[Tt]angent|GmAction|gmAction`, and
  exact item-id search in WeilConjectures: no matching statement. Related root-group
  files cite the positive-weight theorem in proof plans but do not state it.
- Read `Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights`: its `weightSpace`
  uses group-scheme identity tangents and only base-field rational points, explicitly
  intended for algebraically closed fields. It cannot encode this arbitrary affine
  scheme / arbitrary-field universal character test. The new helper is the direct
  dual-number formula for this item, not a copy of that specialized construction.
- Exact-name rg for `tangentLaurentUnit` and `IsPositiveTangentCharacter` found no
  existing project declaration before writing the module.

Validation: scompile.py compiled the delivered file in module mode, both sandbox
and library-path passes, with no errors and no non-sorry warnings. Only the theorem's
proof is postponed; both helper definitions contain real constructions.

## Second reading by Q137

Read the node against the completed signature and expanded both helper definitions.
This is the worker's self-check; no second agent was started, as the dispatcher brief
forbids it. The maintainer supplies the independent review.

Checked every hypothesis and conclusion by the correspondence above. The key checks
were that a basis over κ(x)=k has the requested dimension, the product projections
uniquely fix q, the ring-map composition scales ε after extending coefficients,
and the Laurent parameter is constant in the ε direction. Therefore the action
is differentiated only in X and the weights have the original positive sign.
The isomorphism has both the over-k equality and equality with the zero section.
The empty basis is allowed. Compiler-driven corrections only supplied an explicit
monoid projection for Units.map and coefficient-ring annotations; no mathematical
statement or hypothesis changed.
