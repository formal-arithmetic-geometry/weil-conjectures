## Worker report

The item is stated by `AlgebraicGeometry.MultiplicativeLine.exists_multiplicative_line_dedekind_extension`
in `Sheaf.AlgebraicGeometry.MultiplicativeLineDedekindExtension`. Its only theorem proof is
`sorry`; all definitions have actual data. The theorem's docstring follows all ten DAG proof
steps. The item statement, proof and proof dependencies are unchanged. Its statement dependencies
gain the new coherent-line definition and the already landed split-torus and frame-model nodes.
No statement correction or disputed statement is needed.

Source read: BLR, Neron Models, 10.1 Proposition 7 and its proof, printed p.292 / PDF p.298,
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf.
This is the primitive-line step; the DAG explicitly extracts its coherent rigidified version
and frame-product geometry. Also read the latest sk-thm-sf-ctf-stability unit. This is an auxiliary
node, not a change to that unit. The CompactObject example is currently withdrawn and contains
no declarations, so the landed RigidifiedLineBigOpenExtension and SplitTorusTorsorFrameGeometry
modules supplied current header and namespace conventions.

Hypotheses and data, clause by clause:

- D Noetherian integrally closed domain: `[CommRing D] [IsDomain D] [IsNoetherianRing D]
  [IsIntegrallyClosed D]`; exact Krull dimension one: `_hdim : ringKrullDim D = 1`.
- K = Frac(D): `[Field K] [Algebra D K] [IsFractionRing D K]`. S is literally `Spec (.of D)`;
  `genericMap D K` is Spec of `algebraMap D K`.
- Commutative group scheme over S: `G : CommGrp (Over (Spec (.of D)))`, whose actual
  multiplication, inverse and identity are Mathlib's group-object structure.
- Smooth: `[Smooth G.X.hom]`; separated: `[IsSeparated G.X.hom]`, the closed-diagonal notion;
  finite type: `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`.
- Geometrically connected fibres: `[GeometricallyConnected G.X.hom]`. Mathlib's definition
  tests every field-valued base change and is equivalent to geometric connectedness of all
  residue fibres, using `ConnectedSpace`, which includes nonemptiness.
- Generic fibre with its canonical group operations: `changeBase G (genericMap D K)`.
  `Coherent` contains `Raw.line`, `Raw.invertible`, the actual identity `Raw.unit` frame, and
  `Raw.multiplication`, an isomorphism of exactly the two projection pullbacks tensored
  together to the multiplication pullback. No arbitrary multiplication map is substituted.
- The given two associativity composites, interchange symmetry, and both identity-axis
  laws are `Coherent.assoc`, `.comm`, `.one_mul`, `.mul_one`. They are equalities of dependent
  framed points over every S-test scheme. `mul` uses the specified line isomorphism,
  canonical tensor pullback comparison, normalized composition and ordinary tensor unitors.
  Simultaneous local frames exist for any finite list of lines; equality on such frames is
  equivalent to equality of the tensor-diagram morphisms, since they are locally bases.
  This tests nonreduced schemes too, rather than just field-valued points.
- Extension of one specified datum: the first conjunct, `∀ A, ∃ E, Nonempty (Identification … E A)`.
  E has all the same structure and identities. `Identification.lineIso` is the generic
  module identification; `.unit_eq` and `.mul_eq` preserve precisely the specified frame
  and multiplication on all test frames. The line is not chosen from a sorried definition.
- Every finite list, r >= 0: the second conjunct quantifies `r : ℕ` and `A : Fin r → Coherent …`;
  it returns a simultaneous family E and a generic `Identification` for each index.

The `FrameExtension G r E` conclusion spells out every remaining clause:

- `.frames j : SplitTorusFrames.FrameModel (E j).line` supplies the representing frame scheme
  with its universal frame and its actual pullback classification on every Q-scheme.
- `.productIso` identifies B over Q with the categorical product over Q of these schemes.
  `.universalFrame` and `.product_frame` tie its frames to the product projections.
- `.group : CommGrp (Over S)` supplies a represented commutative group with inverse;
  `.quotient` is B to Q and `.homomorphism` is `IsMonHom quotient`.
- `.multiplication` fixes the group law to multiplication of frames induced by each
  extended mu. `.identity` fixes its identity to the tuple of extended u's.
- `.smooth`, `.separated`, `.finiteType`, `.connectedFibres` assert exactly smoothness,
  closed diagonal, locally finite type plus quasi-compactness, and geometric connectedness
  of the S-fibres of B.
- `.kernelIso` is an isomorphism of group schemes from the already constructed
  `RingGroupSchemes.splitTorus D r` to Mathlib's scheme-theoretic `GrpObj.ker quotient`.
  `.kernel_scalar` fixes this identification to scalar multiples of the identity frames,
  using actual Laurent coordinates `ringCoordinate` / `ringScalar`. The two section types
  are equal after the kernel base-point identity, but not definitionally equal; `HEq`
  expresses their canonical equality without making an arbitrary transport choice.
- `.group_sheaf` and `.quotient_sheaf` assert the representable fppf sheaf conditions on
  the actual topology `Scheme.fppfTopology.over S`. `.quotient_locallySurjective` is fppf
  local surjectivity of `yoneda.map quotient`. Together with the group-kernel isomorphism,
  these are precisely exactness of 1 -> G_m^r -> B -> Q -> 1 as fppf sheaves: kernel
  inclusion is objectwise injective and has image the quotient kernel, and local
  surjectivity is the sheaf epimorphism criterion. No surjectivity on global points is assumed.
- `.rank_zero` says r=0 makes the actual quotient an isomorphism; `.productIso` also
  identifies it with the empty product, the terminal Q-scheme, hence Q itself.
- `RingGroupSchemes.multiplicative` is the existing Spec of the Laurent polynomial Hopf
  algebra over D, and its finite product is the existing `splitTorus`. Since S is affine,
  this is exactly the G_m obtained by the node's gluing description.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `.Hom`, `Spec`, `Spec.map`.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `AlgebraicGeometry.IsClosedImmersion`.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `AlgebraicGeometry.Smooth`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (actual local rank-one trivializations).
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `Limits.pullback`, `.fst`, `.snd`.
- Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSectionComp`, its section-normalized adjunction.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses:
  `SheafOfModules.cochainModulesMonoidal` and the existing sheaf tensor symmetric structure.
- Mathlib.AlgebraicGeometry.Sites.Fpqc: `Scheme.fppfTopology`; Mathlib.CategoryTheory.Sites.Over
  gives its slice topology.
- Mathlib.Topology.Connected.Basic: `ConnectedSpace`; Mathlib.AlgebraicGeometry.Geometrically.Connected:
  `GeometricallyConnected` and its fibre interpretation.
- Sheaf.AlgebraicGeometry.SplitTorusTorsorFrameGeometry: `SplitTorusFrames.FrameModel`,
  `.at`, `pullFrame`, `unitComparison`, all generic in the base scheme without a field restriction.
- Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing:
  `RingGroupSchemes.multiplicative`, `RingGroupSchemes.splitTorus`.
- WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons:
  `Scheme.Modules.boundaryPullbackTensorIso`, derived from the existing monoidal pullback.
- Mathlib's cartesian `CommGrp`, `Over.pullback`, `Over.mapPullbackAdj`, and `GrpObj.ker`
  provide group operations and the canonical projection; no replacement group notion is defined.

All recorded proof-dependency modules that have Lean records are imported for stage 3, with
statement dependencies public and proof-only imports ordinary. General Mathlib leaves are
already supplied by the explicit and transitive imports.

Edge cases checked: r=0 has no indices, a terminal Q-product and trivial kernel, and quotient
is an isomorphism. r=1 is the frame scheme itself. G=S is allowed and has only the identity
base point, so the scalar kernel formula recovers the rigidification. Nontrivial lines
pulled from S require their actual identity frame, not a chosen unrelated trivialization.
All characteristics are admitted; no properness, excellence, splitness of Q or field-point
surjectivity is imposed. Empty test schemes are admitted. Q is nonempty over each field-valued
base by its identity and geometric connectedness. D=0 and fields are excluded by exactly the
stated domain and dimension-one assumptions. No independent smaller test universe is used.

Searches run using msearch.py (the exact logged results are in the new node): LeanFinder on
extension of a rigidified multiplicative line over a Dedekind domain returned Selmer groups,
ring Picard groups and smooth manifold groups, no match. Loogle `"AlgebraicGeometry",
"LineBundle"` returned 0. Mathlib grep `multiplicative.*(line|invertible)|primitive.*line|rigidified`
in AlgebraicGeometry returned 0. LeanSearch on coherent multiplicative invertible sheaves
returned ordinary modules, ring Picard groups and smooth sheaves, no match. Direct rg on
WeilConjectures and Sheaf found RigidifiedLines (algebraic spaces without multiplicative
coherence), CubicalLine (different cubical data), and the reused frame/tensor constructions.
No occurrence of the item's node id appears upstream. DAG and whole-blueprint searches for
multiplicative line and rigidified found no matching coherent-line definition. The existing
ring-base split torus was found and reused rather than recreated.

Validation: scompile.py compiled each file separately, in dependency order, against the
published live server library. Both files are clean; only the theorem uses sorry.

## New nodes

`def-sfb-coherent-multiplicative-line` defines the genuinely missing coherent line data and
compatible generic identification in its own module `Sheaf.AlgebraicGeometry.CoherentMultiplicativeLine`.
It does not move the extension theorem into a definition. Its `Raw` and `Coherent` structures
have explicit actual modules, isomorphisms and coherence fields; `Point`, `mul`, `one`,
`composite`, `changeBase`, `projection`, `projectPoint`, `identifyPoint` and `Identification`
spell out canonical transports and identities. There are no postponed theorem proofs in
this definition module. Source: the BLR primitive-line construction, coherent rigidified
interpretation required explicitly by the item, and Stacks tensor/pullback comparisons.
The three kinds of searches and blueprint searches above established that no existing node
or declaration supplies this notion. The item's nearest blueprint ancestor is null; the
new node preserves that origin and prepends this item to the inherited via chain.

## Repair of returned delivery

The returned head f7fa00a3025a used the geometry theorem as a statement dependency for plain frame constructions. In both the item and the new definition node, this dependency is replaced by their landed owner, `def-sfb-split-torus-frame-model`. The new definition's statement now cites that owner. Its statement dependencies also include `def-sc-tensor-pullback-power-comparison`, which owns `boundaryPullbackTensorIso` used in multiplication, and its statement cites this comparison.

The Lean modules and mathematical statements are unchanged. The repair concerns dependency ownership only.

Repair validation: both retained Lean modules compiled cleanly with `scompile.py`; `deliver2.py --no-push` passed server preflight and per-file compilation (dry-run commit `b9e5c7fbdfe`).

## Second reading by Q49

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
