## Worker report

Item: `lem-pur-finite-tate-source-structural-coherence`. The module is
`Sheaf.Paper.FiniteTateSourceStructuralCoherence`; its namespace is
`WeilConjectures.PurityFiniteSetting.FiniteTateSource`. The one postponed theorem,
`finiteTateSourceStructuralCoherence`, states every clause of the node as four
conjuncts. Its proof is `sorry`. All helper definitions contain real data. No
statement correction, new node, dependency repair, or disputed statement is needed.

Source read: the current `literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-def-sf-weil-complexes/def-pur-tate-datum.md`, specifically the first arrow in
`φpur`, and `sec-six-functors/sk-thm-sf-package/
prop-pur-weil-equivariance-compatibilities.proof.md`, the constituent-compatibility
assembly. The theorem docstring supplies the node's six-step proof: normalized
balanced comparisons, monoidality of C, the input cube, substitution into b,
smooth composition, and shifts/naturality.

Hypotheses and objects, clause by clause:

- The finite field, algebraic closure, prime different from characteristic, fixed
  coefficient closure, finite coefficient extension, and positive quotient exponent
  are exactly `P : PurityFiniteSetting`. Its `Ring` is the existing
  `Padic.coefficientExtensionRing`, and `Coefficient` is its standard `ULift`.
  The ring is not a fresh parameter or an arbitrary coefficient ring.
- `Model P d` bundles `X₀`, `Y₀` as objects over `Spec P.field.k₀`, and their
  actual over-morphism `f₀`. `finiteX/compactX/separatedX` and the corresponding
  Y fields are separated finite type over k₀. The three map fields express
  separated finite type of f₀. `d : ℕ` includes zero; `smooth` says exactly
  `SmoothOfRelativeDimension d (P.frobeniusMap f₀)`.
- `Model.X`, `Model.Y` are the recorded geometric fibres. `F`, `GX`, `GY`
  abbreviate the published exact-derived pullbacks along the actual base-changed
  map and the two actual geometric-Galois maps. They do not accept arbitrary
  Frobenius endofunctors or an unspecified commuting comparison.
- `D P X` is an abbreviation for the published fixed-scalar realization
  `DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u+1} P.Coefficient))`.
  The pro-etale site's object universe is u+1 and morphism universe is u.
  Each finite-Tor-domain premise is the published `finiteTorConstructible`
  applied through `sfIntrinsicDerivedEquivalence.functor`; thus the input really
  lies in the original intrinsic `D^b_ctf`, in these equivalent coordinates.
- `finiteTensorFixedLine X d` is the existing signed coefficient line in degree
  zero, at positive exponent d, not the shifted diagonal Tate object.
  `Model.source` is `(F K ⊗ T_d)[2d]`; `Model.target` is
  `(F (GY K) ⊗ GX T_d)[2d]`, exactly P_f and H_f.
- `square` uses inverse first compositor, the equality of composite scheme maps,
  and second compositor. `Model.c` specializes it with the equality supplied by
  the recorded finite-field Frobenius-square theorem. `Model.b` first commutes
  GX with the even shift, then applies the canonical pullback tensorator and
  `c_f ⊗ 1`, all shifted by 2d. No Weil datum φK or Tate action τ is inserted.

The transport square is expressed by `Change.Square`:

`QX.map b.hom ≫ aH.hom = CX.hom ≫ G'X.map aP.hom ≫ b'.hom`.

This is the node's formula in Lean's left-to-right composition convention.
`Change` only packages constituents; the theorem asserts the equation for the
following two concrete constructors, without assuming coherence of a general Change.

- The first conjunct specializes to `reductionChange M m hm hmn`, where
  `hm : 1 ≤ m` and `hmn : m ≤ P.level`. `Model.reduce` retains the models,
  morphism, dimension, and all structure proofs. QX/QY are the actual
  `finiteTensorReduction`, q is inverse `finiteTensorCore.μIso`, sigma and
  CX/CY are `finiteTensorPullbackComparison` for f and the two Galois maps,
  t is `finiteTensorLineComparison`, and the shift is `finiteTensorScalarShift`.
  Thus scalar extension retains the target quotient action and no quotient
  flatness premise is added. The conclusion is restricted to the stated
  finite-Tor constructible input domain. Pullback, tensoring with a line, and
  derived reduction of such an input are the operations on that domain;
  no finite-level internal-Hom comparison is asserted here.
- The second conjunct specializes to `geometricChange M N u₀ v₀ sq ζ hζ`.
  Both vertical maps have pure dimension d, and
  `sq : ChosenCartesianSquare u₀.left N.f₀.left M.f₀.left v₀.left` supplies
  precisely the given Cartesian square over k₀. QX/QY are pullback along
  `P.frobeniusMap u₀` and `P.frobeniusMap v₀`. `modelSquare` maps its
  commutativity equality through geometric base change. Sigma is the resulting
  compositor comparison; CX/CY use the canonical Frobenius commuting squares
  for u₀/v₀. q and shift are the actual pullback tensorator and termwise shift.
- The positive-line geometric t is `linePullback`. In any primitive-root chart
  it is pullback of the source line chart, the canonical pullback unit, then
  the inverse target chart. These are the existing `finiteTensorPositiveChart`
  and `leftDerivedUpperStarUnitIso` transported through the actual exact-derived
  comparison. This is the canonical root-restriction map: u₀ is defined over
  k₀, so its geometric base change preserves each coefficient root in k.
  Changing the primitive root rescales both charts by the same unit to the
  same d-th power, which cancels because this pullback is k-linear. The theorem
  quantifies over every such chart, rather than selecting an unspecified line
  isomorphism. Primitive roots exist because k is algebraically closed and
  `P.diagonalExponent = ℓ^P.level` is prime to its characteristic. The root
  parameter therefore excludes no field, scheme, level, or input complex.
- `aP` first applies the shift comparison, then q, then `sigma ⊗ t`.
  `aH` first applies shift and q; its input factor is
  `sigma_(GY K)` followed by `F'(CY_K)`, and its twist factor is `CX_(T_d)`
  followed by `G'X(t)`. This matches every factor in the node's definition;
  neither boundary is defined by conjugating b to force the desired equation.

Composition, naturality, and shifts:

- `Following M e` bundles h₀ with domain literally M.Y₀, its separated
  finite-type target and map, and smooth geometric dimension e. `model` is h,
  `composite` is f₀ followed by h₀ with dimension d+e; the ordinary smooth
  composition instance supplies its structure proof. There is no restriction
  to identity maps, affine schemes, or trivial twists.
- `Following.compositor` is `compositionFixedPullbackComp` preceded by the
  geometric base-change functor's actual composition equality.
  `expand` applies the termwise pullback shift, pullback tensor comparison,
  first-factor tensor shift, and shift-addition comparison. Its target is the
  parenthesized triple tensor at total shift 2(d+e).
- `splitLine` uses signed product `finiteTensorProduct` in order e,d, then the
  inverse of the canonical pullback of T_e. `compositeSourceExpansion` combines
  it with the actual compositor and inverse associator. `compositionSource`
  is the canonical map P_f P_h -> P_hf using precisely those comparisons.
- `iteratedRoute` expands b_f followed by f*(b_h), extracts the shifts, and
  uses `c_f` inverse on T_e to express its middle factor as GX(f*T_e).
  `compositeTargetExpansion` instead expands the target of b_hf through the
  compositor, GX(splitLine), tensorator for GX, and inverse associator.
  The third conjunct equates these two actual maps after GX(compositionSource).
  Their common target is exactly
  `((F_f F_h G_Z K ⊗ G_X F_f T_e) ⊗ G_X T_d)[2(d+e)]`.
- The last conjunct states naturality at every morphism a:K->L between the
  finite-Tor constructible inputs, then the shift equation for every integer s.
  Its left boundary is explicitly GX applied to the source's termwise shift,
  followed by GX's termwise shift. Its right boundary is the target's termwise
  shift. `Model.sourceCommShift` and `targetCommShift` are composed canonical
  structures on those actual functors. No equality between cohomology groups
  is substituted for equality of the derived-category morphisms.

Dependency declarations used (full signatures and docstrings inspected in source):

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `.Ring`, `.Coefficient`, `.level_pos` and the recorded finite-field data.
- `Sheaf.SixFunctors.SchemeGeometricFrobenius`: `.frobeniusFiber`, `.frobeniusMap`,
  `.frobeniusGaloisMap`; `FiniteFieldDatum.frobenius_square_cartesian` supplies
  their actual commuting-square equality. The recorded scheme/Galois comparison
  is publicly imported, while the structural b here uses geometric Galois maps.
- `Sheaf.Paper.DerivedPullbackTensorHom`: intrinsic finite operations and
  `sfIntrinsicDerivedEquivalence`; the public definitions used in fixed
  coordinates are the same exact-derived pullback and native derived tensor.
- `Sheaf.Paper.DerivedPullbackTensorIso`: `derivedPullbackTensorIso` and its
  canonical tensor, composition, coefficient, and shift normalization plan.
- `Sheaf.Paper.PurityTateDatum`: the displayed first-arrow interpretation and
  published source-data conventions; no strict Weil datum is an extra hypothesis.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `ChosenCartesianSquare`.
- `Sheaf.Paper.BasicOperationsCoefficientReduction`:
  `basicOperationsCoefficientReduction`, for the finite-Tor coefficient domains.
- `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `integralTowerGeneralPullbackComposition` and its published normalized
  composition interfaces. `compositionFixedPullbackComp` is the exact-derived
  fixed-coordinate compositor used for these actual constant pullbacks.
- `Sheaf.Paper.FiniteTensorFixedComparisons`: `finiteTensorPullbackTensor` and
  `finiteTensorPullbackComparison`.
- `Sheaf.Paper.FiniteTensorReductionData`: `finiteTensorFixedLine`,
  `finiteTensorReduction`, `finiteTensorScalarShift`.
- `Sheaf.Paper.FiniteTensorSignedReduction`: `finiteTensorCore`,
  `finiteTensorLineComparison`.
- `Sheaf.Paper.FinitePositiveRootCharts`: `finiteTensorPositiveChart`.
- `Sheaf.Paper.FiniteSignedTwistProducts`: `finiteTensorProduct`.
- Proof-only imports are the recorded intrinsic coefficient twists, Cartesian
  coefficient twists, independent-coefficient K-flat resolution, finite derived
  normalization, signed total-tensor coherence, ambient pullback-tensor coherence,
  pro-etale derived compositor coherence, and canonical tensor/shift/unit modules.

Existing-definition searches actually run with msearch.py:

- LeanFinder: “Frobenius derived pullback tensor Tate source comparison coherent
  with coefficient reduction and composition”. Eight unrelated scheme tensor/
  spectrum pullback hits, including `Scheme.Pullback.ofPointTensor_SpecTensorTo`;
  no finite Tate-source structural comparison.
- Loogle: `"pullbackComp"`. Twelve categorical pullback comparison hits;
  no statement about the node's derived Frobenius/Tate comparison.
- Mathlib grep: `TateSource|tateSource|structuralCoherence`. Zero hits.
- LeanSearch: “derived pullback tensor Frobenius Tate source comparison coherence
  finite reduction smooth composition”. Eight hits, including categorical
  `frobeniusMorphism`, categorical pullbacks, and underived scheme module
  `pullbackComp`; none is the node's statement.
- Direct rg in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `finiteTateSource|FiniteTateSource|
  finite_tate_source|tate-source-structural`: no existing declaration.
  The exact node-id search in upstream Lean had no hit. Broader searches found
  existing coefficient/tensor/compositor helpers, which are reused here.

The five additional stmt_deps are already landed definition nodes:
`def-pur-finite-tensor-fixed-comparisons`, `def-pur-finite-tensor-reduction-data`,
`def-pur-finite-signed-reduction-comparisons`, `def-pur-finite-positive-root-charts`,
and `def-pur-finite-signed-twist-products`. Their declarations give the precise
normalized coordinate maps used above. Their node files are not changed.

Edge cases checked before and during the rereading: d=0 and e=0 use the existing
signed unit/product and zero-shift maps; m=P.level is included, as is m=1;
identity Cartesian squares and identity Frobenius-compatible paths use the same
compositors; K=0 and empty source/target schemes require no nonemptiness or
chosen point. Nonflat reduction (e.g. a length-two DVR quotient to its residue
field) is still derived scalar extension with its target action, not ordinary
underived tensor or a flatness assumption. The geometric-root description uses
k-linearity only for the geometric base-change arrow, never for the semilinear
Frobenius map. Arbitrary integer input shifts are included.

Validation: all compilation and delivery checks use the prescribed scompile.py
and deliver2.py wrappers. The final module and dry-run results are recorded below.

## Second reading by NK

The dispatcher explicitly forbids starting another agent. This section records
a separate rereading by this worker; the maintainer's independent review remains
the delivery review. The node, current blueprint source, helper definitions,
and full theorem signature were reopened together.

The rereading checked the orientation of c_f (GX F -> F GY), the order of each
boundary composite in Change.Square, use of CY on the input and GX'(t) CX on
the line, and the inverse c_f on the middle composition factor. It checked that
the first line is genuinely degree zero, that no Tate action has been inserted,
and that both composition routes have the same shifted triple-tensor target.
It also checked that primitive-root charts describe k-linear geometric
pullback, while Frobenius remains semilinear, and that the finite quotient
constructor retains its B-action. The result is one theorem with all four
conjuncts, rather than a delivery of the transport square alone.

Compiler-guided fixes supplied the canonical exact-pullback CommShift structure,
explicit inherited instance fields on the reduced and composite models, and
explicitly decomposed the source shift into its two constituent termwise maps.
These repair elaboration without changing any mathematical hypothesis or map.
No other mismatch with the node was found. There are no new nodes, no dependency
modules, no statement change, and no STATEMENT-DISPUTED flag.

Final validation: scompile.py accepted the complete module in both sandbox and
library modes (42.6 s and 36.0 s), with no errors or unexpected warnings. The
required deliver2.py --no-push returned `OK (dry run)` at d7b76301e1e: preflight
and the per-file compile passed. Exactly one named theorem proof is `sorry`.
