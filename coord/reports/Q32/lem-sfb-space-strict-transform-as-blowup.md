## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceStrictTransformAsBlowup` states
`AlgebraicGeometry.AlgebraicSpace.strictTransform_as_blowup`, with its whole proof
`sorry`. No definitions, auxiliary theorems, new nodes or dependency repairs are
introduced. The accepted stage-1 split is retained. The previous worker's stale
stage-1 dispatch objection does not apply: this item is in the stage-2 queue and
has no Lean record; coord/brief-stage2.md section 0 explicitly covers this handoff.

Source read: Stacks spaces-divisors.tex, definition-strict-transform and
lemma-strict-transform-local/lemma-strict-transform (Tags 0862/0863/0864), in
particular the canonical map and closed-image characterization in the proof of
0864(1). The qcqs and finite-type additions follow the item's existing eight-step
proof, not a replacement route. The current blueprint unit is
sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md; this is its inherited
compactification prerequisite, not the unit's own statement.

Hypotheses and clauses, in order:

- The arbitrary base scheme is `{S : Scheme.{u}}`; all spaces are the existing
  `AlgebraicSpace S`. The same explicit universe `u` as their recorded definitions
  is used, with no additional universe equality, size hypothesis or fixed field.
- The centre is `K : QuasiCoherentIdeal T`, hence an actual quasi-coherent
  subobject of the structure-module sheaf. `hK : (K.val : T.Modules).IsFiniteType`
  is exactly etale-local finite generation, without Noetherianity or coherence.
- `g : Y ⟶ T` is unrestricted. `D : BlowupPresentation K` is the previously
  recorded descended ordinary scheme blowup on every affine etale chart, so its
  space and projection render T' and p. This is the same Rees blowup as the node,
  specified up to the canonical isomorphism over T.
- The conclusion's `J : QuasiCoherentIdeal Y` is the actual image of g^* K to O_Y:
  the existential `q` has `Epi q` and `q ≫ J.val.arrow = idealTensorMap g K`.
  Its second factor is monic by the subobject definition. This is the normalized
  image factorization, as used by the landed ideal/closed-subspace correspondence.
  No arbitrary ideal or unspecified tensor map replaces it. An initial attempt to
  use `imageSubobject` required an unavailable `HasImage` instance on the small
  module category; expressing the same image by its epi-mono factorization avoids
  imposing a new hypothesis or choosing an Abelian structure.
- `B : BlowupPresentation J` is Bl_(K O_Y) Y. The fibre product is the actual
  algebraic space `P` with projections `qY`, `qD` and
  `IsPullback qY qD g D.projection`. IsPullback presents the categorical fibre
  product up to its unique projection-preserving isomorphism; it is not an
  assumed arbitrary commuting square.
- `W : ClosedSubspace P` supplies the strict transform and its representable
  closed inclusion `W.val.arrow`. Its defining ideal is specified completely by
  the displayed kernel formula for `moduleStructureMap W.val.arrow` on EVERY
  affine etale chart V of P. A section s is in that kernel exactly when some
  power of `idealSectionImage (idealTensorMap (qY ≫ g) K) V` annihilates s.
  This is the node's exceptional-power-torsion ideal: locally on exceptional
  equation charts the extended ideal is (a), and ideal-power annihilation is
  precisely a^n s = 0. On a general affine chart the finite-type ideal has a
  finite list of generators. Local power annihilation gives a common exponent
  for each generator using a finite affine cover; increasing to a power of the
  entire ideal gives the displayed condition. Conversely ideal-power annihilation
  localizes to every exceptional equation. This keeps the scheme structure and
  is not merely the reduced closed support. Kernel equality on the affine etale
  basis fixes the sheaf ideal on the whole small etale site.
- The arrow `v : B.space ⟶ D.space` satisfies
  `v ≫ D.projection = B.projection ≫ g`, the canonical blowup comparison over T.
  Both target blowups are etale-locally the ordinary ones; their universal
  properties uniquely fix v by this equation because K O_B is Cartier.
- `∃! e : B.space ≅ (W.val : AlgebraicSpace S)` is the canonical isomorphism.
  The two equations in this clause give its projection compatibilities with Y
  and T'. The `IsRepresentableWith ... IsClosedImmersion` clause is precisely
  the canonical closed immersion B to Y times_T T'. Uniqueness follows from
  the two projections and the monic inclusion, so adds no mathematical strength.
- The off-centre clause ranges over every open immersion `j : U ⟶ T` with
  `Epi (idealTensorMap j K)`. This is exactly K O_U = O_U, so these are all
  open subspaces of T minus V(K), including that full complement. It requires
  `IsPullback l (𝟙 U) D.projection j`, identifying the entire inverse image of
  U in T' with U. The two further cartesian squares identify Y times_T U with
  W times_(T') U. The equation `w ≫ W.val.arrow ≫ qY = a` retains the Y
  projection. Consequently the projection to U is the original restriction of
  g, not just some abstractly isomorphic source. Quantifying over all such
  opens is equivalent to restriction on the complement and adds no hypothesis.
- The conditional qcqs clause uses exactly the node's quasi-compactness
  convention: a compact scheme V and a surjective etale atlas. It uses
  `IsAbsolutelyQuasiSeparated` for the absolute diagonal criterion, also when
  S is not quasi-separated. The conclusion repeats those same two properties
  for D.space. This is conditional, not an added qcqs hypothesis on T.
- The final conditional clause assumes `MapIsSeparated g` and
  `MapIsFiniteType g` only here. It concludes both same properties for
  `W.val.arrow ≫ qD` and `MapIsQuasiCompact (pullback.diagonal ...)`, exactly
  quasi-compactness of its relative diagonal. No flatness, finite presentation,
  density, reducedness, separation of S, or quasi-compactness of Y is added.

Recorded dependencies used (module and declaration):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.EtaleSite`, `structureSheaf`, `Modules`, `IsEtale`,
  `IsSurjective` and `IsRepresentableWith` (scheme-test meaning of immersions).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsSeparated`, `MapIsFiniteType`; `ProperCurveModuli`: `MapIsQuasiCompact`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: the existing
  specialization to the small etale module category, with Mathlib's
  `SheafOfModules.IsQuasicoherent` predicate, used by `QuasiCoherentIdeal`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `moduleTensorPullback`, `moduleTensorAdjunction`, and its normalized
  `moduleDirectImage` through `moduleStructureMap`. No alternative pullback.
- `WeilConjectures.Blowup.Gluing`:
  `Scheme.IdealSheafData.blowup` and `blowupMap`, inside the existing
  `AlgebraicSpaceBlowupPresentation.BlowupPresentation` and `blowupChartIdeal`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, giving exactly the category in which the
  displayed IsPullback square is stated.
- Existing landed definition nodes added to stmt_deps, as permitted by
  brief-stage2 section 5: `def-sfb-space-quasi-coherent-ideal`
  (`AlgebraicSpaceQuasiCoherentIdeal.QuasiCoherentIdeal`, `idealTensorMap`),
  `def-sfb-space-blowup-presentation` (module/declarations above),
  `def-sfb-space-closed-subspace` (`AlgebraicSpaceClosedSubspace.ClosedSubspace`),
  `def-sfb-space-absolute-quasi-separated`
  (`AlgebraicSpaceAbsoluteQuasiSeparated.IsAbsolutelyQuasiSeparated`), and
  `def-sfb-space-module-structure-map`
  (`AlgebraicSpaceModuleStructureMap.moduleStructureMap`). Names here are in
  namespace `AlgebraicGeometry.AlgebraicSpace`; module names carry the prefix
  `Sheaf.AlgebraicGeometry`. No existing definitions were restated.
- All already recorded proof-dependency modules are imported without public
  visibility: AlgebraicSpaceModulePullbackQuasiCoherent,
  AlgebraicSpaceFibreProductsEtaleCovers,
  SchemeZariskiEtaleQuasiCoherentEquivalence,
  AlgebraicSpaceIdealClosedSubspaceCorrespondence, SpaceFiniteTypeComposition.
  `Mathlib.RingTheory.Smooth.Flat` supplies the recorded algebra-etale-flat match.
  The other proof nodes have no Lean declarations yet; no imports are invented.

Edge cases checked: K=0 makes every section torsion (power n=1), so the strict
transform and both blowups are empty. For K=O the power ideal is O, so only zero
is torsion and the statement becomes the identity blowup of g. For the affine
ring k[x,y]/(xy) and exceptional equation x, Gamma_x contains y and the quotient
is k[x]; x may be a zero-divisor before this quotient. Empty Y, T, charts and
open U are allowed, and n=0 merely detects the zero section. The base need not
be quasi-separated; the absolute quasi-separatedness predicate is used exactly
to avoid confusing the absolute and relative diagonal. No nonempty universe or
nonempty scheme hypothesis is introduced.

Searches made using the prescribed msearch wrapper under this item:

- leanfinder, "The strict transform of an algebraic space under blowing up the
  base is the blowup of the inverse image ideal": eight hits, including
  Scheme.Hom.liftQuotient, specTargetImage, Scheme.IdealSheafData.comapIso,
  Proj.fromOfGlobalSections; none is this algebraic-space theorem.
- loogle, `"blowup", "strictTransform"`: zero hits.
- grep, `strict.?transform|blow.?up`, Mathlib AlgebraicGeometry: zero hits.
- leansearch, "Strict transform of an algebraic space is the blowup of the
  inverse image ideal": eight hits including Scheme.IdealSheafData.support_comap,
  comapIso, comap and specTargetImageIdeal; none is this statement.
- Source rg and grep for this node id in WeilConjectures: no node-id match.
  rg for strictTransform in WeilConjectures/Compactification/StrictTransformBlowup.lean
  found `Scheme.IdealSheafData.exists_blowup_comap_iso_strictTransform`, whose
  full signature is the scheme case, not algebraic spaces. Its presence does
  not eliminate this node.
- rg for blowups/strict transforms in lean/Sheaf/AlgebraicGeometry, refined to
  AlgebraicSpace*.lean: found the existing BlowupPresentation, common admissible
  blowup and composed blowup modules. Reused those notions; no duplicate theorem.
  DAG search found the quasi-coherent-ideal, blowup-presentation, closed-subspace
  and absolute-quasi-separated nodes used here. No new notion is needed.

No statement correction or disputed mathematical assertion. The item changes
only in lean and by adding the five already-landed statement-dependency nodes.
The only postponed theorem is the item itself; its docstring gives all eight
proof steps with the same DAG dependencies as the accepted split.

Validation: prescribed scompile.py compiled both the sandbox module and its library
module path cleanly, with no errors or warnings (20.2 s and 29.1 s respectively).

## Second reading by Q32

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
