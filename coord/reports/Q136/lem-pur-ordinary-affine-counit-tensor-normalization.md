## Worker report

Item: lem-pur-ordinary-affine-counit-tensor-normalization. The module
Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization states
AlgebraicGeometry.Etale.ordinaryAffineCounit_tensor_normalization, with `sorry`.
Five definition helpers have complete data: descentStep, descent, reassociation,
counit, trace, all in AlgebraicGeometry.Etale.OrdinaryAffineCounitTensorNormalization.
There are no other postponed declarations in this delivery.

Source read: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
lem-amb-affine-space-top-trace.proof.md, both paragraphs, and
cor-pur-vector-bundle-purity.proof.md, paragraph 2. The first identifies the line
trace with the actual composed counit and uses the ordered tower and compactified
projection formula; the second requires these specified maps on trivializations.
The complete eight-step natural-language proof of the DAG node is rendered in the
theorem docstring, including the categorical action argument and the unbounded
successor argument. Stage 2 supplies its statement only.

Hypotheses and clauses:

- N >= 1: `(N : ℕ) (hN : 0 < N)`.
- Finite commutative coefficient ring: `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  Annihilation NA=0: `(hA : (N : A) = 0)`; for a unital ring this is equivalent
  to annihilating every element.
- Noetherian base: `(S : Scheme.{u}) [IsNoetherian S]`. Mathlib's
  isNoetherian_iff_of_finite_iSup_eq_top gives exactly the finite affine cover
  formulation; no finite-dimensional or finite-type-over-a-field hypothesis appears.
- Invertibility on the base: `(hS : IsUnit (N : Γ(S, ⊤)))`.
- Arbitrary nonnegative dimension: `(d : ℕ)`; arbitrary unbounded input:
  `(K : DerivedCategoryModule A S)`. There is no D+, constructibility or Tor premise.
- Small ordinary etale categories are precisely DerivedCategoryModule, the derived
  category of Sheaf S.smallEtaleTopology (ModuleCat.{u+1} A), using the published
  universe convention with scheme universe u and coefficient universe u+1.
- p_d and X_d: affineTraceProjection S d and affineTraceTower S d. The recorded
  affineTraceAffineSpaceIso S d identifies this model with
  AffineSpace (ULift (Fin d)) S over S, using exactly the ordered coordinates.
  At d=0 the model and projection are literally S and its identity.
- W_d: SectionLocalDualizingComparisons.tateObject A N hA (affineTraceTower S d) d,
  whose body is the degree-zero finiteEtaleTateTwist shifted by 2*d. It is the
  concrete ordinary Tate sheaf, not an exceptional object or pro-etale twist.
- G_d K: the derivedTensor object whose first factor is the exact
  `(upperStar ... p_d).mapDerivedCategory.obj K` and whose second factor is W_d.
  The helper reassociation has precisely this target.
- The prescribed normalized line adjunctions: `t : OrdinaryFiniteTwistTransport`
  and `D : ∀ T [IsNoetherian T] hT, OrdinaryFiniteP1Datum ...` are the existing
  normalized datum, not unconstrained adjunction choices. The record constrains
  its decomposition by Kummer components and its actual counit by projection and
  trace. The statement holds for every such normalized presentation. Their existence
  is already supplied by exists_ordinaryFiniteP1Adjunction. No base-change law is
  added as a hypothesis, since the pointwise normalization suffices here.
- Ordered composite: affineTraceAdjunction A N hA t D S hS d, recursively composing
  affineTraceOpenAdjunction with D.adjunction and then through the coordinate tower.
  The recursion starts at Adjunction.id. No right-adjoint uniqueness is used to
  replace the specified counit.
- Left comparison: affineDualizingTowerComparison A S d. Its complete body was read:
  at zero it is inverse unboundedEtaleLowerShriekId; at successors it uses
  rightDerivedLowerShriekIso for the standard line compactification, the preceding
  comparison, and unboundedEtaleLowerShriekCompIso. This is the required proper/open
  normalized unbounded compositor. It is reused rather than defined a second time.
- Right comparison: descent recursively uses affineLinearLineDescent, canonical
  inverse-image tensor/composition comparisons and derivedTensorAssociator.
  Its zero case uses the inverse right unitor and inverse identity pullback.
  reassociation then uses ordinaryFiniteTensorPullback, the comparison from left
  derived to exact inverse image, and the existing root-normalized towerTateIso.
  In particular it makes no `Nonempty.some` choice from affineTraceRight_normalForm.
- Actual epsilon: counit is direct image of inverse reassociation, inverse left
  comparison, then `(affineTraceAdjunction ...).counit.app K`.
- Unit trace t_d: trace is direct image of inverse towerTateIso, inverse left
  comparison, then affineTraceCounit, which is exactly the tower counit evaluated
  at ordinaryFiniteUnit. The coefficient source is thus identified directly with W_d.
  The unit comparison in reassociation is the same canonical tensor-unit comparison;
  coherence identifies this trace with epsilon at the coefficient unit.
- Projection P: `compactSupportProjectionMap A p_d W_d K`, already defined in
  ShriekTensorComposition from the canonical proper/open compactification projection
  with signed symmetry and the exact inverse-image comparison. The theorem supplies
  `∃ P : (K tensor Rp!W_d) ≅ Rp!(p* K tensor W_d), P.hom = ... ∧ ...`.
  Therefore P.inv is the actual specified projection inverse; this packages its
  invertibility as a conclusion, without an extra isIso assumption or a total inverse.
- Formula: `counit ... K = P.inv ≫ ((derivedTensor ... S).obj K).map (trace ...) ≫
  (derivedTensorSingleUnitIso K).hom`. Lean composition order is left to right;
  this is exactly rho_K composed with (1_K tensor t_d) composed with inverse P.
  derivedTensorSingleUnitIso is the right unitor after the canonical identification
  of the degree-zero constant module sheaf with the derived tensor unit.

Dependency declarations used (all signatures and relevant docstrings were read):

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Mathlib.AlgebraicGeometry.AffineSpace: AlgebraicGeometry.AffineSpace, its projection.
- Mathlib.AlgebraicGeometry.Noetherian: IsNoetherian and the finite affine-cover criterion.
- WeilConjectures.AlgebraicGeometry.DerivedCategories and
  WeilConjectures.SixFunctors.Etale.Derived.Coefficients: DerivedCategoryModule.
- WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact:
  etaleInverseImageModulesExact; upperStar's exact derived realization is used
  through leftDerivedUpperStarIsoMapDerivedCategory.
- WeilConjectures.SixFunctors.Etale.Derived.Tensor: derivedTensor, derivedTensorRight;
  TensorStructure: derivedTensorAssociator; ReductionConservative:
  derivedTensorSingleUnitIso, all the existing K-flat monoidal structure.
- Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback:
  Scheme.etaleFiniteTwistPullback, FiniteEtaleTwistPullbackData and its normalized
  coefficient and product comparisons.
- Sheaf.AlgebraicGeometry.AffineSpaceTopTrace:
  exists_affineSpaceTopTrace; its public AffineTraceConstruction gives
  affineTraceAdjunction, affineTraceCounit, affineTraceRight and the ordered tower.
- Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction:
  exists_ordinaryFiniteP1Adjunction; OrdinaryFiniteP1Data/Arrows give
  OrdinaryFiniteP1Datum, OrdinaryFiniteTwistTransport, ordinaryFiniteTensorPullback,
  ordinaryFiniteTensorRightMapIso and ordinaryFiniteShiftedLinePullback.
- Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons:
  unboundedEtaleLowerShriekCompIso and unboundedEtaleLowerShriekId.
- Sheaf.AlgebraicGeometry.ProperProjectionFormula:
  isIso_proper_projection_formula_reordered (proof input).
- WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection:
  derivedOpenImmersionLowerShriekProjectionIso (proof input).
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriek:
  rightDerivedLowerShriekOfCompactification and rightDerivedLowerShriek.
- Sheaf.AlgebraicGeometry.AffineLinearTraceAction:
  affineLinearBaseCoefficient, affineLinearLineDescent,
  affineLinearCoefficientDescent, affineLinearPullbackId.
- Sheaf.Paper.CoordinateCounitArrows: CoordinateCounitArrows.towerTateIso, assembled
  from the canonical shifted Tate products; no new Tate coefficient definition.
- Sheaf.Paper.SectionLocalComparisonData:
  SectionLocalDualizingComparisons.tateObject (the existing shifted Tate object).
- Sheaf.SixFunctors.AffineDualizingCoefficient: affineDualizingTowerComparison.
- Sheaf.AlgebraicGeometry.ShriekTensorComposition:
  compactSupportProjectionMap and compactSupportProjectionMap_comp.

The statement dependencies include the landed definition owners
`def-amb-affine-linear-trace-action`, `def-trf-coordinate-counit-arrows`,
`def-trf-section-local-comparison-data`, and `def-pur-compact-support-projection-map`.
The new existing:true definition-only owner
`def-pur-affine-dualizing-tower-comparison` records the unchanged tower comparison.
The explicit construction, tower, ordinary P1 datum and ordinary P1 arrows owners
are also cited: `def-amb-affine-trace-construction`, `def-amb-affine-trace-tower`,
`def-asd-ordinary-finite-p1-data`, `def-asd-ordinary-finite-p1-arrows`.
Their owning modules are publicly imported. Every already stated proof-dependency
module is imported (public when also needed by the statement). No declaration is
copied or moved. There is no statement correction or dependency-module repair.

Edge cases checked before and after writing: d=0 uses the literal identity tower;
W_0 is the constant coefficient complex with shift zero and the formula becomes the
canonical right unitor, with no d>0 premise. N=1 forces zero coefficients and remains
allowed; the zero ring for any positive annihilator remains allowed because no
Nontrivial instance appears. The empty scheme has no excluded nonempty hypothesis.
For zero coefficients and the empty site all displayed morphisms are unique zero
object maps. Nothing requires nonzero Tate generators. K can have cohomology in
arbitrarily positive and negative degrees. No degree or support condition is implicit
in DerivedCategoryModule. No unresolved statement dispute was found.

Searches for an existing statement:

- msearch.py leanfinder: "The ordinary etale affine space adjunction counit equals
  inverse compact support projection followed by tensor with the trace at the
  coefficient unit". Eight hits: Gamma-Spec counits and affine-space coordinate
  formulas, none the required integration counit equation.
- msearch.py loogle: "CategoryTheory.Adjunction.counit,
  CategoryTheory.MonoidalCategory". Twelve monoidal-adjunction identities, including
  map_mu_comp_counit_app_tensor, but none the specified ordinary affine tower result.
- msearch.py grep: "affine.*counit|counit.*affine|counit.*tensor" in CategoryTheory.
  Sixteen unrelated monoidal/closed-category matches, no affine etale result.
- rg in lean/WeilConjectures and lean/Sheaf for
  affineTrace.*(normal|[Pp]rojection|[Tt]ensor), ordinaryAffine.*[Cc]ounit,
  affine.*counit.*tensor; grep -rn of this exact node id in WeilConjectures returned
  no exact statement. The project search found the reused tower, coordinate Tate
  arrows and compact-support comparator. The similarly named
  AffineCoefficientCounitNormalization handles constructible pro-etale coefficient
  domains and a line assertion, not this all-complexes ordinary theorem.
  AffineTraceRightNormalForm only returns a bare Nonempty normal form, which cannot
  select the canonical actual counit; no copy of it was made.

Validation: prescribed scompile.py compiled this module both in sandbox module mode
and at its final library path with no errors or non-sorry warnings. autoImplicit is
false; every variable/universe is explicitly bound. All lines are at most 100 columns.
The theorem has its only proof `by sorry`; helpers contain real compositions/recursion.

## Second reading by Q136

A separate rereading pass in this worker session compared the final module to the node
and opened the reused definitions; the maintainer supplies the independent review.
Checked the zero/step recursion, the order of projection factors, the actual counit
source and target, and the trace's direct transport from the unit counit. In particular
P.hom is constrained to the published projection, not assumed invertible or replaced
by a chosen isomorphism. The Tate object is the concrete degree-zero finite twist shifted
by 2d. The arbitrary K binder has no boundedness or Tor-amplitude condition. D is a
normalized projective-line datum rather than a hollow arbitrary adjunction. Reused
unbounded tower comparison has the correct inverse orientation before the counit.
The coordinate tower has its published isomorphism to the node's affine space,
including dimension zero. No mathematical statement changes were made on rereading;
the explicit public statement imports and landed dependency ids were completed.


## Repair of return L at 8a5a4c598e0a

H2 is repaired in the sandbox, retaining the accepted mathematical statement,
five actual constructions and eight-step proof. The saved packet initially passed
`deliver2.py --no-push` at 2c677312fc0, demonstrating that the semantic ownership
repair was not detected by the mechanical gate. Relative to current main, the
item's only changed fields are stmt_deps and lean; the original statement, proof,
proof_deps and all other metadata are retained verbatim.

The plain `compactSupportProjectionMap` is now cited through the already landed
`def-pur-compact-support-projection-map`, not through the conclusion of
`lem-amb-shriek-tensor-composition`. The latter remains in proof_deps exactly
because proof step 7 uses its composition equation. The plain irreducible
`affineDualizingTowerComparison` is now cited through the new definition owner
below, not through `lem-coef-dualizing-affine-space`. No proof step uses the
latter's coefficient theorem, so it is not added to proof_deps. In particular,
proof_deps remains exactly the union of every unchanged proof step's uses;
no unused theorem is added merely because its module contains a definition.
The four advisory definition dependencies were added with explicit public imports.
No `Classical.choose`, `.choose`, move or copy was introduced.

Second reading of the repaired packet by Q136: opened the original node, final
Lean file, new node and source comparison body. The new definition node's
signature is the published signature verbatim; its zero branch is the inverse
identity comparison, and its successor is exactly the three whiskering/composition
operations described in the node. It has finite commutative coefficients and a
Noetherian base, with arbitrary r and all unbounded inputs; no N or nonzero-ring
hypothesis is present. Its four statement dependencies are exactly the owners
requested in the return. The main theorem's N>0, NA=0, invertible N, finite A,
Noetherian S, arbitrary d and unbounded K binders are unchanged. Its existential
P still has the canonical projection as hom and the formula still uses P.inv.
The trace remains the transported actual counit with the same ordered Tate
comparison. Dimension zero, zero coefficients and empty base remain included.
Only explicit owning-module imports changed in the Lean file. The maintainer
performs the independent review; this dispatcher worker does not spawn agents.

## New nodes

`def-pur-affine-dualizing-tower-comparison` is the definition-only owner of the
published `AlgebraicGeometry.Etale.affineDualizingTowerComparison` in
`Sheaf.SixFunctors.AffineDualizingCoefficient` (existing:true, no file). Its source
is the latest blueprint affine-space top-trace proof, final paragraph, where the
ordered line tower is compared with compact support on chosen compactifications.
For finite commutative A and Noetherian S it recursively defines the isomorphism
from the literal ordered left functor to Rp_r!: zero uses the inverse identity
comparison, successors use the standard compactification comparison, the previous
comparison and the proper/open compositor. This is actual data already written in
full; it does not extract data from the coefficient theorem or from Nonempty.
The return explicitly requests this owner without moving or copying the definition.

Searches for this new node (2026-10-24, preserved in mathlib_searches):

- msearch.py leansearch, "Canonical natural isomorphism from the iterated affine
  line compact support functor to the compact support functor of affine space":
  eight hits about affine-space geometry and generic categories, no etale comparison.
- msearch.py leanfinder, "Ordered coordinate tower comparison for compact support,
  formed by proper open composition and the identity isomorphism": eight unrelated
  compactly supported continuous map hits.
- msearch.py grep, "affineDualizingTowerComparison|affineTraceLeft|
  unboundedEtaleLowerShriekCompIso": zero Mathlib hits.
- rg on dag/nodes for affineDualizingTowerComparison: only the existing theorem
  node lem-coef-dualizing-affine-space, no definition owner. The broader tower
  comparison search returned unrelated coefficient/reindexing comparisons, not
  this ordinary affine left-functor recursion. rg in lean/WeilConjectures: no hit;
  in lean/Sheaf: the actual definition and uses in AffineDualizingCoefficient.lean.
  blueprint_refs.py search "affine dualizing tower comparison": zero blueprint
  nodes. blueprint_refs.py ancestor reports cor-pur-vector-bundle-purity; the new
  node uses that ancestor and the item's prefixed via chain.

Final repair self-check: the main theorem signature is verbatim in lean.statement;
the proof and proof_deps equal current main, with proof_deps equal to the step-use
union; every base statement dependency is retained; the new existing signature
is verbatim in its source; lines are at most 100 columns. All known reachable
DAG paths were checked for a cycle back to the item, with none found. The wider
upstream DAG contains unresolved references (not introduced by this packet), so
that extra traversal is a partial audit; the server preflight remains authoritative.
The repaired main module compiled via scompile.py in both sandbox and library
modes in 14.2/14.3 seconds, with no errors or non-sorry warnings.

The repaired dry run compiled its probes but reported the new-node metadata key
`import_flags` missing. Added `import_flags: []`, the current schema's required
empty flag list (tools/stage2_delivery.py, 2026-10-23 schema update), and reran the
prescribed dry run. No Lean or statement change was needed for that diagnostic.
