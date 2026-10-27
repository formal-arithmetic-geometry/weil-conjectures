## Worker report

Stage 2, group NU, item lem-pur-affine-line-composite-transpose.
Module: Sheaf.Paper.AffineLineCompositeTranspose.
Namespace: AlgebraicGeometry.ProEtale.AffineLineEvaluation.

The module states four clauses of the item, each with sorry: evaluation_naturality,
evaluation_unit, exceptionalInput, and composite_transpose. All definitions contain real
canonical data. No proof of purity, no arbitrary comparison map, and no ambient exceptional
adjunction is introduced. The node's statement, six reviewed proof steps, and proof dependencies
are unchanged. The former worker's stage-1 stale-dispatch objection does not apply: this is the
new stage-2 statement task, and the reviewed NK split is used verbatim.

### Hypotheses and clauses

- Finite field and coefficient setting: the explicit variable
  P : WeilConjectures.PurityFiniteSetting.{u} is the recorded finite-field datum, coefficient
  prime distinct from the characteristic, finite extension, and positive level. Ring P means
  AffineLinePurity.Ring P, the existing finite Tate coefficient at zero-based index P.level - 1.
  The recorded ringEquiv identifies it canonically with P.Coefficient. The annihilating exponent
  is the already-published AffineSpacePurity.annihilates P, valid at every positive level.
- All bases are separated finite type over k: aB (respectively aY) is the structure morphism
  to Spec P.field.k, with LocallyOfFiniteType, QuasiCompact, and IsSeparated instances.
  The morphism p has these same three properties. The structure morphism of X is p ≫ aY;
  thus p is literally over the fixed base. This avoids an additional equality between two
  independently supplied structure maps. Its source geometry follows by composition.
- The affine-line projection is AffineSpace PUnit.{u + 1} B ↘ B, the recorded affine-space
  construction with exactly one coordinate. No higher-dimensional or affine-base restriction
  is imposed. The canonical compactification is affineTraceLineCompactification B.
- The small pro-etale category is the recorded AffineSpacePurity.D P B, namely derived
  sheaves with values ModuleCat.{u+1} (Ring P) on Scheme.ProEt.topology B. Object and morphism
  universes of the site retain the prescribed sizes. The definitions C, D, Plus and
  etaleFiniteTor are imported existing coordinate abbreviations, not new categories.
- H, M, and K in D^b_ctf are expressed by their arbitrary original pro-etale object together
  with an ordinary etale finite-Tor constructible representative He, Me, or Ke and its
  comparison isomorphism eH, eM, or eK. These are precisely the representative inputs already
  required by the recorded affineLinePurityComparison. The comparison theorem on Noetherian
  schemes supplies such coordinates for every object in the node's domain. K is additionally
  packaged in the recorded Plus category; bounded constructibility supplies that bound.
- F_u is exactly AffineSpacePurity.lineSource P B. Its published lineSource_obj_eq identifies
  its object with AffineLinePurity.source, hence with Lu^*H tensor A_L(1)[2]. Its morphism map
  is the functorial tensor-pullback map, used literally in naturality and theta.
- t_B is trace P B aB, which inserts the derived Noetherian witness into the recorded
  AffineLinePurity.integration. That integration is the actual open-extension counit followed
  by the normalized projective trace. No new trace or normalization is chosen.
- Pi is the specified inverse projection with both symmetries: evaluation calls the recorded
  AffineLinePurity.augmentation, which is projectionTensorTrace with projection_isIso. That
  definition uses inverseProjection of the exact specified projection transformation.
- b_{u,H}=rho_H (1 tensor t_B) Pi_H: evaluation is augmentation precomposed with the map of
  eqToHom (lineSource_obj_eq P B H), solely to align the existing source-functor coordinates.
  No counit is substituted for this definition.
- Naturality on all maps between finite-Tor constructible objects is evaluation_naturality:
  R u_!(F_u(h)) ≫ evaluation(H') = evaluation(H) ≫ h. He and He' and their realization
  isomorphisms are independent; the statement does not require h to be specified etale data.
  This component equation is exactly the natural-transformation law on the full subcategory.
- The coefficient-unit identification is unitSource. It uses the canonical pullbackUnit,
  coefficientUnitIso, and left unitor, applied by the recorded derived tensor bifunctor.
  comparedLeftUnit caches this ordinary construction at general coefficients so elaboration
  does not expand the specialized derived categories. unitTensor then inserts pullbackUnit.
- b_{u,A_B}=t_B under those identifications is evaluation_unit: evaluation at unit equals
  the compact-support map of unitSource.hom followed by trace. It quantifies over every
  permitted representative of the coefficient unit and imposes no extra unit-normalization
  hypothesis.
- Rp^!K is finite-Tor constructible: exceptionalInput states this on its canonical ordinary
  antecedent exceptionalAntecedent. The comparison image is definitionally exceptionalImage
  applied to K, so this is the same assertion in the existing ordinary coordinates.
  exceptionalPlus supplies the published bounded-below preservation as real proof data;
  theta uses exceptionalInput as the finite-Tor proof, never as an additional assumption.
- Exceptional functors and counits are exceptionalImage and counit, which insert Noetherian
  geometry and use the existing rightDerivedUpperShriek and rightDerivedUpperShriekCounit.
  These are the standing-compactification presentations of the recorded finite exceptional
  functor sfFiniteExceptionalAt. The lineComparison additionally applies its existing
  canonical lineExceptionalIso to the recorded affineLinePurityComparison.
- theta's binder t is every morphism M -> Rp^!K. The arrow J in the node is exactly
  (support P aY p).map t ≫ counit P aY p K in composite_transpose.
- alpha is compositor, the actual originCompositionAmbient from thm-sf-comp-composition,
  evaluated at the original line-source object with the explicit canonical lineWitness.
  The retained antecedent and its iso give the existing full-subcategory property directly.
- c^-1 is inverseConjugate: it calls the existing AffineSpacePurity.compositionInverse,
  which transposes the pasted counit using exactly originCompositionAmbient.inv. Thus it is
  the adjunction conjugate of this alpha with the specified composite-adjunction convention;
  it is not a right-adjoint isomorphism chosen from Nonempty.
- Theta is theta: lineSource.map t, then the recorded lineComparison at exceptionalPlus K
  with canonical exceptionalAntecedent and exceptionalInput, then inverseConjugate.
  The realization iso of this antecedent is Iso.refl of the defining exceptional formula.
- The actual transpose identity is composite_transpose. In Lean's left-to-right composition
  convention its left side is R(pq)_!(theta) ≫ epsilon_pq. The right side is
  compositor.inv ≫ Rp_!(standingEvaluation M) ≫ Rp_!(t) ≫ epsilon_p,
  precisely alpha^-1 followed by Rp_!(b) and J in the node's order.
- The b used with standing compact support is standingEvaluation. It transports evaluation
  along changeSupport, the existing fixedCompactSupportOriginIso at the explicit lineWitness.
  changeSupport conjugates that canonical comparison by the retained witness iso. It makes
  no independence claim on arbitrary unbounded pro-etale objects.
- Every source in the transpose is of the allowed class: linePlus and lineWitness are
  constructed from the published source_plus, sourceWitness, and lineSource_obj_eq;
  compositor uses this actual etale origin, and counit only accepts Plus targets. No
  ambient exceptional adjunction is a binder or asserted anywhere.

### Dependency declarations read and used

The module publicly imports the recorded statement dependencies and the additional landed
node owning the source and conjugate helpers. Proof dependencies are plain imports unless
also statement dependencies.

- def-pur-conventions: Sheaf.Paper.PurityFiniteSetting, WeilConjectures.PurityFiniteSetting
  and its finite positive-level coefficient setting.
- def-coefficient-twists-detailed: Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted,
  reexporting intrinsic finite Tate sheaves; the actual compared shifted line is the
  recorded AffineLinePurity.coefficient used by lineSource and integration.
- def-compact-support-direct-image-detailed: Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport,
  Scheme.sfIntrinsicCompactSupport. Fixed-scalar compact-support coordinates are the same
  chosen open extension followed by derived proper image, as in the affine-line dependency.
- def-pur-affine-line-purity-comparison: Sheaf.Paper.AffineLinePurityComparison,
  AffineLinePurity.integration, augmentation, source_plus, sourceWitness and
  affineLinePurityComparison. Its source and coordinate-map modules are publicly reexported.
- def-sbc-affine-space: Mathlib.AlgebraicGeometry.AffineSpace,
  AlgebraicGeometry.AffineSpace and its projection.
- def-weil-derived-pullback-tensor-hom: Sheaf.Paper.DerivedPullbackTensorHom;
  derivedTensor and leftDerivedUpperStar in the fixed finite-coefficient presentation.
- def-weil-exceptional-inverse-image:
  Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients, with the reexported
  sfFiniteExceptionalAt of Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt; the standing
  rightDerivedUpperShriek has the same nu^* f^times Rnu_* construction.
- def-weil-finite-tor-amplitude: Sheaf.Paper.FiniteTorAmplitudeSites, reexporting the
  original pro-etale definition as well as ordinary finiteTorConstructibleEtale.
  etaleFiniteTor uses the same constructibleFiniteTor predicate in ordinary coordinates.
- def-weil-pbc-adjunction-conjugate: Mathlib.CategoryTheory.Adjunction.Mates,
  CategoryTheory.conjugateEquiv and conjugateIsoEquiv, with conjugateEquiv_counit.
- def-weil-pbc-composite-adjunction: Mathlib.CategoryTheory.Adjunction.Basic,
  CategoryTheory.Adjunction.comp and comp_counit_app. The existing compositionInverse
  explicitly uses the resulting pasted counit.
- def-weil-scheme-morphism-properties is a convention record, not a declaration.
  LocallyOfFiniteType, QuasiCompact, IsSeparated and Scheme are the recorded properties.
- thm-sf-comp-composition: Sheaf.Paper.CanonicalOriginCompactSupportComposition,
  originCompositionAmbient and its canonical full-origin comparator.
- Added landed dependency def-pur-affine-space-comparison:
  Sheaf.Paper.AffineSpacePurityComparison, lineSource, lineSource_obj_eq, lineComparison,
  compositionInverse, C/D/Plus, etaleFiniteTor, tensorIso, and annihilates.
  This node does not depend on the item: no dependency cycle is introduced.
- Added existing dependency thm-nagata-compactification:
  WeilConjectures.Compactification.NagataCompactification, NagataCompactification and its
  HasCompactification instance. support and exceptionalImage derive all needed compactification
  instances internally, after deriving Noetherian geometry from aB.
- Proof inputs: Sheaf.Paper.ExchangeProjectionSuppliedDomains;
  Sheaf.SixFunctors.OpenTensorNormalization (openTensorNormalization);
  Sheaf.Paper.ProEtaleConstructibleOrigin (constructible_proEtale_origin);
  Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula (isIso_finiteCompactProjection);
  Sheaf.Paper.ProjectionMateExact (ringedProjectionMateExact);
  Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom (specifiedExceptionalHomEquiv);
  Sheaf.Paper.SfPreservationClass (Scheme.sf_preservation_class).

### Edge cases

Checked the types and mathematical formulas before stating them: empty B or X (no point or
nonempty assumption); M=0 and theta=0 (functorial zero maps); p=id (the normalized origin
compositor and its mate); H=the coefficient unit (the actual left-unit identification is
included); positive level 1 and arbitrary ramification (no e|level or nonzero Kummer-level
assumption); all coefficient extensions and levels already in PurityFiniteSetting; singular
bases and nonsmooth p (no smoothness assumed); arbitrary ambient morphisms between the
constructible inputs (no choice of etale lift of theta); ordinary representatives differing
by an arbitrary comparison iso. All source universes match the published small sites.

### Searches

- msearch.py leanfinder: "Affine line integration evaluation naturality and exceptional
  inverse image composite transpose". Eight hits on curve integrals and continuous-linear
  integration, none on these sheaf-theoretic maps.
- msearch.py loogle: `CategoryTheory.Adjunction, "counit"`. Twelve hits, including
  Adjunction.comp_counit_app and homEquiv_counit; these are generic identities, not the
  specified affine-line result. Read Basic.lean and Mates.lean at those formulas.
- msearch.py grep: `affine.*(counit|transpose)|purity.*comp|integration.*natural`,
  Mathlib/AlgebraicGeometry: zero hits.
- msearch.py leansearch: "The transpose under a composite exceptional adjunction equals
  the iterated compact support counit and affine line integration". Eight hits, including
  Adjunction.comp, comp_counit_app, comp_unit_app, and unrelated linear transpose.
- rg over lean/WeilConjectures and lean/Sheaf for
  `affine.*(counit|transpose)|purity.*comp|integration.*natural` and the exact node id.
  No declaration of the item; the searches identified the published lineSource,
  lineComparison and compositionInverse in AffineSpacePurityComparison, which are reused.
- Source read: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/
  _section.md, the Integration paragraph: affine-line counit at constants and the
  inductive compact-support composition law. The six reviewed item proof steps are retained.

No new definition nodes, dependency repairs, statement correction, or statement dispute.
The only DAG changes besides lean are adding the two existing owning dependencies above.
Compilation is exclusively through the authorized scompile.py wrapper. The expensive unit
elaboration was repaired by constructing comparedLeftUnit at general coefficient categories
before specializing it; the delivered module is not split to evade the per-file limit.

## Second reading by NU

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
