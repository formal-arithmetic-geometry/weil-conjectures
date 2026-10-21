## Worker report

Item: lem-weil-pbc-quotient-diagram-scalar-projection. Module:
Sheaf.Paper.QuotientDiagramScalarProjection. The only postponed theorem is
AlgebraicGeometry.Scheme.StrictScalarBalancing.quotientDiagramScalarProjection;
its proof is `sorry`. The three helper definitions contain actual Mathlib mate
constructions and introduce no independent mathematical notion.

The source was opened: main-20261015/blueprint/sec-proper-base-change/
sk-thm-properbasechange/lemma-weil-pbc-completed-exchange-coherence.proof.md,
second paragraph. It asks for the same projection-formula conjugations before
inverse limit; the node expands the scalar compatibility that paragraph uses.
No statement correction, new node, or dependency repair is necessary.

Clause-by-clause rendering (names below are in Scheme.StrictScalarBalancing,
unless qualified):

- Commutative Noetherian A, finitely generated I, torsion A/I, finite and perfect
  positive quotients: `{A : Type (u + 1)} [CommRing A]` and
  `(d : AdicCoefficientDatum A)`. Read its full inherited signature:
  CompleteCoefficientDatum has ideal, noetherian, finitelyGenerated,
  quotientTorsion, quotientPerfect; AdicCoefficientDatum adds quotientFinite.
  No condition on the ideal or its quotients is silently discarded.
- Schemes and their small pro-etale sites: `{X Y : Scheme.{u}}`, `f : X ⟶ Y`;
  `topology T` is the published proEtaleModelTopology T. It transports the site's
  existing object/Hom universes through AsSmall. Coefficients and modules are
  at u+1. No equality of the original site object and Hom universes is assumed.
- Constant A, finite quotient rings, completed limit and scalar map:
  `ring T d false`, `ring T d true`, `scalar T d` are the dependency's aliases
  of ConstantCompletion.coefficients/coefficientMap. Their finiteSystem is the
  actual constant quotient tower; completed is its limit and coefficientMap
  is the compatible quotient cone. Positive n is represented by Lean index n-1.
- Unbounded derived module categories and restriction r:
  `ConstantCompletion.D`, `dres (scalar T d)`; strict derived tower categories
  and restriction: `ConstantCompletion.TD`, `tdres (scalar T d)`.
  These use HasDerivedCategory.standard and the exact derived functor of
  Mathlib SheafOfModules.restrictScalars, not a new scalar construction.
- J, Delta, Q and both derived reductions:
  `reduction T d b` is the existing quotientPresentation.tower, whose source
  is D(ring T d b) and target TD(ring T d b). Its underlying construction
  tensors strict constant diagrams with the actual quotient tower, retaining
  all transitions. TD is DerivedCategory of the functor category ℕᵒᵖ ⥤ Mod,
  not a functor category into DerivedCategory. The existing delta and
  deltaFactors specify the constant-diagram functor.
- Canonical coefficient inverse images: the supplied `p : PullCompatibility`
  uses modulePull f d b and towerPull f d b; those use inverseData and
  coefficient f d b. The latter is constantMap for false and completedMap,
  defined by finite projections, for true. These are the dependency's
  canonical maps, including the scalar square, not arbitrary ring maps.
- Ordinary and strict derived pullbacks:
  `p.completed.ordinary`, `p.completed.diagrams`, `p.constant.ordinary`,
  `p.constant.diagrams`. Their PullModel fields specify exact localization
  factors and universal derived properties for the actual module pullbacks.
- Right derived images: `Ra`, `R0`, `Ha`, `H0`, together with the four supplied
  adjunctions. These parameterize a presentation of the right adjoints of the
  specified actual derived inverse images. This is the usual universal
  characterization of the ordinary unbounded derived pushforwards; no
  independent left functor or arbitrary natural map is being substituted.
  In particular, different presentations are uniquely isomorphic preserving
  the adjunctions. The equation is invariant under this unique transport.
- Normalized a, p, chi and d: a and p are the existing `p.a`, `p.p`, with
  representative normalization fields retained in PullCompatibility.
  `ordinaryScalarDirect` and `diagramScalarDirect` are exactly their right
  mates, using mateEquiv on the inverse natural transformations. This is also
  the defining formula in flatRingedDiagramRestriction's published proof
  (`delta := (mateEquiv aS aR ... b.inv).natTrans`). The first two conclusion
  clauses assert IsIso for these maps, as the node specifies comparisons by
  isomorphisms. These are structural comparisons, not conditions on K.
- rho and pullback q: `bal : Balancing d` supplies `bal.ρ T`, its K-flat
  representative formula, strict augmentation and its equation. The supplied
  `p` is precisely a PullCompatibility for those rho components, with tau,
  constantReassociation and their ordinary and derived normalizations.
- Both projection arrows: `quotientProjection` applies Mathlib mateEquiv to
  tau.inv with the ordinary and strict adjunctions. By the mate formula its
  component at K is the strict Hom-bijection image of tau.inv at RK followed
  by B_X of the ordinary counit. This is exactly the node's specified
  adjunct of counit tensored with identity after diagonal identification.
  No component chosen after evaluation is used. The constant version uses
  p.constantReassociation, the completed version p.τ.
- Equation: the left side is Lean composition r_Y(piA), then d at B_X^a K,
  then H0(rho_K); the right side is rho at Ra K, then B_Y^0(chi_K), then pi0
  at r_X K. Lean `≫` reads left to right, reversing the written TeX order.
  Each domain and codomain elaborates in TD(ring Y d false).
- Arbitrary ambient inputs and naturality: `∀ K : D (ring X d true)` excludes
  no objects. The three helpers are natural transformations; rho and the
  reduction functors already are natural. Thus all composites are natural,
  and their componentwise equality is equality at every ambient input.
  There is no properness, completeness, boundedness, witness, evaluation,
  inverse-limit or projection-isomorphism hypothesis.

Dependency declarations read and used:

- Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings:
  SheafOfModules.restrictScalars (via ConstantCompletion.dres/tdres).
- Sheaf.Paper.AdicCoefficientDatum and CompletedAdicCoefficientDatum:
  Scheme.AdicCoefficientDatum, inherited CompleteCoefficientDatum, the
  completed coefficient and strict reduction constructions. The recorded
  completedReductionTower signature and docstring were read.
- Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations:
  proEtaleConstantRingDerivedPullback and its ordinary adjunction. The
  higher-coefficient-universe presentation used here is already provided
  by the published StrictQuotientScalarBalancing interface, avoiding its
  older constant-ring specialization's coefficient universe restriction.
- Sheaf.Paper.ProjectionFormulaBaseChangeNaturality:
  proEtaleProjectionFormulaMate, read with the existing
  CategoryTheory.derivedProjectionFormulaMate in ProjectionFormulaArrows.
  The strict source-adjusted map is its counit adjunct, constructed by
  Mathlib.CategoryTheory.Adjunction.Mates.mateEquiv, not a duplicate tensor.
- def-weil-size-convention is a convention record, with no declaration.
- Sheaf.CategoryTheory.DiagramSiteRealization:
  CategoryTheory.exists_diagramSite_realization; its exact equivalence
  justifies the existing strict module-tower presentation.
- Sheaf.CategoryTheory.FlatRingedDiagramRestriction:
  FlatRingedDiagramInput.flatRingedDiagramRestriction, its maps and
  DerivedRestrictionComparison.adjuncts; read both comparison structures
  and the actual right-mate construction in its proof.
- Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage:
  proEtale_profinite_coefficient_inverse_image, coefficient tower, constant
  comparison and the projection-defined completed comparison.
- Sheaf.Paper.StrictQuotientScalarBalancing:
  Balancing, PullCompatibility, PullModel, PullReductionComputes, ring,
  scalar, reduction, coefficient, modulePull and towerPull. These recorded
  declarations supply all coefficient and representative normalizations.
- Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization:
  ringedConstantTowerPushforwardNormalization and its last strict counit
  equation, identifying the source-adjusted projection with our definition.
- Proof-only imports retain ConstantLeftModuleInverseImage,
  CompletedConstantAlgebraFlatQuotients, ReductionPullbackDerivedTower and
  RingedTopoiCanonicalTensorPullbackOfUniverses, with their recorded
  declarations and proof plans read. The proof dependency
  lem-weil-pbc-augmented-diagram-projection-mate has no published Lean record;
  no import can be added for it. It is not needed to type any declaration:
  the actual canonical projection is directly defined by the existing mate
  construction above. Its stated identification is recorded in the proof
  docstring, and may be used in stage 3 when that node is published.

Edge cases checked before writing: zero object K, identity f, empty source or
empty target schemes whenever a morphism exists, I = 0 and I = top when the
datum hypotheses hold, zero coefficient ring, infinite Noetherian A with finite
quotients, and positive exponent 1. No Nonempty site or nonzero ring condition
is introduced. Tensoring with A/I^n is derived: no flatness of that quotient
is assumed. Both ordinary and diagram pullbacks are specified for every
ambient object; no completeness witness narrows K. Right-adjoint choices do
not add a mathematical restriction: existing ordinary unbounded derived
operations provide them, and their adjunctions determine the mate formula.

Searches performed anew (raw summaries are in sandbox searches.jsonl):

- msearch leanfinder: "Restriction of scalars respects strict derived quotient
  tower projection maps defined by the counit adjunction". Eight ordinary
  ModuleCat scalar restriction and counit hits; no strict derived quotient
  compatibility theorem.
- msearch loogle: "CategoryTheory.mateEquiv, CategoryTheory.Adjunction".
  Twelve mate correspondence identities; reused mateEquiv directly.
- msearch grep: "rightAdjointProjectionMap|mateEquiv_counit" in CategoryTheory.
  Four hits in Mathlib Adjunction.Mates and Monoidal.Closed.Functor. These
  abstract identities do not state the specialized coefficient equation.
- msearch leansearch: "Restriction of scalars preserves the counit projection
  morphism on strict derived quotient towers". Eight ordinary scalar/module
  hits; no matching statement.
- rg in lean/WeilConjectures and lean/Sheaf for quotient/scalar/projection,
  strictQuotient and the proposed declaration names; upstream finite-field
  coefficient ScalarExtension/ProjectionExtendScalars concerns extension
  between finite field coefficients, not restriction from a completed
  sheaf to its constant ring and strict quotient diagrams. No declaration
  with the proposed full names exists. grep of the item id in upstream
  WeilConjectures returns no match. dag/lean_names_upstream.json was included
  in the declaration-name check.

Validation: scompile.py compiled this module both in its isolated sandbox and
under its actual library module name with no diagnostics (4.2 s and 4.7 s).
The module has explicit universes and autoImplicit false, real definitions,
source and blueprint docstrings, and a full seven-step theorem proof plan.

## Second reading by NI

A second pass in this worker opened the node and completed file together;
no other agent was started, as the dispatcher brief explicitly prohibits it.
The maintainer's independent reading remains part of delivery review.

The ring/ideal hypotheses are all inherited through the existing datum; I
checked each inherited field, including quotientPerfect's positive-exponent
bound and quotientFinite's n+1 indexing. I checked the equation's six arrows
against their typed sources and targets: both sides run from restricted
completed reduction of Ra K to H0 of constant reduction of restricted K.
The strict right comparison uses p.p.inv and the ordinary comparison uses
p.a.inv, which fixes the otherwise easy orientation error. Projection uses
tau.inv, giving exactly s followed by reduction of the counit.

The supplied PullCompatibility is not an arbitrary square: I read its
ordinaryScalar_normalized, a_computes, p_computes, ordinaryCompleted_normalized,
ordinaryConstant_normalized, tau_computes and constantReassociation_computes
fields. They fix the coefficient and K-flat representative maps required by
the node. The supplied Balancing retains augmentation and all transitions.
All direct images are right adjoints to these fixed actual pullbacks, so
no separate arbitrary-map normalization assumption has been added. Natural
transformations retain naturality in K even though the final equality is
written componentwise. No mismatch or statement correction was found.
