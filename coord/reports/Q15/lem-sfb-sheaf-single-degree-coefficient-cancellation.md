## Worker report

Q15 states `AlgebraicGeometry.sheafSingleDegreeCoefficientCancellation` in
`Sheaf.AlgebraicGeometry.SheafSingleDegreeCoefficientCancellation`. Its sole theorem
has proof `sorry`; all twelve auxiliary constructions contain real data. These helpers
belong to the scalar action and affine/polynomial cone of this node, rather than defining
another derived category, tensor product, pullback, coherence predicate, or base change.
No statement correction, new node, or dependency-interface repair is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- `D A : Type u`, `CommRing`, `IsNoetherianRing D`, and `Algebra D A` give the
  commutative Noetherian base and the specified coefficient homomorphism.
- `X`, `q`, `IsSeparated q`, `LocallyOfFiniteType q`, and `QuasiCompact q` give exactly
  a separated finite type morphism. Finite type is the conjunction of the latter two.
- `r`, `S : Fin r → Type u`, their ring and D-algebra structures, `v` with open-immersion
  instances, `hv`, and `hcover` encode the finite affine open cover over D. This is a
  cover by affine charts with identified coordinate rings, not a closed-immersion cover.
- `s`, `Q`, and `hQ` encode the surjections from polynomial rings on finitely many
  variables, including zero variables. Each `Q j` is a D-algebra homomorphism.
- `pullback q (Spec.map (CommRingCat.ofHom (algebraMap D A)))` is X_A; its first
  projection is pi and its second is q_A. `K : schemeDerivedQCohCategory ...` has
  quasi-coherent cohomology in every integer degree.
- `F`, `hFbounded`, and `hFcoherent` encode bounded coherent cohomology using a common
  finite interval and the recorded `RingedSpace.IsCoherent` predicate. No bound on K
  is added. `γ` is the given arrow into `schemeDerivedDirectImage pi`.
- `vA`, `hvA`, and `hvAcoeff` are the base-changed affine charts. Their two projection
  equations uniquely specify the usual Spec(S_j tensor_D A) map by the pullback
  universal property. They are not arbitrary comparison maps or extra geometric
  conditions on the input: these data always exist for the specified charts.
- `P`, `N`, `eF`, and `eK` express L_j and K_j by module-complex representatives whose
  termwise associated sheaves are the stipulated restrictions. This uses the exact
  termwise-tilde characterization of the recorded affine derived equivalence. P is
  K-flat (`hP`), as allowed by the node's K-flat computation convention. A bounded
  coherent object over Noetherian S_j has a bounded-above projective representative,
  so it can be so represented without restricting the mathematical input.
- `γj` is a chain representative of the local arrow. `hgamma` equates its actual
  derived adjunction transpose (original left-derived counit followed by ordinary
  extension/restriction and tilde/pullback comparison) with the restriction of the
  transpose of the given global γ. The two e-isomorphisms and the canonical commuting
  square comparison appear explicitly. Thus these representatives do not permit
  replacing γ by unrelated arrows. Projective representatives of L_j represent any
  such derived map into the exact restriction of N_j. This is a presentation of
  the node's affine restriction, rather than a new assumption about γ.
- `coefficientCancellationPolynomialCondition` gives the stipulated polynomial cone.
  Q_A is presented as Q_D tensor_D A, canonically A[x] by tensor symmetry and
  `MvPolynomial.algebraTensorAlgEquiv`. The existential T, η, and `IsDerivedBaseChange η`
  encode actual derived extension and its unit. The equation for θ says its transpose
  is the restricted γ_j, hence θ is precisely extension of γ_j followed by the actual
  extension/restriction counit induced by the A-action. The restriction square is
  the already recorded identity-on-elements comparison, not an arbitrary isomorphism.
  A distinguished `Triangle.mk θ ι δ` expresses Cone(θ), independent of cone choice.
  Its final two conditions are H^i=0 for i>n and `Module.Finite Q_A H^n`.
- The conclusion binds E, its commutative ring structure, D-algebra and E-algebra
  structures, `IsScalarTower D E A`, and `Algebra.FiniteType D E`. This is exactly
  a finite type factorization D → E → A; injectivity and flatness are not required.
- The existential pi' has both canonical projection equations, uniquely fixing the
  map X_A → X_E. The second projection of X_E is q'.
- F' and γ' are a sheaf-derived object on X_E and its arrow to R pi'_* K. The next
  two conjuncts give boundedness and coherence of every cohomology sheaf of F'.
- `coefficientCancellationTheta` has source Lq'^*(tilde A[0]) tensor F'. It is defined
  by the original derived adjunction: the original tensor/pullback comparison splits
  the source, the canonical coefficient map acts on the first factor, the transpose
  of γ' acts on the second, and the left unitor gives K. The coefficient map is
  built from the identity on A through tilde/Gamma and the ordinary tensor-pullback
  adjunction, derived counits on degree-zero complexes, and recorded composition.
  The derived unit is definitionally the localized structure sheaf in degree zero.
  This fixes the action in the nonflat case, including identity coefficient maps.
- `C' : schemeDerivedQCohCategory X_E` and the final distinguished triangle express
  that this actual θ' has a quasi-coherent cone. The last condition is H^i(C')=0 for
  every integer i ≥ n. There is no lower-degree claim or map relating F and F'.

The sheaf localization morphism universe w is independent of the scheme/ring universe u.
It is explicitly supplied throughout; no equality w=u is imposed. The ambient
`HasDerivedCategory` binder is the usual framework choice, not a finiteness premise.
Module localizations use the canonical Mathlib instance as the affine cancellation node does.

Dependency declarations read and used:

- Mathlib.RingTheory.Noetherian.Defs: `IsNoetherianRing`; Mathlib.AlgebraicGeometry.Scheme:
  `Scheme`; Mathlib morphism files: `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsOpenImmersion`; Mathlib.Algebra.MvPolynomial.Basic/Eval: `MvPolynomial` and its
  algebra structure; Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`,
  `pullback.fst`, `pullback.snd`; Mathlib.RingTheory.Finiteness.Defs: `Module.Finite`.
- WeilConjectures.AlgebraicGeometry.DerivedCategory: `schemeDerivedCategory`,
  `schemeDerivedQCohCategory`, `schemeDerivedQCohProperty`.
- Sheaf.AlgebraicGeometry.CoherentFiniteType (recorded dependency import) exposes
  WeilConjectures.AlgebraicGeometry.Coherent: `RingedSpace.IsCoherent`.
- WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage: `schemeDerivedDirectImage`;
  WeilConjectures.AlgebraicGeometry.DerivedPullback: `derivedPullback`;
  WeilConjectures.AlgebraicGeometry.DerivedTensorStructure: `schemeDerivedTensorMonoidal`.
- WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence:
  `exists_affineQCohDerivedEquivalence`, including its exact termwise-tilde characterization;
  WeilConjectures.AlgebraicGeometry.AffinePushforwardResolutionQuasiIso:
  `affinePushforward_resolution_quasiIso`, identifying quasi-coherent affine pushforward.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory`, `Q`, `Qh`,
  `singleFunctor`; Mathlib triangulated API: `Triangle.mk`, `distTriang`.
- WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat: `MorphismProperty.kFlat`,
  with its module specialization exposed by ...Abelian.Flat.KFlat.
- Mathlib.AlgebraicGeometry.Modules.Tilde: `tilde`, `tilde.functor`, `tilde.adjunction`,
  `tilde.isoTop`; WeilConjectures.AlgebraicGeometry.DerivedAdjoint:
  `nonempty_derivedPullbackAdjunction`, normalized here with the already published
  `schemeHomOriginalPullbackAdjunction`, `schemeHomPullbackCounitData`, and
  `schemeHomOriginalTensorPullbackIso` from GlobalHomOriginalCounitNormalization.
- DerivedPullbackRecordedComposition: `recordedDerivedPullbackComposition`;
  Modules.PullbackTilde: `pushforwardSpecMapCompΓIso`; TensorPullbackStructureSheaf:
  `tensorPullbackObjUnitToUnit`. These supply canonical maps rather than added hypotheses.
- Sheaf.Algebra.Homology.SingleDegreeCoefficientConeCancellation:
  `coefficientConeRestrictionSquareIso` and `singleDegreeCoefficientConeCancellation`;
  its underlying WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange:
  `IsDerivedBaseChange` and `derivedRestrictScalars`. The theorem is the local proof input;
  the isomorphism and predicate are used literally in the polynomial condition.
- Recorded proof modules are imported for Noetherian coherent/finite-type equivalence,
  affine finite-type generating sections, affine derived pullback/tensor/tilde, and
  module pushforward/open restriction. Noetherian finite-type permanence is the Mathlib
  `Algebra.FiniteType.isNoetherianRing`. The binary patching proof dependency has no
  recorded Lean declaration, so no unavailable module is invented or imported for it.

Sources: read the source paragraph in literature/stacks-project/perfect.tex following
lemma-flat-proper-pseudo-coherent-direct-image-general (Tag 0CSD). It states the Kiehl
finiteness assertion, not this intermediate lemma; the node honestly labels the lemma
agent-formulated and the primary Kiehl descente proof WANTED. Also read the latest blueprint
sk-thm-sf-ctf-stability-direct-images.proof.md. No claim is made that the lemma appears there
verbatim. The complete five-step DAG proof plan is reproduced in the theorem docstring.

Edge cases checked mathematically: r=0 forces X empty by hcover and permits the zero
witness with E=D; zero/redundant charts and zero rings are admitted; s_j=0 is `Fin 0`;
zero F, K, and cones are admitted; n is any integer, including negative n and n=0.
Identity/factorization cases preserve the actual action. No test requires positive r,
nonzero rings, flat D→A, relative pseudo-coherence of K, or vanishing below n.

Searches performed for an existing statement/notion (no global match):

- msearch.py leanfinder: "Global single degree cancellation of finite polynomial coefficient
  obstructions on a separated finite type scheme". Eight hits on polynomial/Chevalley,
  Nullstellensatz and Proj separatedness; none states this assertion.
- msearch.py loogle: `"DerivedCategory", "cone"`. The two hits are
  `DerivedCategory.mappingCocone_triangle_distinguished` and
  `DerivedCategory.mappingCone_triangle_distinguished`, reused as the ordinary cone API.
- msearch.py grep: `coefficient.*(cancel|obstruct)|[Cc]one.*pseudo`. Five hits concern
  Fourier-Motzkin coefficient cancellation and meromorphic trailing coefficients.
- msearch.py leansearch: "Improve a bounded coherent sheaf approximation by one degree
  after finite type extension of coefficients using finite polynomial cone obstructions".
  Hits concern ordinary sheaf cohomology, finite presentations/generators and coherent
  topology; none gives this coefficient cancellation statement.
- rg of WeilConjectures and Sheaf for `single.degree|coefficient.*[Cc]ancell|[Cc]oefficient.*[Cc]one`
  finds the affine cancellation module, not this global theorem. Search for this node id
  in WeilConjectures finds no declaration. Searches for bounded coherent predicates found
  no additional required notion; boundedness and recorded coherence are written inline.
- Further focused source searches found the original-counit normalization, recorded
  composition, tensor unit, and tilde/pullback APIs used instead of duplicating them.

No STATEMENT-DISPUTED flag: no counterexample or source conflict was found. The primary
source limitation above is inherited explicitly from the reviewed node.

## Second reading by Q15

The dispatcher forbids starting other agents, so this is a separate self-reading of the
node and final module, not an independent-agent review. The maintainer's review remains
independent. I checked each clause against the correspondence above, in particular the
strict input bound i>n versus inclusive output i≥n, the polynomial coefficient ring,
the use of the original global γ in hgamma, and the explicit coefficient scalar action.
The initial draft's implicit universe inference chose incompatible localization choices;
explicit scheme localization universe parameters and affine-Q carrier annotations repaired
this without changing the mathematics. The unit comparison now uses the definitionally
recorded unit rather than an expensive reconstruction of its lax-unit isomorphism.
Checked that no theorem other than the item is postponed, no definition contains sorry,
and every helper carries its owning-node source and blueprint docstring.

Validation: prescribed scompile.py compiles the module in isolation against the live
published build. The prescribed deliver2.py --no-push completed successfully: its server
preflight and per-file compilation passed, producing dry-run commit d0700b39ca0.
No warnings remain in the final module.
