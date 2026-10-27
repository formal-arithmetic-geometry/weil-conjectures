## Worker report

This stage-2 delivery states the accepted stage-1 node without changing its statement,
proof, or accepted split. The previous unchanged-item stage-1 refusal does not apply:
coord/brief-stage2.md section 0 explicitly permits the stage-2 statement of this reviewed
node, whose live Lean record was absent. There is no released repair note for the item.

The main module is Sheaf.TraceFormula.GradedEvaluationZariskiEtaleComparison. The complete
statement has three named clauses: graded_evaluation_zariski_etale,
graded_evaluation_ordinary_scheme, and graded_evaluation_line_powers. Its additional
declarations construct the actual site restrictions, their tensor adjunction, canonical
mate, counits, coproduct descents, and transported tensor powers. Every theorem proof is
sorry. Definitions have real data; there is no choice of an arbitrary comparison map.
evaluationContext contains only continuity and adjoint-existence proof data.

Hypotheses and conclusions of the node correspond as follows.

- S is the explicitly bound Scheme.{u}; T : Over S retains its S-structure; X :
  AlgebraicSpace S and f : X ⟶ schemeSpace T retain the morphism over S and the specified
  representable target. No independent small coefficient universe or equality of site
  object and Hom universes is imposed.
- Quasi-compactness and separatedness are exactly IsQuasiCompactPresheafMap f.hom.hom and
  IsSeparatedPresheafMap f.hom.hom, the recorded predicates. B : ℕ → X.Modules is arbitrary;
  _hB asserts the recorded IsQuasicoherent predicate in every degree, including zero.
- BG : EtaleGradedModuleAlgebra B supplies additive maps with both scalar-linearity laws,
  all chart restrictions, associativity, ordinary commutativity and both unit laws. The
  existing GradedSheafAlgebra is retained for the Zariski family; it cannot itself accept
  module sheaves on an algebraic-space site. The new definition node fills this precise gap.
- evaluationDegree T f B d is literally evaluationZariskiRestriction T applied to the
  fixed moduleDirectImage f of B d. The restriction first includes the ordinary scheme
  etale charts, then the actual open subschemes, with the existing regular-function ring
  map. It is not a new arbitrary family. The first conclusion makes these degrees
  quasi-coherent and makes the extension/restriction counit invertible, giving the
  specified identification (A_d)_et ≅ f_*B_d.
- AG supplies all the Zariski homogeneous products and unit. CG supplies the products on
  the actual direct images. The next two conjuncts require their chart projections to
  be the products of the original sections and the original unit after moduleChartScalar.
  The following two conjuncts identify AG's products and unit with CG on the actual
  open chart. These fix the graded structure, not just the underlying degrees.
- evaluationCounit is exactly moduleTensorAdjunction.counit. The Hom ev has degree maps
  equal to these counits. Its Hom.mul and Hom.unit fields express preservation of all
  products and the degree-zero unit. The explicit local evaluation conjunct is
  ev_d(moduleTensorSection f (f_*B_d) V q a s) = a times the chart projection of s.
  The projection is coerced to the actual B_d chart module, retaining its scalar action.
- PG supplies the tensor-pulled-back graded structure. Its product is explicitly normalized
  on every pair of local tensors to moduleTensorSection with coefficient a*b and CG's
  product of s,t. Its unit is the chart tensor 1 tensor 1_B. Together with Hom.mul and
  the local counit formula this is precisely epsilon((a tensor s)(b tensor t)) =
  ab (st)|_W = (a s|_W)(b t|_W). Separate scalar laws and additivity extend this from
  representatives; no global section is assumed to be a pure tensor.
- The cofans c,b,p are actual sheaf coproduct presentations, each with IsColimit.
  evaluationPullbackCofan applies the actual tensor pullback to each injection. Its
  IsColimit and the injection-normalized isomorphism e are the canonical coproduct
  comparison. evaluationTotal is IsColimit.desc of the degree counits followed by the
  target injections; the displayed equations determine it on every summand. The
  additional cofan z and normalized q identify the total of (A_d)_et with c and require
  the total evaluation there to restrict to evaluationFromZariski on every summand.
  Thus the statement uses sheaf coproducts throughout, and asserts no false equality
  between infinite direct sums and sections on each open. Product preservation on
  homogeneous pairs is exactly the graded-algebra homomorphism condition on these totals.
- In graded_evaluation_ordinary_scheme, U,T : Over S and a : U ⟶ T are arbitrary scheme
  data, with the stated qc and separated hypotheses. H_d are arbitrary quasi-coherent
  Zariski modules with HG : GradedSheafAlgebra H; B_d, BG, and e_d specify exactly the
  given identifications B_d ≅ (H_d)_et. _hmul and _hunit spell out transport of the
  homogeneous products and unit on every open via the actual extension/restriction unit.
- The natural isomorphism r identifies R_T f_et,* with f_* R_U for EVERY etale module.
  Its section equation is exactly the chart projection to a^{-1}W, constructed by
  evaluationOpenChart. That projection identifies compatible sections with the same
  section on the inverse-image open; it is the identity-on-open-sections comparison.
- The j_n have hom equal to the actual Zariski/etale unit. The d_n identify A_n with
  ordinary pushforward of H_n, with hom explicitly fixed as R(f_*e_n^{-1}), then r,
  then f_*j_n^{-1}. The next two identities identify every homogeneous product and
  unit under d_n, with the prescribed regular-function pullback a.left.app W.
- evaluationPullbackComparison is constructed by leftAdjointUniq from the given r and
  the specified adjunctions. The following equality identifies the actual etale counit
  from (A_n)_et with the ordinary tensorPullbackSectionAdjunction counit, transported
  by this canonical mate, d_n and e_n. It is not a freely chosen natural isomorphism.
- The last universal clause of the scheme theorem supplies arbitrary coproduct
  presentations and their normalized comparisons q,x,y. It asserts equality of the
  total etale evaluation and extension of evaluationOrdinaryTotal under exactly these
  comparisons. Both total evaluations are real descents of the specified counits.
- graded_evaluation_line_powers takes precisely a line module L on schemeSpace U.
  It returns an ordinary H with H.IsInvertible and its extension identification i.
  evaluationLinePower is the actual sheaf tensor power, computed on the existing
  SmallEtaleModel and transported through its fixed module equivalence; it uses the
  existing monoidalCategory and tensorPowNat, with structure module in degree zero.
- The isomorphisms e_n identify extension of H.tensorPow n with those powers of L.
  evaluationPowerComparison uses the counit of the actual small-module equivalence.
  The degree-one equation normalizes these maps to i using the right unitors. The
  product equation identifies the canonical tensor-power products on every affine
  chart over every open, using tensorPowAddIso, the recursively explicit unitors and
  associators in evaluationPowerAddIso, and actual sheafification pure tensors.
  The degree-zero equation is the pullback of regular functions, so includes the unit
  and both products involving the zeroth power. The final restriction isomorphism
  identifies the corresponding ordinary H_n with H.tensorPow n.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme, Scheme.Hom and Over S.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicSpace, EtaleSite, etaleForget,
  structureSheaf, Modules, IsLineModule; Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite:
  schemeSpace. Scheme tests use representable_etale_scheme_tests in
  Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations: ModuleChart,
  moduleDirectImageModel and its projection, moduleDirectImage, moduleTensorPullback,
  moduleTensorAdjunction, moduleTensorSection, and moduleChartScalar.
- Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal: IsQuasiCompactPresheafMap and
  IsSeparatedPresheafMap (imported through the recorded Zariski/etale module).
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: QCoh and the slice
  sheafification instances for the same Mathlib SheafOfModules.IsQuasicoherent predicate.
- Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence:
  SmallEtaleModules, ZariskiEtaleModuleContext, its restriction/extension/adjunction,
  scheme_zariski_etale_quasiCoherent_equivalence. The contexts contain proof data only.
- WeilConjectures.AlgebraicGeometry.GradedSheafStructures: GradedSheafAlgebra.
- Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction: tensorPullbackSectionAdjunction;
  its public upstream TensorPullback supplies the actual functor tensorPullback.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible: IsInvertible, tensorPow and
  tensorPowAddIso; Modules.TensorSection supplies tmulSection and unitSectionsEquiv.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel (the additionally cited existing
  definition def-sfb-space-small-ringed-model): SmallEtaleModel, smallStructureSheaf,
  smallModuleRestriction, smallModuleEquivalence. The object universe remains u+1 and
  Hom/section universe u; evaluationPowerAddIso binds these universes independently.
- WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal, the recorded tensor API
  imported via Modules.Invertible: monoidalCategory and tensorObjIsoSheafification.
  TensorProductOfUniverses/SiteTensorFunctoriality and their original tensor APIs are
  reused through the existing module operations; no new tensor product is defined.
  WeilConjectures.CategoryTheory.Monoidal.TensorInverse supplies tensorPowNat.
- The stated proof dependencies TensorClosed.tensorClosed, TensorBilinearUniversal.
  tensor_bilinear_universal, RingedTopoiTensorComparisonConstruction.
  canonicalRingedTensorComparison_nonempty, RingedTopoiTensorComparisonData.
  CanonicalRingedTensorComparison, and TensorPullbackAdjunction.
  exists_tensorPullbackAdjunction are imported for stage 3. The three proof dependencies
  graded-qc-section-algebra-construction, space-chart-adjunction-tensor-realization,
  and zariski-etale-functor-comparison-square have no recorded Lean declaration in the
  inspected base; no import is invented for them. Their intended properties needed to
  STATE this item are expressed by the actual constructions and explicit equations above.

Edge cases checked: empty X or T (including an empty scheme source), empty chart/open,
zero module in any degree and the zero graded algebra, degrees m=0, n=0, and d=0,
identity scheme morphism, arbitrary qc separated scheme morphism, and a trivial line
module. Coproducts are indexed by all natural numbers; no finite generation or nonzero
condition occurs. Bilinearity and HEq degree transports impose ordinary commutativity,
not Koszul signs. The canonical maps are normalized, and no arbitrary choice of a
Nonempty comparison or extra monoidal structure is a theorem hypothesis.

Searches (real msearch.py calls; searches.jsonl retained):

- leanfinder: "The counits of tensor pullback and module pushforward assemble to graded
  algebra evaluation and agree under the Zariski etale comparison": eight unrelated
  scheme pullback/Proj facts; no statement of this node.
- loogle: "Adjunction.counit, SheafOfModules.pullback": no hits; unknown short identifier.
- grep: "graded.*evaluation|evaluation.*graded" in Mathlib AlgebraicGeometry: no hits.
- leansearch: "commutative graded algebra sheaves of modules on a site": eight hits,
  including SheafOfModules, GradedAlgebra, and DirectSum.GAlgebra.commutes; none provides
  the restriction-compatible homogeneous algebra on the small etale site.
- loogle: "CategoryTheory.GradedObject": twelve hits for graded objects, their maps,
  and total coproduct, but not homogeneous multiplication and algebra laws.
- grep: "structure.*Graded.*Algebra|Graded.*Sheaf" in Mathlib Algebra: only an unrelated
  ZMod algebra comment. rg of lean/WeilConjectures and lean/Sheaf found the existing
  Zariski GradedSheafAlgebra and scheme-test line maps; neither accepts this node's
  arbitrary etale B_d. rg of the item id in WeilConjectures found no attachment.
- DAG concept searches: blueprint_refs.py search graded, and rg in dag/nodes, found
  the scheme graded structures and this item's unformalized section-algebra proof
  dependency. No separate definition of the small-etale homogeneous operations exists.

Sources opened: spaces-descent.tex lemma-descending-property-ample, its graded algebra,
psi_d and psi paragraph; spaces-morphisms.tex the representable pushforward discussion
before lemma-pushforward; descent.tex proposition-equivalence-quasi-coherent-functorial
(1),(3); sites-modules.tex lemma-adjoint-pullback-pushforward-modules. No statement
correction is made and no STATEMENT-DISPUTED issue was found.

## New nodes

**def-trf-etale-graded-module-algebra.** This definition gives homogeneous commutative
unital algebra operations and homogeneous morphisms for B : ℕ → X.Modules on the small
etale site of an algebraic space. It uses existing module sheaves and sheaf coproducts.
It is the precise site counterpart of the existing Zariski GradedSheafAlgebra, which is
retained unchanged. The source is the graded algebra and map in Stacks 0D3C and the
bilinear tensor universal property of Section 03EK. The LeanSearch, Loogle, Mathlib grep,
project grep and DAG searches above found general ingredients only. This is a missing
notion under section 1(A), not a replacement of an existing usable declaration.

## Second reading by NK

No independent worker was started: the dispatcher explicitly prohibits other agents.
The maintainer's independent delivery review is the second reading, as provided by the
current direct-delivery workflow. A final self-check matched every hypothesis and clause
above, checked that the actual units fix the comparison maps, and checked zero and empty
cases. During elaboration the nested-linear-map form on the RingCat presentation was
replaced by the equivalent additive maps with two explicit scalar laws. An independent
Hom universe was added to the generic tensor-power concatenation interface so that the
small affine module category is not forced to have equal object and Hom universes.
