## Worker report

Stage 2, NL, 2026-10-22. The delivery states the ordinary whole-system calculation
of lem-trf-sequence-scalar-generator-interchange in
Sheaf.Paper.SequenceScalarGeneratorInterchange.lean. The node changes only in lean.
There are six definitions giving the two routes in each equation, and eleven
named theorems, all with whole proofs `by sorry`. The route definitions have real
data: whiskering and composition of the already recorded natural transformations,
with functor associators/unitors to expose their domains and codomains. They are
helpers of this node, not replacements for a dependency construction.

The previous worker's ending concerned a stage-1 live-wins gate. The live node
is indeed split and independently reviewed by Q99, but has no lean record;
this task is stage 2, and does not re-split or edit that reviewed proof.
There is no repair note for this item and no item-specific return in NL's return file.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Prime ell | `(l : ℕ) [Fact l.Prime]` |
| Finite coefficient extensions E, L, M of Q_l | Explicit types `E L M : Type u`, each with `Field`, `Algebra ℚ_[l]`, and `FiniteDimensional ℚ_[l]` instances |
| E subset L subset M, equality allowed | `ι : E →ₐ[ℚ_[l]] L`, `j : L →ₐ[ℚ_[l]] M`, composite `j.comp ι`; algebra homomorphisms of fields are embeddings and may be identities |
| Valuation rings, chosen uniformizers, positive quotient rings | The dependency's actual `coefficientSequenceCommRingSheaf l F X`, built from `Padic.coefficientExtensionRing l F (n + 1)` and `Padic.coefficientExtensionTransition`; no new ring or uniformizer is chosen |
| Every scheme has ell invertible | Every theorem has `_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x)` and the analogous hypotheses for every other scheme it mentions |
| Small pro-etale ringed sequence site and strict semilinear systems | `coefficientSequenceModules l F X`, the existing module-sheaf category over `coefficientSequenceTopology (Scheme.ProEt.topology X)` |
| Ordinary u_f,F | `integralComparisonSequencePullback l F f`, the actual left adjoint of the specified sectionwise direct image |
| Ordinary s_L/E,X | `(integralComparisonSequenceScalarModel l E L ι X).E`; this is its prescribed ordinary sheafified extension, not the derived functor `.T` |
| Prescribed adjunction-mate compositor c | `integralComparisonSequenceComposition l F h k`, unchanged |
| Prescribed scalar/pullback kappa | `integralComparisonSequenceScalarPullback l E L ι f`, unchanged |
| Prescribed scalar associator alpha | `integralComparisonSequenceScalarComposition l E L ι M j X`, unchanged |
| Multiplication scalar unitor e | `integralComparisonSequenceScalarUnit l E X`, unchanged |
| Geometric equation for Z -> W -> V and every N | `sequenceScalarGeometric_interchange`: equality of `sequenceScalarGeometricLeft` and `sequenceScalarGeometricRight` as natural transformations. The left route is c_E followed by kappa_h followed by u_h,L(kappa_k); the right is kappa_kh followed by c_L. `h ≫ k` is the paper's kh. Evaluating at arbitrary N gives exactly the displayed equation |
| Scalar identity equation for every f | `sequenceScalarUnit_interchange`: left route kappa_E/E then u_f,E(e_Y); right route e_X after u_f,E. Functor unitors give the common target u_f,E |
| Scalar tower equation for every f | `sequenceScalarTower_interchange`: left route s_M/L(kappa_L/E), then kappa_M/L after s_L/E, then u_f,M(alpha_Y); right route alpha_X after u_f,E, then kappa_M/E |
| Equalities of natural transformations of ordinary whole-system functors | Each of the six routes is a natural transformation between functors of the exact `coefficientSequenceModules` categories; the three equality theorems quantify over the transformations, not just their section values |
| Commute with every vertical site restriction and horizontal quotient transition | Every component is an actual `SheafOfModules` morphism on the product sequence site. Its `val.naturality` is precisely the square for every arrow `(n,U) -> (m,V)`. Vertical arrows have identity index map, horizontal arrows have identity site map. Thus both compatibilities are retained in the type, including all composite arrows; no isolated-level model or independent transition is substituted |
| Degreewise application gives equal cochain maps for arbitrary unbounded complexes | The three `sequenceScalar*_interchange_cochain` theorems evaluate `NatTrans.mapHomologicalComplex ... (.up ℤ)` at arbitrary `P : CochainComplex (coefficientSequenceModules ...) ℤ`. These are equal morphisms of complexes, with no boundedness hypothesis. Their components remain module-sheaf morphisms on the sequence site |
| Geometric generator value gamma_h gamma_k(1 tensor x) | `sequenceScalarGeometric_generator`: applies the left route to `integralComparisonSequenceTensorSection ... 1 (integralComparisonSequenceGenerator ... (h ≫ k) ... x)` and gives the iterated generators applied to `1 tensor x`. It explicitly restricts along `MorphismProperty.Over.pullbackComp h k` because the composite and iterated test objects are canonically isomorphic, not definitionally equal. The natural-transformation equality gives the same value for the right route |
| Unit generator value gamma_f(x) on 1 tensor gamma_f(x) | `sequenceScalarUnit_generator`, using exactly `integralComparisonSequenceTensorSection` and `integralComparisonSequenceGenerator` |
| Tower generator value gamma_f(c b tensor x) on c tensor (b tensor gamma_f(x)) | `sequenceScalarTower_generator`: b,c are sections on the source test object, transported by `integralComparisonSequenceRingComponent`; the right side uses `c * (integralComparisonSequenceScalarMap ...).hom.app ... b`, making the inclusion j in cb explicit |
| Equality determined through inverse-image and tensor adjunctions on all local sections | `sequenceScalarPullback_hom_ext` and `sequenceScalarTowerPullback_hom_ext` test arbitrary parallel morphisms into arbitrary target module systems on respectively one and two unit tensors over every n, every U, every source section x |
| No global pure-tensor assertion, no flatness, no derived scalar or realization | No such hypotheses or constructions occur in the signatures. The proof docstrings use adjunction injectivity and sheafification uniqueness, not global generation by pure sections |

Dependency declarations read and used:

- Sheaf.Paper.IntegralComparisonSequenceSystems: all eight ordinary constructions
  named above, `integralComparisonSequenceGenerator`,
  `integralComparisonSequenceTensorSection`, `integralComparisonSequenceRingComponent`,
  and the additive instance for ordinary pullback. Their full signatures,
  defining data, and the generator-normalized existsUnique specifications were read.
- Sheaf.Paper.CoefficientRingedSequenceSite:
  `coefficientSequenceTopology`, `coefficientSequenceCommRingSheaf`,
  `coefficientSequenceModules`; the actual quotient system and transition definitions
  were read. The scheme universe t is independent of coefficient universe u; the
  module universe is max u (t+1), retaining the full small pro-etale site.
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite:
  `Padic.finite_coefficientExtensionRing`, and its imported coefficient constructions
  in Sheaf.NumberTheory.Padics.CoefficientExtension. The full statements and docstrings
  of the actual uniformizer, ideal, quotient and transition were read.
- Mathlib.AlgebraicGeometry.Sites.Proetale: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- Mathlib.Algebra.Homology.HomologicalComplex: `CochainComplex`, its ℤ-indexed
  homological complex and morphisms. Degreewise lifting is
  `NatTrans.mapHomologicalComplex` (Mathlib.Algebra.Homology.Additive).
- def-weil-scheme-morphism-properties is a convention with no declaration; its
  relevant condition here is the explicit stalkwise invertibility hypothesis.
- All already stated proof dependencies are imported without `public`:
  Sheaf.Paper.RingedTopoiTensorSections (`SheafOfModules.RingedTensor.pure` and
  its sectionwise calculus), Mathlib.CategoryTheory.Adjunction.Basic
  (`Adjunction.comp`), Mathlib.CategoryTheory.Adjunction.Mates
  (`unit_conjugateEquiv_symm`), and
  Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
  (`PresheafOfModules.sheafification`, `sheafificationAdjunction`).
  The proof dependency owned by the main sequence-comparison module is already public.

Sources read: the full eight-step node proof; Stacks sites-cohomology.tex,
lemma-derived-pullback-composition (0D6D); sites-modules.tex,
lemma-adjointness-tensor-restrict, lemma-adjoint-pullback-pushforward-modules
(03D7), and section-tensor-product (03EK); and the current main-20261015
prop-trf-karoubi-independence.proof.md final common-stage transport paragraph.
The mixed equations are the node's agent calculation, not a purported verbatim
claim of Stacks. The proof plan is carried by the declaration docstrings:
adjunction tests, pasting-mate unit equation, three generator calculations,
vertical/horizontal restrictions, then degreewise chain maps.

Edge cases checked before writing: E=L=M and identity embeddings; identity h,k,f;
zero N; empty schemes (the invertibility hypothesis is then vacuous as it should be);
first sequence index n=0 (the quotient exponent is 1); arbitrary negative cochain
degrees; ramified/non-flat quotient ring maps. None requires cancellation, a
nonzero coefficient section, a nonempty scheme, positive degree, or a flatness
instance. Functor associators do not alter any comparison or add a coherence choice.

Searches (2026-10-22):

- msearch leanfinder, “Ordinary scalar extension and inverse image of sheaves of
  modules commute with geometric composition scalar units and towers on ringed
  sequence sites”: eight hits, including SheafOfModules.pullbackComp and free
  pullback generator formulas, no exact whole-sequence statement.
- msearch loogle, “SheafOfModules.pullbackComp, ModuleCat.extendScalarsComp”:
  zero hits for the combined query. Read the named declarations directly;
  each treats one comparison, not this three-equation assertion.
- msearch grep, `scalar.*pullback|pullback.*scalar|extendScalarsComp`,
  Algebra/Category/ModuleCat: six hits in Pseudofunctor and ChangeOfRings;
  ordinary module-category scalar composition, not the prescribed sequence-site maps.
- msearch leansearch, “Scalar extension and inverse image of module sheaves satisfy
  compatible geometric composition unit and coefficient tower equations”: eight
  hits, including ModuleCat.extendRestrictScalarsAdj and
  SheafOfModules.sheafificationCompPullback, no exact match.
- rg of lean/WeilConjectures and lean/Sheaf for scalar interchange, sequence scalar,
  and scalar coherence; grep of lean/WeilConjectures for this item id: no existing
  declaration of this item. Read upstream ProEtale.ScalarExtensionCoherence:
  it concerns single-site constant-coefficient ModuleCat sheaves, not the product
  sequence ringed site or the named maps of this item. Read upstream
  ScalarInverseImageCompositionCoherence: it concerns modules on scheme Zariski
  spaces over a field, a different category.
- Read the related node lem-pur-strict-coefficient-comparison-calculus and its
  recorded module's main signature: it is a normalized strict diagram tensor
  comparison construction with scalar unit/tower laws. It neither identifies the
  prescribed sequence-site maps here nor states the mixed geometric compositor
  equation. Its advisory mention in Q99's review therefore does not give an exact
  existing match for this item.

No new DAG node, dependency replacement, statement correction or
STATEMENT-DISPUTED finding. Every variable and universe is explicitly bound;
there are no file-local notations, private copies of notions, axioms, or proofs.
The sheafification instance exclusions and transparency settings follow the
owning sequence-comparison dependency, without additional assumptions.

Validation: scompile.py compiled the final single module in sandbox mode and at
its library module name, cleanly (8.6 and 7.9 seconds). Only the prescribed
per-file wrapper was used. deliver2.py --no-push passed the server preflight and
per-file compile (dry-run commit 236febfcf15).

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
