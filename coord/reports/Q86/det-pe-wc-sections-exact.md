## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleWContractibleSectionsExact` states
`AlgebraicGeometry.Scheme.ProEt.wContractible_sections_exact`, with its proof `sorry`.
It states both cases of the node: evaluation on abelian sheaves and evaluation on
sheaves of modules over an arbitrary sheaf of rings preserve finite limits and
finite colimits. These are the usual exactness assertions for these additive
functors between abelian categories. No node correction or new definition is needed.

Hypotheses and clauses, checked against the node and its current blueprint source:

- The ambient scheme is `(X : Scheme.{t})`.
- `U = Spec D` is represented directly by the source of
  `(f : Spec (CommRingCat.of D) ⟶ X)`. Consequently no affine chart, chosen
  coordinate-ring isomorphism, or extra affine hypothesis is needed.
- `(D : Type t) [CommRing D] [IsWContractibleRing D]` is exactly the stated
  w-contractible commutative ring, using the recorded upstream class.
- `[WeaklyEtale f]` makes `ProEt.mk f` an object of `X.ProEt`, the recorded
  small pro-etale site. The topology is `AlgebraicGeometry.Scheme.ProEt.topology X`.
- `(R : Sheaf (topology X) RingCat.{u})` is the arbitrary sheaf of rings;
  commutativity of the coefficient rings is not assumed.
- The abelian evaluation functor is
  `(sheafSections (topology X) AddCommGrpCat.{max v (t + 1)}).obj
  (op (ProEt.mk f))`. Its object map is precisely `F ↦ F(U)` and its
  morphism map is the component at `U`, by the definition of `sheafSections`.
- The first and second conjuncts assert `PreservesFiniteLimits` and
  `PreservesFiniteColimits` for that abelian evaluation functor.
- The module evaluation functor is
  `SheafOfModules.evaluation.{max v (t + 1)} R (op (ProEt.mk f))`.
  Its domain is definitionally `ringedSiteModules R` and its codomain is
  `ModuleCat (R.obj.obj (op (ProEt.mk f)))`, exactly the `R(U)`-modules.
  Its morphisms are the `R(U)`-linear component maps.
- The third and fourth conjuncts assert preservation of finite limits and
  finite colimits for that module evaluation functor.
- The section universe `max v (t + 1)` contains the site; `v` is arbitrary.
  This is the size convention of the dependency records. The independent
  coefficient-ring universe `u` is unrestricted. There is no equality imposed
  between the site's object universe `t + 1` and morphism universe `t`.

Dependency declarations read and used:

- `def-weil-pbc-small-proetale-site`: Mathlib module
  `Mathlib.AlgebraicGeometry.Sites.Proetale`, declarations
  `AlgebraicGeometry.Scheme.ProEt`, `ProEt.mk`, and `ProEt.topology`.
- `sk-def-pe-wlocal`: `WeilConjectures.RingTheory.ProEtale.WContractible`,
  `IsWContractibleRing`; its inherited `IsWStrictlyLocalRing` and `IsWLocalRing`
  in `WeilConjectures.RingTheory.ProEtale.WLocal`, and `WLocalSpace` in
  `WeilConjectures.Topology.SpectralSpace.WLocal.Basic` were read as well.
  This is the specified connected-component/extremal-disconnectedness condition,
  not an assumed section-surjectivity condition.
- `def-weil-pbc-sites-and-cohomology`:
  `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`. Its documented remaining
  interfaces are Mathlib's `Sheaf` and `sheafSections`; the latter is used here.
- `def-weil-sheaf-of-modules-category`:
  `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
  This abbreviation is exactly `SheafOfModules`; evaluation uses Mathlib's
  functor on that category without a second definition or abelian instance.
- The already stated proof dependency
  `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`,
  `CategoryTheory.moduleSheaves_colimits_forgetful`, is imported privately.
  Its current published source was read with `scompile.py --source`, because
  this upstream module is absent in the older local source checkout.
- The Mathlib proof interfaces are imported through the dependency modules and
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`,
  `Mathlib.CategoryTheory.Sites.EpiMono`, and
  `Mathlib.CategoryTheory.Sites.LocallySurjective`. Their relevant declarations
  are `SheafOfModules.evaluationPreservesLimitsOfSize`,
  `SheafOfModules.Finite.evaluationPreservesFiniteLimits`,
  `CategoryTheory.Sheaf.isLocallySurjective_iff_epi'`,
  `CategoryTheory.Sheaf.isLocallySurjective_iff_epi`, and the finite-limit
  preservation instances for sheaf inclusion and sheafification.
- `det-pe-wcb-projective` has no published Lean record in the supplied DAG;
  it is only a proof dependency, not needed to type this statement. Its use in
  the proof is preserved in the declaration docstring. No other node is restated.

Edge cases checked before writing:

- The zero ring `D` is allowed: no `Nontrivial D` or nonempty-spectrum
  assumption is added. For its empty affine, sections of an abelian or module
  sheaf are zero, so exactness is consistent.
- The base scheme may be empty. The statement requires only the indicated
  weakly etale map, and does not assume connectedness, qcqs of the base, or
  nonemptiness.
- Arbitrary characteristic and noncommutative coefficient-ring sheaves are allowed.
- Zero sheaves and zero ring sheaves are allowed. Preservation of finite
  limits/colimits includes the empty finite diagrams and hence both endpoints
  of a short exact sequence. Exactness at the middle alone is not substituted.
- The affine source is automatically quasi-compact; no additional finiteness or
  arbitrary section-surjectivity hypothesis is introduced.

Searches (2026-10-17):

- `msearch.py leanfinder`, query "Evaluation of abelian sheaves and sheaves of
  modules at a w-contractible affine of the pro-etale site is exact": eight
  hits, including Mayer-Vietoris exactness and `SheafOfModules.instAbelian`,
  but no exact match.
- `msearch.py loogle`, query
  `SheafOfModules.evaluation, PreservesFiniteColimits`: zero hits; the service
  reports unknown identifier `PreservesFiniteColimits`. This is a search-index
  limitation; the identifier exists in the compiled library.
- `msearch.py grep`, query
  `IsWContractible|evaluationPreservesFiniteLimits|def sheafSections`: two hits,
  the existing module-evaluation finite-limit instance and the sheaf-evaluation
  comparison, neither the geometric exactness assertion.
- `msearch.py leansearch`, query "Sections of abelian sheaves over a projective
  object of a site form an exact functor": eight hits, including
  `CategoryTheory.sheafSections`, `SheafOfModules.sectionsFunctor`, and
  `CategoryTheory.sheafIsAbelian`; no theorem with this node's hypotheses.
- Direct `rg` of Mathlib, the project's `lean/Sheaf`, the source repository,
  and the upstream name index for `IsWContractibleRing`, evaluation/exactness
  patterns, and the proposed declaration name found no existing exact match.
  The source repository's `IsWContractibleRing` occurrences are confined to
  the ring-theoretic construction module.
- Direct search for the node id in the source repository found no declaration.
  Project hits in `ProEtaleProductsExact` and `IntegralLisseReductionEquivalence`
  are proof-docstring citations. The existing
  `ProEtaleWeaklyContractibleEvaluationColimits` theorem was read in full:
  it instead assumes section-surjectivity for every set-sheaf epimorphism and
  restricts coefficients to commutative ring sheaves. It is not this statement.

The theorem docstring carries all five proof steps from the node, including
the two local-surjectivity criteria and clause 2 of `det-pe-wcb-projective`.
There are no statement disputes or interface repairs.

Validation: the delivered file passed `scompile.py Q86 det-pe-wc-sections-exact`
as both a sandbox module (2.1 seconds) and its declared library module (1.9 seconds),
without errors or warnings. No proof was supplied.

## Second reading by Q86

I independently read the sandbox node and module against the blueprint statement
and proof at main-20261015/sec-proetale-coefficients/sk-cor-pe-wc-sections/
det-pe-wc-sections-exact.{md,proof.md}. The statement is unchanged from that
source. I also read the supporting Stacks text: sites-modules.tex,
lemma-abelian-abelian (03CN), lemma-limits-colimits-abelian-sheaves (03CO),
lemma-abelian (03DA), lemma-limits-colimits (03DB); sites.tex,
definition-sheaves-injective-surjective (00WM) and lemma-mono-epi-sheaves
(00WN). These assume a site and a sheaf of rings, with no Noetherian,
connectedness, nonzero-ring, or characteristic hypothesis. In proetale.tex I
checked definition-w-contractible and its equivalent w-local/strictly-henselian/
extremally-disconnected criterion, and lemma-w-contractible-is-weakly-contractible.

My itemized statement inventory and comparison follows. Each item passes.

1. Ambient scheme X and its small pro-etale site: `(X : Scheme.{t})`,
   `topology X`, and `ProEt.mk f`. The dependency
   def-weil-pbc-small-proetale-site records Mathlib's
   `AlgebraicGeometry.Scheme.ProEt`. I read Sites/Proetale.lean: its objects
   are weakly etale schemes over X, `mk` bundles the given map, and its topology
   is generated by the pulled-back pro-etale precoverage. This is the node's
   small site, not the big site or the etale site.
2. Affine object U = Spec D: `(D : Type t) [CommRing D]` and
   `(f : Spec (CommRingCat.of D) ⟶ X) [WeaklyEtale f]`. Evaluation is at
   `op (ProEt.mk f)`, whose underlying scheme is this exact affine. Sharing
   the scheme universe is the small-site convention, not an additional
   finiteness restriction. No surjectivity or quasi-compactness of f is assumed.
3. W-contractibility of D: `[IsWContractibleRing D]`. I opened the recorded
   declaration in WeilConjectures/RingTheory/ProEtale/WContractible.lean,
   and its inherited classes in WLocal.lean and
   Topology/SpectralSpace/WLocal/Basic.lean. `IsWContractibleRing` extends
   `IsWStrictlyLocalRing` and requires
   `ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum D))`.
   The inherited fields require a w-local spectrum and strictly henselian
   localizations at maximal ideals. WLocalSpace includes spectrality,
   uniqueness of closed specializations and closedness of the closed points.
   These are exactly sk-def-pe-wlocal's definitions; the hypothesis is not an
   assumed conclusion about sections or epimorphisms.
4. Arbitrary ring sheaf R: `(R : Sheaf (topology X) RingCat.{u})`. Coefficients
   may be noncommutative and their universe u is independent. No field,
   constant-ring, constructibility or finiteness condition is added.
5. Abelian-sheaf sections functor: the source of
   `(sheafSections (topology X) AddCommGrpCat.{max v (t + 1)}).obj
   (op (ProEt.mk f))` is precisely abelian sheaves and the target is abelian
   groups. I read Mathlib Sites/Sheaf.lean: `sheafSections` is the flipped
   inclusion into presheaves, so both its object map F(U) and its morphism
   map phi_U are the required evaluation. I read the sites-and-cohomology
   dependency module too; its site-axiom repair retains these Mathlib
   sheaf and sections interfaces.
6. Exactness in the abelian case: the first two conjuncts are
   `PreservesFiniteLimits` and `PreservesFiniteColimits` of that same functor.
   Evaluation is additive by componentwise addition. For additive functors
   between abelian categories this is equivalent to preserving short exact
   sequences, including both endpoint conditions. It adds no infinite-colimit
   assertion and does not merely assert exactness at the middle term.
7. Module-sheaf sections functor:
   `SheafOfModules.evaluation.{max v (t + 1)} R (op (ProEt.mk f))`.
   I opened the recorded RingedSiteModules module: `ringedSiteModules` is
   transparently `SheafOfModules`, so the domain uses the dependency's exact
   category. I read Mathlib ModuleCat/Sheaf.lean: objects are module presheaves
   with sheaf underlying abelian presheaves, morphisms are module-presheaf
   morphisms, and evaluation is the forgetful functor followed by module
   evaluation. Thus the codomain is exactly
   `ModuleCat (R.obj.obj (op (ProEt.mk f)))`, with R(U)-linear component maps.
8. Exactness in the module case: the third and fourth conjuncts are
   `PreservesFiniteLimits` and `PreservesFiniteColimits` of this evaluation.
   They express exactly the second case of the node. There is no replacement
   by underlying-set surjectivity, and the coefficient action is retained.
9. Quantifiers and sizes: t, u, v are explicitly bound; X, D, f and R are
   universally quantified in the source order. The section universe is
   `max v (t + 1)`, the dependency's small-site size convention with arbitrary
   enlargement v. The site's object universe t+1 and morphism universe t
   are not forced equal. No unbound auto-implicit variable is present.

Edge cases: D may be the zero ring, U may be empty, and X may be empty;
there is no Nontrivial or Nonempty binder. The empty affine is covered by
its empty covering family, so sections there are zero in both categories.
The zero sheaf and a zero coefficient-ring sheaf are allowed. Finite limit
and colimit preservation includes empty diagrams and hence the zero objects,
as well as kernels and cokernels. No index set or degree n occurs in this
statement, so no n = 0 or nonempty-index case is silently removed. Rings of
all characteristics are included. Affineness supplies the quasi-compactness
of U that the geometric projectivity proof needs; the base need not be qcqs.

Independent searches, with wording different from the first worker:

- `msearch.py leanfinder`, "Global sections at a weakly contractible proetale
  affine preserve cokernels of module sheaves": eight hits, all module
  presentation/generating-section tools, not this theorem.
- `msearch.py loogle`, `CategoryTheory.sheafSections`: twelve hits, including
  the definition, its evaluation isomorphism and constant-sheaf adjunctions;
  none asserts this geometric exactness statement.
- `msearch.py leansearch`, "Taking sections of abelian sheaves on a weakly
  contractible object preserves short exact sequences": eight hits, including
  sheafSections, sectionsFunctor, sheafIsAbelian, Mayer-Vietoris and concrete
  short-complex exactness. No exact match.
- Direct `rg` in Mathlib, upstream WeilConjectures, and project lean/Sheaf
  for wcontractible, contractible near exact/cokernel, and the proposed full
  name found no duplicate. The upstream name index has no match. I inspected
  the relevant project candidates rather than relying on names:
  `affine_weaklyContractible_evaluation_colimits` assumes section-surjectivity
  and has only commutative coefficients;
  `weaklyContractible_evaluation_preservesHomology` (read via
  `scompile.py --source`) has the same extra hypothesis and coefficient
  restriction. `properHeartContinuitySections` assumes categorical weak
  contractibility and evaluates into underlying abelian groups; it does not
  supply either the ring-geometric hypothesis or both exact functors here.
  PointProEtaleSectionsExact concerns an algebraically closed field point.
  WContractibleAffineEvaluation supplies a set-section surjectivity tool,
  not the claimed additive exactness theorem. Therefore this module is needed.

I checked every recorded statement dependency's node and the actual
signatures above, and the proof interfaces in Mathlib's module-sheaf limits,
EpiMono and LocallySurjective modules. The existing proof dependency
`CategoryTheory.moduleSheaves_colimits_forgetful` was read from its current
published WeilConjectures module using `scompile.py --source`: its exact
forgetful functor applies with arbitrary ring sheaves and independent
coefficient/module universes. The item imports it privately, as required.
The other already available proof interfaces are Mathlib imports.
`det-pe-wcb-projective` is a proof-only dependency without a Lean record;
its clause 2 is accurately retained in the proof plan and is not needed to
form the statement. No missing definition or unusable recorded dependency
requires another module or node. No maintenance repair note exists for this item.

The declaration docstring reproduces all five DAG proof steps: sectionwise
kernels/additivity; forgetting module actions preserves epimorphisms; the
abelian and set local-surjectivity criteria; clause 2 of geometric projectivity;
and preservation of an arbitrary short exact sequence. The module and theorem
both carry the source and `(blueprint: det-pe-wc-sections-exact)`. There is
one theorem, with proof `sorry`, and no new definition, private copy, local
notation/instance, proof, hollow data or additional axiom.

Mismatches found: none. I left the Lean file and node unchanged and appended
this independent reading. No statement correction or citer audit is needed.
A direct comparison confirms that only the node's lean field differs from the
base, and lean.statement equals the file signature verbatim. All Lean lines
are at most 100 characters. The prescribed scompile.py check passed both the
sandbox module (1.5 seconds) and declared library module (1.7 seconds), with
no errors or warnings.
