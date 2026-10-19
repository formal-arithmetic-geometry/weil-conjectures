## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.PerfectCategoricalTrace` defines the
scalar-valued categorical trace, with its internal-Hom dual, evaluation, coevaluation,
Koszul braiding and degree-zero scalar identification. The main declaration is
`WeilConjectures.finiteCoefficientCategoricalTrace`; the ring-general declaration is
`DerivedCategory.perfectCategoricalTrace`. Every new declaration is a definition with
real data. There are no new theorems, axioms or postponed proofs. The node copy changes
only `lean`.

The prior worker's BLOCKED note concerned the already merged stage-1 split. It is not
an existing stage-2 implementation: the current node has no `lean` record. The retained
sandbox contained dispatcher brief markers only. This delivery preserves the reviewed
stage-1 statement and all its dependency lists.

Source read: the exact blueprint node, order 1826, read on the project server because
its untracked literature tree is not present in the local shared source mirror; also
the containing unit record and the current expanded DAG statement. The source defines
the intrinsic duality maps and their trace; the DAG spells out their projective-model
normalization. No statement correction is made.

Hypothesis and clause correspondence:

1. The global finite-field datum is the binder `D : FiniteFieldDatum`. This is the
   recorded `WeilConjectures.FiniteFieldDatum`, including the prime `p`, positive
   exponent, cardinality, base field and fixed algebraic closure. The binder
   `c : D.CoefficientDatum` supplies the prime `c.l`, its primality, `c.l ≠ D.p`,
   and the fixed algebraic closure `c.Qbar` of `Padic c.l`.
2. A finite extension contained in that fixed closure is
   `E : IntermediateField (Padic c.l) c.Qbar` with
   `[FiniteDimensional (Padic c.l) E]`. These are exactly the embedded finite
   extensions in the node. `n : ℕ` and `_hn : 1 ≤ n` retain the positive-level
   hypothesis. The valuation ring, uniformizer and quotient are the already
   recorded `Padic.coefficientExtensionIntegers`,
   `Padic.coefficientExtensionUniformizer`, and
   `Padic.coefficientExtensionRing c.l E n`. No new coefficient-ring definition
   is introduced.
3. `P : DerivedCategory (ModuleCat.{u} A)` is an object of the derived category of
   ordinary modules over exactly that quotient `A`. The localization is the existing
   `DerivedCategory.Q`. `v : P ⟶ P` is an arbitrary derived endomorphism, not an
   unquotiented chain endomorphism or an invertible endomorphism.
4. `hP : DerivedCategory.IsPerfectRingComplex P` uses the recorded predicate without
   copying it. `perfectTraceCategory` is its `ObjectProperty.FullSubcategory` in the
   derived category. Thus morphisms are derived morphisms and all perfect objects
   are admitted. This does not identify perfectness with `pointFiniteCohomology`.
5. `perfectTraceModelDual B` is literally the recorded
   `CochainComplex.moduleHomComplex B (singleFunctor.obj (ModuleCat.of R R))`.
   Its terms are the total homogeneous cochains, and its differential is the existing
   `HomComplex.δ_hom`: specializing its target to degree zero gives precisely the
   dual-degree reversal and `(-1)^(j+1)` differential in the node. No new Hom complex
   is substituted.
6. The tensor in the new definitions is the upstream K-flat derived tensor on
   `DerivedCategory (ModuleCat R)`, not an assumed arbitrary monoidal structure.
   Its representative tensor is the recorded `CochainComplex.mapBifunctor` with
   `curriedTensor (ModuleCat R)`: the signed direct-sum total tensor of ordinary
   modules. Ordinary modules are precisely the specialization to the terminal site
   described in the node. There is no change of coefficient category.
7. `perfectTraceCanonicalBraiding` applies the actual construction
   `DerivedMonoidal.braidedCategory Qh (HomotopyCategory.quasiIso _ (.up ℤ))`.
   This descends the Koszul symmetry of the homotopy category. It is not a choice
   from `nonempty_braidedCategory`, or a free braiding hypothesis. The small generic
   wrapper caches that construction before specializing to modules, avoiding the
   expensive reconciliation of monoidal structure instances inside concrete types.
8. For the existing `ModuleCat.StrictPerfectCoefficientPackage B`, the helpers
   `perfectTraceFrameVector s i a` and `perfectTraceFrameFunctional s i a` are
   literally `(s.p i).hom (Pi.single a 1)` and
   `(LinearMap.proj a).comp (s.i i).hom`. Thus they are the specified `e_{i,a}`
   and `epsilon_{i,a}` and retain the package's degreewise splitting relation.
9. `perfectTraceDual P = (ihom P).obj (𝟙_ _)` is the actual derived internal Hom
   into `R[0]`. `perfectTraceDualMap f = (MonoidalClosed.pre f).app (𝟙_ _)`
   gives the contravariance used for `alpha^vee`. In particular an isomorphism
   `alpha : Q(B) ≅ P` induces the map from `P^vee` to the dual of `Q(B)` in the
   direction required by the node.
10. `perfectTraceEvaluation P` is the canonical signed symmetry followed by the
    internal-Hom evaluation counit, with domain `P^vee ⊗ P`. On the total-Hom
    projective representative this is `phi ⊗ x ↦ phi(x)`, and the target single
    complex is zero in all other total degrees. The symmetry is necessary because
    the upstream closed structure writes its counit in the order `P ⊗ RHom(P,R)`.
11. `perfectTraceCoevaluation P hP` is
    `MonoidalClosed.coevaluationOfIsIso P` followed by the inverse symmetry putting
    `P` first. The upstream definition is
    `curry (ρ_ P).hom ≫ inv (ihomUnitTensorToIhom P P)`.
    Its inverse is justified by the existing
    `DerivedCategory.IsPerfect.isIso_ihomUnitTensorToIhom hP P`; at localization
    universe `u` the recorded perfect predicate is definitionally the predicate
    accepted by this upstream theorem. Thus the construction is the unique inverse
    image of the identity, not a bare existence choice or an arbitrary map.
    On the strict projective model the inverse sends the identity to
    `sum_{i,a} e_{i,a} tensor epsilon_{i,a}`. The finite-frame decomposition of the
    identity shows why this is the very same map specified in the node. Bounds
    and the stipulated rank zero on zero terms make that model sum finite.
12. The representative transport formulas are the intrinsic maps above expressed
    through `alpha` and its contravariant derived dual: coevaluation transports by
    `alpha tensor (alpha^vee)^(-1)`; evaluation transports by
    `alpha^vee tensor alpha^(-1)`. The implementation defines these maps
    intrinsically using the actual derived closed structure, so it requires no
    extra representative or splitting datum as a hypothesis and makes no
    arbitrary selection of a representative. These are equivalent constructions
    of the same canonical evaluation and coevaluation, not extra assumptions of
    dualizability or a replacement by a cohomological supertrace.
13. `perfectTraceHasRightDual P hP` constructs a right-dual datum with actual dual
    `perfectTraceDual P`. Its exact pairing is obtained from
    `MonoidalClosed.exactPairingOfIsIso P` and
    `BraidedCategory.exactPairing_swap`. Its evaluation and coevaluation are the
    two maps just described. This lets `perfectCategoricalTrace` reuse the
    existing `CategoryTheory.MonoidalCategory.trace`, whose definition is exactly
    `coevaluation ≫ v ▷ dual ≫ braiding.hom ≫ evaluation`. No second abstract
    categorical-trace notion is defined.
14. `perfectTraceScalar` first transports an endomorphism of the monoidal unit to
    `(DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)` using
    `singleFunctorObjUnitIso`. It then uses that fully faithful functor's
    `preimage` and evaluates the resulting ordinary linear endomorphism at `1`.
    `perfectTraceScalarInverse a` applies the same functor to
    `ModuleCat.ofHom (a • LinearMap.id)` and transports back. This is exactly the
    node's scalar identification, including its stated inverse.
15. The triangle, chain-supertrace and independence assertions are not added as
    assumptions and are not newly proved here. No import or premise from the
    downstream `lem-trf-chain-supertrace` is used. Existing upstream duality
    results suffice to construct the defining inverse comparison.

Dependency declarations read and used:

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`,
  `WeilConjectures.FiniteFieldDatum` and `.CoefficientDatum`; its imported
  `Sheaf.NumberTheory.Padics.CoefficientExtension` supplies the valuation and
  quotient constructions used in the main signature.
- `def-trf-coefficient-conventions`: the current DAG statement has no Lean record.
  This item's opening explicitly takes only its finite-field/finite-coefficient
  datum. Every object in that part is already supplied by the preceding recorded
  declarations and the ordinary intermediate-field construction. The scheme,
  constructible sheaf, compact-support and point-fiber conventions from that node
  do not occur in this ordinary-ring-complex definition. There is no missing new
  notion needed here and no private replacement coefficient package.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and `Q`.
- `def-pc-perfect-ring-complex`:
  `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`,
  `DerivedCategory.IsPerfectRingComplex`. Its upstream import supplies the
  bounded-projective duality theorem used by the construction.
- `def-weil-point-finite-cohomology-complexes`:
  `Sheaf.Paper.PointFiniteCohomologyComplexes`,
  `DerivedCategory.pointFiniteCohomology`; imported to retain the distinction
  expressly drawn by the statement, never used as the trace domain.
- `lem-pc-ring-derived-map-representative`:
  `Mathlib.Algebra.Homology.DerivedCategory.KProjective`,
  `CochainComplex.IsKProjective.Qh_map_bijective`; its domain consists of homotopy
  classes, as required, and is not confused with unquotiented chain maps.
- `def-sc-module-total-hom-complex`:
  `Sheaf.Algebra.Homology.ModuleHomComplex`, `CochainComplex.moduleHomComplex`.
- `def-pc-tensor-complex-sheaves`:
  `Mathlib.Algebra.Homology.BifunctorShift`, `CochainComplex.mapBifunctor` and
  `MonoidalCategory.curriedTensor`, used by the upstream module derived tensor.
- `def-weil-pbc-strict-perfect-coefficient-package`:
  `Sheaf.Paper.StrictPerfectPackageOnSite`, reexporting
  `ModuleCat.StrictPerfectCoefficientPackage` from
  `Sheaf.Paper.StrictPerfectCoefficientPackage`. The ordinary-ring version is
  present and usable; no repair to the site-universe interface is needed.
- `lem-weil-pbc-derived-single-fully-faithful`:
  `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`, the `Full` and
  `Faithful` instances on `DerivedCategory.singleFunctor` at degree zero.
- `lem-sc-bounded-above-projective-kprojective`:
  `Mathlib.Algebra.Homology.HomotopyCategory.KProjective`,
  `CochainComplex.isKProjective_of_projective`, for bounded projective models.
- `lem-weil-pbc-projective-module-flat`:
  `Mathlib.RingTheory.Flat.Basic`, `Module.Flat.of_projective` and `.of_free`.
- `lem-pc-module-bounded-flat-kflat`:
  `Sheaf.Algebra.Homology.BoundedFlatKFlat`,
  `CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat`.

The upstream files defining `DerivedCategory.IsPerfect.isDualizable`, the internal
Hom tensor comparison, `MonoidalClosed.coevaluationOfIsIso`,
`MonoidalClosed.exactPairingOfIsIso`, the descended braiding,
`CochainComplex.rightDual`, its evaluation/coevaluation, and
`MonoidalCategory.trace` were opened and their complete relevant signatures and
docstrings read. The source PerfectTrace theorem was also read: it is a supertrace
statement with extra duality/braiding inputs, not this scalar-valued definition.

Edge cases checked mathematically: zero object and empty degree support give the
zero coevaluation and scalar zero; a zero frame rank supplies no summands; a
nonzero complex in one odd degree uses the Koszul sign and gives minus the
ordinary trace; the identity on `R[0]` has scalar one; a zero endomorphism has
scalar zero. No freeness, field, nonzero rank, chosen basis or invertibility of
`v` is assumed. Finite projective modules that are not free remain covered in
the ring-general construction. The general scalar construction makes sense
even for the zero ring, while the finite-coefficient specialization retains
`n ≥ 1`. The localization universe is the module Hom universe, using the
existing locally small Grothendieck derived-category construction; no site object
universe is identified with its morphism universe.

Searches performed with the prescribed `msearch.py`, plus source `rg`:

- LeanSearch: “The scalar valued categorical trace of an endomorphism of a perfect
  complex over a commutative ring”; service returned Internal Server Error.
- LeanFinder: “Categorical trace of endomorphism of perfect complex over commutative
  ring signed dual evaluation coevaluation”; eight hits, including
  `LinearMap.trace_eq_contract`, `FGModuleCat.exactPairing`, and field-module
  evaluation/coevaluation. They do not supply the perfect-derived scalar trace.
- Loogle: `"coevaluation", "evaluation"`; twelve hits on abstract exact pairings
  and mate identities, none giving the full item.
- Mathlib grep: `def trace|def evaluation|def coevaluation` in
  `CategoryTheory/Monoidal`; the two hits are abstract exact-pairing evaluation
  and coevaluation, not the scalar trace on perfect complexes.
- `rg` of upstream and `lean/Sheaf` for the item id, categorical trace names,
  perfect duals and derived tensors found the upstream abstract
  `MonoidalCategory.trace`, the perfect duality implementation and the supertrace
  theorem. The abstract trace and duality implementations are reused. There was
  no exact declaration of this whole node. New declaration names were searched
  in upstream and the shared `Sheaf` tree with no collision.
- `tools/lean_names_upstream.py show def-trf-categorical-trace` found no exact
  attachment for this node in the indexed blueprint/docstring matches.

Validation uses only `scompile.py` per-file compilation. The first complete draft
compiled cleanly after fixing a broken-line dotted field notation in the full
subcategory definition. The final refinement reuses the upstream abstract trace
through a canonical right-dual structure. Its per-file scompile.py check passed
with no errors or warnings before the delivery dry run.

No STATEMENT-DISPUTED or newly discovered mathematical node fault remains. The
historical stage-1 split-report text is preserved unchanged with all reviewed
fields. No live sources or tools have been edited; nothing is pushed by the worker.

## Second reading by NF

I independently opened the sandbox node and complete module, the source blueprint
node at order 1826 on the project server, and the dependency declarations below.
The source introduces the perfect category, derived dual, canonical evaluation and
coevaluation, their trace composite, and the scalar identification. It has no extra
standing scheme, field, Noetherian, or freeness hypothesis for this construction.
The expanded DAG gives the bounded-projective normalization of those same maps.
There is no stage-2 statement_change, new node, or dependency module in this delivery.

Here is my item-by-item list of the objects, hypotheses, and defining clauses,
matched to the Lean with a verdict for each:

1. Global datum `(p,a,q,k₀,k)` and fixed coefficient prime/closure: `D :
   FiniteFieldDatum.{u}` and `c : D.CoefficientDatum`. I read both structures in
   `Sheaf.Paper.FiniteFieldFiber`: prime, positive exponent, cardinality, algebraic
   closure, `Fact c.l.Prime`, and `c.different : c.l ≠ D.p` are present. PASS.
2. Embedded finite extension, valuation ring, chosen uniformizer, positive level,
   quotient `A`: `E : IntermediateField (Padic c.l) c.Qbar`,
   `[FiniteDimensional (Padic c.l) E]`, `n`, `_hn : 1 ≤ n`, and
   `Padic.coefficientExtensionRing c.l E n`. I opened `CoefficientExtension.lean`:
   its quotient is by `(Ideal.span {coefficientExtensionUniformizer ...}) ^ n`.
   These are the recorded ring and uniformizer conventions; no field is substituted
   for the quotient ring. PASS.
3. Ordinary module derived category and localization: the argument `P :
   DerivedCategory (ModuleCat.{u} A)` and upstream `DerivedCategory.Q`.
   `v : P ⟶ P` is any derived endomorphism, not merely a chain map, automorphism,
   or a map with a selected lift. PASS.
4. Perfectness and full subcategory: `hP : IsPerfectRingComplex P` and
   `perfectTraceCategory R := ObjectProperty.FullSubcategory IsPerfectRingComplex`.
   I opened `PerfectRingComplexGeneral.lean`: boundedness is both strict degree
   bounds, terms are projective and finite, and an isomorphism with `Q.obj B`
   is required. Its specialization here is definitionally upstream `IsPerfect`.
   `pointFiniteCohomology` was also opened: its finite cohomology condition is
   not used in place of perfectness. PASS.
5. Homotopy classes for projective representatives: all actual maps are in the
   derived category. The imported `IsKProjective.Qh_map_bijective` has homotopy
   category morphisms as its domain, and `isKProjective_of_projective` assumes
   only a strict upper bound and projective terms. I opened both signatures;
   neither creates a category of unquotiented chain maps. PASS.
6. Model dual and its differential: `perfectTraceModelDual B` is precisely
   `moduleHomComplex B (singleFunctor.obj (ModuleCat.of R R))`. I opened
   `moduleHomComplex`, `HomComplex.δ` and `δ_hom`: the standard differential
   `d_M φ - (-1)^j φ d_B` becomes `(-1)^(j+1) φ d_B` for target `R[0]`;
   only model degree `-j` survives. PASS.
7. Derived tensor and signed symmetry: tensor notation uses the existing upstream
   K-flat derived monoidal structure. `perfectTraceCanonicalBraiding` calls
   `DerivedMonoidal.braidedCategory Qh (HomotopyCategory.quasiIso ...)` directly.
   I opened `DerivedBraided.lean`, including its comparison characterization:
   this descends the actual homotopy-category Koszul braiding. I also checked
   `mapBifunctor`, `Module.Flat.of_projective`, and the recorded bounded-flat
   K-flat theorem. Thus the differential is `dx ⊗ y + (-1)^|x| x ⊗ dy`, and
   the symmetry has `(-1)^(|x|*|y|)`; no arbitrary braiding is an input. PASS.
8. Degreewise splitting and frame: I read the ordinary
   `ModuleCat.StrictPerfectCoefficientPackage`, reexported through the recorded
   site module. Its data are `N`, `i`, `p`, `i ≫ p = 1`, with no chain-map
   condition. `perfectTraceFrameVector s i a = (s.p i).hom (Pi.single a 1)`
   and `perfectTraceFrameFunctional s i a = (LinearMap.proj a).comp (s.i i).hom`
   are exactly `e_{i,a}` and `epsilon_{i,a}`. The normalization of ranks on zero
   terms is for writing the finite model sum; the intrinsic maps take no frame
   argument and impose no extra nonzero-rank restriction. PASS.
9. Derived dual and contravariance: `perfectTraceDual P = (ihom P).obj (𝟙_ _)`
   and `perfectTraceDualMap f = (MonoidalClosed.pre f).app (𝟙_ _)`. The direction
   for `alpha : Q(B) ≅ P` is from the dual of `P` to the dual of `Q(B)`.
   I read the derived closed instance, its homotopy internal Hom, and its
   tensor-Hom adjunction, rather than inferring this from names. PASS.
10. Evaluation and its zero components: `perfectTraceEvaluation P` is the
    dual-first braiding followed by `(ihom.ev P).app _`. The upstream internal
    Hom has differential `(-1)^p (d_M f - f d_B)` on model-degree `p`
    components. Its identification with the recorded standard total Hom in
    Hom degree `j` multiplies those components by `(-1)^(p*j)`. This is a
    chain isomorphism: on the target differential the two coefficients become
    `(-1)^(p*j)` and `-(-1)^j (-1)^((p+1)*j)`, as required.
    When `p+j=0`, braiding contributes the same `(-1)^(p*j)`, so under this
    identification evaluation is exactly `φ(x)`, not an extra signed evaluation.
    Target degree other than zero is zero. PASS, with documentation clarified.
11. Coevaluation: `perfectTraceCoevaluation P hP` uses
    `coevaluationOfIsIso P` and then `(β_ P (perfectTraceDual P)).inv`.
    I opened its body `curry (ρ_ P).hom ≫ inv (ihomUnitTensorToIhom P P)` and
    the comparison definition. `IsPerfect.isIso_ihomUnitTensorToIhom hP P`
    supplies invertibility without a new hypothesis. After the same signed
    Hom identification, the inverse image of the identity is precisely
    `sum e_{i,a} ⊗ epsilon_{i,a}`: the splitting expresses each identity as
    `x ↦ sum epsilon_{i,a}(x)e_{i,a}`. Hence this is the prescribed canonical
    map, not a choice of an unspecified duality structure. PASS.
12. Transport through `alpha`: the intrinsic evaluation is natural in `P`,
    and the inverse-comparison coevaluation is its uniquely determined dual
    unit. On the bounded-projective model these are the previous two maps.
    Thus transporting to `P` gives `alpha ⊗ (alpha^vee)^(-1)` for coevaluation
    and `alpha^vee ⊗ alpha^(-1)` before evaluation, in exactly the directions
    in the node. No representative, splitting, or independence assertion is
    made an additional argument to the trace. PASS.
13. Trace composite: I opened `exactPairingOfIsIso`, Mathlib's
    `exactPairing_swap`, and upstream `MonoidalCategory.trace`.
    `perfectTraceHasRightDual` has the actual internal dual, with coevaluation
    and evaluation definitionally the preceding two constructions. The reused
    trace body is `η ≫ v ▷ dual ≫ β.hom ≫ ε`, precisely the node's composite.
    There is no dependency on the forward lemma `lem-trf-chain-supertrace`.
    The ring-general definition is specialized by
    `finiteCoefficientCategoricalTrace D c E n _hn P hP v`. PASS.
14. Scalar and inverse: `perfectTraceScalar` conjugates by
    `singleFunctorObjUnitIso`, applies `(singleFunctor _ 0).preimage`, and
    evaluates the ordinary linear map at `1`. I opened the full/faithful
    single-functor instances and the unit isomorphism. `perfectTraceScalarInverse`
    maps `ModuleCat.ofHom (a • LinearMap.id)` through that functor and conjugates
    back. These are exactly the specified identification and inverse. PASS.
15. No extra assertions: all fourteen declarations are definitions with real
    data, using existing canonical constructions and isomorphism witnesses.
    There are no new theorems, axioms, or sorries. The node has empty proof
    and proof_deps lists, so no new proof docstring is missing. PASS.

Edge cases: the zero perfect object, empty degree support, and zero frame rank
are admitted. An empty frame contributes zero, and zero endomorphisms have zero
trace. For one odd-degree free summand the single symmetry contributes minus;
for `R[0]` the identity has scalar one. Characteristic two identifies the minus
sign with plus without excluding that case. Projective nonfree terms remain
allowed; no module basis, Noetherian ring, or field assumption is introduced.
The finite-coefficient entry point excludes `n=0` exactly as the node does;
the ring-general helper also makes sense over the zero ring. There is no scheme
argument, so empty schemes introduce no omitted case. The universe `u` is
arbitrary and matches the recorded ordinary module/coefficient size convention;
`HasDerivedCategory.{u}` is the available small-Hom localization for modules,
not an additional geometric finiteness condition or a site-universe equality.

Independent searches, with different queries from the worker:

- `msearch.py ... leansearch`: “The derived categorical trace takes a perfect
  complex endomorphism to a scalar in the coefficient ring”; eight hits on
  ordinary `LinearMap.trace`, algebra trace, matrices and base change. No
  perfect-derived scalar trace definition.
- `msearch.py ... leanfinder`: “derived perfect module complex categorical
  dimension evaluation coevaluation supertrace”; eight hits on Ext and Tor
  vanishing and module HasExt. No exact item.
- `msearch.py ... loogle`: `"trace", "DerivedCategory"`; zero hits.
- Direct `rg` in Mathlib, upstream `WeilConjectures`, and shared `lean/Sheaf`
  for categorical traces, trace definitions, perfect duals, and RHom. I opened
  upstream `PerfectTrace.lean`: it states a supertrace theorem with extra
  braiding, duality, and free-term inputs, not this definition. The abstract
  `MonoidalCategory.trace` and existing duality constructions are reused.
  No exact existing whole-item declaration was found. No private replacement
  of a dependency or independent missing notion is needed.

Mismatch and repair: the worker's explanation passed too quickly from upstream
internal Hom to the standard module total Hom. The two chain-level conventions
are isomorphic rather than literally identical. I added the component sign
comparison and its cancellation with braiding to the module docstring, and
made the evaluation docstring refer explicitly to that comparison. Definition
bodies, signatures, node statement, and dependency lists remain as reviewed.
The node's lean.statement is still verbatim the main signature.

Validation: the initial module passed scompile.py for both sandbox and library
module names with no errors or warnings. The final documented module is checked
again through scompile.py and the required deliver2.py dry run before pushing.
