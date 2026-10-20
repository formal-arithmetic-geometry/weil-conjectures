## Worker report

Item: lem-pur-finite-adjoint-mate-compatibility. The delivery states the four clauses in
Sheaf.Paper.FiniteAdjointMateCompatibility. All four theorem bodies are `sorry`; the three
helper definitions contain actual equality propositions built from the published maps.
There is no new coefficient ring, operation functor, adjunction, projection, compositor,
or arbitrary comparison datum. The mathematical statement and proof are unchanged.

Sources read: the complete DAG node, its seven proof steps, and the current blueprint
main-20261015/sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, especially Steps 2 and 4. I read the eight
original statement dependencies and their recorded interfaces, including the Mathlib
matches for mates and composite adjunctions. I also read the finite exceptional
compositor, scalar comparison definitions, upstream UpperShriekCanonicalMaps, and
SmoothTensorDuality's displayed definition and its symmetry comparison.

Hypotheses and objects, clause by clause:

* The datum k=algebraic closure of the fixed finite field, ell distinct from p,
  E inside the fixed coefficient closure, and n positive is the recorded
  `P : PurityFiniteSetting`. Its fields are `field`, `coefficients`, `extension`,
  `level`, and `level_pos`. `P.Coefficient` is precisely ULift of O_E/(varpi_E^n),
  using the existing ring structure; it is not replaced by ZMod(ell^n).
* The positive integer m and m<=n are `m : ℕ+` and
  `hmn : (m : ℕ) ≤ P.level`. The B ring is
  `ULift (Padic.coefficientExtensionRing P.coefficients.l P.extension m)`.
  The ring homomorphism is the existing `PurityFiniteSetting.finiteReductionRingHom`,
  lifted with `RingHom.ulift` to the coefficient universe. Its body is the
  quotient-factor map for the two powers of the uniformizer ideal, as recorded
  by `def-pur-finite-reduction-root-charts`; thus ramified E and nonflat
  reduction are included.
* Each scheme has `Over (Spec (.of P.field.k))`, `LocallyOfFiniteType` and
  `QuasiCompact` for its structure map, together with `IsSeparated` for that
  map in every theorem. Together these are the stated separated finite-type
  k-schemes. Morphisms have their `IsOver` instances, and the separated,
  locally-finite-type and quasi-compact instances expressing separated finite
  type. These are not affine, proper, or projective assumptions.
* The first three clauses use the canonical etale-origin coordinates already
  used by the recorded def-pur-co-smoothness module. The arbitrary representative
  K is in `Etale.DerivedCategoryModule P.Coefficient`, with
  `Etale.DerivedCategory.boundedConstructibleFiniteTor ... K`. This tests the
  entire pro-etale Dctf domain: every bounded constructible pro-etale object
  has an etale origin; comparison is fully faithful on bounded-below complexes,
  and the finite-ring Tor comparison preserves and reflects the same interval.
  This is a coordinate expression of the prescribed maps. It does not assume
  an etale origin for only a selected subclass or an ambient pro-etale adjunction.
  Conjugating the equality by the canonical origin isomorphism handles every
  pro-etale input and is independent of the witness.
* Smoothness of pure relative dimension is `[SmoothOfRelativeDimension d f]`
  with `d : ℕ`. The composition clause also has `[SmoothOfRelativeDimension e g]`
  with `e : ℕ`. Dimension zero is permitted.

Clause 1, theta: `finite_adjoint_mate_tensor` asserts
`P.finiteAdjointMateTensorClause m hmn f K`. The helper is exactly the existing
`Etale.ExceptionalCoefficients.TensorCompatibility` for this quotient homomorphism.
Its left side is Q_X(theta_A) followed by the specified exceptional mate b at K.
Its right side is `tensorDomainMap` followed by theta_B. The domain map is the
canonical tensorator, scalar/pullback comparison, b at the coefficient unit and
G_B of `unitIso`. Thus Q_Y(A_Y)=B_Y is included. The map `smoothTensorDualityMap`
has source f* K tensor omega and is the counit/inverse-projection transpose.
The source of the recorded co-smoothness module writes omega tensor f* K;
SmoothTensorDuality compares these by the canonical derived braiding. This is
the source order specified by this item's theta, with no chosen orientation.

Clause 2, composition: `finite_adjoint_mate_composition` asserts the equality
`finiteAdjointMateCompositionClause`. The left side is Q_X(c_A), then b_f at
G_g,A K, then G_f,B(b_g,K); the right side is b_gf,K followed by c_B at Q_Z K.
The actual compositor is `(finiteExceptionalComposition ... f g).hom.app K`,
the published adjunction conjugate of the canonical compact-support compositor.
It is an isomorphism by its definition, not a map chosen with the desired endpoints.
Both f and g have the stated smoothness and relative dimensions, and K ranges
through Dctf(Z,A) via its arbitrary representative.

Clause 3, extraordinary comparison: `finite_adjoint_mate_baseChange` uses arbitrary
X', Y', u', f', v and `sq : IsPullback u' f' f v`. It asserts the equality in
`finiteAdjointMateBaseChangeClause`: Q_X'(beta_A,K), then b_f',v_A*K, then G_f',B
of the scalar/pullback identification equals the other path consisting of the
u scalar/pullback identification, u_B*(b_f,K), and beta_B,Q_YK.
The map beta is exactly the recorded `rightDerivedUpperShriekBaseChangeMap`,
the mate of inverse compact-support exchange. The instances needed for f' are
obtained from sq by `MorphismProperty.of_isPullback`; none is imposed as an
additional base-change hypothesis. There is no flatness, smoothness, or properness
hypothesis on v. At K=A_Y, the recorded
`dualizingComplexBaseChangeMap` is definitionally this component followed by
G_f' of `leftDerivedUpperStarUnitIso`. Consequently this is the coefficient-object
comparison of def-pur-co-smoothness, using the same scalar-unit normalization
as the tensor clause. The arbitrary-K square includes this component; it is
not replaced by a claim only at the unit.

Clause 4, all transposes: `FiniteExceptional.finite_adjoint_mate_transpose` uses
the intrinsic small-pro-etale categories directly. Here l, E, D and hl spell out
the corresponding fixed coefficient and finite-field data; instantiate them
with P.coefficients.l, P.extension, P.field, and its unequal-characteristic proof.
The dependency uses predecessor indices, so r and s mean the positive exponents
r+1 and s+1. `hsr : s ≤ r` is exactly the quotient-level inequality; every pair
n>=m>=1 occurs. T and U are separated finite-type schemes over D.k and
h:T->U is any separated finite-type map, without smoothness. The parameter
c is an arbitrary compactification of h; Nagata supplies one in this setting,
and the standing functor's refinement comparisons identify its presentations.
`M : (domain l E T r).FullSubcategory` and the analogous L encode exactly M,L
in Dctf, not extra perfectness. `a : (F ... r).obj M ⟶ L` is arbitrary.
The left side is Q_T(eta_A,M followed by G_A(a)) then b_h,L; the right side is
eta_B,Q_TM followed by G_B(q_h,M inverse followed by Q_U(a)). These are precisely
the two transposes specified in the node, with the reduced a spelled out.

Dependency declarations used (modules read with signatures and docstrings):

* Sheaf.Paper.PurityFiniteSetting: `WeilConjectures.PurityFiniteSetting`,
  `PurityFiniteSetting.Coefficient` and its coefficient ring instance.
* Sheaf.Paper.CohomologicalSmoothnessFiniteComparison:
  `ProEtale.IsCohomologicallySmoothFiniteCompared`, `finiteComparedTensorClause`,
  `finiteComparedBaseChangeClause`; their canonical etale maps are the ones used here.
* Sheaf.Paper.BasicOperationsCoefficientReduction:
  `WeilConjectures.basicOperationsCoefficientReduction`, particularly the finite
  pullback/tensor, structural-unit/counit and finite compact-support clauses.
  This is imported for the proof plan, without imposing its conditional
  exceptional-admissibility hypothesis.
* Sheaf.SixFunctors.FiniteExceptional: `FiniteExceptional.domain`, `F`, `G`, `Q`,
  `adjunction`, `q`, `b`, and `finite_exceptional`. The first two are the actual
  intrinsic compact-support and transported exceptional functors restricted to
  finite Tor; q is the normalized compact-support comparison, b its right mate.
  The theorem's unit/counit equations are the exact normalization used in the
  transpose clause, not an assumed existence of a compatible right adjoint.
* Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients:
  `ConstructibleExceptionalCoefficients.System`; its public finite construction
  is also available through FiniteExceptional and is the recorded
  def-weil-exceptional-inverse-image interface.
* Sheaf.Paper.ExceptionalCoefficientComparison:
  `Etale.ExceptionalCoefficients.mateMap`, `tensorIso`, `unitIso`,
  `tensorDomainMap`, `TensorCompatibility`; the maps accept a general ring
  homomorphism, so the definitions are used for actual O_E quotients. The
  ownership is recorded by `def-per-exceptional-coefficient-maps` for the
  compact-support/mate maps and by the new definition node
  `def-pur-exceptional-coefficient-tensor-maps` for every tensor/unit
  normalization, `tensorDomainMap`, and `TensorCompatibility`. Its separate
  ZMod-specialized exceptional_coefficient_comparison theorem is not used as
  if it applied to ramified coefficient rings.
* Sheaf.Paper.PurEtaleScalarMateProjection: `Etale.scalarPullbackIso` and
  `Etale.scalarPullbackIso_existsUnique`; the repair node
  `def-pur-etale-scalar-pullback-iso` owns the existing normalized comparison
  used in clauses 1 and 3.
* Sheaf.Paper.FiniteReductionRootCharts:
  `PurityFiniteSetting.finiteReductionRingHom`, the canonical quotient-factor
  map used in the statement via `RingHom.ulift`.
* Sheaf.SixFunctors.CompactCoefficientComposition:
  `ProEtale.finiteCompositionReduction` and
  `finiteCoefficient_compactSupport_composition` (both site realizations);
  these remain proof dependencies for the compact-support composition square,
  but the theorem is not a statement dependency.
* Sheaf.Paper.PurityFiniteExceptionalComposition:
  `PurityFiniteSetting.finiteExceptionalComposition`, including its specified
  unbounded compact-support compositor and composite exceptional adjunction.
* Sheaf.Paper.ExchangeProjectionSuppliedDomains:
  `SuppliedExchangeProjection.ExchangeProjectionStage` and its `compactExchange`
  and `projection`; the inverse-projection and inverse-exchange formulas are
  the published finite-coefficient specializations of these composites.
* Mathlib.CategoryTheory.Adjunction.Mates: `CategoryTheory.mateEquiv`, with
  its actual unit/alpha/counit formula, and `mateEquiv_vcomp` for the proof plan.
* Mathlib.CategoryTheory.Adjunction.Basic: `Adjunction.comp` (and its displayed
  `comp_homEquiv`, `comp_unit_app`, `comp_counit_app`) and `Adjunction.id`.
* The remaining proof imports correspond to the recorded compact-support
  coefficient comparison, constructible origin, finite compact projection
  formula and finite-level pro-etale compact-support base-change statements.

The statement dependencies include the canonical helper interfaces
`def-pur-finite-reduction-root-charts` (for the lifted quotient ring map),
`def-pur-finite-exceptional-composition`, the existing compact-support/mate
owner `def-per-exceptional-coefficient-maps`, the tensor/unit owner
`def-pur-exceptional-coefficient-tensor-maps`, and the scalar/pullback owner
`def-pur-etale-scalar-pullback-iso`. The theorem node
`lem-pur-exceptional-coefficient-comparison` is not used as an ownership
substitute. The compact-support composition node
`lem-sf-compact-coefficient-composition` remains in `proof_deps` only, where
its theorem is used by the proof plan.

Edge cases checked: m=n is retained and uses the canonical scalar unit rather
than literal identity functors; m=1 and n=1 are retained; ramification is
unrestricted; no quotient is assumed flat. Zero objects and zero morphisms are
included in each domain and transpose identity. Empty schemes need no chosen
point, nonempty cover or dimension; dimension zero smooth maps and identity
maps are permitted. The Cartesian square is arbitrary and not required to be
the particular chosen categorical pullback. All coefficient objects are in the
standard u+1 universe over Scheme.{u}; the small sites retain object universe
u+1 and morphism universe u. No universe equality or site-size restriction was
introduced.

Searches made (actual msearch output is logged in searches.jsonl):

* leanfinder, "Finite coefficient reduction preserves exceptional inverse image
  tensor maps composition base change and adjoint transposes": eight hits,
  headed by IsBaseChange.finitePow, IsBaseChange.of_comp and IsBaseChange.comp_iff,
  with tensor-product and polynomial base-change lemmas; no geometric statement.
* loogle, `CategoryTheory.Adjunction, "mate"`: twelve hits including mateEquiv,
  its unit/counit formulas and mateEquiv_vcomp. These are the generic ingredients,
  not the finite-coefficient operation-compatibility statement.
* msearch grep, `exceptional.*(reduction|coefficient)|coefficient.*exceptional`,
  Mathlib/CategoryTheory: zero hits.
* Direct rg of lean/WeilConjectures and lean/Sheaf for finite-adjoint names,
  exceptional composition, TensorCompatibility and BaseChangeCompatibility,
  plus the item id and dag/lean_names_upstream.json: no existing statement for
  the whole item. This found the existing finiteExceptionalComposition, which
  is reused instead of defining another compositor, and the scalar tensor/mate
  interfaces reused in the three helper propositions. Exact searches for the
  seven proposed declaration names found no clashes in the project or Mathlib.

Validation: scompile.py compiled the module in both the sandbox and its final
library path with no errors or warnings. A preliminary expensive custom compositor
was removed in favor of the existing canonical compositor; the complete module
then took 15--22 seconds per file, within the unchanged 60-second limit.
The latest check took 21.4 seconds in sandbox coordinates and 17.8 seconds at
the final module path. Redundant direct imports of already available interfaces
were removed after a subsequent dry-run timeout; the complete statements then
compiled cleanly again.
The final delivery dry run and delivery are performed with deliver2.py.

No statement correction or disputed statement was found. The returned ownership
fault is repaired below; no unresolved node fault remains.

## New nodes

`def-pur-exceptional-coefficient-tensor-maps` is an `existing:true` definition
owner for the declarations `TensorNormalizationAux`, `TensorNormalization`,
`tensorIso_existsUnique`, `siteTensorIso_existsUnique`, `tensorIso`,
`UnitNormalizationAux`, `UnitNormalization`, `unitIso_existsUnique`, `unitIso`,
`tensorDomainMap`, and `TensorCompatibility` in
`Sheaf.Paper.ExceptionalCoefficientComparison`. Its statement records the
canonical normalized tensor/unit transport and cites
`def-per-exceptional-coefficient-maps` for the compact-support/mate maps and
`def-pur-etale-scalar-pullback-iso` for scalar pullback. Searches found no
prior DAG owner and no Mathlib or upstream duplicate.

`def-pur-etale-scalar-pullback-iso` is an `existing:true` definition owner for
`AlgebraicGeometry.Etale.scalarPullbackIso` and its local uniqueness theorem in
`Sheaf.Paper.PurEtaleScalarMateProjection`. It records the normalized K-flat
representative construction in that theorem's module, citing its construction
prerequisites directly rather than citing the projection-identity theorem.
Searches found no prior DAG owner and no Mathlib or upstream duplicate.

## Dependency modules

None were needed: both repaired owners point to existing project declarations,
and the item module already imports the two source modules.


## Repair self-check by NP

The return for immutable head 281b10d770e1 was checked against the saved packet
and the current read-only sources. The four theorem statements and the three
helper propositions in FiniteAdjointMateCompatibility.lean are byte-unchanged.
Only the item statement-dependency ownership is repaired. The removed theorem
`lem-pur-exceptional-coefficient-comparison` supplies none of the mathematical
hypotheses in the four signatures; its plain map helpers now have explicit
definition owners. The item cites `def-per-exceptional-coefficient-maps` for
mateMap, `def-pur-exceptional-coefficient-tensor-maps` for TensorCompatibility
and its tensor/unit domain transport, and `def-pur-etale-scalar-pullback-iso`
for the two scalarPullbackIso terms of the arbitrary Cartesian square.

For the tensor owner, I matched the two normalization equations to
TensorNormalizationAux and UnitNormalizationAux, their small-etale
specializations, and the .choose terms defining tensorIso and unitIso. The
site tensor iso uses heterogeneous equality to the normalized tensorator,
not a fresh arbitrary iso. tensorDomainMap uses tensorIso, inverse
scalarPullbackIso, then mateMap at the unit followed by G(unitIso); its
source is S_X(f_A^*K tensor omega_A). TensorCompatibility is the equality
of this domain transport followed by theta_B with S_X(theta_A) followed
by mateMap. For the scalar owner I matched the displayed equation on every
K-flat complex to scalarPullbackIso_existsUnique, and scalarPullbackIso
is exactly its unique witness. Its ordinary, complex and geometric
representative helper definitions are listed as owned declarations.

The current sources still place these helpers in the two theorem modules;
no earlier definition node owns them. No source module is copied or changed.
The generic Aux normalization predicates retain all their abelian,
Grothendieck, braided monoidal, flat-resolution and universe parameters.
The geometric specialization retains Scheme.{u}, coefficients Type (u+1),
and ModuleCat.{u+1}. Equal coefficient levels, nonflat quotients, dimension
zero, empty schemes and arbitrary base change remain included as before.
FiniteExceptional's definition ownership was advisory in the return; its
existing theorem remains a genuine proof dependency for the unit/counit
normalization equations used by the fourth clause.

Fresh searches in searches.jsonl cover both new nodes. LeanSearch for the
tensor normalization initially timed out (recorded unavailable); a second
query returned eight ordinary scalar/module results, including
ModuleCat.ExtendScalars.obj' and extendRestrictScalarsAdj_unit_app_apply.
LeanFinder returned HomologicalComplex unitors and generic localization
monoidal comparisons. The scalar/pullback LeanSearch and LeanFinder queries
returned ordinary module pullback and etale base-change results. None is
the exact notion. Mathlib grep for TensorNormalization, UnitNormalization,
tensorDomainMap, TensorCompatibility and scalarPullbackIso returned zero
hits; Loogle on CategoryTheory.mateEquiv returned the generic mate API.
Direct searches of both source trees found the exact existing project
helpers. blueprint_refs.py reported no blueprint nodes for 'scalar pullback'
or 'tensor normalization', and reported the required ancestor as
thm-pur-finite-reduction-of-purity. The ownership scan found the theorem
records but no pre-existing definition owner. Searches and unavailable
services are recorded as they actually returned.


The item compiled cleanly after the ownership repair with scompile.py:
16.8 seconds in sandbox coordinates and 13.8 seconds at its library path.
The subsequent dry run compiled its declaration probes successfully, then
found only two citation-shape errors: a combined bracket citation was not
recognized as two separate node references. Both were separated into the
required individual bracket citations. The tensor owner cites the ordinary
etale tensor node def-kun-derived-tensor for the actual category used.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
