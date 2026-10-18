## What changed

Replaced the single `galois_lisse_representations` hole by a complete Lean assembly from
three proper component theorems. The theorem's signature is unchanged. The finite-set
correspondence, finite-etale comparison and normalized action comparison use the already
proved fundamental-group equivalence. The finite lisse module category's abelianity,
closure under kernels and cokernels, and its actual sheaf monoidal/braided structure are
proved here. The scalar-extension functors are restrictions of actual sheafified scalar
extension; their underlying-sheaf comparisons are identities. Constructed the natural
comparison for composite extensions by inverting the sheafification of the first unit
after the second extension, then sheafifying the module scalar associator. Proved its
section formula `b ⊗ (a ⊗ z) ↦ b g(a) ⊗ z` using naturality and the adjunction units.
The lisse composite comparison is lifted through the full inclusion. Constructed a
natural scalar-stalk isomorphism directly at the unlifted geometric point from preservation
of filtered colimits by the scalar-extension left adjoint and invariance of the point under
sheafification. Its formula on every pure section germ is proved by naturality. This
comparison and its germ formula are supplied inputs of the remaining tensor/scalar lemma.
Equivalences preserve the
required finite limits and colimits.

Proved that FLC has finite limits and its full sheaf inclusion preserves them, by the
finite-etale/Yoneda comparison and change of morphism property. Also constructed the
finite-carrier universe equivalence explicitly: module ULift is fully faithful, and each
finite representation shrinks with its transported linear action. Its natural comparison
is an isomorphism of linear G-actions, so the required carrier and action normalization
are retained. Also constructed the equivalence from ambient-product `LambdaModuleObject`
to `InternalModule` in FLC. Addition and zero use the product and terminal comparisons;
the ten ambient diagrams imply all generalized-element module laws. The reverse
construction recovers the diagrams, and operation-preserving morphisms agree in both
descriptions. Full faithfulness and the explicit reverse objects give the equivalence.
Its underlying objects, maps and operations are supplied as normalized inputs to the
remaining finite module lift, together with the carrier-universe equivalence. The
comparison from module stalks to underlying-set stalks is constructed using the forgetful
functor and proved to send every section germ to the same underlying germ; it too is a
normalized input to that component. The completed proof combines its action formula
with this proved germ formula to assemble the full evaluation clause. Also constructed
the profinite model: the fundamental-group homeomorphism gives Hausdorffness and total
disconnectedness of G, so its given compact group structure defines `ProfiniteGrp.of G`.
The identity continuous group isomorphism supplies the model used by the adic component.

Proved that every fibre automorphism fixes every germ of a finite constant module.
The proof constructs an underlying-set map from the constant zero module for each value,
uses the singleton source stalk and naturality, and checks its image on representative
section germs. This proves the constant-coefficient unit clause from normalized evaluation;
the finite module split-off therefore does not assume or assert that clause.

Moved the 46 unchanged data declarations to
`Sheaf.Paper.GaloisLisseCorrespondenceData`, publicly re-exported by the original module,
to let the three component modules import their signatures without a cycle. Locally
disabled optional generated constructor injectivity and size-of specification lemmas on
four large structures after profiling their expensive p-adic unfolding. The mathematical
signatures and bodies were checked identical to the original using the declaration parser.
See `coord/changes/e4-galois-correspondence-data.md` for the full definitions and 34-user check.

Validation: all five delivered modules compile together with `lcompile.py --all`; the
item compiles in about 25 seconds. An unchanged TraceEnergy consumer also compiled
against the extracted public interface. The original theorem signature and all 46 moved
signatures and definition bodies were checked against the shared repository.

## Proved and sorry left

Closed the original upper hole `AlgebraicGeometry.Scheme.galois_lisse_representations`
by a complete compiling combination of the components below. This is a decomposition,
not an axiom-free proof: one upper hole is closed and three lower holes are added.
There are zero holes in the item module and zero in the data module.

Private helpers proved without additional holes:
`galoisUnderlyingStalkIso_germ`, `galoisLisse_iff_finiteLocallyConstant`,
`galoisLisse_closedUnderIsomorphisms`, `galoisLisse_closedUnderKernels`,
`galoisLisse_closedUnderCokernels`, `galoisLisse_abelian`,
`galoisFiniteEtaleComparison`, `galoisConstantModule_lisse`,
`galoisLisseTensorStructure`, `galois_constant_action_trivial`, and
`galoisFiniteUnit_of_evaluation`, `galoisFiniteEtale_preservesFiniteLimits`,
`galoisFLC_preservesFiniteLimits`, `galoisFiniteCarrierLift_isEquivalence`, and
`galoisFiniteCarrierComparison`, `galoisModuleObjectInternal`,
`galoisModuleObjectRestrict_isHom`, `galoisModuleObjectFunctor_fullyFaithful`,
`galoisInternal_ext`, and `galoisModuleObjectFunctor_essSurj`
(all in `AlgebraicGeometry.Scheme`). The private constructions
`galoisModuleObjectRestrict`, `galoisInternalAmbient`, `galoisModuleObjectFunctor`, and
`galoisModuleObjectEquivalence` contain no holes. Also proved
`galoisScalarMapTmul`, `galoisScalarCompTmul`, `galoisSheafScalarComp_sections`, and
`galoisSheafScalarComp_tmul`, `galoisScalarStalkIso_germ`, and `galoisProfiniteModel`; `galoisSheafScalarComp` constructs the natural composite
isomorphism without holes. `galoisScalarStalkIso` constructs the natural comparison
at the same unlifted geometric point used by the original theorem.
`galoisFiniteCarrierLift` is the actual module ULift functor with its restricted codomain;
its finiteness and open-stabilizer proofs contain no hole.

Every remaining hole, exactly one per new component module:

- `AlgebraicGeometry.Scheme.galois_finite_module_lift`
  (`new-e4-galois-finite-module-lift`, `Sheaf.Paper.GaloisFiniteModuleLift`).
  Still needs the normalized linear fibre comparison after composing the supplied
  internal-module equivalences with the known transport and reconstruction equivalences.
  The ambient-product `LambdaModuleObject` / `InternalModule` equivalence is now proved
  and supplied, including every operation and the action on underlying maps. The module/set stalk
  comparison and its formula on germs are also proved inputs. Finite products with
  their product-preserving sheaf inclusion and finite carrier universe transport are now
  proved inputs, including an isomorphism of the transported linear group actions. The two internal-module
  transport results and the lisse/module-object equivalence are already proved inputs.
- `AlgebraicGeometry.Scheme.galois_finite_tensor_scalar`
  (`new-e4-galois-finite-tensor-scalar`, `Sheaf.Paper.GaloisFiniteTensorScalar`).
  Still needs to lift the existing tensor/scalar stalk comparisons to equivariant maps
  using the normalized evaluation action, then construct the braided functor and scalar
  comparison natural isomorphisms and their representation composite identity. The actual
  scalar functors, their underlying-sheaf comparisons, their natural composite comparison
  and its section formula, sheaf braided inclusion and unit are
  supplied by the completed proof. The unlifted scalar-stalk comparison at the exact
  point used by `d.τ` and its pure-germ formula are now also proved inputs. The source
  provides the tensor comparison at the lifted point; its unlifted counterpart can be
  constructed by the same filtered-colimit/sheafification method as the proved scalar
  comparison.
- `AlgebraicGeometry.Scheme.galois_adic_from_finite`
  (`new-e4-galois-adic-from-finite`, `Sheaf.Paper.GaloisAdicFromFinite`).
  Still needs the integral inverse-system equivalence, rationalization of equivariant
  Hom and stable lattices, passage to finite coefficient models, and coherence of these
  equivalences. It assumes the complete finite correspondence and now also the proved profinite model
  and group isomorphism, which its result retains. The inverse-limit,
  finite-coefficient-field and stable-lattice declarations are its existing inputs.

## No longer needed

Moved the eight original public imports to the data module. They remain publicly
re-exported by the item's sole public data import. Removed these proof imports from
the item module:
`Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence`,
`Sheaf.CategoryTheory.EquivalenceInternalModule`,
`Sheaf.NumberTheory.Padics.AdicLimitFiniteModules`,
`Sheaf.NumberTheory.Padics.FiniteCoefficientFields`,
`Sheaf.Paper.LisseAdicSheaves`,
`Sheaf.RepresentationTheory.ProfiniteStableLattice`,
`WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`, and
`WeilConjectures.AlgebraicGeometry.LisseModuleSheaves`.
The first and last two are already exposed by existing public interfaces; the other
inputs belong to the component modules. The optional direct point-constant-sheaf import
used while developing the proof was removed because `KernelCokernel` exposes it.

`prop-weil-pbc-geometric-stalks-exact` is no longer needed for this proof: preservation of
finite limits and colimits follows directly from the finite equivalence.
`thm-galois-lc-etale` is no longer a direct proof dependency of the item because the proved
`thm-galois-fundamental` supplies its simultaneous comparison. It remains a transitive
input there. The finite module, tensor/scalar and adic inputs remain needed in their
respective components; they are not claimed globally pruned.
The new proof also uses `Mathlib.CategoryTheory.Sites.PreservesLimits` and
`WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty` for the FLC Cartesian
interface. `FiniteContinuousModule` and module ULift are public statement imports of
the finite-lift component because they describe its now supplied universe bridge.

No module is withdrawn. The direct import in the unfinished TraceEnergy parent remains:
a compile of its current partial proof would not establish that its reserved dependency
is unnecessary.

## Where the brief, the DAG or earlier work was wrong

The planned mathematical route is valid, but its module-object interfaces do not compose
by applying the advertised theorem names alone. `LambdaModuleObject` records operation
maps on products in all sheaves; `InternalModule` uses products in the full FLC category.
In addition, finite continuous-action reconstruction has carrier universe `u`, while this
correspondence requires module carriers in `u + 1`. Finite-product preservation and the carrier-universe equivalence have now been proved;
the conversion of all operation diagrams and all morphisms is now proved as well.
The normalized linear fibre comparison remains in that component. None of these interfaces is silently identified.

The automatic generation of auxiliary structure lemmas caused expensive elaboration
through p-adic norm definitions. Scoped generation options repair this without changing
any mathematical data or raising the time limit.

## New nodes

`def-pod-galois-correspondence-data-e4` records the 46 extracted data declarations;
its source, fields and normalization are those already present in the item. No new
mathematical definition is substituted. Change record:
`coord/changes/e4-galois-correspondence-data.md`.

`new-e4-galois-finite-module-lift` is steps 1 and 3: lift the given finite-set equivalence
to finite module equivalences with normalized module-stalk evaluation. It omits all
abelian, tensor, unit, scalar and adic assertions.

`new-e4-galois-finite-tensor-scalar` is steps 4 and 5 after the sheaf monoidal structure
and the unit have already been supplied. It concerns the equivariant representation
comparisons for the supplied actual balanced scalar-extension functors and the
representation composite formula. The sheaf composite comparison and its section formula
are now proved inputs.

`new-e4-galois-adic-from-finite` is steps 6–10 conditional on a complete finite
correspondence and the supplied profinite model. It constructs the three adic
equivalences with that model, the same evaluation automorphism, and the original
coherence and exactness clauses.

All four nodes inherit `sec-poincare-duality` / `sk-lem-finite`. The unit's `realized`
statement and proof-step lists are empty; no realized unit step is bypassed. Searches
of the blueprint, the existing DAG, Mathlib and the source library found no matching
normalized component theorem. The existing more general internal-module theorems are
retained as dependencies, rather than duplicated.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
