## Worker report

The delivery states `WeilConjectures.lisse_rank_one_aut` in
`Sheaf.Paper.LisseRankOneAut`. Its sole theorem has proof `by sorry`.
`WeilConjectures.rankOneScalarMap` supplies the canonical ordinary scalar map with
real data: the inverse of the unit/global-sections equivalence applied to the
identity under the Hom/global-sections equivalence. No basis, arbitrary map,
existence choice, derived object, or extra coefficient system is substituted.
The helper belongs to the scalar-map clause of this node and is included in
`lean.declarations`.

I read the current node, every statement dependency and its recorded interface,
the master blueprint item at order 1959, and the finite default in
`sk-def-purity-conv/def-pur-conventions.md`. The source proof's instruction to
multiply a given phi agrees with the already repaired node's explicit given-phi
binder. The node statement is unchanged. No new nodes or dependency repairs
are necessary.

Hypotheses and clauses are rendered as follows:

| Node text | Lean rendering |
| --- | --- |
| The finite purity conventions, including the global finite field, ell unequal to p, the finite subextension E, and n >= 1 | `P : PurityFiniteSetting.{u}`; its `field`, `coefficients`, `extension`, `finiteExtension`, `level` and `level_pos` are the recorded construction |
| Lambda = A = O_E/(varpi_E^n) | `P.Ring`; `P.Coefficient` is its recorded `ULift` to the sheaf-value universe, not another quotient |
| T a k-scheme | `T : Scheme.{u}` and `[T.Over (Spec (.of P.field.k))]` |
| T separated | `[IsSeparated (T ↘ Spec (.of P.field.k))]`; this is separatedness, without a properness assumption |
| T finite type | `[LocallyOfFiniteType ...]` and `[QuasiCompact ...]`, precisely the two recorded parts |
| Ordinary sheaves of Lambda-modules on the small pro-etale site | `L M : proEtaleRingModules T (proEtaleConstantRing T P.Ring)`; these are `SheafOfModules.{u+1}` over the constant commutative ring sheaf, with site objects in u+1 and morphisms in u |
| Local constancy | `_hL`, `_hM : IsLocallyConstantProEtaleModuleSheaf ...`; this is the existing intrinsic version publicly retained by the recorded fixed-coefficient dependency module |
| Finite and rank one | `[L.IsFiniteLocallyFreeOfRank 1]`, likewise M; its local one-element free presentations are local coefficient-line trivializations. The actual coefficient ring is finite by `Padic.finite_coefficientExtensionRing` at `P.level_pos`, so these local modules are finite, without a new finiteness hypothesis |
| Restrictions on localized sites | The original local-constancy definition uses `SheafOfModules.over`; `homObj` uses the same slice restrictions on underlying module presheaves |
| Canonical Lambda_T -> Hom(L,L), 1 -> identity, is an isomorphism | `IsIso (rankOneScalarMap L)`. The helper is defined by `unitHomEquiv.symm (homObjSectionsEquiv.symm (identity))`, which specifies the actual canonical map |
| Every endomorphism is multiplication by a unique locally constant scalar | The ring isomorphism `eL : LocallyConstant T P.Coefficient ≃+* End L`; bijectivity supplies existence and uniqueness, and its displayed action on every geometric stalk identifies the scalar with the value of that function. `eM` is the same assertion applied to M, used by clause (2) |
| Aut(L) is the group of locally constant units | `gL : LocallyConstant T P.Coefficientˣ ≃* Aut L`, together with `(gL u).hom = eL (LocallyConstant.map Units.val u)`. `gM` is the corresponding classification for M. Thus these are the actual invertible scalar maps, not unspecified abstract group isomorphisms. Locally constant unit-valued maps are exactly global sections of the unit sheaf |
| Two given isomorphisms differ by a unique unit on M | `∀ φ ψ : L ≅ M, ∃! u, ψ = φ ≪≫ gM u`; the equality is an equality of actual sheaf isomorphisms, in the composition order phi followed by multiplication on M |
| Given phi, any geometric point and any unit v | Explicit binders `φ`, `Ω : Type u`, `[Field Ω]`, `[IsAlgClosed Ω]`, `y : Spec (.of Ω) ⟶ T`, and `v₀ : P.Coefficientˣ` |
| There is psi, namely the constant-v multiple of phi | `∃ ψ, ψ = φ ≪≫ gM (LocallyConstant.const T v₀) ∧ ...` |
| psi on that stalk is v times phi on that stalk | The final equality of linear-map values uses the recorded `finiteCoefficientModuleStalkFunctor y P.Ring` on both sheaf maps and the action of `(v₀ : P.Coefficient)` |
| Integral/rational transports are separate | The only coefficient objects in the signature are P.Ring and its standard size lift; no integral, rational, completion or derived assertion is inserted |

The stalk normalization of eL and eM is not the conclusion that two arbitrary
derived maps agree on stalks. These are ordinary module-sheaf endomorphisms of
finite local systems. Scalar multiplication on an open constant-value fiber has
exactly the displayed stalk action; finite locally constant maps are determined
by those actions after local trivialization. The scalar map itself is supplied
as a concrete construction independently of the existential ring/group
isomorphisms. No arbitrary map appears as an input hypothesis.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `PurityFiniteSetting.Ring`, `PurityFiniteSetting.Coefficient`, and their ring
  instances. The full coefficient data and positive quotient level are retained.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, for the finiteness step in the proof plan.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` and `.FiniteType`:
  `AlgebraicGeometry.IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`.
- `Sheaf.Paper.ProEtaleFixedModuleLocalConstancy`: publicly imports the original
  `Sheaf.Paper.ProEtaleLocallyConstantSheaf` and its
  `AlgebraicGeometry.Scheme.IsLocallyConstantProEtaleModuleSheaf`. This original
  intrinsic interface is usable here, since the coefficient ring is exactly
  ULift P.Ring. The later fixed-module extension does not retire that definition.
- `WeilConjectures.SixFunctors.ProEtale.Derived.ModuleDerivedCategory`: the current
  source was read with `scompile.py --source`; the site's definition remains
  `AlgebraicGeometry.Scheme.ProEt` and `ProEt.topology` in Mathlib. The ordinary
  intrinsic module presentation here is `proEtaleRingModules` from
  `Sheaf.AlgebraicGeometry.ProEtaleOperations`, not a new derived-category definition.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.over`, `overFunctor`, `Hom.over`, `overMap`, and
  `overFunctorMap` give the dependency's exact slice restriction and relocalization.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`, `homObjSectionsEquiv`; its upstream presheaf implementation
  uses `PresheafOfModules.restrictOver`, `overSections`, and `sectionsSMul`.
  `Mathlib.Algebra.Category.ModuleCat.Sheaf` supplies `unit` and `unitHomEquiv`.
- `Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor`:
  `AlgebraicGeometry.Scheme.geometricRingModuleStalkFunctor` and
  `finiteCoefficientModuleStalkFunctor`. The current server source was read with
  `scompile.py --source`; these are the original pointed-neighbourhood colimits
  and their induced linear maps, restricted along the actual constant germ.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`, whose definition requires a local
  free presentation with index set equivalent to `Fin 1`, not a global basis.

The non-public proof imports supply the already stated plan of this node:
`ProEtaleSiteComparisonFiniteLevel`, `ConstantModuleLocallyConstant`,
`SiteConstantModuleFunctorGeneral`, `SiteCoveringAxioms`, and Mathlib
`Sites.LocallyBijective`; their prerequisites supply the comparison adjunction,
sheafification, small etale site and open immersions being etale. They are retained
for stage 3 as required by stages/2-statements.md rule 7.

Edge cases checked before drafting:

- Empty T: both locally constant function rings and the endomorphism rings of
  the unique sheaf are one-element rings; the unit and automorphism groups are
  trivial. There is no geometric point for the final quantified clause. No
  nonemptiness or connectedness binder is present.
- A geometric field spectrum: the assertion becomes End(L) = Lambda and
  Aut(L) = Lambda units, with the ordinary one-dimensional scalar action.
- Two disconnected components: LocallyConstant permits distinct scalars and
  distinct units on the two components; it is not replaced by Lambda itself.
- A nontrivial rank-one local system: the canonical scalar map uses no chosen
  global basis and the hypotheses require only local trivializations.
- Nonfield coefficients, e.g. a positive second quotient level: every nonunit
  gives an endomorphism but no automorphism; gL/gM have unit-valued domain.
- A pair of nonisomorphic L,M: the final clause quantifies over an existing phi,
  so it does not force an isomorphism between an arbitrary pair.
- n = 1 is included. n = 0 is outside the source's positive-level convention,
  retained inside P; no independent restriction on coefficient characteristic is added.
- Universes: the small site still has object universe u+1 and morphism universe u.
  The scalar helper's module/ring universe is the maximum of the two site universes;
  in the theorem that is exactly u+1. No equality of site universes is imposed.

Searches actually run using `msearch.py` (the raw records are in searches.jsonl):

1. LeanFinder, “endomorphisms and automorphisms of locally constant rank one
   sheaves are locally constant scalars and units”: 8 hits concerning condensed
   locally constant module functors and `LocallyConstant.congrRightₗ`; none states
   the ordinary rank-one sheaf assertion.
2. Loogle, `SheafOfModules.homObj, SheafOfModules.unit`: query error, unknown
   identifier `SheafOfModules.homObj`. This failed query is not evidence of absence.
3. Mathlib grep `rank.?one|[Aa]utomorphism|scalarMap` in
   `Algebra/Category/ModuleCat/Sheaf`: 0 hits. The actual unit/global-sections
   equivalence and local-freeness source were separately opened and reused.
4. LeanSearch, “canonical scalar map from a commutative coefficient sheaf to
   endomorphisms of a locally free rank one sheaf is an isomorphism”: 8 hits,
   including `LinearEquiv.smul_id_of_finrank_eq_one`, scheme structure-sheaf
   global sections, and module sheafification scalar formulas. None gives the
   site's local-to-global result, its locally constant global scalars and both
   isomorphism assertions.
5. Direct rg of the upstream tree for the item id found no declaration.
   Concept searches for `Lisse|lisse|rank.one|RankOne|lem_pur_lisse` found the
   local rank-one evaluation computation in `Presheaf.InternalHom`, which was
   read, and distinct adic lisse results. These are ingredients, not duplicates.
6. Direct rg in `lean/Sheaf` found `PurityFiniteSetting.a1RankOne` in
   `AffineLineInvariance`; it is only a predicate combining local constancy with
   the existing finite-locally-free rank condition. The current file uses those
   existing ingredients on the intrinsic encoding, without redefining rank one.
7. The item-id hit in side upstream `Purity/Smooth/Deformation.lean` was opened:
   it is a docstring citation in `existsUnique_iso_sectionInvariant_normalCone`,
   not a declaration of this scalar/Hom assertion.
8. Direct name searches for `rankOneScalarMap|lisse_rank_one_aut` in Mathlib,
   upstream, the project and the upstream-name index found no prior declaration.

No mathematical statement fault or dispute was found. The previous attempt had
left no delivery files; this worker supplies the missing module, node record and
report. Compilation and the required dry run are recorded below when complete.

Validation: the final `scompile.py NK lem-pur-lisse-rank-one-aut` invocation
passed both the sandbox check (41.9 s) and the library-path check (31.1 s), with
no errors or warnings. The scalar helper uses the maximum of the site universes
so that ordinary Hom stays in the coefficient/module universe; no site or
statement restriction was added. Every Lean line is at most 100 characters,
`autoImplicit` is false, the sole theorem has a sorry proof, and the primary
signature in the node record is verbatim from the module. The only changed node
field is `lean`.


## Second reading by NK

I independently read the current DAG statement and all seven proof steps, the
sandbox Lean file, each statement dependency's record and the actual interfaces
used below. The source blueprint is order 1959,
`sec-smooth-purity/sk-prop-a1-inv/lem-pur-lisse-rank-one-aut.md`; I read it and
`sk-def-purity-conv/def-pur-conventions.md` in the available literature mirror
`/home/ubuntu/work-bp/sheaf/literature/blueprint/master/blueprint/` (the same
paths are absent from this machine's shared checkout). The source's final
sentence refers to the given phi, as made explicit in the already reviewed DAG;
its proof explicitly multiplies that phi. The chapter defaults to the finite
quotient A; the integral/rational transports are separate. I also read Stacks
`sites-modules.tex`, `lemma-internal-hom-restriction` (0E8H), and `proetale.tex`,
`lemma-fully-faithful` (099T), in the literature mirror. The former applies to
any ringed site and imposes no extra finite-presentation hypothesis; the latter
applies to any scheme. No unmentioned Noetherian, connectedness, properness,
nonemptiness or coefficient-field hypothesis is needed.

My object/hypothesis/conclusion checklist, made from the node before comparing
it with Lean, is as follows. All entries pass.

| Node object, hypothesis or conclusion | Lean rendering and reading verdict |
| --- | --- |
| Global finite-field datum, coefficient prime ell different from p, finite E inside the fixed algebraic closure, positive integer n | `P : PurityFiniteSetting.{u}`. I opened `PurityFiniteSetting`, `FiniteFieldDatum` and `CoefficientDatum`: the fields retain the actual finite field, algebraic closure, `different : l ≠ p`, finite-dimensional intermediate field and `level_pos : 1 ≤ level`. Pass. |
| Lambda is the ordinary quotient O_E/(varpi_E^n), in the finite setting | `P.Ring` unfolds to the recorded `Padic.coefficientExtensionRing`; `P.Coefficient` is exactly its `ULift` to u+1, with the transported commutative ring structure. Finiteness is supplied by the imported positive-level theorem, not an added hypothesis. Pass. |
| A k-scheme T | `T : Scheme.{u}` and `[T.Over (Spec (.of P.field.k))]`. The base and structure morphism are the specified ones. Pass. |
| T separated and of finite type | `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` on `T ↘ Spec (.of P.field.k)`. I read the Mathlib classes: respectively closed-immersion diagonal, affine-local finite-type algebra maps, and quasi-compact underlying map. The latter two are exactly finite type; there is no properness assumption. Pass. |
| L and M ordinary coefficient-module sheaves on the small pro-etale site | `L M : proEtaleRingModules T (proEtaleConstantRing T P.Ring)`. I opened these abbreviations: they are `SheafOfModules.{u+1}` over the actual sheafification of the constant commutative ring, on `Scheme.ProEt` with `ProEt.topology`. No derived object occurs. Pass. |
| Both sheaves locally constant | `_hL` and `_hM : IsLocallyConstantProEtaleModuleSheaf ...`. I read the original ringed-site definition, retained by public import of the dependency's newer fixed-coefficient module. It quantifies over a pro-etale covering and module sheafifications on the localized sites; the constant module may depend on the member. This is the dependency's original usable encoding for the current coefficient ring, not a private replacement. Pass. |
| Finite, with rank one meaning locally the coefficient line | `[L.IsFiniteLocallyFreeOfRank 1]` and the same for M. I read `IsFiniteLocallyFreeOfRank`, `IsLocallyFreeData` and `freeUniqueIso`: local generator maps are isomorphisms, with generator index equivalent to `Fin 1`. Thus this is local, not global, freeness of rank one. The coefficient ring is finite, so these local coefficient lines have finite underlying modules. No additional finite-dimensional-vector-space assumption is inserted. Pass. |
| Restrictions on the localized ringed site | The local-constancy predicate uses `F.over U`; `SheafOfModules.over`, `Hom.over`, `overMap` and `overFunctorMap` were read in Mathlib. They give exactly the slice restrictions and relocalization in the node. Pass. |
| Ordinary internal Hom | `SheafOfModules.homObj` in the scalar helper. I read its source and `homObjSectionsEquiv`: the underlying sections are linear morphisms of restrictions on slices, and global sections are actual sheaf maps. Pass. |
| Canonical map Lambda_T to Hom(L,L), sending 1 to id, is an isomorphism | `IsIso (rankOneScalarMap L)`. The helper is real data: `unitHomEquiv.symm (homObjSectionsEquiv.symm (𝟙 L))`. The actual `unitHomEquiv_apply_coe` formula evaluates at 1, so this specifies the canonical scalar map, rather than assuming some isomorphism. Pass. |
| Every endomorphism is multiplication by a unique locally constant scalar | `eL : LocallyConstant T P.Coefficient ≃+* End L`, together with its formula on every geometric stalk. Bijectivity supplies existence and uniqueness, and the formula specifies which scalar endomorphism it is. `eM` is the same conclusion applied to M, as used by the source proof. These are finite local systems, so their geometric fiber actions identify their maps; this does not claim arbitrary pro-etale sheaves or derived maps are detected by geometric points. Pass. |
| Aut(L) is the group of locally constant units | `gL : LocallyConstant T P.Coefficientˣ ≃* Aut L`, with `(gL u).hom = eL (LocallyConstant.map Units.val u)` written with an explicit coercion lambda. It is the scalar-unit action, not an unnormalized abstract group isomorphism. `gM` renders the application to M. Locally constant unit maps are precisely sections of the coefficient unit sheaf. Pass. |
| Any two given phi, psi differ by a unique unit acting on M | `∀ φ ψ : L ≅ M, ∃! u₀, ψ = φ ≪≫ gM u₀`. The composition means phi followed by the scalar automorphism of M. Equality is of actual isomorphisms and uniqueness is for the whole locally constant function. Pass. |
| Given phi, every geometric point and every coefficient unit v | The final quantifiers bind `φ : L ≅ M`, then `Ω : Type u`, `Field Ω`, `IsAlgClosed Ω`, `y : Spec (.of Ω) ⟶ T` and `v₀ : P.Coefficientˣ`. The geometric field is in the prescribed bound of the recorded stalk construction. Pass. |
| There is psi, specifically the constant-v multiple of phi, with the required stalk action | `∃ ψ, ψ = φ ≪≫ gM (LocallyConstant.const T v₀) ∧ ...`. The remaining equality evaluates the two maps of `finiteCoefficientModuleStalkFunctor y P.Ring` on every vector x, giving exactly multiplication by v. I opened the functor and `proEtaleConstantRingGerm`: it uses pointed-neighbourhood colimits and restriction along the actual constant-section germ. Pass. |
| Integral and rational coefficient transports are outside this assertion | Only the finite quotient and its standard universe lift occur in the signature. Pass. |

Edge cases were checked independently. For empty T the coefficient-function ring
and endomorphism ring are singleton rings and both groups are trivial; the
geometric-point clause is vacuous. No nonemptiness binder excludes this case.
On disconnected T the locally constant scalar and unit functions may vary by
component. For a nontrivial rank-one local system only local generators are
required. For nonisomorphic L and M the last clause is conditional on an existing
phi, so it creates no isomorphism between them. The zero sheaf on a nonempty T
with this nonzero positive-level coefficient ring does not satisfy the rank-one
hypothesis; the zero sheaf on the empty scheme is included. Both n=1 and higher
levels, including nonfield quotients, are covered; n=0 is excluded by the source's
own convention. Nonunits belong to eL's domain but not gL's. The characteristic
condition is the existing `CoefficientDatum.different`. The site has objects in
u+1 and morphisms in u, module values in u+1; `rankOneScalarMap` uses `max v w`
so its Hom stays in that universe. No site-universe equality, extra instance
assumption, or unbound universe/variable occurs. The final field universe is
exactly the chosen bound in the geometric-stalk node.

I independently searched with alternative words, using the required wrapper:

- LeanFinder: “Endomorphisms of an invertible module sheaf are scalar
  multiplication; its automorphisms are units of global sections”. Eight hits
  concern the Picard group of ordinary semimodules; none is this sheaf theorem.
- Loogle: `"SheafOfModules", "unitHomEquiv"`. Eight hits give the actual unit
  and sections equivalence and its formulas. I opened and reused this API;
  none states the rank-one local-to-global result.
- Grep: `IsInvertible|endomorphism|scalar` in
  `Algebra/Category/ModuleCat/Sheaf`. Ten hits concern scalar restriction;
  they do not state the theorem.
- LeanSearch: “The automorphisms of a rank one locally constant sheaf of
  modules are the locally constant units of its coefficient ring”. Eight hits
  include `ContinuousLinearEquiv.unitsEquivAut`, condensed discrete modules
  and `SheafOfModules.unit`; these are distinct categories or ingredients.
- Direct rg on the source project and `lean/Sheaf`, with
  `rankOneScalarMap|lisse_rank_one_aut|lem-pur-lisse-rank-one-aut` and
  endomorphism/automorphism patterns using “invertible” and “line”, found
  `Scheme.Modules.exists_eq_smulHom` and its faithfulness lemma in
  `AlgebraicGeometry/Modules/Endomorphism.lean`, and their pseudofunctor forms
  in `Picard/TwistedDescent.lean`. I opened them: they concern O_X-modules on
  the Zariski site of a scheme, not modules over the constant finite ring on
  the small pro-etale site, and cannot replace this statement. The other
  derived invertible-object result is also a different assertion. No exact
  name collision was found, including in `dag/lean_names_upstream.json`.

No new nodes or dependency modules are present, so there are no additional
stage-1 definitions or dependency repairs to review. The helper scalar map is
part of this node's explicit construction and appears in `lean.declarations`.
It has no sorry data or choice from an unspecified existence theorem. The only
theorem is `lisse_rank_one_aut`, with whole proof `by sorry`. Its seven-step
docstring follows the seven DAG steps, including evaluation at 1, sheaf gluing,
constant-label-compatible comparison, global functions, units, and cancellation
of the given phi. Every declaration has its source and blueprint tag. Imports
include the statement interfaces and the stated proof dependencies; all Lean
lines are at most 100 characters and `autoImplicit` is false.

Mismatches and changes: none found in the Lean or the node. I preserved both
verbatim and appended this independent reading only. Comparing the delivered
node with the shared node confirms that only the authorized `lean` field differs;
there is no new `statement_change` and no citer audit is required. A direct
signature comparison confirms `lean.statement` is verbatim the file signature.

Validation: I ran `scompile.py NK lem-pur-lisse-rank-one-aut` with the absolute
sandbox path. Both single-file checks passed cleanly: sandbox 9.3 seconds,
library path 15.5 seconds; no errors or warnings. My first wrapper invocation
used a relative path from the shared checkout; it failed to locate the sandbox
file before compilation. The absolute-path invocation above corrected that
invocation error without any source change. The prescribed delivery dry run and
push are recorded below after completion.

Delivery validation: `deliver2.py NK lem-pur-lisse-rank-one-aut --no-push`
printed `OK (dry run)` at temporary commit `e6edc61763`: the preflight and
compilation passed, with exactly the report, item node and one module staged.
