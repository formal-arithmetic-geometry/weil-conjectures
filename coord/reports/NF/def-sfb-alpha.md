## Worker report

Bound def-sfb-alpha to the existing declaration
`AlgebraicGeometry.ProEtale.condensedPullbackHom` in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, without a new module.
The source is the current main-20261015 blueprint,
`sec-proetale-coefficients/sk-def-sfb-coefficient-morphisms/def-sfb-alpha.md`
(order 1559). Both the shared framework source and the published source returned by
`scompile.py --source WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
were read, including the surrounding binders, docstrings and construction bodies.
The published source agrees on this definition; some supporting proofs are newer.
Only the item's `lean` field changes.

Clause-by-clause correspondence:

- A condensed ring Λ is `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`
  with `[MonObj Λ]`, the unbundled ring-object encoding. No commutativity is assumed.
  The arrow itself does not use the ring operations, so Lean may omit this unused
  section instance from its elaborated parameters; specializing to any ring object
  gives exactly the required arrow.
- Arbitrary schemes and their morphism are the section parameters
  `{X Y : Scheme.{u}} (f : X ⟶ Y)`. There is no finiteness, étaleness, nonemptiness,
  separation, or characteristic restriction on f, X, or Y.
- The source `f^* Λ_Y = f^* p_Y^* Λ` is
  `(f)^*[Ab.{u + 1}].obj (condensedRingObj Λ Y)`.
  The source uses pullback on abelian pro-étale sheaves, not module pullback.
- The target `p_X^* Λ = Λ_X` is `condensedRingObj Λ X`, whose defining body is
  `(upperStarFromPoint X).obj Λ`.
- The required component of the specified natural isomorphism is the actual body
  `Functor.compAlgHom (upperStarFromPoint Y) (f)^*[Ab.{u + 1}]
  (upperStarFromPointComp f).hom Λ`.
  `CategoryTheory.Functor.compAlgHom` in
  `WeilConjectures.CategoryTheory.ModuleObjects.MapMod` is literally the abbreviation
  `τ.app R`. Thus this is definitionally `(upperStarFromPointComp f).hom.app Λ`,
  with the specified direction, rather than a chosen or arbitrary morphism.

Dependency declarations used:

- `def-sfb-pullback-from-point-comp-iso` records
  `AlgebraicGeometry.ProEtale.upperStarFromPointComp` in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.
  Its signature is `upperStarFromPoint Y ⋙ (f)^*[Ab.{u + 1}] ≅ upperStarFromPoint X`.
  Its body is the functor associator followed by whiskering the inverse
  `upperStarComp Ab.{u + 1} f (toSpecZ Y)` and the equality identification coming
  from `comp_toSpecZ f`, exactly the dependency's specified comparison.
- `sk-def-sfb-pulled-back-coefficients` records
  `AlgebraicGeometry.ProEtale.coefficientRing`, `coefficientRing_X`,
  `condensedRingObj` and `isCommMonObj_condensedRingObj` in that same module,
  together with Mathlib's `CategoryTheory.Functor.monObjObj`, `mapMon` and
  `isCommMonObj_obj`. Their full signatures and docstrings were read in the
  framework and Mathlib's `CategoryTheory/Monoidal/Mon.lean` and `CommMon_.lean`.
  For the bundled ring `Mon.mk Λ`, `(coefficientRing X (Mon.mk Λ)).X` and
  `condensedRingObj Λ X` both reduce to `(upperStarFromPoint X).obj Λ`.
  This uses the dependency's actual ring objects and their transported structure.

Edge cases checked by reading the unrestricted parameters and actual construction:
identity morphisms still give the specified comparison component (with its canonical
identity-pullback identification); empty schemes impose no excluded cases; zero rings
and noncommutative rings are allowed because no nontriviality or commutativity instance
is required. Universes are the same `Scheme.{u}`, `Profinite.{u}` and `Ab.{u + 1}` as
the two dependencies. There is no smaller test universe or extra universe equality.
No statement correction, new node, dependency repair, hollow definition or dispute.
The existing term is fully constructed; no theorem or proof is added by this delivery.
Underlying prerequisites that remain postponed in the library are left as they are.

Searches (2026-10-18):

- `msearch.py NF def-sfb-alpha leanfinder`: query
  `coefficient morphism alpha_f from pullback of condensed coefficient ring given by
  component of point pullback comparison`; eight hits, including
  `LightCondensed.ihom_map_val_app`, `Condensed.underlying_map`,
  `LightCondensed.ihomPoints_symm_comp` and `TopCat.continuousFunctions.pullback`;
  none constructs the scheme-specific comparison component.
- `msearch.py NF def-sfb-alpha loogle`: query
  `CategoryTheory.NatTrans.app, CategoryTheory.Functor.obj`; twelve generic component
  and naturality hits, including `NatTrans.app` and `NatTrans.naturality`, not the
  pro-étale coefficient morphism.
- `msearch.py NF def-sfb-alpha leansearch`: query
  `coefficient morphism pullback condensed ring sheaf natural isomorphism component`;
  eight hits, including `SheafOfModules.freeFunctorCompPullbackIso`,
  `CondensedMod.LocallyConstant.functorIsoDiscrete` and `PresheafOfModules.pullbackComp`;
  none is this definition.
- `msearch.py NF def-sfb-alpha grep` on Mathlib: query
  `condensedPullbackHom|coefficientPullbackIso|upperStarFromPointComp`; zero hits.
- `rg -n` with that same pattern on the named slopmaster2 `WeilConjectures` tree,
  and `grep -rn def-sfb-alpha` there: zero hits. The module is absent from that
  older checkout, as expected from `coord/pefw-upstream-framework.md`.
- `rg -n` with the same pattern on `lean/Sheaf`: uses in
  `Paper/ProfinitePointPullback.lean` and
  `Compactification/NagataDensityNormalization.lean`, not another definition.
- Reading the item's `lean_audit.slopmaster2.decls` and searching the published
  side framework finds the exact existing declaration in `ModuleObject/Basic.lean`.
  `rg` on `dag/lean_names_upstream.json` gives no stale-index match; the actual
  source and `scompile.py --source` confirm the declaration and its dependencies.
- `rg` for `compAlgHom` on Mathlib and the named project source trees finds its
  definition in the published `CategoryTheory/ModuleObjects/MapMod.lean`.

Validation: `deliver2.py NF def-sfb-alpha --no-push` passed: its generated `#check`
probe compiled against the published library, and the maintainer's server preflight
printed `OK (dry run): commit 217e299c8a passes the preflight and compiles; nothing pushed`.
The push invocation repeats these checks. No new Lean module is delivered because
this packet only binds an existing declaration.

## Second reading by NF

No independent second reading by a worker: the dispatcher requires this worker to
finish and deliver directly, without starting another agent. The maintainer's
independent review reads the delivery. The author reread the item, both dependency
records and the exact source bodies: the coefficient sheaf, arbitrary morphism,
source, target, comparison direction and defining component all agree, with no
mismatch or statement change.
