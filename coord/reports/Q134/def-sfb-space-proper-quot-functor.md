## Worker report

Q134 states def-sfb-space-proper-quot-functor in
`Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor`, main declaration
`AlgebraicGeometry.AlgebraicSpace.properQuotFunctor`.

Source read: Stacks `quot.tex`, Tag 09TR, `situation-quot`, and
`spaces-perfect.tex`, Tag 0CZI, `lemma-module-support-proper-over-base`, especially
clause (3). The source's printed `X ×_S T` in the pullback sentence is the typo
already corrected to `A ×_B T` by the accepted DAG statement. No further statement
correction is needed. No node is disputed and no new node or dependency repair
is delivered.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Base scheme and arbitrary algebraic spaces over it: `S : Scheme.{u}`,
  `A B : AlgebraicSpace S`, and `a : A ⟶ B`. No scheme-source restriction.
- Finite presentation of a: `ha : ProperQuotFinitePresentation a`, defined as
  `MapIsLocallyOfFinitePresentation a ∧ MapIsQuasiCompact a.hom.hom ∧
  MapIsQuasiCompact (Limits.pullback.diagonal a.hom.hom)`. The last conjunct is
  precisely quasi-separatedness. No properness, flatness or separation is assumed.
- Quasi-coherent F: `F : A.QCoh`; the underlying module is `F.obj`, with the
  existing full-subcategory predicate `F.property`. It need not be finite type
  or finitely presented.
- Test schemes T → B: `ProperQuotTest B = CostructuredArrow yoneda B.obj.obj`.
  Its objects retain an S-scheme `T.left : Over S` and its specified map
  `T.hom : yoneda.obj T.left ⟶ B.obj.obj`. Arrows are exactly S-scheme maps
  commuting with these B-maps. `properQuotTestMap` embeds the same natural
  transformation in algebraic-space morphisms.
- Actual sheaf fibre product A_T: `properQuotFibre a T` bundles
  `Limits.pullback a.hom (properQuotTestMap T).hom` with the already recorded
  algebraic-space closure theorem. `properQuotFst` and `properQuotSnd` are its
  actual first and second projections.
- Module F_T and surjection: `ProperQuotient.quotient` has source
  `(moduleTensorPullback (properQuotFst a T)).obj F` and target
  `ProperQuotient.target`. `ProperQuotient.surjective : Epi quotient` expresses
  sheaf surjectivity, which is locally surjective rather than sectionwise
  surjective on every object. The module category is the existing small-etale
  `Modules`, not a copied category.
- Quasi-coherent Q: field `quasicoherent : target.IsQuasicoherent`, Mathlib's
  local arbitrary-free presentation predicate specialized by the recorded QCoh
  module. Finite presentation: field `finitePresentation :
  target.IsFinitePresentation`, Mathlib's local finite-free presentation
  predicate, read in `Sheaf/Quasicoherent.lean:265`.
- Flatness over T: field `flat`, for every `U : (properQuotFibre a T).EtaleSite`,
  applies `Scheme.Modules.IsFlatOver` to the actual `schemeRestriction` of Q
  and the scheme map obtained by `yoneda.preimage` of U → A_T → T. For
  quasi-coherent Q this is equivalent to flatness at every ordinary stalk over
  the corresponding local ring of T. This is the same exact interface as the
  recorded base-change dependency; no unrelated flatness predicate is introduced.
- Proper support: field `properSupport` existentially retains Z and i, with
  `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom`,
  `MapIsProper (i ≫ properQuotSnd a T)`, and G with `G.IsQuasicoherent`,
  `G.IsFiniteType`, and `Nonempty ((moduleDirectImage i).obj G ≅ target)`.
  Thus it is the specified closed-carrier convention, including all finiteness
  requirements, using canonical direct image rather than an arbitrary functor.
- Isomorphism classes of surjections: `ProperQuotientRel` means
  `∃ e : q.target ≅ r.target, q.quotient ≫ e.hom = r.quotient`.
  `ProperQuotClasses` is `Quot` of this relation. The relation is already an
  equivalence: identity, inverse and composite isomorphisms intertwine the
  arrows. Consequently taking its equivalence closure adds no identifications.
  In particular the relation remembers the quotient map, not just the target.
- Base-change transition for every T' → T: `properQuotFibreMap` is the actual
  pullback map with components identity on A and the given scheme map on T.
  `properQuotSourceIso` is the existing `moduleTensorComposition` component
  followed by transport along the first-projection equality; it identifies
  `(F_T)_T'` with `F_T'` using the canonical tensor associator. The arrow
  `properQuotPullbackArrow` is its inverse followed by tensor pullback of q.
  `properQuotPullback` uses exactly this arrow and the actual pulled target.
- Preservation of the target conditions: named theorem
  `properQuotPullback_properties` asserts epimorphicity plus all four clauses
  on those specific objects. Its full proof docstring reproduces the accepted
  chart argument establishing A_T → T locally of finite type: choose V → B
  and U → A ×_B V, use lfp ⇒ lft, base-change the charts to T, use the
  Mathlib lft base-change instance and `local_properties_chart_test`. It then
  applies `moduleTensorPullback_flat_properSupport_baseChange` and uses left
  adjoint right exactness for the actual surjection. No extra condition on h.
- Descent to classes: `properQuotPullback_rel` uses the pulled target
  isomorphism and naturality of the source comparison. `properQuotMap` is
  `Quot.map` of the constructed pullback, using this proof obligation.
- Identity and composition: named `properQuotMap_id` and
  `properQuotMap_comp` assert the function identities on classes, using tensor
  unit and associativity and the uniqueness of pullback maps. The final
  `properQuotFunctor` uses these proof fields, with `TypeCat.ofHom` wrapping
  the explicit transition functions.
- Size convention: all universe variables are explicitly declared; `autoImplicit`
  is false. Test schemes and algebraic spaces retain the original universe u;
  the type of module-sheaf quotient objects and its isomorphism classes lies
  in `Type (u+1)`, the allowed larger universe. There is no imposed equality
  of independent site and coefficient universes, no index restriction, and no
  assumption that the quotient collection is inhabited.

Dependency declarations read and used (public imports are explicit):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `Scheme.Hom`; `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `IsClosedImmersion`; `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `locallyOfFiniteType_isStableUnderBaseChange` (proof plan).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `IsRepresentableWith`, `EtaleSite`, `Modules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, with the etale-cover base-change theorem
  used in the supporting proof plan.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocallyOfFinitePresentation`, `MapIsProper`, and its inherited
  `MapIsQuasiCompact` from `ProperCurveModuli`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, the public
  general-site alias for the same Mathlib `SheafOfModules` used by `Modules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`,
  its Mathlib `SheafOfModules.IsQuasicoherent` predicate and the recorded slice
  instances; Mathlib `IsFinitePresentation` and `IsFiniteType` are reused.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `moduleTensorPullback` and `moduleDirectImage`, with their specified units.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `AlgebraicGeometry.Scheme.Modules.IsFlatOver` (full affine-local signature and
  stalkwise-equivalence docstring read).
- `Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest`:
  `local_properties_chart_test` (proof plan for preservation).
- `Sheaf.AlgebraicGeometry.SpaceModuleBaseChangeFlatProperSupport`:
  `moduleTensorPullback_flat_properSupport_baseChange` (full signature and
  proof docstring read; its four conclusion clauses exactly match the fields).
- Added existing dependency `def-trf-space-module-scheme-restriction`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`: `schemeRestriction`.
- Added existing definition dependency `def-trf-scheme-algebraic-space`, module
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`:
  `AlgebraicGeometry.AlgebraicSpace.schemeSpace`, retaining the actual
  representable-scheme sheaf. Its owner record is Q87, 2026-10-18, existing:true.
- Added existing dependency `def-sfb-space-module-tensor-composition`, module
  `Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange`:
  `moduleTensorComposition` and its unique local-tensor normalization.

These three additions are already landed nodes, allowed by the stage-2
stmt_deps extension rule. Their records and sources are not modified.
`def-weil-size-convention` is metatheoretic, with no module or object to import.
No proof-dependency import is missing: the item's proof_deps is empty.

Edge cases checked mathematically before finalizing the declaration:

- Empty A, empty B/test bases, and empty base changes are allowed by every
  binder and by the genuine sheaf fibre products; no Nonempty hypothesis occurs.
- The zero quotient F_T → 0 is allowed: zero is quasi-coherent, finitely
  presented and relatively flat, and it is carried by the empty closed subspace.
- F = 0 permits its zero quotient; the class construction imposes no accidental
  nonzero-rank or nonempty-support requirement.
- Identity T → T is handled on isomorphism classes, not by asserting a false
  definitional equality of separately chosen tensor pullback objects.
- Composable arbitrary, including nonflat, scheme maps are permitted. Tensor
  preserves epimorphisms even when it does not preserve arbitrary monomorphisms.
  A finite proper flat quotient base-changed from Z to F_p remains admissible;
  the quotient O/p over Z itself fails the required relative flatness.
- Two maps with the same target but different kernels are identified only when
  an isomorphism actually intertwines the surjections. Different choices of
  carrier (Z,G) are merely proofs of the existential support property.
- All six named theorem proofs are sorry, as required for stage 2. Every one
  has the source, blueprint tag, and complete natural-language proof plan in its
  docstring. Every definition's data is explicitly built; only proof fields
  refer to these named obligations.

Searches executed for an existing definition (no exact match):

- msearch leanfinder: `Quot presheaf isomorphism classes of surjective quotients
  of a quasi coherent sheaf flat finite presentation proper support`. Eight
  hits, all module presentations/quasi-coherence, not this moduli presheaf.
- msearch loogle: `"Quot", "sheaf"`. Four hits, all total quotient ring
  presheaves, not Quot moduli.
- msearch grep: `QuotFunctor|quotFunctor|properQuot|QuotPresheaf`. Zero hits.
- msearch leansearch: `Quot scheme presheaf of flat finitely presented module
  quotients with proper support`. Eight hits, module sheaves/presentations and
  module flatness; no Quot functor.
- rg of the source `lean/WeilConjectures` and project `lean/Sheaf` for
  `quot.*(functor|presheaf)|properQuot|quotient.*(setoid|surjection)` found only
  unrelated homotopy/integral-coefficient quotient constructions and total
  quotient rings. rg for the exact blueprint id in upstream returned no hits.
- Targeted rg for `moduleTensorPullback.*([Cc]omp|[Ii]d)` found the already
  existing canonical comparisons. They are reused rather than redefined.
- Targeted rg for `MapIsFinitePresentation` and the finite-presentation
  conjunction found expanded uses in other statement modules, but no existing
  algebraic-space finite-presentation predicate to duplicate.

Validation: prescribed `scompile.py` compiled the module twice (sandbox and
library module name), clean, in 3.7 and 4.0 seconds, after fixing the pullback.map
orientation and wrapping function maps with TypeCat.ofHom. All statements have
explicit binders, all lines are at most 100 characters. The dry-run and final
wrapper checks are recorded below after execution.

## Second reading by Q134

This is a self-check, not an independent agent review: the dispatcher's explicit
instruction forbids starting other agents. The maintainer performs the independent
review. I re-read Stacks 09TR and 0CZI(3), the accepted node, and the final module.
The main binder `F : A.QCoh` preserves arbitrary quasi-coherent F. The finite
presentation hypothesis includes both quasi-compactness and quasi-compact diagonal.
Each target field agrees with the node and with Q133's base-change interface.
In particular flatness is on actual chart restrictions through the given map
U → T, and proper support retains finite type G, a representable closed immersion
and its canonical pushforward. The relation intertwines arrows, and transitions
have F_T' as source through the previously normalized tensor comparison. No
condition was added on h, and no empty case was excluded. The initial compile
exposed only a reversed projection-compatibility equality and Lean's bundled
Type morphisms; both were corrected without changing the mathematical statement.
The three existing dependency additions name exactly the constructions used.

Delivery validation: `deliver2.py Q134 def-sfb-space-proper-quot-functor
--no-push` returned `OK (dry run)` at commit `1df6726b94e`: server preflight
passed and the module compiled cleanly under both required module names. Only
this module, the item's node record, and this report were staged.

## Returned delivery repair (2026-10-24)

The independent review of immutable head `336a23f6277b` returned H2: the
additional dependency `lem-trf-space-enlarged-etale-ringed-site-model` was used
only for `AlgebraicGeometry.AlgebraicSpace.schemeSpace`. The landed definition
node `def-trf-scheme-algebraic-space` owns precisely that construction. I read
its statement and Lean ownership record and the full `schemeSpace` declaration
and docstring in `EnlargedEtaleRingedSite`. The repair replaces that extra
theorem dependency with the existing definition node and replaces the direct
`AtlasEtaleRestriction` import with `EnlargedEtaleRingedSite`. Relative to the
current base, all original statement dependencies remain and the three extra
landed definition dependencies are added. This does not remove any dependency
from the base or change the mathematical statement, proof or proof dependencies.

The saved packet was retained and its required initial dry run returned
`OK (dry run)` at `658a5cb5373`. That validation preceded this repair; the repaired
packet is compiled and dry-run again before delivery. The wrapper rebases the
delivery on current main without direct Git commands in the shared repository.

Repair self-check by Q134: I reopened the node and the complete module. The
only Lean change is the owning module import; every declaration and binder is
unchanged. `schemeSpace T.left` still has exactly the actual Yoneda sheaf
specified by the definition node. Empty test schemes, the zero quotient,
identity transitions and arbitrary nonflat transitions retain the cases checked
above. The inline quasi-separatedness conjunct remains the node's exact
quasi-compact-diagonal condition. This reading is a self-check; the maintainer
provides the independent review.

Repair validation: prescribed `scompile.py` compiled the repaired module under
both sandbox and library names without errors or warnings (4.7 s and 3.5 s).
A local field comparison against the current read-only base verified that only
`lean` and the three added landed definition dependencies differ; the recorded
main signature is verbatim and every Lean line is at most 100 characters.
