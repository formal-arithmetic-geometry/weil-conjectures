## Worker report

The delivery states `AlgebraicGeometry.directImageHom_openExt` in
`Sheaf.AlgebraicGeometry.DirectImageHomOpenExt`. Its sole postponed proof is `sorry`.
The auxiliary declarations are explicit constructions, abbreviations for recorded
objects, and the representative-normalization predicate for the implicit canonical
Ext identifications. No auxiliary existence theorem chooses arbitrary data.

I read the node and its eight proof steps, its six statement dependencies and their
Lean signatures/docstrings, and Stacks `cohomology.tex` at
`remark-projection-formula-for-internal-hom` (0B69),
`lemma-section-RHom-over-U` (08DK), `lemma-restriction-RHom-to-U` (08DL),
`lemma-restrict-direct-image-open` (08FE), and `lemma-Leray-unbounded` (0D5W).
The published CompactObject example is now a withdrawn module with no declarations;
this module uses the current `module`, public-section, source-docstring conventions.
This delivery repairs maintainer return L on immutable head e34b529f3f0b (H4/H12).

The hypothesis and clause correspondence is as follows.

| Node text | Lean rendering |
| --- | --- |
| Any morphism of schemes f:X→Y | `∀ {X Y : Scheme.{u}} (f : X ⟶ Y)`; no property instance on f |
| Unbounded derived module categories | The shared `schemeDerivedCategory` on `SheafOfModules (moduleRings ...)`; no QCoh, boundedness, compactness, properness, or flatness binder |
| E,N arbitrary in D(O_X) | Every comparison and its equations quantify over `E N : schemeDerivedCategory X` |
| Rf-star and internal RHom | Recorded `schemeDerivedDirectImage` and `derivedInternalHom`, the latter only abbreviated by `sfbRHom` |
| Canonical comparison c from evaluation | `sfbDirectImageHomComparison` in the new definition module selects the component of `Classical.choose (exists_mixedHomDirectImageComparison f)`. This is exactly the construction of the published `mixedHomDirectImageComparison`, with no recomputed evaluation formula. The new definition node `def-sfb-direct-image-hom-comparison-data` records this published natural transformation and its pinned adjunction and tensorator. The proved `exists_mixedHomDirectImageComparison` characterizes it on every test map by the evaluation-mate equation. No separate evaluation formula or arbitrary map is introduced. |
| Every open V, U=f⁻¹V and g=f restricted to U | `V : Y.Opens`, `f ⁻¹ᵁ V`, and `f ∣_ V` |
| Canonical restriction comparisons | `singleComplexOpenDirectImageIso` is the existing sectionwise derived comparison; `sfbOpenHomComparison` is the evaluation transpose of pullback along V.ι, transported with the existing `singleComplexOpenPullbackIso`. Its `IsIso` clauses expose the canonical internal-Hom restriction identifications. |
| Restricted c is c for g | The equation starting with `(schemeOpenRestriction Y V).mapDerivedCategory.map (sfbDirectImageHomComparison f E N)` compares the two maps after exactly these source/target comparisons. The contravariant Hom entry uses the inverse of the E-comparison and the covariant entry the forward N-comparison. |
| H^q(V,A)=H^q RΓ(V,A) | `sfbOpenCohomology X V q` abbreviates `openModuleDerivedSections X.toRingedSpace V ⋙ DerivedCategory.homologyFunctor AddCommGrpCat q`. The abelian localization universe `wA` is independent of the module localization universe `w`. |
| First canonical identification H^q(V,Rf-star RHom(E,N)) ≅ Hom(E_U,N_U[q]) | Apply homology to `(ell V).inv.app (RHom(E,N))`, then `α X E N (f ⁻¹ᵁ V) q`. The derived natural isomorphism ell is pinned by `(ell V).hom = sfbOpenLerayComparison f V`; the latter is the actual descent of the underived sectionwise identity through the composite right-derived units. |
| Second identification with Hom(Rg-star E_U,Rg-star N_U[q]) | Apply `α Y (Rf-star E) (Rf-star N) V q`, then `sfbTargetOpenExtEquiv`; the latter conjugates by the existing direct-image open isomorphisms, shifting the target isomorphism. |
| Every integer q | `(q : ℤ)` everywhere, including the normalizations |
| H^q(V,c) sends u to Rg-star u | The final equation: its left side is the second identification applied to cohomology of c; its right side is `sfbPushforwardOpenExt` applied to the first identification. Since both identifications are additive equivalences, this is the claimed formula for every u. |
| Canonical shift comparison | `sfbPushforwardOpenExt` is exactly `(schemeDerivedDirectImage (f ∣_ V)).map u ≫ ((schemeDerivedDirectImage (f ∣_ V)).commShiftIso q).hom.app _`. |
| Canonical, rather than unrelated Ext equivalences | `sfbIsCanonicalOpenExt` specifies α on every cocycle of the actual section complex Hom(L,I(M)): the `homComplexπ` components identify its corresponding chain map k, and α of its class must be the localization of k. `sfbRHomResolutionIso` is `Localization.fac` for the actual definition; `sfbHomSectionClass` uses the actual right-derived unit. The inverse target-resolution augmentation is used only with the existing proved QuasiIso. |
| Naturality in E and N | The α-naturality clause displays precomposition by restricted t and postcomposition by restricted s shifted by q. The c-naturality clause displays the corresponding bifunctor square for c. ell is a natural isomorphism of derived functors. Together with the final equation these are naturality of both identified arrows. |
| Smaller-open and successive restriction compatibility | The α-restriction clause uses `sfbOpenCohomologyRestriction` and `sfbOpenExtRestriction` for every inclusion W→V. The latter uses the existing `schemeDerivedOpenRestrictionCompIso`, exact overlap restriction and its shift isomorphism. The ell-restriction clause uses the actual derived section restrictions on Y and on inverse-image opens. Thus the final formula holds compatibly on every smaller open; applying these equations twice gives successive compatibility with the canonical composition maps, including identity inclusions. |
| No Rf-star as left adjoint or extra finiteness assumption | Only the published pullback-left/direct-image-right adjunction occurs. Importing the module containing fixed adjunction helpers does not introduce the separate QCqs right-adjoint theorem's hypotheses. |

All implicit variables and universes are declared explicitly, with `autoImplicit false`.
The family of module localizations is quantified over schemes in the existing convention;
it fixes the presentations on X, Y and their open subschemes rather than imposing
an extra geometric hypothesis. The theorem supplies a derived Leray isomorphism as
well as its cohomological action, following the stage-2 requirement to retain derived
comparisons rather than merely independent per-degree isomorphisms.

The generic proof-only node `lem-trf-open-ext-hypercohomology-comparison` currently
has no Lean declaration. This delivery does not assume such a declaration: the
scheme-open Ext identifications needed by this item, including their cocycle
normalization, naturality and restrictions, are explicitly included in this item's
single theorem. They are part of the two identifications in the item's own statement.
There is no additional sorried theorem needing a separate DAG node, and no wait.
The generic ringed-space prerequisite remains available for its own stage-2 assignment.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`: `schemeDerivedDirectImage`.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` publicly preserves the
  generic `derivedInternalHom` and universe-generalized presentation. The statement
  uses the original sheaf-module functor from
  `WeilConjectures.Algebra.Homology.DerivedInternalHom`, not the ordinary ModuleCat
  abbreviation in that dependency's most recent record.
- `WeilConjectures.AlgebraicGeometry.DerivedDirectImageInternalHom`:
  `exists_derivedDirectImage_internalHom_comparison` specifies the evaluation mate.
- `WeilConjectures.Topology.OpenModuleDerivedSections`:
  `RingedSpace.openModuleDerivedSections`.
- `WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom`:
  `schemeDerivedTensorHomEquiv`.
- `Sheaf.AlgebraicGeometry.DirectImageHomComparisonData`:
  `sfbHomPullbackAdjunction`, `sfbHomTensorPullbackIso` and
  `sfbDirectImageHomComparison` expose the existing pinned constructions.
  They use `schemeHomPullbackAdjunction`, `mixedHomTensorPullbackIso` and the
  proved `exists_mixedHomDirectImageComparison` from its smaller source module.
  No conclusion of the qcqs global-Hom theorem is used.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedMateEvaluation`:
  `canonicalSchemeDerivedAdjunction`, owned by the existing
  `def-sfb-canonical-scheme-derived-adjunction-composition`, is definitionally
  the same pinned adjunction. It is cited by the new node rather than copied.
- `WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps`:
  `schemeOpenRestriction`, `schemeOpenOverlapRestriction`,
  `schemeDerivedOpenRestrictionCompIso` and their exact/additive structures.
- `WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData`:
  `singleComplexOpenPullbackIso`.
- `WeilConjectures.AlgebraicGeometry.SingleComplexOpenBaseChangeComparisons`:
  `singleComplexOpenDirectImageIso`.
- `CategoryTheory.Functor.rightDerivedNatTrans`,
  `rightDerivedFunctorCompUnit`, `rightDerivedFunctorNatTrans`,
  `rightDerivedFunctorUnitQ`, `mapDerivedCategoryFactors`, `commShiftIso`,
  `DerivedCategory.homologyFunctorFactors` and the published K-injective replacement
  provide the explicit canonical constructions.
- `WeilConjectures.Algebra.Homology.HomComplexComponents`: `homComplexπ`;
  Mathlib's `CochainComplex.HomComplex.Cocycle.equivHomShift` fixes shift signs.

The four already recorded helper definition nodes added to stmt_deps are
`def-pc-derived-open-restriction-maps`,
`def-pc-single-complex-open-restriction-data`,
`def-pc-n3-open-base-change-comparisons`, and
`def-pc-canonical-derived-tensor-hom-bijection`. The fifth addition is now the
new definition node `def-sfb-direct-image-hom-comparison-data`.
`lem-pc-global-hom-adjunction` has been removed from the item's stmt_deps:
its qcqs global-Hom isomorphism is not needed to state this result. The item
now imports the module recorded by the new definition node, which defines
interfaces for all three fixed data declarations. The original node statement, proof,
proof_deps and every field other than lean and stmt_deps remain unchanged.

The module imports the stated proof dependencies. For the legacy Sheaf twins of
`derivedInternalHom_restrict_open` and
`isKInjective_homComplex_of_isKFlat`, it imports the adopted WeilConjectures modules
instead, as the launcher's duplicate-declaration instruction requires. The
ringed-space derived-adjunction compatibility module publicly re-exports its
adopted upstream theorem. Mathlib KInjective and derived-adjunction modules cover
the two Mathlib proof leaves. The only proof dependency with no declaration is
the generic open Ext node discussed above.

Edge cases checked before the statement was written:

- V empty or X empty: all definitions still use genuine section functors and
  exact restrictions; the Hom groups on the empty open are zero. No Nonempty
  assumption excludes these cases.
- V=top and q=0: the normalization sends a cycle representing a chain map to
  precisely its localized morphism, and the formula specializes to Rf-star(u).
- q negative or zero: `equivHomShift`, `commShiftIso` and the integer-indexed
  homology functor retain these degrees; there is no Nat conversion.
- E or N zero: Hom and Ext groups vanish, but the displayed conjugations and
  evaluation mates remain defined.
- f identity and W=V: actual identity section restrictions and canonical
  composition isomorphisms are retained; no strict-equality substitute is used.
- Nonproper/nonflat f and arbitrary unbounded E,N: no finite Tor dimension,
  QCoh, compactness, boundedness, nor preservation of K-injectivity by f-star is
  assumed. `sfbHomSectionClass` is defined by a derived unit even on the
  sections-acyclic Hom-complex model.

Searches actually run for this item:

- `msearch.py leanfinder`, query `Derived direct image internal Hom comparison
  induces pushforward on open Ext groups and commutes with open restriction`:
  8 hits, including `Scheme.Modules.pushforward_map_app`,
  `SheafOfModules.pushforwardPushforwardAdj`, `pushforwardNatIso`,
  `pushforwardComp_hom_app_val_app`, `Scheme.Modules.restrictAdjunction`,
  `pushforward_obj_presheaf_map`, `TopCat.Sheaf.pullbackPushforwardAdjunction`,
  and `pushforwardComp_inv_app_val_app`. These concern underived operations.
- `msearch.py loogle`, query
  `CategoryTheory.Functor.mapExtAddHom, CategoryTheory.Abelian.Ext.mapExactFunctor`:
  `mapExtAddHom_coe` and `mapExtAddHom_apply`. These are Ext under exact ordinary
  functors, not the unbounded derived-direct-image internal-Hom comparison.
- `msearch.py grep`, query
  `internalHom.*(pushforward|directImage)|(pushforward|directImage).*internalHom`:
  zero Mathlib hits.
- `msearch.py leansearch`, query `Derived direct image internal Hom comparison
  acts by pushforward on Ext groups over every open subset`: 8 hits including
  ordinary `Scheme.Modules.pushforward_map_app`, presheaf pushforward, and
  `Abelian.extFunctor_map_app`; none states this result.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, querying the item id,
  directImage/Ext combinations and internal-Hom/comparison combinations, found
  the existing evaluation mate, global-Hom helpers and restriction statements,
  which are used here; no existing theorem has the full open-Ext action and
  restriction normalization of the item. A separate item-id search upstream
  had no hits. The new declaration names were also searched in both trees and
  `dag/lean_names_upstream.json` with no collisions.

No statement dispute, source correction or dependency-record repair.
There is one new definition ownership node, described below.
The proof docstring reproduces all eight DAG proof steps and their cited nodes.

Validation: all compiles use the prescribed scompile wrapper, including separate
sandbox and library-path checks against the live published build, with the
unchanged 60-second per-file limit. Only the expected sorry warning is permitted.
The final delivery is checked with deliver2.py --no-push before pushing.


## New nodes

`def-sfb-direct-image-hom-comparison-data` records the canonical evaluation-mate
natural transformation, together with its pinned pullback adjunction and
shared-counit pullback tensorator, for arbitrary schemes and unbounded module
complexes. Its source is Stacks cohomology.tex, Tag 0B69,
`remark-projection-formula-for-internal-hom`, with Tags 079W and 079U for the
pullback data. The module `Sheaf.AlgebraicGeometry.DirectImageHomComparisonData` exposes the
three existing constructions through canonical aliases: the pinned adjunction and
tensorator from `GlobalHomAdjunctionIso`, and the evaluation-mate component from
`exists_mixedHomDirectImageComparison` in `MixedHomDirectImageComparison`. The
new node owns these interfaces and has a real definition module; it does not copy
their construction or use the unrelated qcqs global-Hom isomorphism. The
comparison is selected from the existing existence theorem whose mate equation
determines it, so no arbitrary map is chosen.

The new node's clause-to-source correspondence is:

| Definition clause | Existing Lean data |
| --- | --- |
| Arbitrary f, X and Y and their unbounded module categories | `{X Y : Scheme.{u}} (f : X ⟶ Y)` and the explicit family of `HasDerivedCategory.{w}` instances |
| Pinned pullback adjunction a_f | `sfbHomPullbackAdjunction f := schemeHomPullbackAdjunction f`; its choice is exactly the one in `canonicalSchemeDerivedAdjunction f`, using `exists_schemeDerivedAdjunction` and `exists_derivedPullbackComposition` |
| Canonical pullback tensorator t_f | `sfbHomTensorPullbackIso f := mixedHomTensorPullbackIso f`, where the latter is `Classical.choose (exists_mixedHomTensorPullbackIso f)`; the existence statement includes `IsCanonicalPullbackTensorComparison` |
| Fixed tensor-Hom bijection b_X | `schemeDerivedTensorHomEquiv X`, whose source record is cited in stmt_deps |
| Natural c on both Hom entries | `Classical.choose (exists_mixedHomDirectImageComparison f)`, the existing evaluation-mate natural transformation, with its component recorded as `sfbDirectImageHomComparison` |
| Evaluation-mate equation for every test map alpha | The full conclusion of `exists_mixedHomDirectImageComparison f`, from which the existing c is selected; it uses the same adjunction, tensorator, counit and b_X |
| Component c(E,N) in the item | `sfbDirectImageHomComparison f E N`, owned by the new definition node |
| No extra hypotheses | Neither this c nor its pinned adjunction/tensorator has a qcqs, boundedness, compactness, ordinary-module localization, or additional adjoint binder |

The dependency traversal through both stmt_deps and proof_deps found no route
from any new-node dependency back to the item. The new-node statement cites
exactly its recorded stmt_deps. No existing dependency record is edited.

New-node searches, run during this repair: LeanSearch and LeanFinder queried
`Canonical derived pullback pushforward adjunction tensorator and evaluation mate
internal Hom direct image comparison`; each returned eight generic or ordinary
adjunction hits. Loogle queried `CategoryTheory.Adjunction.homEquiv,
CategoryTheory.Functor.LaxMonoidal.μ`, returning the two generic adjoint monoidal
formulas. Mathlib grep queried
`internalHom.*(pushforward|directImage)|(pushforward|directImage).*internalHom`,
returning no hits. The raw search-log records are stored in mathlib_searches.
Repository rg located the three exact upstream definitions and their consuming
theorem nodes, with no existing definition node for the tensorator or direct-image
comparison. Blueprint search `evaluation-mate` returned zero nodes; `internal Hom`
returned 85 nodes about general operations or other sites/coefficients, without
this fixed scheme-module datum. `blueprint_refs.py ancestor` reports None, which
is retained with the item's full source route and the extra evaluation-mate step.

## Second reading by Q128

I reread the repaired node, new definition node, their source declarations and
the complete consumer module. This is a second pass by the dispatched worker,
not a claimed independent reviewer; the dispatcher prohibits starting agents.
The maintainer's immutable-head return already checked the geometric and Ext
clauses and identified H4/H12 as the repair needed. The earlier report's claim
that the global-Hom theorem supplied a statement dependency was incorrect.
That dependency is now replaced by a definition record for the actual data.
The earlier helper recomputed c by an explicit evaluation formula; it now
uses the existing canonical natural transformation from the new definition module, removing that copy.

The new definition's f:X→Y is arbitrary; its categories, tensor, pullback,
direct image and internal Hom are the existing ones. Its adjunction is the
same normalized choice as canonicalSchemeDerivedAdjunction, and its tensorator
is the one selected by the shared-counit theorem. Its c is precisely the existing
mixed comparison selected by the all-test-map evaluation equation, through the
same Classical.choose expression as the published convenience name. No global
ring localization instance, finiteness hypothesis or arbitrary comparison is
introduced. These facts were checked against the full source signatures and
choice expressions, not just names.

For the consumer, the clause table above still applies: all integer q, inverse
image opens, canonical restriction maps, cocycle normalization of alpha,
right-derived-unit normalization of ell, naturality, smaller-open restrictions,
and the Rg_* map followed by commShiftIso are present. The theorem signature is
textually unchanged from the returned delivery; the c helper is now owned by
the definition node rather than the theorem node. Replacing c's explicit formula
by the published comparison preserves its meaning because the published mate
equation at the identity test map determines precisely that formula. The only
sorry remains the main theorem proof; all definitions have real data. The empty
open/scheme, nonpositive q, zero inputs and identity-morphism cases remain
included. No additional mismatch was found.


Compile repair: the first direct abbreviation for c passed the sandbox check
in 52.8 seconds but timed out at the 60-second library/source-confirmation limit.
The final interface uses the smaller MixedHomDirectImageComparison module and
the same selected transformation directly, avoiding the extra mixed global-Hom
module import. All three pinned interfaces now belong to the definition module
requested by the maintainer. Their values and types are unchanged; no timeout
increase or mathematical assumption is used.


Final verification: scompile.py compiled both modules separately in dependency
order against the live published build, with exit 0 and no error or warning.
The definition module's private/library checks completed in 11.4 seconds; the
consumer sandbox and library checks completed in 54.3 and 57.1 seconds. The
wrapper also reported a preliminary sandbox duration of 76.4 seconds without
a timeout or diagnostic; its library/private check remained successful. The
per-file timeout was never changed. Both module declaration lists and verbatim
main signatures were checked against their node records; line width is at most
100. The definition module has no sorry, and the consumer has only the main
theorem's required sorry.


Dry run: deliver2.py --no-push returned OK at 3dc2c12bf51, confirming
preflight and both per-file compiles. The final search-verdict prose was then
updated to describe the delivered definition module, and the dry run is repeated
for that exact delivery content before pushing.
