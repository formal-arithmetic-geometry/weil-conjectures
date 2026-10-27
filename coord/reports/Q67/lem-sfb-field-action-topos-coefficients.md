## Worker report

The new module `Sheaf.Paper.FieldActionToposCoefficients` states
`AlgebraicGeometry.ProEtale.FieldActionTopos.field_action_topos_coefficients`.
Its conclusion is `Nonempty (Normalization k Ω)`. The structure packages one
simultaneously normalized equivalence; none of its data are selected from this
existence theorem. The only postponed theorem is this item's own theorem, with
the complete eight-step DAG proof in its docstring. Definitions have real data.

Source read: Bhatt–Scholze, Examples 4.1.9–4.1.10, printed pages 27–28
(`pdftotext` pages 27–30), including the weakly étale G-torsor, profinite continuous
G-sets, and finite jointly surjective covering criterion. Also read the current
main-20261015 direct-images proof, paragraph (3). The additional normalization is
the agent refinement already explicitly present in the node's statement/proof.
The TeX statement needs no correction. The returned Lean packet is repaired below; a new definition node records existing data, without introducing a new module.

Hypotheses and clauses, matched against the node:

- `k Ω : Type u`, `[Field k]`, `[Field Ω]`, `[Algebra k Ω]`, and
  `[IsSepClosure k Ω]` express exactly the field and its separable closure.
  `Ω ≃ₐ[k] Ω` uses the imported Krull topology and profinite instances.
- `FieldSheaves k` is `Sheaf (Scheme.ProEt.topology (Spec (.of k))) (Type (u+1))`.
  `Cond` is sheaves on the existing coherent profinite site. `Actions` is the
  recorded `InternalActionSite.SetActions`, not another definition of actions.
- Compatible sizes are explicit: profinite spaces and schemes have size `u`,
  set values have size `u+1`. Existing `Base = AsSmall.{u+1} Profinite.{u}`
  lifts the morphism universe without identifying object and morphism sizes.
  `transport` is actual precomposition by `AsSmall.down`, using `base_transport`.
- `profiniteToProEtOf` followed by `Scheme.ProEt.forget` is the recorded T[P]
  construction. `geometric` identifies each free object over s with bar s[P].
  `geometric_naturality` retains the actual maps between test schemes.
  `geometric_galois` fixes each constant Galois label by both pullback coordinates:
  the profinite coordinate is unchanged and the field coordinate is `Spec.map σ`.
  `sections` gives the underlying condensed sections on that geometric test.
- `equivalence` is the equivalence of topoi. `free`, `fullyFaithful`, and `dense`
  specify the free dense subsite of the qcqs field site. `coordinates` identifies
  these objects with `G × P` with left translation; `arrow` fixes the formula
  `(g,t) ↦ (g*b(t), f(t))`. `free_arrows` states uniqueness of f and b among all
  continuous equivariant arrows, using continuous maps in the existing group
  presheaf. The actual `free` functor uses the recorded action-site category:
  its composite is exactly `(fh, c h*b)`, including noncommutative G.
- `restriction` states b acting on f-star with precisely that category's labels;
  `sections_maps` gives naturality in sheaf maps. The f variable supplies all
  profinite restrictions, so the section identification is natural in parameters.
  `covers` equates the actual induced-topology covering presieve with finite
  joint surjectivity of f; it includes zero arrows and empty target.
- `pointDirect`, `pointEvaluation` give p_s*F(P)=F(s[P]) naturally in F and P.
  `pointAdjunction` uses the recorded set inverse image
  `profinitePointSetSchemeInverseImage`, rather than an arbitrary left adjoint.
  The abelian point construction is imported as the node requires.
- `actionTopos`, `trivial_eq`, `trivialUnderlying`, and `trivial_action`
  specify p_G inverse image using the existing action-topos presentation and
  unchanged underlying sheaf with trivial action. `actionAdjunction` gives
  its right adjoint. `point_leftExact`, `trivial_leftExact` assert finite-limit
  preservation; equivalences preserve limits. `leftComparison` is E p_s^-1
  isomorphic to trivial inflation.
- `rightComparison` is p_s* isomorphic to p_G* E. `inclusion` and `injective`
  give its subobject of the underlying sheaf; `inclusion_counit` ties this
  inclusion to the adjunction, not a separately selected embedding. `image`
  quantifies over every test T, every T→P, and every continuous T→G. It is
  universal internal fixedness, not fixedness under constant group elements.
- `cover_coordinate` pins `cover` to the canonical bar s[P]→s[P]: it is already
  an arrow over s and preserves the other pullback coordinate. `covering`
  asserts this singleton is a pro-etale cover. `right_restriction` says its
  section restriction is exactly the comparison followed by invariant inclusion.
  `kernel_pair` gives a free object with parameter G×P, the two labeled
  projections (f,1), (f,b), and the actual pullback square. Combined with
  `coordinates`/`arrow`, these are (g,h,p)↦(g,p) and (gh,p), respectively.
  `equalizer` spells out the sheaf equalizer: a unique arithmetic section
  lifting a geometric section iff it satisfies universal fixedness.
- `mate` gives the Hom-adjunction equation for the left comparison and this
  exact right comparison. Thus neither comparison has an arbitrary normalization.
- `finite_operations` specifies both mapped finite product cones as limits and
  the same component comparison for every operation R^n→R and every projection.
  For n=0 this includes unit and zero; n=1 negation; n=2 multiplication and
  addition. This is the finite-product ring-object transport on E p_s^-1 R.
- `coefficientSet` uses the existing section-ring construction on an arbitrary
  `Profinite.CondensedRing` with `[IsCommMonObj R.X]`. No topological presentation
  or discrete coefficient assumption is imposed. `coefficientComparison`
  identifies its image with the recorded `trivialCoefficient`. Its underlying
  morphism is exactly alpha_R by `coefficient_underlying`; compatibility with
  all ring operations is `finite_operations`, so this is a ring-object
  isomorphism with the transported operations. `coefficient_maps` gives its
  naturality for every map of the actual commutative ring sheaves.

Dependency interfaces read and used:

- `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`:
  `IsSepClosure.exists_intermediateField_mem` and the underlying `IsSepClosure`.
- `Sheaf.Paper.ProfiniteTestObjectFunctor`:
  `AlgebraicGeometry.ProEtale.profinite_test_object_functor`;
  the actual `profiniteToProEtOf` is from the imported ModuleObject.Basic.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `.topology`.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Sheaf.AlgebraicGeometry.ProEtalePointPullback`: `sfbPullbackFromPoint`,
  its right adjoint and full specification, for the abelian version.
- `Sheaf.Paper.ProfinitePointPullback`: `profinitePointSetSchemeInverseImage`.
- `Sheaf.CategoryTheory.InternalActionSitePresentation`: `Object`, `Arrow`,
  category, `opArrow`, and their precise label order.
- `Sheaf.CategoryTheory.ActionToposGeometricRestriction`: `SetActions`,
  `setAction`, `inflation`, and `GeometricRestriction`.
- `Sheaf.CategoryTheory.ProfiniteActionParameters`: the recorded `freeAction`.
- `Sheaf.AlgebraicGeometry.ProEtaleQcqsSubsite`: `Scheme.ProEt.Qcqs`,
  `Scheme.ProEt.qcqsInclusion`, now a directly cited landed definition node.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt.forget`; composing
  it with the inclusion and test functor spells out the two over-category functors.
- `Sheaf.Paper.FieldProfiniteGaloisSite`: imported privately for the existing
  proof dependency `field_profinite_galois_site`; no signature uses its helpers.
- `Mathlib.FieldTheory.Galois.Profinite`: the Krull topology and its profinite
  group instances, now imported directly for the statement.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`.
- Mathlib `Sites.DenseSubsite.SheafEquiv`: the recorded dense restriction
  equivalence instance; `Adjunction.Mates`: `conjugateEquiv` and the exact
  `unit_conjugateEquiv_symm` signature, for the future proof.
- New definition node `def-sfb-profinite-action-base-coefficients`, with
  `existing: true` on `Sheaf.CategoryTheory.ProfiniteActionCoherentPresentation`:
  `Base`, `parameter`, `baseCoverage`, `base_site`, `groupPresheaf`,
  `group_isSheaf`, `Actions`, `base_transport`, `coefficient`,
  `coefficientSets_isSheaf`, `coefficientSets`, `trivialCoefficient`.
  The typing/gluing lemmas justify these constructions. The theorem
  `profiniteAction_coherentPresentation` and its proof are not used to state
  this item and its node is no longer a statement dependency.

Edge checks: empty profinite spaces, n=0 covers, zero and terminal ring objects,
G=1 (including separably closed imperfect fields), infinite and noncommutative G,
and arbitrary non-discrete condensed coefficient rings. No Nonempty parameter,
finite G, perfect field, algebraic closedness, invariant exactness, or site universe
equality is required. For empty P, universal quantification and the empty covering
family give the sheaf terminal value. For G=1, the two kernel-pair projections
coincide and all sections satisfy fixedness. The ring arity-zero case is explicitly
included in finite_operations, not inferred from a positive-arity-only assertion.

Searches performed with the prescribed msearch wrapper:

- LeanFinder: “The pro etale topos of a field is equivalent to condensed sets
  with internal continuous Galois actions normalized on profinite tests”:
  eight hits (profinite-to-condensed embeddings and discrete condensed criteria),
  no field equivalence or normalized adjunction match.
- Loogle: `Condensed, Mod, ContAction`: no hits.
- Mathlib grep: `Galois.*(Sheaf|Condensed)|(Sheaf|Condensed).*Galois`:
  one unrelated ideal-sheaf Galois connection.
- LeanSearch: “Field pro etale sheaves equivalent to internal condensed Galois
  actions with normalized trivial coefficients”: eight hits, including the finite
  pre-Galois-category equivalence and condensed definitions; no match.
- Direct rg on `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the proposed namespace/declaration: no clash.
  Item-id search in both source trees: no existing statement. Concept searches
  found the reused field-site and internal-action modules, and then the landed
  profinite action presentation with the needed size transport.

Validation: prescribed scompile checks compile both the sandbox and the final
module path. Initial universe errors in use of the small-category-only
`precomposition` helper were repaired by direct `ObjectProperty.lift` with the
same actual precomposition data and the existing base_transport proof. No live
source was changed. The final dry run and delivery are run with deliver2.py.

## Second reading by Q67

Author's separate self-check; the maintainer supplies the independent review.
Reopened the complete node and final module. Checked each clause against the
mapping above, especially the noncommutative label order, all-test fixedness,
canonical cover coordinate, actual kernel-pair square, mate equation, and arity
zero. During this check added explicit `covering`, `equalizer`, `fullyFaithful`,
`dense`, `finite_operations`, and coefficient comparison/naturality fields so
none of those clauses is left only in prose. Reused the existing AsSmall action
presentation instead of duplicating internal group actions. Every theorem proof
is sorry; no definition chooses data from that theorem. The node statement, proof and proof_deps are unchanged. Statement dependencies
now cite the new definition node and the landed parameter and qcqs definitions.


## New nodes

`def-sfb-profinite-action-base-coefficients` records the already existing small
profinite parameter site, its continuous-map group sheaf, the internal-action
category, the AsSmall sheaf transport, and the trivial action on the section-ring
sheaf of an arbitrary commutative condensed ring. Its `existing: true` record
lists the original declarations, including their typing/gluing theorems, in
`Sheaf.CategoryTheory.ProfiniteActionCoherentPresentation`. There is no new Lean
module and no duplicate construction. Source: Bhatt--Scholze Examples 4.1.9--4.1.10
and the paragraph (3) coefficient refinement of the current blueprint.

Searches actually run for this definition node: LeanSearch query “Small model of
the profinite site with continuous group presheaf internal actions and trivial
condensed coefficients” returned eight general condensed/Galois definitions,
without this particular model. Loogle `"AsSmall", "Sheaf"` returned zero hits;
Mathlib grep `baseCoverage|groupPresheaf|trivialCoefficient` returned zero hits.
The actual wrapper results are copied into its `mathlib_searches`. Direct rg of
`lean/WeilConjectures` and `lean/Sheaf` found these exact declarations only in the
landed coherent-presentation module. DAG search for these recorded names found
only the theorem node; a parsed search of all definition nodes found none.
`tools/blueprint_refs.py search 'profinite action parameter'` returned zero
blueprint matches, and `ancestor` returned None, as recorded in the new node.
The separate existing `def-sfb-profinite-action-parameters` provides the free
profinite-action functor, and is cited directly rather than duplicated here.

## Repair of return at 902340878c53

H2: Removed the added theorem statement dependency
`lem-sfb-profinite-action-coherent-presentation`. Added the definition node above,
with an existing record on the same landed module. The imported definitions and
typing proofs are unchanged, and no data or hypothesis comes from the coherent
presentation theorem. The saved packet was compared with the current shared
node (whose `lean` is still null and which lacks the old added dependency) and
the current landed construction module. Delivery wrappers refresh their base.

H4: Replaced every `FieldGaloisSite.regular` by the recorded
`Profinite.ContinuousActionParameter.freeAction`, and cited its definition node.
Spelled out `qcqsOver` as `Scheme.ProEt.qcqsInclusion ⋙ Scheme.ProEt.forget` and
`testOver` as `profiniteToProEtOf ⋙ Scheme.ProEt.forget`. Read the full signatures
and bodies of these functors. The qcqs definition node is now a statement
dependency, and the Krull topology/profinite instances and induced topology are
public imports in their own right. The field-site theorem module is only a
proof import, and no `FieldGaloisSite` name remains in the statement.

H3: Added `Normalization.geometric_galois`, for every P and every actual
`σ : Ω ≃ₐ[k] Ω`. Under `geometric P`, the free arrow labelled
`⟨𝟙 P, const σ⟩` preserves the profinite coordinate and composes the field
coordinate with `Spec.map σ`. These are both projections of the actual pullback
that constructs bar s[P], so together they fix its scheme automorphism. This is
the source's Galois fibre functor normalization, not an arbitrary free-object
identification. A point `g : Ω →ₐ[k] Ω` is sent to `g ∘ σ`, namely `g * σ`;
therefore the formula uses σ itself, not its inverse, in agreement with step 2.
The theorem proof docstring now records this geometric-point calculation.

Second reading of the repair: checked the new node against all twelve existing
declarations, including the actual finite-presieve definition and ULift
restriction maps. Checked the two geometric_galois equations at σ=1, at empty P,
and for a noncommutative group: composing labelled arrows first σ then τ gives
σ τ on right-translation coordinates, while contravariant Spec gives the same
composite. For finite k, a Frobenius-inverted labeling now fails the field
projection equation unless the two field automorphisms agree. All source and
coefficient universes, arbitrary-base-change fixedness, empty covers, mate,
ring operations and original eight proof steps remain as matched above.
There are no new sorry declarations: the only delivered theorem still has
exactly `by sorry`, and all data constructions are unchanged explicit definitions.
