## Worker report

The module `Sheaf.CategoryTheory.LocallyConstantPresheafSlice` constructs the two specified
functors and states `SSet.LocallyConstantPresheafSlice.locally_constant_presheaf_slice`.
Its sole postponed theorem has proof `sorry`. There is no definition containing `sorry`, no
choice of a canonical map from a mere existence statement, and no statement correction.
`Presentation` bundles the clauses of this one statement; its model structures are existential
data of the theorem, not objects extracted by definitions from its unproved existence.

Clause correspondence (all names below are in `SSet.LocallyConstantPresheafSlice`):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Small ordinary category, enlarged universe | `(C : Type u) [SmallCategory C]`, with explicitly declared `universe u`; presheaf values are `SSet.{u}` and presheaf and slice categories live in `Type (u+1)`. There is no inhabitance assumption. |
| Simplicial sets, nerve, spaces and weak equivalences | Mathlib `SSet`, `nerve`, `KanComplex`, and dependency `Enhanced.IsWeakHomotopyEquivalence`. This last predicate uses realized path components and all positive based homotopy groups. |
| Discrete representable h_x(y)=Hom(y,x) | The dependency's `ProjectivePresheaf.representable x`; its action is the actual Yoneda restriction followed by the constant simplicial-set functor. |
| Projective model structure | `Presentation.projective` with `projective_weak`, `projective_fib`, and `projective_cof` specifying exactly the objectwise Kan classes and their left lifting class. |
| Localization at every arrow-induced representable map | `representableArrow : Arrow C → ...` is the whiskered actual Yoneda map. `localized_cof` keeps cofibrations fixed. `localized_weak` is the dependency's `BousfieldLocalization.localEquivalences` for the entire small family indexed by `Arrow C`, with the actual projective enrichment and functorial cofibrant replacement. `replacement_property` fixes the required replacement properties. |
| Fibrant iff objectwise Kan and all arrows invertible | `localized_fibrant` is an iff, with a conjunction of every objectwise Kan condition and the weak homotopy equivalence condition for every restriction map. |
| N_C(F)_n is the coproduct over chains with a final F(c_n)_n coordinate | `total.obj` is the dependent sum over `ComposableArrows C n.unop.len` of `(F.obj (op s.right)).obj n`. |
| Projection forgets the last coordinate | `projection.app` is `fun z ↦ z.1`; `left.obj` is `Over.mk (projection F)`. |
| Faces, last-face restriction and degeneracies | `total.map` uses `nerve.map` on the chain, the simplicial operator on its fiber, and `F.map (lastArrow ...).op`. `lastArrow` is the chain's composite from the last selected vertex to the original last vertex. For every non-last face and every degeneracy this arrow is an identity; for the last face it is exactly c_(n-1) → c_n. One formula covers all ordinal maps and their compositions. |
| Functoriality in F | `left.map f` keeps the chain and applies the actual component of f at its final object. The functor laws contain real proofs. |
| S_C(T)(x) is the slice mapping object from N(C/x) | `overNerve x = Over.mk (nerveMap (Over.forget x))`; `right.obj` uses the existing `Enhanced.transportOverHom (overNerve x).hom T.hom`. Its simplex is the full natural family representing a map N(C/x) × Δ[n] → T over NC. `right` constructs restriction by the nerve of `Over.map` and covariance by postcomposition with the actual slice map. |
| Stated adjunction | `Presentation.adjunction : left C ⊣ right C`. `adjunction_formula` specifies its transpose on every simplex and every chain over x, so it is the canonical adjunction. |
| Simplicial adjunction | `enriched` is an isomorphism of the actual enriched mapping simplicial sets. `enriched_formula` specifies the transpose on every test degree, simplex parameter and input pair. `chainOver` is the explicit chain in C/x obtained by postcomposing every tail with the final arrow. |
| Slice of the Kan--Quillen model over NC | `slice_cof`, `slice_fib`, and `slice_weak` identify the three slice classes with underlying monomorphisms, Kan fibrations and realization weak equivalences, respectively. No `KanComplex (nerve C)` assumption occurs. |
| Simplicial model categories | `enrichment_usual` is the dependency's normalized usual enrichment; `presheafTensor_formula` and `presheafCotensor_formula` use the actual pointwise products/internal homs. `sliceMapping`, its vertex and composition normalizations, and `sliceTensor_formula` specify the actual slice enrichment and Cartesian tensor. `localized_sm7` and `slice_sm7` assert both simplicial model axioms. |
| Quillen equivalence | `left_quillen` preserves cofibrations and trivial cofibrations. `quillen_equivalence` is the standard exact adjunct criterion for every cofibrant source, fibrant target, and map between them, using precisely `adjunction.homEquiv`. |
| Left(h_x)=N(C/x) | `representableIso` is an isomorphism over NC; `representableIso_formula` fixes its entire simplex map as `chainOver z.1 z.2`. |
| Derived mapping-space comparison on h_y,h_x | Given a fibrant slice replacement `i : left(h_x) → T`, `derived_representable_unit` says its actual adjunct `h_x → right(T)` is a local weak equivalence; `right_fibrant` makes its target local fibrant. `representable_cofibrant` makes h_y a valid source without replacement. Thus the left mapping space is represented by `mapping h_y (right(T))`, and the right by `transportOverHom (overNerve y).hom T.hom`. The actual isomorphism between these is `evaluation (right(T)) y`, since `(right(T)).obj (op y)` is definitionally this slice mapping complex. `derived_comparison` identifies it in every degree with `enriched` precomposed by `(representableIso y).inv`, so this is exactly the comparison of the stated adjunction. This replacement formulation covers every x,y and every such T,i. |
| Representable arrows, identities, composition and associated homotopies | The functors are actual functors, the adjunction is the actual simplex-normalized adjunction, and `enriched_formula`, `representableIso_formula`, `evaluation_formula`, and `derived_comparison` are equations in every simplicial degree. These fix the entire natural enriched transpose, not just its effect on components or unrelated equivalences. The derived comparisons use its actual unit. The existing simplicial-model and derived-adjunction interfaces identify these representatives with coherent derived maps and their composition homotopies. |
| Evaluation for local fibrant F | `evaluation` is an isomorphism even before deriving, and `evaluation_formula` fixes it to evaluation on `(id_y,id_[n])`. For local fibrant F, h_y is cofibrant by `representable_cofibrant` and `localized_cof`, so this same formula is the derived evaluation `Map^h(h_y,F) ≃ F(y)`. |

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.IsWeakHomotopyEquivalence`
  and the simplicial conventions of the recorded `SSet.Enhanced.coneCategory` node.
- `Sheaf.CategoryTheory.SimplicialPresheafLocalizationComparison`:
  `SSet.ProjectivePresheaf.simplicial_presheaf_localization_comparison`; it exposes the
  actual projective enrichment and the exact Bousfield local-equivalence predicate used here.
- Its projective dependency `Sheaf.AlgebraicTopology.SimplicialPresheafProjectiveModel`:
  `SSet.ProjectivePresheaf.representable`, `.mapping`, `.tensor`, `.cotensor`,
  `.IsUsualEnrichment`, and `.simplicial_presheaf_projective_model`.
- `Sheaf.CategoryTheory.BousfieldLocalFibrations`:
  `CategoryTheory.BousfieldLocalization.localEquivalences` and `.IsLocal`.
- Added already-landed statement dependency `lem-coef-space-transport-classification`, module
  `Sheaf.CategoryTheory.SpaceTransportClassification`: `SSet.Enhanced.transportOverHom`
  and its defining subcomplex. This is exactly the slice mapping object required by the node;
  it is reused rather than copied. The node's statement and recorded theorem/docstring were
  read as well. A source-only dependency traversal found no path back to this item (629 nodes
  in that dependency's combined statement/proof closure).
- `Mathlib.AlgebraicTopology.ModelCategory.Over`:
  `HomotopicalAlgebra.ModelCategory.over` and the three underlying-class equivalences,
  the recorded exact Mathlib match of `lem-coef-model-over-structure`.

All already-stated proof dependencies are imported, without `public`, as the proof plan.
The still-unstated `lem-coef-simplicial-bousfield-model-structure` has no recorded module to
import; no definition needed to state this item is missing, since the localization predicate
and existence interface are already supplied by the recorded statement dependency.

The source was opened online at HAG II Appendix A (PDF pages 214--215 in one-based counting;
printed pages 207--208). It gives exactly the chain/final-coordinate functor, the mapping
right adjoint, its representable identification and Proposition A.0.3. The module's theorem
docstring records all nine node proof steps, including the node's expanded arbitrary-base
fiber argument and coherent mapping comparison. The original TeX statement is unchanged.

Edge cases checked before finalizing:

- Empty C: the sum is empty in every degree, there are no representables to test, and both
  presheaves and the slice over the empty nerve have the required terminal-category behavior.
- Terminal C: total is canonically F(*) and right is the actual simplex mapping presentation
  of T; the adjunction/evaluation reduce to their usual simplicial-set forms.
- Degree zero: the final restriction is the identity; degree one: deleting the last vertex
  uses F(c_0 → c_1), whereas deleting the first only applies the simplicial face.
- Degeneracies insert identity arrows; arbitrary composites use the tail to the final vertex.
- All-empty fibers: no nonemptiness is imposed on F or its Kan values.
- Non-Kan NC, for example the nerve of [1]: fibrancy is the Kan fibration T → NC, not the
  Kan property of T or NC. The slice and replacement clauses do not silently assume either.
- Non-projectively-cofibrant local fibrant F: evaluation still applies since its source h_y
  is cofibrant; the Quillen criterion is restricted to cofibrant sources only where required.

Searches for reuse:

- `msearch.py ... leanfinder "locally constant simplicial presheaves Quillen equivalence slice
  over nerve"`: ordinary nerve/homotopy-category adjunction hits, no matching equivalence.
- `msearch.py ... leansearch "simplicial replacement presheaf category of elements nerve
  slice"`: nerve, simplicial nerve and quasicategory-of-nerve declarations; no such functors
  or locally constant presheaf/slice Quillen equivalence.
- `msearch.py ... loogle "SSet, CategoryTheory.Over, CategoryTheory.QuillenEquivalence"`:
  zero hits; `CategoryTheory.QuillenEquivalence` is not an identifier in this Mathlib.
- `msearch.py ... grep "simplicialReplacement|locallyConstant.*SSet|QuillenEquivalence"`:
  zero matching Mathlib declarations.
- `msearch.py ... grep "transportOverHom|ProjectivePresheaf|locallyConstant.*SSet"`:
  zero Mathlib hits. Direct project grep found the already-recorded `transportOverHom`
  and `ProjectivePresheaf` constructions; those are imported here.
- Direct `rg` of `lean/Sheaf/CategoryTheory` and `WeilConjectures` for locallyConstant,
  simplicialReplacement, presheafSlice and QuillenEquivalence found ordinary locally constant
  sheaf modules and the different existing right-fibration Quillen presentation. Neither is
  this homotopy-locally-constant presheaf/Kan slice statement. The general projective change
  of index criterion is likewise a different result.
- `grep -rn` of the item id in `WeilConjectures` returned no match. Final full-name search
  of Mathlib, upstream, `lean/Sheaf`, and `dag/lean_names_upstream.json` returned no collision
  for this module/namespace, theorem, or its helper names.

Verification: the prescribed `scompile.py NR lem-coef-locally-constant-presheaf-slice <file>`
compiled both the sandbox probe and the named library module cleanly (3.8 s / 4.8 s in the
latest run). All variables and universes are bound explicitly; `autoImplicit` is disabled.
No mathematical dispute or node fault was found.

## Second reading by NR

This is the author's second pass; the dispatcher forbids starting another agent, and the
maintainer performs the independent delivery review. I reopened the node and the complete
module. The two constructions have the correct variance: a map x → x' gives C/x → C/x',
so the right presheaf restricts in the opposite direction. The tail map in `total` restricts
from c_n to c_alpha(m), including precisely the special last-face case. I checked each row
of the correspondence table against the actual fields, especially both directions of
`localized_fibrant`, the actual Yoneda localization family, the ordinary and enriched
transpose formulas, and the all-degree normalization of the derived comparison. No added
hypothesis, missing clause, private replacement notion or arbitrary comparison was found.
The derived statement is given by explicit fibrant-replacement representatives: it does not
assert that underived maps between two non-fibrant representables compute derived maps.
The definitions, functor laws and chain-over construction compile without postponed proofs;
only the named main theorem is postponed. No statement change or dependency repair was needed.
