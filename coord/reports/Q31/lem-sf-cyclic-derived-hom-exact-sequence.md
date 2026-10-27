## Worker report

The delivery states the existing reviewed node without changing its statement, proof,
dependencies, or stage-1 review. The earlier worker's stale-dispatch diagnosis confused a
completed stage-1 split with a completed stage-2 statement. The live node had no `lean`
record when this work began. No split was repeated.

The module is `Sheaf.CategoryTheory.CyclicDerivedHomExactSequence`, in the upstream
namespace `CategoryTheory.Endofunctor.IsoAlgebra`. The main declaration is
`exists_cyclicDerivedHomBoundary`. Three companion theorems give exact, right-derived,
and finite-composite functoriality. These four theorems have `sorry` proofs. All definitions,
including comparisons and finite-composite data, have real bodies. Each declaration has
a source/blueprint docstring; each theorem's docstring contains its natural-language proof.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Grothendieck abelian A | `{C : Type u} [Category.{v} C] [Abelian C]` and `[IsGrothendieckAbelian.{v} C]` on the existence and functoriality theorems. |
| Additive exact autoequivalence P | `(F : C ⥤ C) [F.Additive] [F.IsEquivalence]`; an equivalence preserves finite limits and finite colimits, so exactness is inferred, rather than added as another hypothesis. |
| Fixed-pair category B and forgetting U | The existing upstream `IsoAlgebra F` and `IsoAlgebra.forget F`. This is exactly the full subcategory of `Endofunctor.Algebra F` on invertible structure maps described by the dependency's `mathlib_match`. No replacement category is defined. |
| Ordinary derived categories | `DerivedCategory`, with separate `[HasDerivedCategory.{w} C]` and `[HasDerivedCategory.{wF} (IsoAlgebra F)]`. |
| M,N have bounded cohomology | `DerivedCategory.TStructure.t.bounded M` and the same predicate for N. Mathlib defines this as bounded below and above for its standard t-structure; `DerivedCategory.isGE_iff` and `isLE_iff` identify these bounds with cohomological vanishing. |
| V^r = Hom(D(U)M,D(U)N[r]) | `CyclicDerivedHom F M N r`, an abbreviation for this exact Hom type; `r : ℤ`, including negative degrees. |
| Termwise structure map θ | `cyclicDerivedStructure`, obtained by localizing the natural isomorphism whose components are the existing `IsoAlgebra.str`, and using `Functor.mapDerivedCategoryCompIso`. The naturality proof is the existing fixed-pair morphism equation `f.hom.h`. |
| T^r(u) = θ_N[r]D(P)(u)θ_M^-1 | `cyclicDerivedHomAction`: first θ_M inverse, then `F.mapDerivedCategory.map`, then its canonical shift comparison, then the shift of θ_N. `Preadditive.leftComp`, `rightComp` and `Functor.mapAddHom` make this a genuine additive homomorphism. |
| Invariants and coinvariants | `cyclicDerivedHomDefect = AddMonoidHom.id _ - cyclicDerivedHomAction`; `CyclicDerivedHomInvariants` is its actual kernel in degree zero, and `CyclicDerivedHomCoinvariants` is the quotient by its actual range in degree minus one. |
| Boundary ∂ | `CyclicDerivedHomBoundary F`, a family of additive homomorphisms on those quotients, indexed by bounded M,N. `exists_cyclicDerivedHomBoundary` asserts existence and uniqueness with the prescribed exactness, morphism naturality, and normalization. |
| Right arrow is forgetting | In `CyclicDerivedHomBoundaryExact`, the existential additive map `q` has values in the actual invariant subgroup and satisfies `(q f).val = cyclicDerivedForget F M N f` for every f. The latter is exactly D(U)(f) followed by the canonical zero-shift identification. This condition uniquely determines q. |
| 0 at both ends; exactness | `Function.Injective (b M N hM hN)`, `Function.Exact (b M N hM hN) q`, and `Function.Surjective q`, with b and q additive. |
| Boundary from free resolution, equivalently off-diagonal extension | `CyclicDerivedHomBoundaryNormalized`. For every short exact sequence of strict fixed-pair complexes A→E→J with split underlying chain projection s, the equation `P(s)θ_E = θ_J s + P(u)θ_A j` says exactly that E's off-diagonal entry is θ_A P(u). The value on the class of u is required to equal `DerivedCategory.triangleOfSESδ hS`, including its sign. |
| Degree-minus-one class in that normalization | `cyclicDerivedOffDiagonalClass` uses `mapDerivedCategoryFactors`, the canonical inverse cancellation `Q(A) ≅ Q(A)[1][-1]`, and the forgetful shift comparison. This places the underlying u in V^-1 for M=Q(J), N=Q(A)[1]. It introduces no arbitrary arrow. |
| Natural under pre/postcomposition in D(B) | `CyclicDerivedHomBoundaryNatural` quantifies over every a:M'→M and c:N→N'. Its square uses precisely `D(U)(a) ≫ u ≫ D(U)(c)[-1]` on representatives. No morphisms are assumed to be strict or to be detected faithfully by forgetting. The right and outer naturalities follow from the natural structure isomorphism and the identified forgetting arrow. |
| A',P',B',U' | Independent `{D : Type uD}`, `[Category.{vD} D]`, `[Abelian D]`, `[IsGrothendieckAbelian.{vD} D]`, autoequivalence G, and separate derived universes wD,wG in the two single-step theorems. |
| H additive and a:P'H≅HP | `(L : C ⥤ D) [L.Additive]`, `(e : L ⋙ G ≅ F ⋙ L)` in Lean's diagrammatic functor-composition convention. |
| H^eq(M,θ)=(HM,H(θ)a_M) | The existing upstream `IsoAlgebra.mapOfNatIso e`; its object action uses exactly `e.app ≫ L.map θ`. |
| H exact; termwise derivation | `cyclicDerivedHom_exact_functorial`, under `[PreservesFiniteLimits L] [PreservesFiniteColimits L]`, uses `(mapOfNatIso e).mapDerivedCategory` and `L.mapDerivedCategory`. |
| Exact forgetting comparison | `cyclicDerivedExactForgetComparison` localizes the existing `mapOfNatIsoCompForgetIso e` and uses the two canonical composition comparisons. It is the ordinary termwise equality expressed through Mathlib's chosen localizations. |
| H left exact; total right derivation | `cyclicDerivedHom_rightDerived_functorial`, under `[PreservesFiniteLimits L]`, uses the recorded `rightDerivedFunctorOfQuasiIsoResolutions` for both functors. It quantifies over arbitrary resolution witnesses hF,hC; these are proof choices whose existence follows from the already stipulated Grothendieck property, not extra mathematical hypotheses. |
| Canonical comparison identity on H(UI) | `cyclicDerivedRightForgetComparison` chooses the uniquely specified isomorphism from the recorded `exists_fixedPairDerivedForgetComparison F G L e hF hC`. That node's unit equation determines this actual comparison; its construction is the identity on the common K-injective computation. No `Nonempty` comparison is chosen without normalization. |
| Canonical right-derived shift comparison | The right-derived theorem asserts existence of coherent `CommShift ℤ` structures for the native and underlying functors and explicitly requires their units to satisfy `NatTrans.CommShift`. This states, rather than assumes, the canonical unit-compatible shift comparison for the arbitrary-resolution interface. |
| Prescribed maps on both outer terms | `cyclicDerivedHomTransport` is α_M, the actual underlying functor applied to u, its shift comparison, then α_N inverse shifted by r. `CyclicDerivedHomBoundaryFunctorial` asserts additivity and T-compatibility of these formulas in every r, so they induce exactly the maps on the kernel and quotient. |
| Whole sequence, including ∂ | The same predicate asserts the right square on every native f and the left square on every quotient representative u. Thus it preserves the specified boundary, not merely forgetting or the existence of some short exact sequence. |
| Functoriality only when source and images are bounded | `CyclicDerivedHomBoundaryFunctorial` quantifies over bounds on M,N,J(M),J(N). It adds no exactness, compactness, or cohomological-dimension assumption. |
| Finite composites | `CyclicDerivedTransport.Generated` has exactly identity, exact, canonical right-derived, and composition constructors. `cyclicDerivedHom_finite_composite_functorial` asserts the full predicate for every such finite word. Composition uses the actual composite functors, the standard composite shift, and the pasted forgetting comparison. |
| Intermediate images may lack an upper bound | Neither `Generated` nor its composition constructor has boundedness hypotheses. The finite-composite theorem assumes only source and final bounds through its conclusion. Its proof docstring explains the auxiliary bounded-below construction needed to paste through such intermediate stages. |
| No derived faithfulness claim | No declaration assumes or asserts faithfulness or injectivity of D(U) on derived morphisms. Its kernel is exactly the displayed image of ∂. |

The finite-diagram data package uses a common chosen ambient object universe u, hom
universe v, and localization universes w,wF for the vertices of one finite diagram;
these four sizes are independent. The single-step functoriality statements additionally
have independent source and target sizes u,v,w,wF,uD,vD,wD,wG. No object universe is
identified with a morphism universe, and no equality of site universes is introduced.
The `checkUnivs` suppression is confined to the packaging structure: its sort is the
maximum of those levels, while its projections retain the separate category sizes.

Dependency declarations used, read with their full signatures and docstrings:

- `def-sp-grothendieck-abelian`: `CategoryTheory.IsGrothendieckAbelian`,
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`, the exact recorded match.
- `def-weil-endofunctor-fixed-pair-category`: its recorded
  `CategoryTheory.Endofunctor.Algebra` and invertible-structure full-subcategory
  specialization, as already implemented by `IsoAlgebra`, `str`, `forget` and
  `mapOfNatIso` in
  `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra` and
  `WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra`.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`, Q and
  the canonical shift, from `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `lem-sf-fixed-pair-derived-forget-comparison`: the existing
  `CategoryTheory.Endofunctor.IsoAlgebra.exists_fixedPairDerivedForgetComparison` in
  `Sheaf.CategoryTheory.FixedPairDerivedForgetComparison`, used directly to select the
  unique unit-normalized comparison. The file and its structural theorem were read.
- `def-sfb-right-derived-functor`: `Functor.rightDerivedFunctorOfQuasiIsoResolutions`
  and `rightDerivedFunctorOfQuasiIsoResolutionsUnit` from the recorded
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`.
- The SES normalization uses the recorded `DerivedCategory.triangleOfSESδ` from
  `Mathlib.Algebra.Homology.DerivedCategory.ShortExact` without redefinition.
- The other stated proof-dependency modules are imported without `public`: Hom out of
  triangles; enough injectives; bounded-below injective representatives; K-injective
  shifts and Hom localization; injective objects; the cohomology long exact sequence;
  and the existing right-derived triangulated interface. Exact termwise derivation and
  the SES triangle are already reached through public statement imports.
- `lem-sf-free-derived-weil-resolution` has no Lean declaration. Its mathematical
  free-resolution argument remains in the proof docstrings. No free-resolution object
  is needed in a signature: the node explicitly permits the equivalent off-diagonal
  normalization, expressed using the existing SES boundary. Consequently no missing
  proof-only node has been silently assumed as a Lean input or restated incompletely.

Edge cases checked before writing and rechecked against the final signatures:

- M=0 or N=0 gives zero Hom groups, zero kernel/quotient and the zero exact sequence.
- P=identity does not force T=identity: θ_M and θ_N remain in the action formula.
  For equal trivial actions over abelian groups, M=Z[0], N=Z[1], V^-1=Z and V^0=0;
  the surviving extension class is allowed and D(U) is not declared faithful.
- If 1-T is an isomorphism on the relevant groups, both outer terms vanish and the
  middle vanishes as the sequence requires. No division or eigenvalue restriction occurs.
- The degree-zero identification is an actual canonical shift isomorphism; r=-1 and
  all other negative degrees are allowed by `r : ℤ`.
- Off-diagonal u=0 produces the split extension with zero connecting map. The matrix
  formula uses the source node's positive upper entry and Mathlib's -p cone convention,
  not a boundary selected up to an arbitrary sign.
- Zero and identity H are permitted in both exact and right-derived cases. A left
  exact functor is not required to preserve arbitrary short exact sequences: the
  proof uses degreewise split sequences of injectives instead.
- The identity constructor covers an empty composite. Mixed finite words are permitted,
  and their intermediate images carry no extra upper-bound requirement.
- Object and morphism universes are separate. Derived-localization morphism universes
  are also independently bound; all variables and universe levels are explicit.

Searches for an existing statement or notion:

| Tool | Query | Result |
| --- | --- | --- |
| `msearch.py leansearch` | Morphisms in the derived category of fixed pairs for an exact autoequivalence fit in a short exact sequence of invariants and coinvariants | Eight generic SES/derived-category/Ext hits, including `triangleOfSESδ`, but no native fixed-pair invariant/coinvariant sequence. The canonical SES boundary was reused. |
| `msearch.py leanfinder` | Morphisms in the derived category of objects with infinite cyclic action form an exact sequence of coinvariants in degree minus one and invariants in degree zero | Eight low-degree group cohomology/homology and long-exact-sequence hits; none states this theorem or its canonical connecting-map functoriality. |
| `msearch.py loogle` | `"IsoAlgebra", "DerivedCategory"` | No hits. |
| `msearch.py grep`, Mathlib `RepresentationTheory/` | `coinvariant\|infiniteCyclic\|homotopyFixed` | Twenty-five hits in induction, finite cyclic homology and ordinary representation coinvariants; no exact match for arbitrary Grothendieck fixed pairs. |
| `rg`, upstream `lean/WeilConjectures` and project `lean/Sheaf` | Item id, `cyclicDerivedStructure`, `CyclicDerivedHom`, `CyclicDerivedSetting`, `CyclicDerivedTransport`, and cyclic/coinvariant searches in the endofunctor and derived-functor directories | No existing declaration for this node. The existing geometric `CyclicDerivedHomComparison*` modules concern cyclic coefficient resolutions, a different statement. Existing fixed-pair, exact-derived and right-derived interfaces were reused. |

The source blueprint proof's last sentence was read, together with the item's detailed
agent-formulated proof and the source declarations above. It does not itself prove the
new native-derived foundation, as the node already records. There is no statement
correction and no mathematical dispute. No new independent definition node or dependency
replacement is required: the auxiliary predicates and finite-word packaging belong to
this node's own sequence and its stated functoriality clause.

Validation uses only the prescribed server `scompile.py` and `deliver2.py` wrappers.
The live repository and upstream library were read only. The final server compilation,
dry-run preflight, and delivery results are recorded by those wrappers.

## Second reading by Q31

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
