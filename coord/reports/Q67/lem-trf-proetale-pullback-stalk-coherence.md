## Worker report

Repair of the returned immutable head `353ac7ec5cd1`. The saved packet was inspected
first and `deliver2.py --no-push` accepted its syntax and compilation (dry-run commit
`fc11b87f3c`). The required clause-by-clause self-check still found the semantic defects
listed in the return. The existing module and node were retained and repaired; this is
not an unchanged re-push. The node's mathematical statement, proof, source, and all
statement and proof dependencies are unchanged. Only its `lean` field changes.

The module is `Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence`, main declaration
`AlgebraicGeometry.Scheme.proEtalePullbackStalkCoherence`. All theorem proofs are `sorry`;
all definitions have real data. The comparison and reparametrization are selected from
**unique, explicitly germ-normalized** characterizations, never from mere `Nonempty` or
an unnormalized existential. Uniqueness fixes the data up to the equality used downstream,
as allowed by AGENTS §5. The auxiliary declarations are parts of this node's specified
comparison, identity, reindexing and derived descent; all are in `lean.declarations`.

The hypotheses and clauses are rendered as follows:

1. The finite commutative ring is `(A : Type u) [CommRing A] [Finite A]` in the main
   theorem and `ProEtalePullbackStalkCoherent`. The schemes and maps are unrestricted
   `h : Z ⟶ Y`, `f : Y ⟶ X`, and `t : T ⟶ S`, with `Scheme.{u}`. The recorded
   `proEtaleRingModules` and `proEtaleConstantRing` use the original `ProEt` site:
   objects have universe `u+1`, morphisms `u`. Coefficients are `ULift.{u+1,u} A`,
   exactly as in the recorded operations and stalk functor; no site universes are
   identified. Geometric points are `x : Spec (.of Ω) ⟶ T` with `Ω : Type u`,
   `[Field Ω] [IsAlgClosed Ω]`, inside the chosen site bound.
2. The natural A-linear comparison is `proEtalePullbackStalkComparison A t x`, a
   natural isomorphism from pullback followed by `finiteCoefficientModuleStalkFunctor`
   to the stalk at `x ≫ t`, in `ModuleCat (ULift A)`. Thus linearity and naturality
   in the module are part of its type. `proEtaleCoefficientModuleGerm` is the actual
   coprojection of the recorded underlying additive colimit, with the existing module
   action and restriction of scalars; it is not a second stalk construction.
3. The forward represented-germ formula is the first half of
   `ProEtalePullbackStalkGermNormalized`. Here `P` is `(U,u')`, `N.right` is `V`,
   `θ : P.right ⟶ (proEtaleBaseChange t).obj N.right`, and `a : M(V)`. The equality
   `P.hom.left ≫ θ.left ≫ pullback.fst N.right.hom t = N.hom.left` says exactly
   that the target lift is `pr_V θ u'`. The source germ is the restriction along θ
   of the actual normalized module-adjunction unit section. Its image under c is
   the germ `[V,pr_V θ u',a]`. All such representatives are quantified, not only
   representatives at an identity neighbourhood.
4. The inverse formula is the second half of that predicate. A lift `l` to the
   base-change object with its specified projection is necessarily `(x,w)` by the
   fibre-product universal property. The inverse sends `[V,w,a]` to the unit section
   at `StructuredArrow.mk l`. `proEtalePullbackStalkComparison_existsUnique` specifies
   both formulas in Lean, and the first conjunct of the main proposition asserts
   them for the selected canonical c.
5. Bounded coefficient complexes are `H : CochainComplex (...) ℤ` with
   `∃ a b : ℤ, ∀ n, n < a ∨ b < n → IsZero (H.X n)`. The old termwise complex
   functors are retained. `proEtaleCoefficientStalk_exact` supplies precisely the
   exactness used in proof step 5. `proEtaleFiniteCoefficientDerivedStalk` is the
   existing exact-functor `mapDerivedCategory` construction. The derived c is formed
   from `Functor.mapDerivedCategoryCompIso` and
   `Functor.mapDerivedCategoryNatIso` applied to the normalized module c. The latter
   is Mathlib's `Localization.liftNatIso` through ordinary `DerivedCategory.Q`, as
   in the recorded localization node. The fifth conjunct explicitly equates its
   component on `Q.obj H`, after the factorization isomorphisms, with `Q.map` of
   the termwise comparison. This replaces the old tautology `IsIso (Q.map iso.hom)`.
6. The composition equation is the sixth conjunct, an equality of morphisms in the
   **ordinary derived category** on `DerivedCategory.Q.obj H`. Its first factor is
   the derived stalk of
   `(proEtaleConstantRingPullbackComposition h f A).inv.app (Q.obj H)`.
   This is the recorded canonical chi, in the requested direction: the existing
   constant-ring comparison is the inverse of `proEtaleCanonicalPullbackComposition`,
   transported along `proEtaleConstantRingCompositeCoefficients_eq`. It is followed
   by c for h at `Lf*H` and c for f at `v ≫ h`. The last `eqToHom`, using
   `Category.assoc v h f`, only identifies the two parenthesizations of the same
   geometric point. There is no existential per-object compositor `a`.
7. The identity comparison `proEtaleStalkIdentityPullback` is independently fixed by
   its inverse's section formula: the identity-pullback unit followed by restriction
   along `(MorphismProperty.Over.pullbackId ...).inv`. Its derived version uses
   `Functor.mapDerivedCategoryNatIso` and the canonical localization identity unitor
   `Functor.mapDerivedCategoryIdIso`. The third conjunct equates c for the identity
   with the stalk of this canonical module identity comparison; the seventh makes
   the same assertion on bounded complexes in D. `Category.comp_id x` supplies the
   explicit point transport. Neither equation is hom composed with its own inverse.
8. For every `α : Ω ≃+* Ω`, `proEtaleStalkNeighbourhoodReparam x α` is the actual
   `StructuredArrow.map` induced by `Spec.map (CommRingCat.ofHom α.toRingHom)` over T.
   It sends `(V,w)` to `(V,Spec(α) ≫ w)` and leaves the object and section unchanged.
   `proEtaleStalkReparam_existsUnique` specifies the induced colimit isomorphism r
   by that formula on **every** germ. The second conjunct states the formula for
   the selected r. The fourth conjunct is `c ≫ r = r ≫ c` on module stalks, with
   only the point-associativity transport added. The eighth is precisely that
   equation on `Q.obj H` in D, using `proEtaleDerivedStalkReparam`. The comparisons
   are natural isomorphisms of functors, so termwise naturality and naturality after
   localization are retained, rather than replaced by a bare existential isomorphism.

Dependency declarations read and used:

- `def-weil-geometric-point`: the recorded inline `IsAlgClosed` field and scheme
  morphism representation, with Mathlib's `Scheme.SpecToEquivOfField` interpretation.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.ProEt` and `ProEt.topology`.
- `prop-weil-pbc-proetale-constant-ring-map`:
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`,
  `AlgebraicGeometry.ProEtale.finiteCoefficientInverseImageMap_isIso` and the
  constant-preserving coefficient identification. The module pullback uses the
  recorded `proEtaleConstantRingComparison`, not a chosen coefficient isomorphism.
- `def-weil-pbc-proetale-operations`:
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`,
  `Scheme.proEtaleConstantRingPullback`, `proEtaleConstantRingAdjunction`, and
  `proEtaleConstantRingDerivedPullback`. Their actual unit occurs in both germ
  formulas and in the identity normalization.
- `def-weil-proetale-geometric-stalk`:
  `Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor`,
  `Scheme.geometricRingModuleStalkFunctor` and `finiteCoefficientModuleStalkFunctor`;
  `ProEtaleGeometricNeighbourhood` and its forgetful functor from the reexported
  `ProEtaleGeometricStalk` module are used for the actual coprojections and reindexing.
- `def-weil-proetale-inverse-image`: `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
  the recorded base-change functor, module inverse image, sheaf adjunction and constant
  coefficient map. The germ formulas use the existing pullback and its normalized unit.
- `lem-weil-pbc-proetale-derived-pullback-composition`:
  `Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition`,
  `Scheme.proEtaleCanonicalPullbackComposition`. Its constant-coefficient transport
  is `Scheme.proEtaleConstantRingPullbackComposition` in
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison`. That declaration
  now occurs in the composition equation; this import is used.
- `lem-weil-pbc-localization-universal-property`: the Mathlib match
  `CategoryTheory.Localization.liftNatIso`, `liftNatTrans`, and `natTrans_ext`.
  The exact-functor derived comparison interfaces used here implement this same
  localization at quasi-isomorphisms, with the explicit representative equation.

Proof-only imports are the published `ProEtaleInverseImageStalk`,
`ProEtaleSheafificationGeometricStalk`, and `ProEtaleClassicalStalk` modules. Their
recorded declarations `proEtaleInverseImage_abelianStalk`,
`proEtaleGeometricStalk_sheafification`, and `proEtale_classical_stalk` are cited by
name at the precise steps of the construction/proof docstrings. They supply the
canonical underlying comparison, invariance under sheafification, and exactness.
They are imported without `public`, as required for proof dependencies. The unused
old `ProEtaleModulePullbackComposition` import was removed.

Edge cases checked: the zero finite ring is allowed (unitary modules then vanish);
there is no nontrivial-ring hypothesis. A zero complex and an empty range of nonzero
terms satisfy the boundedness predicate. The identity and every composable pair of
scheme morphisms are included with no flatness or properness assumption. An empty
scheme has no geometric point, and that quantified case is vacuous without altering
its site or coefficient definitions. The identity automorphism is included, and the
inverse reindexing uses alpha inverse. All point reparenthesizations and the identity
point are explicitly transported, so exponent-zero and identity cases are not dropped.
No K-flatness of H, injectivity, constructibility, completion, characteristic, or
nonemptiness assumption has been added.

Searches retained from the original packet: `msearch.py ... leanfinder
"canonical inverse image geometric point fibre functor compatible with composition
and field automorphism reparametrization"` found only ordinary scheme fibres and
Galois fibres; `loogle "stalkPullback"` found ordinary topological stalk maps;
`grep "stalkPullbackIso|stalk.*[Cc]omp|[Cc]omp.*stalk"` found only ordinary sheaf
stalk declarations; `leansearch "pro etale derived pullback geometric stalk
isomorphism composition coherence"` found no matching statement. These exact
results remain recorded in the node's `mathlib_searches`.

Repair searches: `msearch.py Q67 lem-trf-proetale-pullback-stalk-coherence leanfinder
"pro etale geometric stalk pullback normalized germs derived composition
reparametrization"` returned eight ordinary structure-sheaf stalk/germ results,
no matching pro-etale statement. `loogle '"mapDerivedCategoryCompIso"'` returned
seven exact-functor localization interfaces; their pinned upstream source was read.
`grep 'StructuredArrow.map|pullback.*stalk|stalk.*pullback' CategoryTheory/Comma`
returned 17 comma-category/reindexing references; `StructuredArrow.map` supplies
our actual reindexing functor. `rg` over the permitted Mathlib, upstream
`WeilConjectures`, and shared `lean/Sheaf` sources found the published inverse-image
stalk comparison, normalized derived chi and module stalk functor used here, but no
existing declaration of this node or the new coherence family. No new independent
notion or dependency module was introduced.

No `STATEMENT-DISPUTED` issue or node statement correction was needed. The source
places were read in full: sites.tex Tags 05V1/0F4F, proetale.tex Tag 0993, and
sites-cohomology.tex Tag 0D6D, including the canonical representative/K-flat formulas.

## Repair checklist

- H3/H6: removed arbitrary c/a and the identity and derived tautologies; c is fixed
  by both representative formulas, chi is the canonical derived comparison, and
  identity and reparametrization are actual equations, also in D.
- H4/H9: use the existing stalk, coefficient/pullback operations and canonical chi;
  define derived comparisons by the existing localization construction. The generic
  canonical inverse-image stalk comparison is a proof import with its explicit role
  in the proof docstring. Removed the unused module-composition import.
- H8: the main theorem now has all five proof steps, including the two restriction
  relations, identity unit, canonical compositor, reindexing, and derived descent.
  Each auxiliary postponed construction has a complete proof docstring too.
- H11: the second reading below is a clause-by-clause match against the actual repaired
  declarations and explicitly records what differs from the returned head.

## Second reading by Q67

I reread the full node, the return entry, the saved module/report, the repaired file,
and the actual dependency signatures/docstrings. In order through the node:

- “finite commutative ring”: the main theorem and proposition bind A, CommRing and
  Finite. No characteristic or nonzero restriction is hidden in the helpers.
- “schemes, composable maps, small pro-etale sites”: unrestricted h and f, the original
  recorded ProEt and constant-ring module categories, site universes u+1/u preserved.
- “canonical inverse-image coefficient identifications”: the recorded pullback and its
  specified normalized adjunction unit occur literally in the germ and identity formulas.
- “bounded complex and geometric point”: explicit cochain complex, both integer bounds,
  Ω/Field/IsAlgClosed and a morphism from Spec Ω in every relevant conjunct.
- “natural A-linear c”: the selected object is a natural isomorphism of module-valued
  functors; its existence theorem has unique germ normalization in its Lean type.
  This replaces the returned unnormalized existential family.
- “forward germ”: P, θ, a and the target-lift equation in the first normalization
  clause encode every displayed representative and its exact projected germ.
- “inverse germ”: the second normalization clause uses the pullback-unit section and
  the paired lift, forced by both projections. Both formulas are now Lean clauses,
  rather than prose in a docstring.
- “composition with chi”: the sixth conjunct applies the stalk to the inverse of the
  recorded `proEtaleConstantRingPullbackComposition`, hence to the canonical chi in
  the node's direction. It is an equation in D on QH; no per-object a remains.
- “identity”: the third and seventh conjuncts use the independently unit-normalized
  canonical identity-pullback isomorphism, at modules and in D, with comp_id transport.
  The former hom/inv cancellation tautology has been removed.
- “r defined by neighbourhood reindexing”: `StructuredArrow.map` actually reindexes
  neighbourhoods, and the second conjunct states the value of the chosen colimit iso
  on every germ. The former unspecified Nonempty iso has been removed.
- “r composed with c equals c composed with r”: the fourth and eighth conjuncts are
  exactly that square, on modules and on bounded derived complexes. The explicit
  assoc transport only identifies the two equal point maps; no compatibility is dropped.
- “termwise and ordinary derived localization”: the fifth conjunct identifies the
  derived c with Q of its termwise maps through the existing factorization isos;
  the last three conjuncts give the requested equations in D. Functor naturality is
  built into c, r and their localized natural isomorphisms. The old IsIso tautology
  has been replaced by this representative equation and the three coherence equations.

The theorem docstring was compared against each of the node's five proof steps:
colimit/germ normalization and scalar action; naturality and identity; canonical chi;
field reindexing and its square; exact termwise descent and localization uniqueness.
Every step is present, with the recorded dependency that supplies it. Helpers have real,
uniquely determined data and independent construction-proof docstrings. All binders and
universes are explicit (`autoImplicit false`). No node fields outside lean were edited.

## Validation

The final repaired module passed the prescribed `scompile.py Q67
lem-trf-proetale-pullback-stalk-coherence` file-only compilation, both sandbox
(8.4 seconds) and library namespace (21.9 seconds), with no errors or warnings.
A separate packet check confirms that only the node's `lean` field changes, its
recorded signature is verbatim from the module, every line is at most 100 characters,
and the five named postponed theorems have exactly five `sorry` proofs.
The current shared node was reread: its statement agrees verbatim with this packet,
and the returned module has not been landed in the shared read-only source tree.
Delivery and rebasing use only the prescribed wrappers.
