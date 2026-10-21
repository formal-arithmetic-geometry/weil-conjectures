## Worker report

The delivery states `lem-sfb-constructible-cocone-ambient-realization` in
`Sheaf.AlgebraicGeometry.ConstructibleCoconeAmbientRealization`. Its four theorem declarations
jointly render the node; each proof is `sorry`. Four accompanying constructions provide the
actual ambient vertex functor, its canonical derived and termwise realization isomorphisms,
and its transported integer-shift comparison. These have real data, with no choice of an
unspecified isomorphism and no additional mathematical notion or dependency node.

Source read: the main-20261015 blueprint,
`sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/lem-sfb-constructible-cocone-obj.proof.md`,
Modules and Complexes paragraphs, including the exact scalar extension, cone and finite-stage
triangulatedness argument. The item and every statement dependency were read with their
recorded declaration signatures and docstrings. The current server source of `TwoColimit`
and `ProEtaleModule.DerivedCategory` was also obtained using `scompile.py --source`.

Hypotheses and clauses, in order:

- The scheme is `(X : Scheme.{u})`, the prime is `(ℓ : ℕ) [Fact ℓ.Prime]`, and its fixed
  algebraic closure is `PadicAlgCl ℓ`. An index `E : PadicAlgCl.FiniteIntermediateField ℓ`
  is exactly an intermediate field finite-dimensional over the p-adic base. Its given norm
  and topology are the restricted ambient ones. There is one explicit universe `u`; the
  coefficient abelian sheaves have universe `u + 1`, as in the recorded framework.
- The topologically Noetherian hypothesis is `[TopologicalSpace.NoetherianSpace X]` in
  `constructibleCocone_ambient_triangulated` and the canonical shift instance. The elementary
  coefficient, predicate and comparison identities and realization definitions need no
  Noetherianity; the assertion about inherited triangles retains exactly this hypothesis.
- The coefficient rings are the existing `padicSubfieldRingObj X ℓ E` and
  `padicAlgClRingObj X ℓ`. `constructibleCocone_coefficient_identifications` first identifies
  them with `sfbPullbackFromPoint` applied to `Profinite.continuousMapRingObj E` and
  `Profinite.padicAlgClRingObj ℓ`. The latter is the finite-subextension-valued function sheaf,
  not unrestricted continuous functions to the algebraic closure. The definitions of the
  pulled-back rings use the same transported pointwise monoid structure; no ring structure
  or coefficient morphism is replaced.
- The same theorem identifies `PadicSubfieldConstructible` and `PadicAlgClConstructible`
  with the archived `BoundedConstructible (condensedRingObj ... X)` categories. This is a
  type equality of the existing full subcategories: the ambient module categories,
  boundedness predicate, morphisms and all cohomology objects are unchanged. In particular
  boundedness remains vanishing outside a finite integer interval as in
  `mem_boundedConstructible_iff`, with no Tor-amplitude or completeness condition.
- `constructibleCocone_constructibility_identifications` states both finite-field and closure
  cases. Each right side introduces `S : Scheme.Stratification X`, its indices `a : Fin S.n`,
  a pro-etale `Scheme.Cover` of `S.domain a`, and a local finite presentation on each cover
  member. The coefficient and module are pulled back first along `S.immersion a`, then
  `𝒰.f i`, using the recorded `upperStar` and `mapMod`. `Mod.IsFinitelyPresented` is exactly
  the existing existential of finite ranks `m,n : ℕ`, a map `finiteFree R m ⟶ finiteFree R n`
  and an isomorphism with its cokernel (Free.lean:50-51). Thus the finite locally closed
  stratification, pro-etale locality and finite free cokernel clauses all appear.
- In `constructibleCocone_ambient_triangulated`, the first conjunct is
  `(boundedConstructible (padicSubfieldRingObj X ℓ E)).IsTriangulated`. Mathlib's full
  subcategory instances give precisely the inherited pretriangulated structure, with
  distinguished triangles detected by the inclusion. The next conjunct is additivity of
  every integer shift on `PadicSubfieldConstructible X ℓ E`; the third is triangulatedness
  of its actual full inclusion `.ι`.
- `constructibleCoconeAmbientFunctor` is defined as `(constructibleCocone X ℓ).Φ E ⋙ ι_Ω`,
  exactly the specified composite. The next conjunct makes this functor triangulated into
  the ordinary unbounded `DerivedCategory (Mod ... (padicAlgClRingObj X ℓ))`. No triangulated
  structure on the closure constructible category is needed for this definition or assertion.
- `constructibleCoconeAmbientDerivedIso` is the reflexive isomorphism with
  `ι_E ⋙ derivedExtendScalarsToPadicAlgCl X ℓ E`: these functors are definitionally equal,
  because the actual vertex is the lift of that ambient functor on the full subcategory.
  `constructibleCoconeAmbientTermwiseIso` composes it with the existing canonical
  `leftDerivedFunctorIsoMapDerivedCategory`, whiskered by `ι_E`. Its target is exactly
  `ι_E ⋙ (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapDerivedCategory`,
  hence ordinary exact scalar extension applied termwise. The canonical transported
  `CommShift` is `Functor.CommShift.ofIso` along the inverse of this specific isomorphism;
  the last conjunct asserts shift compatibility of its forward natural transformation.
- Finally `constructibleCocone_ambient_comparisons` quantifies over the actual `h : E ≤ F`
  and every `K` in the finite-stage full subcategory. It states that applying `ι_Ω.map` to
  the forward component of `(constructibleCocone X ℓ).iso h` is the forward component of
  `derivedExtendScalarsCompIso X ℓ h` at `K.obj`, and separately states the inverse equation.
  These are componentwise equations of the already specified natural comparisons, not an
  existence claim for alternative comparison isomorphisms. The source/target identifications
  are definitional, exactly those supplied by `constructibleCoconeAmbientDerivedIso`.

Dependency declarations used:

- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicSubfieldCondensedRing` (95-100),
  `Profinite.padicAlgClCondensedRing`, `Profinite.padicAlgClRingObj` (220-229).
  The finite-field node has no `lean` field but its closed upstream audit explicitly records
  the first declaration; it is therefore already usable under brief-stage2 section 0.
- `Sheaf.AlgebraicGeometry.ProEtalePointPullback`:
  `AlgebraicGeometry.ProEtale.sfbPullbackFromPoint` (the alias of `upperStarFromPoint`).
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing` publicly exports the archived
  condensed module construction, including `condensedRingObj` and the bounded constructible
  operations. Its commutativity declaration is the recorded coefficient-node interface;
  the particular archived category in the node uses the existing
  `Profinite.continuousMapRingObj E`, as specified there.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`:
  `PadicSubfieldConstructible`, `PadicAlgClConstructible`, `constructibleCocone`,
  `constructibleExtendScalars`, `constructibleToPadicAlgCl`,
  `constructibleToPadicAlgClCompIso`, `derivedExtendScalarsToPadicAlgCl`,
  `derivedExtendScalarsCompIso`, and the constructibility-preservation declarations.
- `WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def`:
  `IsConstructibleModuleObject`, `IsLocallyFinitelyPresented`;
  `WeilConjectures.CategoryTheory.ModuleObjects.Free`: `Mod.IsFinitelyPresented`.
- `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`:
  `boundedConstructible`, `BoundedConstructible`, `mem_boundedConstructible_iff`.
- `Mathlib.CategoryTheory.Triangulated.Subcategory`:
  `CategoryTheory.ObjectProperty.IsTriangulated` (182), the canonical full subcategory
  `Pretriangulated` instance (693), and triangulated inclusion instance (719).
- The exact canonical comparison used in the construction is
  `CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory`, in the upstream
  `CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory` (128-132).
  Its uniqueness/counit normalization is already part of the existing definition.
- The stated proof dependencies' modules are imported, including
  `CondensedConstructibleSerre`, `CoefficientBoundedConstructibleProEtale`,
  `LeftDerivedTotalTensorExact`, `Colimit.Compatibility`, and Mathlib's additive/exact-derived
  interfaces. Proof-only imports stay ordinary imports as required by stage 2.

Edge cases checked before writing: the empty scheme permits the empty stratification; zero
modules admit the rank-zero presentation; zero complexes meet boundedness; ranks can be zero;
`ℓ = 2` is allowed and nonprimes are excluded only by the stated prime assumption. The bottom
finite coefficient field, the identity inclusion `E ≤ E`, all finite inclusions and every
integer shift (including zero and negative shifts) are admitted. There is no assumption of
Noetherian rings, nonempty strata, finite Tor dimension, completeness, separation, smoothness
or nonempty scheme. The closure coefficient retains its finite-image-subextension condition.

Searches performed (actual logged calls):

- msearch leanfinder: `Bounded constructible condensed l-adic coefficient cocone ambient
  triangulated realization exact scalar extension`. Eight hits: generic condensed solid/free
  and exact-colimit/locally-constant constructions; none gives this realization or its maps.
- msearch loogle: `CategoryTheory.ObjectProperty.IsTriangulated,
  CategoryTheory.Functor.IsTriangulated`. Six hits: generic full-subcategory, essential-image,
  inverse-image and lift triangulatedness interfaces. Reused the relevant full-subcategory
  interface; none states the coefficient identification and prescribed comparisons.
- msearch grep: `constructibleCocone|padicSubfieldRingObj|padicAlgClRingObj`: zero Mathlib hits.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf`: searched the node id,
  `ambientRealization`, `ambient_realization`, `constructibleCocone`,
  `padicSubfieldRingObj`, `padicAlgClRingObj`, and bounded-constructible interfaces. Found the
  exact upstream coefficient/cocone ingredients used above. Existing `CondensedTateRealization`
  concerns a different Tate realization, and no existing theorem states the present bundle.
  A direct node-id grep in `WeilConjectures` returned no hit.

No statement correction, disputed statement, new node or dependency repair is required.

Validation: the initial server compile diagnosed using `S.stratum a` (a set) where the
pro-etale cover needs `S.domain a` (the scheme stratum). This was corrected in both coefficient
cases. All theorem proofs remain `sorry`; none is proved in this stage.

The revised module compiled cleanly through `scompile.py`, both as its sandbox module
(20.3 seconds) and under its delivered library module name (22.1 seconds), with no warnings.

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
