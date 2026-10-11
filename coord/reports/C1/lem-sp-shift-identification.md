## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.ShiftIdentification` states the three
clauses of lem-sp-shift-identification. It introduces no definitions; its three named
theorems have `sorry` proofs. The canonical isomorphisms already exist as ingredients,
but neither Mathlib nor the source has the whole composite with this domain and all
three clauses as a declaration. The source's Grothendieck spectral-object proof and
`grothendieckSpectralObjectHIso` use this composite for different, special domains.

Hypotheses and notation, clause by clause:

- Abelian categories A and B are `{C : Type u₁} [Category.{v₁} C] [Abelian C]` and
  `{D : Type u₂} [Category.{v₂} D] [Abelian D]`. All six universe variables, including
  the localization morphism universes `w₁`, `w₂`, are explicitly declared.
- A has enough injectives: `[EnoughInjectives C]`. No enough-injectives hypothesis on
  B, and no Grothendieck hypothesis on either category, is added. The node mentions
  Grothendieck only as an example of the enough-injectives condition.
- Left exact additive v is `(F : C ⥤ D) [F.Additive]` together with an explicit
  `[PreservesFiniteLimits F]` binder on EACH theorem. The latter is deliberately
  not merely a section variable, since Lean could omit an unused section instance.
- The categories D+ and Rv are the standard `DerivedCategory.Plus C`,
  `DerivedCategory.Plus D`, and `F.rightDerivedFunctorPlus`. The
  `[HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]` binders specify the
  localization sizes, not a mathematical smallness restriction; every category
  has the standard localization at a sufficiently large universe.
- K in Ch+(A) is the domain `CochainComplex.Plus C` of the two natural isomorphisms,
  and `(K : CochainComplex.Plus C)` in the vanishing theorem. The functor `Hq` is
  `CochainComplex.Plus.ι C ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q`.
  Thus `Hq.obj K` is H^q(K), and its map on a chain map is the induced cohomology map.
- X[0] is `S.obj X`, with `S := DerivedCategory.Plus.singleFunctor C 0`.
  X[-q] is its literal shift via `shiftFunctor (DerivedCategory.Plus C) (-q)`.
  This avoids substituting another single-complex model for the specified shift.
- p,q in Z are `(p q : ℤ)` in part 1 and part 3. Part 2 uses `(n : ℕ) (q : ℤ)`
  and p = `(n : ℤ)`, which covers exactly all p >= 0, including zero.
- Sigma is `(RF.commShiftIso (-q)).app (S.obj (Hq.obj K))`. This is the source's
  transported shift structure on the bounded below right derived functor: its
  unit commutes with shifts, and its components compare injective resolutions.
- Tau is `(H.shiftIso (-q) (p + q) p (by omega)).app (RF.obj (S.obj (Hq.obj K)))`,
  where `H := DerivedCategory.Plus.homologyFunctor D 0`. `H.shift a` is the
  cohomology functor in degree a. The proof in this expression only certifies
  the arithmetic index identity -q+(p+q)=p; it proves no mathematical lemma.

Part 1 is `exists_rightDerived_shift_identification`: existence of a natural
isomorphism of functors from Ch+(A) to B, with source
`Hq ⋙ S ⋙ shiftFunctor _ (-q) ⋙ RF ⋙ H.shift (p + q)` and target
`Hq ⋙ S ⋙ RF ⋙ H.shift p`. The equation for EVERY component `e.app K` specifies
exactly `H^(p+q).mapIso sigma ≪≫ tau`. Consequently this is the displayed composite,
not an unspecified isomorphism between its endpoints. Naturality in every chain map
K -> K' is part of the type of the natural isomorphism `e`.

Part 2 is `exists_rightDerived_shift_identification_nonneg`. Its source is the same
functor with p = n and its target is `Hq ⋙ F.rightDerived n`. Every component is
required to be the SAME sigma/tau composite followed by
`F.homologyRightDerivedFunctorPlusObjSingleFunctorIso (Hq.obj K) n`, the canonical
injective-resolution comparison H^n(RF(X[0])) -> R^n F(X). The intermediate object
is visible in the types of these factors. Again, `e` is a natural isomorphism, so
naturality in K is encoded, and not merely objectwise nonemptiness.

Part 3 is `isZero_rightDerived_shift_identification`, with `(hp : p < 0)`.
Its conjunction asserts `IsZero` for H^(p+q)(RF(X[0][-q])), H^p(RF(X[0])), and the
negative-degree ordinary derived functor under the node's convention. Since
`Functor.rightDerived` is indexed by Nat, that last convention is written inline as
`if p < 0 then (0 : D) else (F.rightDerived p.toNat).obj X`. In particular negative
p is NOT converted to `rightDerived 0`. This also covers the middle term's notation
H^p(Rv(H^qK)): as the node specifies, an unshifted object means placement in degree zero.
`IsZero` is the invariant meaning of an object being zero in an abelian category;
no equality to a particular implementation's chosen zero object is asserted.

Dependency declarations read and reused:

- def-sp-left-exact-additive: `CategoryTheory.Functor.Additive` in
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`, `PreservesFiniteLimits` in
  `Mathlib.CategoryTheory.Limits.Preserves.Finite`, and `Functor.rightDerived` in
  `Mathlib.CategoryTheory.Abelian.RightDerived`. The recorded
  `InjectiveResolution.isoRightDerivedObj` is the underlying ordinary-resolution
  computation used by the source's canonical comparison.
- def-sp-grothendieck-abelian: `CategoryTheory.IsGrothendieckAbelian` in
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`, read as the node's
  optional example, not imposed as an extra assumption.
- def-sp-kinjective-bridge: read all four declarations in
  `Sheaf.CategoryTheory.KInjectiveBridge`, notably
  `Functor.rightDerivedComplexWithResolution`. That declaration names F(I) for a
  PARTICULAR chosen resolution and is not itself the choice-independent derived
  functor or its shift structure. This statement uses the already-existing canonical
  `F.rightDerivedFunctorPlus` of Mathlib, which is computed on bounded below injective
  resolutions; these are K-injective. No private resolution notion or second derived
  functor is introduced, and no arbitrary choice is mistaken for a natural functor.
- def-weil-pbc-bounded-derived-subcategories: `DerivedCategory.Plus` in
  `Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
- def-weil-abstract-derived-category: `DerivedCategory`, its localization and
  `DerivedCategory.homologyFunctor`; the restriction to Plus uses
  `DerivedCategory.Plus.homologyFunctor` and `singleFunctor` in
  `Mathlib.Algebra.Homology.DerivedCategory.Plus`.
- The used shift comparison comes from
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`,
  whose CommShift instance is transported along `rightDerivedFunctorPlusIsoInjectiveObject`.
  Its `commShift_rightDerivedFunctorPlusUnit` identifies this with resolution comparison.
- The comparison in part 2 is `Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso`
  from `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle`;
  its full signature, docstring, and naturality theorem were read. The module's single
  import provides all the ingredients actually used in these signatures.
- Tau is `Functor.shiftIso` from `Mathlib.CategoryTheory.Shift.ShiftSequence`.

Edge cases checked before writing: K = 0, H^q(K) = 0, q = 0, positive and negative q,
p = 0, arbitrary positive p, and p < 0 including p+q >= 0. The last case still vanishes
because the shifted input is cohomologically >= q and p+q < q. No bounded-above condition,
finite cohomological dimension, or Grothendieck assumption is added. The p = 0 comparison
is the usual H^0/R^0 comparison. Nothing excludes zero or trivial abelian categories.
There are no field or characteristic assumptions and no index-family nonemptiness
assumptions. The signs give X[-q] in degree q, and tau has degree -q+(p+q)=p.

Searches performed (the service queries are logged in searches.jsonl):

- LeanFinder through msearch.py: "cohomology of a right derived functor applied to a
  shifted single object is the right derived functor, naturally". Eight hits, including
  `DerivedCategory.singleFunctorIsoCompQ` and `Functor.mapDerivedCategorySingleFunctor`;
  no declaration of the full statement (the latter concerns exact functors).
- Loogle through msearch.py: "CategoryTheory.Functor.rightDerivedFunctorPlus,
  CategoryTheory.Functor.rightDerived". Zero hits.
- Mathlib grep through msearch.py: "shift.*rightDerived|rightDerived.*shift" in
  Algebra/Homology. Zero hits.
- LeanSearch through msearch.py: "right derived functor cohomology of shifted single
  complex natural isomorphism". Service unavailable: Internal Server Error; recorded
  as unavailable, no mathematical verdict inferred from this failure.
- rg of WeilConjectures and lean/Sheaf for the item id and shift-identification names:
  no item declaration. Direct inspection of PlusSingle, the source's
  Mathlib/.../RightDerivedFunctorPlus, and SpectralSequence/Grothendieck found the
  component isomorphisms and an embedded/specialized composite, not this full statement.
- rg of dag/lean_names_upstream.json, Mathlib, WeilConjectures and lean/Sheaf for each
  proposed full declaration name: no clash. No new notion or definition node is needed.

The blueprint source file named by the node is not installed in this read-only clone.
The node's complete statement and six-step proof were read; the underlying source places
were opened directly: [Stacks 05SU](https://stacks.math.columbia.edu/tag/05SU) for shifts and
[Stacks 05TC](https://stacks.math.columbia.edu/tag/05TC) for negative vanishing. The source
Lean implementations were also read. No statement correction and no dispute is needed.

Server validation: the final module compiled cleanly through scompile.py, with no warnings.
The first compile required opening the standard `ZeroObject` scoped instance for the
inline negative-degree convention; the final source uses `open scoped ZeroObject`.

## Second reading by C1

Independent second reader: I opened the node copy, the entire delivered module, all five
statement dependency nodes and their recorded declaration sources. There are no new nodes,
no dependency modules in this delivery, and no statement_change record to audit.

Object/hypothesis/conclusion checklist (each verdict: exact):

1. A and B are arbitrary abelian categories: C and D with separate object universes u₁/u₂,
   morphism universes v₁/v₂, Category and Abelian instances. No ring, field, scheme,
   finiteness, or Noetherian hypothesis is imposed.
2. A has enough injectives: [EnoughInjectives C]. The optional Grothendieck example is
   not imposed; B needs no injectives. I read IsGrothendieckAbelian in its Mathlib source.
3. v is additive and left exact: (F : C ⥤ D), [F.Additive], and explicit
   [PreservesFiniteLimits F] on each theorem. I read Functor.Additive,
   preservesFiniteLimits_of_preservesKernels and rightDerived/isoRightDerivedObj:
   finite-limit preservation is equivalent here to the node's kernel-preservation clause.
4. D+ and Rv: DerivedCategory.Plus, F.rightDerivedFunctorPlus, and separate
   HasDerivedCategory localization universes w₁/w₂. I read TStructure.Plus, the standard
   localization instance, and the bounded-below derived-functor definition and unit.
   No object-universe or morphism-universe equality is required. These implement the
   localization and bounded-below condition stated by the dependency nodes.
5. Resolution meaning: I read KInjectiveResolutionChoice and
   rightDerivedComplexWithResolution in Sheaf.CategoryTheory.KInjectiveBridge.
   The latter retains one chosen resolution; it is not a canonical functor on D+.
   The delivered theorem correctly uses the existing total right derived functor,
   rather than making a private copy or mistaking that choice-dependent definition
   for a functor. I read rightDerivedFunctorPlusIsoInjectiveObject and its CommShift
   instance: it computes by termwise F on bounded-below injectives, which are K-injective.
6. K is any bounded-below cochain complex: the two natural isomorphisms have domain
   CochainComplex.Plus C, and the third theorem binds K of that same type. Hq is the
   inclusion followed by the usual homologyFunctor in degree q; X in part 3 is
   K.obj.homology q, the identical cohomology notion.
7. p and q are integers: (p q : ℤ). Part 2's n : ℕ with p = (n : ℤ) covers exactly
   p ≥ 0, without losing p = 0 or restricting q.
8. X[0] and X[-q]: S = DerivedCategory.Plus.singleFunctor C 0 and its literal
   shift by -q. I read singleFunctor and singleFunctorιIso; it is the degree-zero
   single complex in D+, shifted so that X occurs in degree q.
9. sigma is the canonical resolution comparison:
   (RF.commShiftIso (-q)).app (S.obj (Hq.obj K)). The source's transported shift
   instance and commShift_rightDerivedFunctorPlusUnit give precisely this comparison,
   including the unit shift and all positive/negative iterates.
10. tau is the canonical cohomology shift:
    (H.shiftIso (-q) (p + q) p (by omega)).app (RF.obj (S.obj (Hq.obj K))).
    I read ShiftSequence.shiftIso and the Plus homology ShiftSequence instance;
    the arithmetic premise is -q + (p + q) = p, with the correct direction.
11. Part 1: exists_rightDerived_shift_identification gives a natural isomorphism e
    between the displayed endpoint functors. Its equation for every e.app K identifies
    it with H^(p+q).mapIso sigma followed by tau. This states the specified composite,
    and a natural isomorphism encodes naturality for all chain maps K → K'.
12. Part 2: exists_rightDerived_shift_identification_nonneg uses the identical two
    factors followed by homologyRightDerivedFunctorPlusObjSingleFunctorIso (Hq.obj K) n.
    I opened that declaration and its naturality theorem in PlusSingle.lean: its source
    is H^n(RF(X[0])) and its target is (F.rightDerived n).obj X, computed using an
    injective resolution. The intermediate endpoint and specified comparison are exact.
13. Part 3: isZero_rightDerived_shift_identification binds hp : p < 0 and asserts all
    three zero-object clauses with IsZero: shifted derived cohomology, unshifted derived
    cohomology, and the ordinary derived functor's negative-degree convention. The inline
    conditional returns zero for p < 0; it does not accidentally identify negative p
    with rightDerived 0. This is exactly the node's explicit convention.

Source check: the local literature checkout has no Stacks .tex or blueprint source body.
I read the official raw Stacks derived.tex and homology.tex on GitHub, including
situation-derived-functor, lemma-derived-shift (05SU),
lemma-enough-injectives-right-derived (05TI), definition-higher-derived-functors (015A),
lemma-negative-vanishing (05TC), definition-shift-cochain (011G) and
 definition-cohomology-shift (011H). The general shift situation assumes an exact functor
on triangulated categories and a compatible saturated multiplicative system; the
termwise additive functor on homotopy categories and quasi-isomorphisms provide these
here. Enough injectives ensures RF is everywhere defined on D+. No extra ambient
hypothesis is missing. References:
https://raw.githubusercontent.com/stacks/stacks-project/master/derived.tex
https://raw.githubusercontent.com/stacks/stacks-project/master/homology.tex

Edge cases: zero K or zero H^q(K), zero abelian categories, q = 0, either sign of q,
p = 0, arbitrary positive p, and p < 0 with p+q ≥ 0 are all included. In the last
case the lower bound after shifting is q, and p+q < q, so vanishing is consistent.
The zero shift is handled by the standard commShiftIso and shiftIso unit laws.
There is no index family, scheme, characteristic, or coefficient ring to constrain.
All six universes are explicitly bound and localization sizes are independent.

Independent H4 searches used different phrasing from the first reader:
- LeanFinder via msearch.py: "natural identification cohomology shifted derived single
  object ordinary right derived functors". Eight hits: singleFunctorIsoCompQ,
  mapDerivedCategorySingleFunctor (exact functors), and other localization/cohomology
  ingredients; none states these three clauses or the specified natural composite.
- Loogle via msearch.py: "Functor.shiftIso". The remote index rejected the short
  identifier; no mathematical absence claim follows. I read the actual pinned
  ShiftSequence.shiftIso/Functor.shiftIso signatures directly.
- LeanSearch via msearch.py: "cohomology right derived shifted degree zero complex
  natural isomorphism negative degrees vanish". Service returned Internal Server Error;
  unavailable, not a negative mathematical verdict.
- grep via msearch.py: "commShiftIso.*homology|shift_identification|shift.*singleFunctor.*rightDerived"
  returned no hits. Direct rg on pinned Mathlib, WeilConjectures, and lean/Sheaf used
  shiftIdentification, shift_identification, shift.*rightDerived, rightDerived.*shift,
  and grothendieckSpectralObjectHIso. I read the latter's source and the embedded
  nonempty_grothendieckSpectralObject_H_iso composite: these concern spectral-object
  truncations and nonnegative spectral-sequence indices, not arbitrary K and integer
  p,q as here. PlusSingle supplies the unshifted canonical comparison, not this item.
  Therefore keep the module; no duplicate definition or missing notion was found.

H5/H6/H8/H9: no definitions or hollow data; exactly three named theorem sorries.
The arithmetic omega terms certify only index equalities. The three docstrings cover
proof steps 1–4, then step 5, then step 6 with their cited proof nodes, and each names
its source and blueprint id. The single import supplies used declarations; namespace,
line lengths, and explicit universe/variable binding comply. The node's lean.statement
was checked programmatically against the exact first theorem signature and is verbatim.

Mismatches and changes: none found in the statement, dependencies, or Lean module.
I left correct code and node fields unchanged and added this independent review only.
