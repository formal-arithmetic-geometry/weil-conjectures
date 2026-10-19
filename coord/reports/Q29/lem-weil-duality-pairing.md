## Worker report

The module `Sheaf.Paper.DualityPairing` states
`AlgebraicGeometry.Etale.ambient_duality_pairing`, with proof `sorry`.
The four additional declarations only package its formulas: the double-Hom functor,
the compatibility predicate, and the two site-specific evaluation/transpose predicates.
Their data are fully written out; no definition chooses an unspecified map or uses `sorry`.
All declarations carry the item's blueprint identifier. No node statement is changed.

Hypotheses and clauses, in order:

- A separated finite-type scheme over a field is rendered by `{k : Type u} [Field k]`,
  `{Y : Scheme.{u}}`, `aY : Y ⟶ Spec (.of k)`, and `[IsSeparated aY]`,
  `[LocallyOfFiniteType aY]`, `[QuasiCompact aY]`. The last two conditions together
  are finite type. Nagata's existing instance supplies a compactification, so there
  is no additional compactification hypothesis in the theorem.
- Finite commutative coefficients invertible on the field are
  `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]` and
  `[HasInvertibleExponent Λ (Spec (.of k))]`, the existing exponent convention.
- The ambient etale category is `Etale.DerivedCategoryModule Λ Y`, written out through
  the types of the existing `derivedTensor`, `derivedHom`, and `dualizingComplex`.
  It is the full unbounded derived category of `Sheaf Y.smallEtaleTopology (ModuleCat Λ)`.
- The dualizing object is exactly `Etale.dualizingComplex (ModuleCat Λ) aY`.
  Its definition is ordinary ambient `rightDerivedUpperShriek` of the constant complex,
  i.e. the chosen right adjoint of ordinary `rightDerivedLowerShriek` applied to the unit.
  The finite-coefficient right-adjoint instance is the upstream form of the ambient
  adjoint assertion; the recorded compactification-specific theorem is also imported.
  No pro-etale constructible exceptional functor is used to define this object.
- Internal Hom is the existing `Etale.derivedHom` (respectively `ProEtale.derivedHom`),
  the right adjoint of the existing K-flat derived tensor. Thus `((H.obj (op K)).obj W)`
  is exactly `D K`. `dualityDoubleFunctor H W` is `(H.flip.obj W).rightOp ⋙ H.flip.obj W`,
  including its action on morphisms.
- For every ambient `K`, the predicate binds `e K : DK ⊗ᴸ K ⟶ W`. It does not bind
  an arbitrary pairing without a defining property: the displayed hom-equivalence
  equation says that `K ⊗ᴸ DK → DK ⊗ᴸ K → W` corresponds to `id_DK`.
  The symmetry `b` is fixed component by component by `HEq` with
  `DerivedMonoidal.braiding` at the existing homotopy-to-derived localization.
  This is the descended Koszul braiding, not a merely existing natural isomorphism.
  `HEq` is only a way of stating equality between the two existing presentations of
  the tensor structure without forcing an expensive kernel conversion.
  Koszul symmetry is involutive, so the equation says precisely
  `e K = symmetry(DK,K) ≫ evaluation(K,W)`.
- The next binder is `δ K : K ⟶ DDK`. Its defining equality fixes it to
  `(derivedTensorHomAdjunction A DK).homEquiv K W (e K)`.
  The library adjunction uses *left* tensor. This is the transpose of evaluation
  already written in the order `DK tensor K`; in the blueprint's right-tensor
  Hom-set convention it is the transpose of evaluation after `symmetry(K,DK)`.
- Naturality of evaluation is the first clause of `DualityPairingCompatibility`:
  `(Df tensor id_K) ≫ e K = (id_DL tensor f) ≫ e L` for every `f : K ⟶ L`.
  This is the correct mixed-variance naturality square.
- Naturality of the double-dual map is its second clause:
  `f ≫ δ L = δ K ≫ (dualityDoubleFunctor H W).map f`.
- Compatibility with every integer shift is the existential `s : D².CommShift ℤ`
  and the following equation `δ(K[n]) ≫ s_n(K) = δ(K)[n]`. `CommShift` includes
  naturality and coherence for shift zero and addition, not just unrelated isomorphisms.
- For every distinguished triangle `U`, the final clause both makes its displayed
  `D²` image distinguished and supplies `t : U ⟶ D²(U)` whose three components are
  precisely `δ U.obj₁`, `δ U.obj₂`, `δ U.obj₃`. The `TriangleMorphism` type checks all
  three squares, including the connecting arrow using the same `s.commShiftIso 1`.
- The last conjunct quantifies over every supplied pro-etale ambient object `W` on
  the same scheme and states exactly the same normalized construction there.
  The site is the dependency's existing `Scheme.ProEt.topology Y`, with its actual
  object/morphism universes; no equality between these universes is imposed.
  As in the existing etale coefficient API, the category is written in the
  coefficient-valued presentation `DerivedCategory (Sheaf (ProEt.topology Y)
  (ModuleCat Λ))`: sheaves of Λ-modules, equivalently modules over the constant ring
  sheaf Λ_Y. The recorded `Scheme.proEtaleDerivedCategory` uses the constant-ring
  `SheafOfModules` presentation and an explicit coefficient lift. We retain its
  module and its site; we do not introduce another site, topology, tensor, or Hom.
- Neither the domains of `e` and `δ` nor any predicate contains constructibility,
  boundedness, perfectness, or invertibility of the biduality map. In particular,
  there is no assumption that `D K` is constructible.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`:
  `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
  The associated ordinary right adjoint is exposed by upstream
  `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek`,
  `Etale.rightDerivedUpperShriek` and `rightDerivedUpperShriekAdjunction`;
  `Etale.dualizingComplex` is from `...Derived.Dualizing`.
- `Sheaf.AlgebraicGeometry.DerivedCategories` and upstream
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule`, `Etale.constantComplex`.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `Etale.derivedTensor`;
  `...Etale.Derived.Hom`: `Etale.derivedHom`, `Etale.derivedTensorHomAdjunction`.
  Their pro-etale counterparts are in `...ProEtale.Derived.Tensor` and `...Derived.Hom`.
  These are existing specialized derived tensor/Hom interfaces, not new definitions.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses` and its representative comparisons
  give the recorded general ringed-site K-injective presentation. The existing
  specialized closed-category interface above gives the same derived internal Hom
  as the right adjoint of derived tensor. It avoids inventing a duplicate Hom.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `Scheme.proEtaleDerivedCategory`, `Scheme.ProEt.topology`.
- `WeilConjectures.CategoryTheory.Monoidal.DerivedBraided`:
  `CategoryTheory.DerivedMonoidal.braiding`, its canonical descent from the homotopy
  category's Koszul braiding. This fixes every component of `b` in the predicates.
- `WeilConjectures.Compactification.NagataCompactification`: the existing
  `HasCompactification` instance for the finite-type separated morphism.
- All recorded proof-dependency modules are directly imported, including
  `RingedInternalHomExactRestriction`, `RhomGlobalSections`, `BifunctorShift`,
  `SiteDerivedTensorDescent`, `RingedSiteKInjectiveResolutionsOfUniverses`,
  `HomComplex`, `QuasiIsoHomComplexMap`, `KFlatResolutionIndependentCoefficients`,
  `KInjectiveHomComplex`, derived category `Basic`, and
  `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor` (`NatTrans.mapTriangle`).
  The theorem docstring gives all six proof steps, including the signed double-Hom
  representative, the cone comparison, and the connecting square.

Edge cases checked: `K = 0`, `W = 0` in the pro-etale clause, the empty scheme,
zero coefficients, shift zero, positive and negative shifts, and arbitrary unbounded
complexes. All formulas still type in these cases. No nonemptiness or nonzero condition
was added. Evaluation and δ are not asserted to be isomorphisms. The diagonal signs
are necessary: on local homogeneous sections the double-Hom representative is
`x(f) = (-1)^(pq) f(x)`. The proof docstring retains the exact shift sign
`χ = -s_(T(C),-1) ∘ T(s_(C,1))⁻¹` and the cone triangle's negative projection.

Searches actually run:

- `msearch.py ... leanfinder` with query “Derived internal Hom evaluation defines a
  natural double dual morphism compatible with shifts and distinguished triangles”:
  eight hits, chiefly Ext functoriality, `MonoidalClosed.internalHom_map`, generic
  currying and `ihom.ev`. No complete derived duality/shift/triangle statement.
- `msearch.py ... loogle 'CategoryTheory.MonoidalClosed.curry'`: twelve hits, including
  curry/uncurry, their inverse laws and naturality in the generic closed category.
  They give ingredients rather than the complete node.
- `msearch.py ... grep 'doubleDual|bidual|evaluation' CategoryTheory/Monoidal/Closed`:
  two hits, the evaluation and coevaluation docstrings in `Closed/Basic.lean`.
- `msearch.py ... leansearch` for “Derived internal Hom evaluation and the double dual
  natural transformation compatible with shifts”: unavailable, Internal Server Error.
  This was not treated as a negative search result.
- Direct `rg` of upstream `WeilConjectures` for the item id: no occurrence.
  Searches for `bidualityMap|dualityPairing|doubleDual|biduality.*shift|biduality.*triang`
  find `ProEtale.GeometricOperations.bidualityMap` in `ProEtale/TraceFormula/Defs.lean`.
  Its definition is package-dependent and supplies neither the ambient evaluation
  dinaturality nor coherent shifts/triangle compatibility. It is not the same statement.
- Direct `rg` of existing `lean/Sheaf` and the upstream declaration-name index:
  no complete pairing statement and no collision with any of the five delivered names.
  Upstream `Etale.Derived.Dualizing`, `Etale.Derived.TensorStructure`, and
  `ProEtale.Derived.Hom` were read: constructible biduality is a different theorem;
  tensor symmetry and tensor-Hom adjunction are existing ingredients used here.

Validation: all compilation was through `scompile.py`, file by file. Initial direct
construction of the maps triggered the known kernel conversion cost between monoidal
presentations and was replaced by exact adjunction normalization in Prop. The final
statement packages uniquely specified maps, not arbitrary maps. The final single-file
compile is clean; the expected sorry is the sole postponed theorem. No `#check` or
scratch declarations occur in the delivery module. No statement dispute was found.

## Second reading by Q29

I read the unchanged node and all five statement dependencies, their recorded Lean
signatures and source modules, and the complete delivery module independently. There
are no new definition nodes, dependency modules or statement_change in this delivery.
The four auxiliary declarations package this item's construction and conclusion; none
defines a second tensor product, internal Hom, topology or dualizing object.

The local literature checkout contains only the literature indexes, not Stacks TeX.
I fetched the published upstream sites-cohomology.tex and derived.tex into this item's
scratchpad and read the internal-Hom section, including its standing ringed-site
hypothesis, equation-internal-hom, lemma-internal-hom (08J9),
lemma-section-RHom-over-U (08JA), lemma-RHom-triangulated (08JC), and the triangle
and distinguished-triangle definitions. The official corresponding pages are
https://stacks.math.columbia.edu/tag/08J9,
https://stacks.math.columbia.edu/tag/08JA and
https://stacks.math.columbia.edu/tag/08JC. These passages impose no boundedness,
constructibility or perfectness condition on the complexes. The additional field,
finite-type and coefficient hypotheses come from the node's geometric specialization.

Objects, hypotheses and conclusion clauses, in the node's order:

1. A field and a separated finite-type scheme over it: `{k : Type u} [Field k]`,
   `{Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))`, `[IsSeparated aY]`,
   `[LocallyOfFiniteType aY] [QuasiCompact aY]`. Verdict: exact. Finite type is the
   last two conditions together. There is no extra Noetherian, dimension or
   compactification binder; the Nagata instance supplies the latter.
2. Finite commutative coefficients invertible on the field: `(Λ : Type (u + 1))`,
   `[CommRing Λ] [Finite Λ] [HasInvertibleExponent Λ (Spec (.of k))]`. Verdict: exact,
   in the project's established ModuleCat coefficient universe. This is a ring,
   not an extra coefficient field.
3. The ambient etale derived category: the category in Etale.AmbientDualityPairing
   specializes to `DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat Λ))`.
   Verdict: exact; I checked DerivedCategories and the upstream coefficient
   definition, rather than substituting a bounded or constructible category.
4. The object omega = RaY^times A: the theorem passes
   `Etale.dualizingComplex (ModuleCat Λ) aY`. Verdict: exact. I opened Dualizing
   and UpperShriek: the definition applies the chosen ordinary right adjoint of
   ordinary ambient derived lower shriek to the monoidal unit. The finite-ring
   adjoint instance supplies this adjunction. The recorded compactification
   adjoint module is imported, and no constructible exceptional functor is used.
5. D = RHom(-,omega): `Etale.derivedHom A X`, contravariant in its first argument.
   Verdict: exact. The recorded DerivedInternalHomOfUniverses is the general
   ringed-site K-injective model; I read it and the already existing etale and
   pro-etale derivedHom interfaces. The latter are the internal right adjoints
   of the K-flat-derived tensor, hence the same RHom by its defining adjunction.
6. For every ambient K, evaluation DK tensor K to omega: the existential family
   `e : ∀ K, ((derivedTensor A X).obj (((derivedHom A X).obj (op K)).obj W)).obj K
   ⟶ W`. Verdict: exact, including variance and quantifier scope. This is fixed
   to evaluation by its following homEquiv equation, rather than left arbitrary.
   I checked the actual signature: the library fixes the LEFT tensor factor K.
   Thus `homEquiv DK W (b(K,DK) ≫ e K) = 𝟙 DK` fixes precisely the evaluation
   in the displayed order DK tensor K. The b components are fixed by HEq to
   DerivedMonoidal.braiding at Qh and the homotopy quasi-isomorphisms. I read that
   declaration and its descent characterization: this is the Koszul symmetry.
7. Its transpose K to DDK: the existential delta family has precisely that type,
   and `δ K = (derivedTensorHomAdjunction A DK).homEquiv K W (e K)` fixes its
   value. Verdict: exact. In the source's RIGHT-tensor convention this is the
   transpose after symmetry; the difference is the adjunction convention, not
   a changed map. The double functor is `(H.flip.obj W).rightOp ⋙ H.flip.obj W`,
   so it acts on morphisms by D applied twice, not just on objects.
8. Naturality of evaluation: the first compatibility conjunct says
   `(Df tensor id_K) ≫ e K = (id_DL tensor f) ≫ e L`, for every `f : K ⟶ L`.
   Verdict: exact. Both sides have source DL tensor K and target W.
9. Naturality of delta: the next conjunct says
   `f ≫ δ L = δ K ≫ (dualityDoubleFunctor H W).map f`. Verdict: exact.
10. Compatibility with shifts: `∃ s : D².CommShift ℤ` followed by
    `δ (K[n]) ≫ (s.commShiftIso n).hom.app K = (shiftFunctor C n).map (δ K)`.
    Verdict: exact. The comparison is coherent for zero and addition and the
    same s is used in the triangle clause, not an unrelated comparison.
11. A morphism of distinguished triangles: for every distinguished U the
    displayed D²-image triangle is distinguished, and `∃ t : U ⟶ ...` fixes
    all three components to the respective delta maps. Verdict: exact. The
    Triangle morphism type includes the third square, and its target connecting
    arrow uses `D².map U.mor₃ ≫ (s.commShiftIso 1).hom.app U.obj₁`.
12. The same formal construction on the pro-etale site for a supplied ambient
    dualizing object: the last conjunct is `∀ W, ProEtale.AmbientDualityPairing ... W`.
    Verdict: exact. Its e, delta, canonical-braiding equations and compatibility
    predicate are the same formulas on `Sheaf (Scheme.ProEt.topology Y) (ModuleCat Λ)`.
    I checked ProEtaleDerivedCategory, the actual ProEt site, ProEtale.Derived.Hom,
    and the framework note. Module-valued sheaves give the coefficient-valued
    presentation of modules over the constant ring sheaf on this same site.
    The recorded SheafOfModules/ULift presentation is equivalent, not a different
    topology. No equality of site object and morphism universes is assumed.
13. No assumption that DK is constructible: neither predicate, family of maps,
    compatibility definition nor theorem binder imposes this. Verdict: exact.
    Nor is evaluation or delta asserted to be an isomorphism.

Edge cases: K = 0 and the supplied pro-etale W = 0 are allowed; no Nonzero or
Nonempty premise appears. The empty scheme is covered (its structural morphism is
separated and finite type). The zero coefficient ring is not excluded. Every
characteristic satisfying HasInvertibleExponent is covered, with no extra
characteristic-zero or algebraically-closed assumption. Shifts quantify over all
integers, including zero and negative shifts; no finite-amplitude bound appears.
There is no index set in the statement. The site and coefficient universes are
the existing six-functor convention; the generic compatibility definition keeps
category object and morphism universes independent. autoImplicit is false, all
variables/universes are bound, and the theorem uses no extra coefficient-category
instances beyond those synthesized for ModuleCat.

Independent searches performed in this reading:

- msearch leanfinder: “Contravariant internal Hom into a fixed object composed
  twice, bidual natural transformation preserving triangle connecting maps”.
  Eight hits: internalHom_map, coevaluation naturality and generic currying or
  triangulated Yoneda lemmas. None states the complete item.
- msearch loogle `CategoryTheory.Functor.rightOp`: twelve hits. I checked its
  type and object formula; this validates the double-functor construction and
  provides no complete duality compatibility theorem.
- msearch grep `bidual|doubleDual|dualityDouble|DualityPairing` in
  CategoryTheory/Monoidal/Closed: zero hits. Direct rg over all Mathlib, upstream
  WeilConjectures and repository lean/Sheaf found no complete existing item or
  collision with the five delivered declaration names.
- Those direct searches found upstream SheafOfModules.bidual,
  PresheafOfModules.bidual, toIhomIhomUnit and GeometricOperations.bidualityMap.
  I opened the last declaration and its hypotheses: it depends on a geometric
  operations package and its chosen dualizing object. The others concern
  underived module sheaves or duality into the monoidal unit. None supplies
  ambient arbitrary-W duality together with coherent shifts and all triangle
  squares, and none is duplicated by these packaging predicates.
- msearch leansearch for the evaluation transpose natural transformation
  commuting with shifts and triangles returned Internal Server Error. This is
  recorded as unavailable, not as evidence of absence.

H5/H6/H8/H9: all four definitions have explicit data and no sorry. The sole theorem
is postponed with sorry, as stage 2 requires. Each declaration names its source
and blueprint node. The theorem docstring retains the six proof steps, including
the signed representative, K-flat/K-injective currying, the exact double-Hom cone
comparison and its negative projection, and the connecting square. There are no
file-local definitions, notation or instances, and every Lean line is within 100
characters. The node's lean.statement was checked verbatim against the file.

Mismatches and changes: no mathematical or interface mismatch found; no Lean or
node change was needed. I added this independent audit and its search records.
Compilation through `scompile.py Q29 lem-weil-duality-pairing
lean/Sheaf/Paper/DualityPairing.lean` passed for the sandbox and library views,
with no errors or warnings. The proof remains intentionally sorry.
