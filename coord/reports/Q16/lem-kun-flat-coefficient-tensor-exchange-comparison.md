## Worker report

This stage-2 delivery states `AlgebraicGeometry.Etale.flatCoefficientTensorExchangeComparison`
in `Sheaf.AlgebraicGeometry.FlatCoefficientTensorExchangeComparison`. It contains six
fully constructed helper definitions and one theorem, whose sole proof is `sorry`.
The natural-language statement and seven proof steps are unchanged. This is stage 2,
not a re-split of N5's independently PASS-reviewed stage-1 delivery.

### Hypotheses and clauses

- A unital homomorphism of commutative rings is `(φ : R →+* B)` with
  `{R B : Type (u + 1)} [CommRing R] [CommRing B]`. No flatness, surjectivity,
  finiteness, nontriviality or coefficient characteristic is assumed.
- The four schemes are `{Y Z T S : Scheme.{u}}`; the four arrows have exactly
  the stated domains and codomains, and `w : h ≫ f = e ≫ g` is the specified
  commutativity equality. There is no `IsPullback`, qcqs or geometric hypothesis.
- Their sites are the recorded `V.smallEtaleTopology`. Coefficients and module
  sections use `Type (u + 1)` and `ModuleCat.{u + 1}`. This is the existing
  small-etale/derived-category size convention: site object universe u+1 and
  morphism universe u; no equality of these universes is imposed.
- Constant-coefficient module sheaves are `Sheaf V.smallEtaleTopology (ModuleCat R)`.
  These are the fixed-coefficient encoding specified in the recorded
  `def-weil-pbc-derived-categories`, not a new module-sheaf category.
- Flatness of M is `exactFunctor _ _ (tensorRight M)`: exactness of tensor by M,
  exactly the fixed-coefficient interpretation explicitly authorized in the
  recorded `def-pc-flat-sheaf-modules` lean.note. The imported predicate is the
  same `CategoryTheory.exactFunctor` used by `SheafOfModules.IsFlatOnSite`.
- M_B is `(primeCoefficientQuotient φ Z).obj M`, the existing sheafification of
  objectwise scalar extension, defined using `Sheaf.composeAndSheafify` and
  `ModuleCat.extendScalars`. Its conventional B tensor_R M order is canonically
  the symmetric presentation of the node's M tensor_R B. The second conjunct
  states flatness of M_B for every flat M, without a flat ring-map hypothesis.
- U_V is the existing `Sheaf.restrictScalars V.smallEtaleTopology φ`, and its
  exact termwise derived descent is `Sheaf.derivedRestrictScalars`.
  The first conjunct asserts exactness and `ReflectsIsomorphisms` on D for
  every V, hence conservativity on its full bounded-below subcategory as well.
  These functors keep the underlying abelian sheaf and maps; no replacement
  functor or unspecified comparison is introduced.
- N ranges over `_root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat B))`.
  Its `.obj` is the object in the full unbounded category. In
  `flatExchangeRestrictedInput`, `DerivedCategory.Plus.ι` is followed by exact U.
  N may have a negative lower bound; it need not be a sheaf or bounded complex.
- `flatExchangeSource R f g M` is exactly M[0] tensor^L f^-1 Rg_* of its input.
  `flatExchangeTarget R h e M` is exactly Rh_*(h^-1 M[0] tensor^L e^-1 of its input).
  `primeSingle`, `primePullback`, `primePushforward` use the recorded degree-zero,
  inverse-image and direct-image functors. Tensor is the recorded `derivedTensor`.
  The helper definitions simply assemble these functors and their maps in M.
- The families `a` and `b` are natural isomorphisms from the R expressions at U_T N
  to U_Z of the B expressions at N. Their functor domains are D+(T,B).
  They are displayed in D(Z,R) via its fully faithful inclusion of D+(Z,R).
  The final conjunct supplies a common integer n and `.IsGE n` for each of the
  two R and two B endpoints. Thus the displayed isomorphisms are literally
  isomorphisms of bounded-below objects, equivalently isomorphisms in D+(Z,R);
  the full derived-category inclusion loses no maps, inverses or equations.
- Their ordinary representative normalization uses the existing
  `PrimeTensorCoefficientNormalized` with the actual scalar-extension unit on Z
  and its canonical inverse-image coefficient arrow on Y. This predicate tests
  every cochain complex and fixes the localization diagram on each representative.
  Its `PrimeTermwiseTensorCompatibility` specifies the actual unit followed by
  the lax tensorator: m tensor n goes to (1 tensor m) tensor n. In the symmetric
  presentation this is precisely (m tensor 1) tensor n. Its inverse necessarily
  sends (b tensor m) tensor n to m tensor bn, since the balanced relation rewrites
  (b tensor m) tensor n as (1 tensor m) tensor bn. These formulas hold on local
  tensor generators and extend by sheafification, not on fictitious sectionwise
  descriptions of sheaf tensors. The normalized natural isomorphisms fix the
  forward map and its inverse, rather than asserting arbitrary object isomorphisms.
- The source normalization equation is `(1 tensor f^-1 directMate_g);a =
  (1 tensor pullbackComparison_f);ΦZ`. The target equation is
  `b;directMate_h = Rh_*(d)`, where `flatExchangeInnerRestriction` is the
  pullbackComparison_e followed by ΦY. Both equations use the existing canonical
  `scalarRestrictionDirectImageMap`. Its direction is U Rg_B -> Rg_R U, so
  these equations express precisely the inverses δ_g and δ_h in the proof.
  It is invertible on the bounded-below inputs at issue by the recorded bounded
  comparison theorem; no assertion of invertibility on all unbounded objects
  and no injective-preservation hypothesis is substituted.
- Naturality in N is part of the `NatIso` types, for every derived map in D+.
  The next two conjuncts give naturality in every map k : M -> M' between flat
  sheaves, using `flatExchangeSourceMap` and `flatExchangeTargetMap`, with actual
  scalar extension applied to k. The same families a,b satisfy all clauses.
- α_R and α_B are the existing `tensorBaseChangeMap` in
  `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary`. I read its definition:
  it is the adjunction transpose under h^-1 adjoint to Rh_* of monoidal pullback,
  composition comparisons through w, and e^-1 of the counit for g, exactly as
  specified by the node. The penultimate conjunct is `α_R ≫ b.hom = a.hom ≫ U.map α_B`,
  Lean's left-to-right composition rendering of b circle α_R = U(α_B) circle a.

### Recorded dependencies used

All original stmt_deps were read, including full recorded signatures and docstrings.
The metatheoretic `def-weil-size-convention` has no declaration, as its record says.

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, morphisms;
  `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, `Scheme.Etale`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`, exposing the `CategoryTheory.exactFunctor` predicate
  used in its recorded fixed-coefficient interpretation.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `Etale.DerivedCategoryModule`, `DerivedCategory.Plus`, `DerivedCategory.IsGE`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  the recorded sheaf tensor and independent-site-universe infrastructure;
  fixed-coefficient tensor is the already installed `Sheaf` monoidal tensor.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`. For the constant-coefficient encoding the
  identical notion is the existing `CategoryTheory.Sheaf.restrictScalars` from
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars`, and its
  exact descent `Sheaf.derivedRestrictScalars` from `...Sheaf.DerivedBaseChange`.
  No private copy, new scalar action or dependency-node rewrite is needed.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `Etale.derivedTensor`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `Etale.upperStar`, `Etale.lowerStar`, their adjunction; their existing derived
  functors are the definitions wrapped by `primePullback` and `primePushforward`.
- Added already-landed statement dependencies:
  `def-kun-prime-coefficient-constructions` / module
  `Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReductionFoundation`:
  `primeCoefficientQuotient`, `primeCoefficientQuotientUnit`, `primeCoefficientTensorMap`,
  `primeSingle`, `primePullback`, `primePushforward`;
  `def-kun-prime-coefficient-pullbacks` / module
  `Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReductionPullbacks`:
  `primePulledSheaf`, `primePullbackCoefficientMap`, `primePullbackSingleIso`;
  `def-kun-prime-coefficient-iso` / module
  `Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReductionNorm2`:
  `PrimeTensorCoefficientIso`;
  `def-kun-prime-coefficient-normalization` / module
  `Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReductionCompat`:
  `PrimeTensorCoefficientNormalized`;
  `def-kun-scalar-restriction-comparison-maps` / existing module
  `Sheaf.Paper.EtaleUnboundedRestrictionComparison`:
  `scalarRestrictionPullbackIso`, `scalarRestrictionDirectImageMap`.
  All four coefficient-definition nodes state the general-ring constructions,
  despite their historical prime-coefficient names. Their dependency closures
  were checked for a return path to this item: none exists.
- Proof-only recorded imports are retained, including exact-functor cohomology,
  derived factorization, sheafification, flat module pullback, K-flat criteria,
  exact inverse image, inverse-image monoidality, site composition, ordinary
  pullback tensor comparison, scalar derived adjunction identities and mates.

### Edge cases and source check

Read Stacks `etale-cohomology.tex`, `lemma-punctual-base-change-upgrade` (0F1J),
especially the two coefficient identities and the phrase "by the flatness of E.
Similarly for the other term." The node explicitly generalizes these identities
and supplies their canonical-map compatibility. No claim of the Kunneth/base-change
map itself being invertible is made.

Checked R=B with φ the identity (balancing comparison); a non-flat coefficient
map Z -> F_p with M the constant free rank-one sheaf; B=0; R=0 (which forces B=0
for a unital map); M=0; N=0; empty schemes; identity scheme arrows; arbitrary
negative shifts of N. A noncartesian square is allowed: Y empty and Z=T=S a
point, f=g identities; both paths of the exchange equation are zero and b has
zero endpoints. No cohomological-dimension bound, scheme finiteness or ring-map
flatness has entered the signature. Dropping flatness of M would not compute
derived scalar extension by ordinary scalar extension (for example M=Z/p),
so the exact tensor hypothesis is retained. No disputed statement, statement correction or dependency module is required. The repair adds the definition-owner node below.

### Searches

- `msearch.py ... leanfinder "Flat coefficient tensor exchange commutes with
  restriction of scalars on derived etale module sheaves"`: eight hits, on
  Kaehler differentials and ordinary formally-etale base change; no match.
- `msearch.py ... loogle 'SheafOfModules.restrictScalars, "tensor"'`: zero hits.
- `msearch.py ... grep 'restrictScalars.*[Tt]ensor|[Tt]ensor.*restrictScalars'
  CategoryTheory`: zero hits.
- `msearch.py ... leansearch "Restriction of coefficients commutes with flat
  sheaf tensor product and derived tensor exchange"`: eight hits, including
  `SheafOfModules.restrictScalars`, ordinary module flat tensor results and
  `PresheafOfModules.Monoidal.tensorObjMap`; none states this derived exchange square.
- `rg` in `lean/WeilConjectures/SixFunctors/Etale` and `lean/Sheaf` for tensor/restriction,
  coefficient exchange and 0F1J located the existing ordinary Kunneth map,
  scalar comparisons and the generic prime-coefficient normalization modules.
  The prime-torsion theorem is only for Z/n -> F_l and degree-zero second sheaves,
  so it is not this arbitrary-ring, arbitrary D+ statement. Its generic definitions
  are reused and cited, not rewritten.
- `rg` for the exact item id in `lean/WeilConjectures` returned no declaration;
  searches of `lean/Sheaf`, `lean/WeilConjectures` and `dag/lean_names_upstream.json`
  for every new declaration name returned no hit. The main statement has no exact
  existing declaration, so `existing: false` is appropriate.

### Validation

The full module compiled cleanly through the prescribed `scompile.py`, both as
sandbox and at its intended module name (21.4 s and 15.2 s for the initial complete
statement). All variables and universe levels are explicitly bound; there are no
file-local definitions, notations, instances or diagnostic commands. Every helper
has real data and a source/blueprint docstring. The single postponed theorem has
the full seven-step source-based proof plan in its docstring and its matching DAG
node. Final compile and prescribed delivery preflight are run before pushing.

## New nodes

`def-kun-scalar-restriction-comparison-maps` records the already existing
`AlgebraicGeometry.Etale.scalarRestrictionPullbackIso` and
`AlgebraicGeometry.Etale.scalarRestrictionDirectImageMap`, in
`Sheaf.Paper.EtaleUnboundedRestrictionComparison`, with `existing: true`.
For any unital map of commutative rings A to B in Type(u+1) and any scheme
morphism f : Z to W in universe u, rho is exact derived descent of the canonical
sheaf inverse-image/restriction isomorphism, transported through the canonical
left-derived/exact identifications; d is its right-adjunction mate. The node
asserts no ambient invertibility for d. Source: Stacks 03FD, 0D6J(3), and 07A7.
The three fresh searches are recorded verbatim in mathlib_searches: LeanSearch
returns eight ordinary restriction results, Loogle finds no named identifier,
and Mathlib grep finds zero hits. Project grep and DAG scans locate the two
existing definitions but no definition node owning them. Blueprint search finds
related condensed coefficient constructions, which use different categories.
The ancestor command returns None through the maintainer-created intermediate
node, as already documented on this item; the new blueprint record follows it.
No Lean module or declaration is duplicated.

The signatures, verbatim from the live server module, are:

```lean
def scalarRestrictionPullbackIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {Z W : Scheme.{u}} (f : Z ⟶ W) :
    Sheaf.derivedRestrictScalars W.smallEtaleTopology φ ⋙
        L(upperStar (ModuleCat.{u + 1} A) f) ≅
      L(upperStar (ModuleCat.{u + 1} B) f) ⋙
        Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ
```

```lean
def scalarRestrictionDirectImageMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {Z W : Scheme.{u}} (f : Z ⟶ W) :
    R(lowerStar (ModuleCat.{u + 1} B) f) ⋙
        Sheaf.derivedRestrictScalars W.smallEtaleTopology φ ⟶
      Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ ⋙
        R(lowerStar (ModuleCat.{u + 1} A) f)
```

## Repair of independent review at 52f4a8f0d3b8

H2 repaired: replace only the added theorem entry in stmt_deps by
`def-kun-scalar-restriction-comparison-maps`. Keep
`lem-sbc-canonical-restrict-scalars-functor-comparisons` in proof_deps, where
its bounded-below invertibility is needed. Both ambient maps are plain defs;
neither is extracted by choice or asIso from that theorem. The item module,
its theorem signature, the natural-language statement, and all seven proof steps
are retained. The initial saved-packet dry run passed as af45c9a63de, but the
reviewer's semantic ownership fault is repaired in this packet. Comparison
against current main showed that the saved item differs only in lean and
added stmt_deps; all unrelated current node fields are retained by delivery.
The live server source was read with scompile.py --source and agrees with
the local comparison module.

Self-check of the new node: the two ring types, CommRing instances, ring map,
scheme universes and morphism are exactly its explicit binders; the first
result is the specified natural isomorphism U_W followed by Lf_A versus
Lf_B followed by U_Z; the second is Rf_B followed by U_W to U_Z followed by
Rf_A, exactly the right mate. The composite isos and mateEquiv bodies construct
the data explicitly. Identity coefficients, zero rings, empty schemes, and
arbitrary unbounded derived inputs are permitted. No flatness hypothesis or
boundedness is added to the map definitions. The original theorem's clauses
and edge cases were accepted in the independent review and are retained.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
