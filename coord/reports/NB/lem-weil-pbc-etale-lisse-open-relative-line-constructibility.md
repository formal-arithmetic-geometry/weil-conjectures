## Worker report

The module `Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility` states
`AlgebraicGeometry.Etale.isConstructibleEtaleModuleSheaf_lisse_openRelativeLine_shriek`.
Its sole theorem has proof `sorry`; it introduces no definitions. The node is unchanged
except for its `lean` record. No statement correction or disputed statement is needed.

Source read: Stacks Project `literature/stacks-project/more-etale.tex`, Tag 0GKY,
label `lemma-loc-constant-shriek-rel-dim-1`, including the whole proof. That source assumes
an affine Noetherian finite-dimensional base and a torsion Noetherian coefficient ring.
The node specializes these to a finitely generated integer algebra and a finite ring,
respectively. The finite local trivializations below are the finite-type locally constant
module sheaves in that source.

Hypotheses and clauses, matched individually:

- Finite commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
- Finitely generated integer algebra: `(R : Type u) [CommRing R]
  [Algebra.FiniteType ℤ R]`. The canonical integer algebra structure is used. Generation
  as an integer algebra is exactly generation by finitely many elements as a ring.
- The base `Y = Spec R` appears literally as `Spec (.of R)` throughout the signature;
  an arbitrary isomorphic affine presentation adds no mathematical case.
- The relative affine line is Mathlib's `AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R))`.
  Its index type has exactly one element at the scheme universe.
- An arbitrary open subscheme is the binder `U : (...).Opens`, with scheme `U.toScheme`.
  This includes every open with its canonical open subscheme structure.
- The restricted projection is the explicit composite
  `U.ι ≫ (AffineSpace ... (Spec (.of R)) ↘ Spec (.of R))`.
- The module sheaf is `L : Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
- Local triviality with finite module values is `hL`: an existing
  `Scheme.LocallyConstantDatum L` supplies a jointly surjective étale cover and local
  constancy; for each member we require `M : ModuleCat Λ`, `Finite M`, and a module-sheaf
  isomorphism from `L.over ...` to `(constantSheaf ... (ModuleCat Λ)).obj M`.
  The witness for local constancy is redundant *data within the same existential*, not an
  additional hypothesis; precisely the existing definition's trivialization datum is used.
- A complex in degree zero is
  `(_root_.DerivedCategory.Plus.singleFunctor (Sheaf ... (ModuleCat Λ)) 0).obj L`.
- Every chosen compactification is the arbitrary binder `c : Compactification (...)`.
  This structure has the proper factor `c.g`, open factor `c.i`, and their factorization
  equality. Upstream allows non-quasi-compact open factors in general. Here its open factor
  is automatically quasi-compact: the restricted projection is quasi-compact since the
  relative line is Noetherian, and `Compactification.quasiCompact_openImmersion_iff`
  identifies quasi-compactness of `c.i` with that of the projection. Thus the binder covers
  exactly the node's compactifications without imposing an extra condition.
- The opening paragraph about general separated finite-type qcqs morphisms explains the
  convention for shriek; it does not assert a second theorem about arbitrary morphisms.
  The restricted projection in this statement has those properties automatically, since
  it is an open restriction of the affine line over a Noetherian affine base.
- Bounded-below compactification-dependent shriek is exactly the existing
  `rightDerivedLowerShriekOfCompactificationPlus (ModuleCat Λ) c`, namely the derived exact
  extension by zero followed by the bounded-below derived direct image.
- All degrees are covered by `(q : ℤ)`.
- The cohomology sheaf is `DerivedCategory.Plus.homologyFunctor ... q`, which by definition
  is inclusion into the unbounded derived category followed by the recorded
  `DerivedCategory.homologyFunctor`.
- Constructibility on the base is the recorded
  `Scheme.IsConstructibleEtaleModuleSheaf` applied to that cohomology sheaf, so the same
  finite locally closed constructible stratification and finite-module trivialization
  notion is used in the conclusion.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` (structure and docstring).
  The scheme-conventions node explicitly has no independent declaration.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AlgebraicGeometry.AffineSpace`, its canonical
  `AffineSpace.over` projection; `ULift (Fin 1)` specializes the index type to dimension one.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification` and its Plus version.
  The structure `AlgebraicGeometry.Compactification` was read in
  `WeilConjectures.Compactification.Defs`, including its quasi-compactness comparison.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`, used by the shriek definition.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, used by the derived direct-image factor.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: the recorded derived module categories and
  their standard `DerivedCategory.Plus` bounded-below subcategory.
- `WeilConjectures.ConstructibleSheaf.Defs`:
  `AlgebraicGeometry.Scheme.LocallyConstantDatum` and `IsLocallyConstantSheaf`.
  The former is used explicitly to give the finite trivializing values rather than replacing
  finite local triviality with the upstream finitely-generated-geometric-stalk predicate.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`; its restriction is the Plus homology functor from
  `Mathlib.Algebra.Homology.DerivedCategory.Plus`. The degree-zero Plus single functor and
  their docstrings were read there too.

Proof dependencies that have declarations are imported, with proof-only imports ordinary
rather than public. Dependencies without statements yet are not imported:
`lem-weil-pbc-etale-lisse-finite-etale-filtration`,
`lem-weil-pbc-etale-shriek-qcqs-composition`,
`lem-weil-pbc-etale-shriek-compactification-independence`,
`lem-weil-pbc-etale-constant-shriek-rel-dim-1`, and
`lem-weil-pbc-etale-shriek-relative-mayer-vietoris`.
The theorem docstring records all five proof steps, including the primary decomposition,
trace retract, filtration, and principal-open Mayer--Vietoris induction.

Edge cases checked: the empty open and zero ring R (empty base) are permitted; no
nonempty-scheme binder occurs. The zero coefficient ring and zero sheaf are permitted;
no nontriviality or positive rank hypothesis is introduced. The trivializing cover need
not be finite or nonempty. Negative degrees, degree zero, and arbitrarily large positive
degrees are included. There is no invertibility-of-coefficients hypothesis, so the
characteristic-primary case is retained. The only universe variable is explicitly bound;
coefficient modules live one universe above schemes as required by the shared framework.

Searches actually run:

- `msearch.py ... leanfinder "compactly supported direct image finite locally constant
  etale module sheaf open relative affine line constructible"`: eight hits about scheme
  constructible images, limits and qcqs sections; no matching étale cohomology theorem.
- `msearch.py ... loogle "IsConstructibleSheaf, rightDerivedLowerShriekOfCompactification"`:
  zero hits; the service reports unknown identifier `IsConstructibleSheaf` (project names
  are absent from its Mathlib index), not evidence that project definitions do not exist.
- `msearch.py ... grep "IsConstructible.*[Ll]owerShriek|[Ll]ocallyConstant.*[Cc]onstructib"`:
  zero Mathlib matches.
- `rg` of the item id, source label, lisse/constructibility and constructibility/lower-shriek
  patterns over upstream `WeilConjectures` and project `lean/Sheaf`: no exact statement.
  Found the generic bounded constructible shriek theorem in upstream
  `SixFunctors/Etale/Derived/Finiteness/DirectImage.lean`; its signature assumes field
  bases and invertible coefficient exponent, so it does not state this integer-base
  result, including noninvertible torsion.
- `rg` of affine space, homology/single functors and compactification declarations in
  Mathlib/upstream located the reused constructions. `dag/lean_names_upstream.json` was
  also checked for affine-space and derived-category names. No new notion was needed.

Validation: `scompile.py NB lem-weil-pbc-etale-lisse-open-relative-line-constructibility`
compiled the delivered module on the server cleanly (1.8 seconds), nice 19, two threads,
60 seconds per file. No local Lean compiler or global build was run.

## Second reading by NB

Independent second reader, 2026-10-15. I opened the item JSON, its complete five-step
proof, the delivered Lean file, all ten statement-dependency records, and the source
at `more-etale.tex`, label `lemma-loc-constant-shriek-rel-dim-1` (Tag 0GKY), including
its proof and surrounding reduction. The source assumes an affine Noetherian base
of finite dimension and a torsion Noetherian coefficient ring. The node deliberately
specializes these to a finite-type integer algebra and a finite commutative ring.
A finite-type integer algebra is Noetherian and finite-dimensional; a finite ring is
Noetherian and torsion. These consequences must not become additional binders.

Here is my object/hypothesis/conclusion checklist against the actual signature:

1. A finite commutative coefficient ring: `Λ : Type (u + 1)`, `[CommRing Λ]`,
   `[Finite Λ]`. Exact; neither a field nor an invertible exponent is required.
2. A finitely generated integer algebra: `R : Type u`, `[CommRing R]`,
   `[Algebra.FiniteType ℤ R]`. Exact: the integer algebra structure is canonical,
   and algebra generators together with integers generate the ring.
3. The affine base `Y = Spec R`: every base occurrence is `Spec (.of R)`.
   Exact; the node fixes this presentation, so no arbitrary-base case is dropped.
4. The relative line: `AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R))`.
   I read Mathlib `AffineSpace` and `AffineSpace.over`: it is relative polynomial
   affine space, and the canonical map used here is its first pullback projection.
   The lifted singleton indexes one variable, not an arbitrary relative dimension.
5. Any open subscheme: `U : (...).Opens`, with `U.toScheme` and `U.ι`.
   Exact; there is no affineness, nonemptiness, or density assumption on U.
6. Its restricted projection `f`: precisely
   `U.ι ≫ (AffineSpace ... (Spec (.of R)) ↘ Spec (.of R))`.
   Exact. It is separated and finite type, with qcqs source and target, as consequences
   of being an open restriction of the line over this Noetherian affine base.
7. A module sheaf L on the small etale site:
   `L : Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
   Exact constant-coefficient module category, matching the recorded derived-category
   convention rather than an unrelated sheaf category.
8. Etale-local constancy with finite module values: `hL` existentially chooses
   `d : Scheme.LocallyConstantDatum L`, then for each member of `d.cover` chooses
   `M : ModuleCat Λ`, `Finite M`, and a nonempty module-sheaf isomorphism between
   `L.over ...` and the constant sheaf with value M on the localized site.
   I read `LocallyConstantDatum.cover` and `.isConstant` in the upstream Defs module.
   Its cover is jointly surjective and etale. The `.isConstant` field follows from
   the displayed isomorphisms; packaging it in d adds no stronger condition.
   Conversely this package gives exactly the required finite trivializations.
9. Regard L in degree zero: `DerivedCategory.Plus.singleFunctor ... 0`.
   I read the Plus definition: this lifts the usual single-degree derived functor.
   Exact; no choice of resolution or boundedness condition on L is added.
10. Every compactification c of f: the binder `c : Compactification (...)` precedes
    the degree binder and conclusion. I read the structure in Compactification.Defs:
    it supplies the open map, proper map, and factorization, with no extra properties.
    Its missing general quasi-compact-open requirement causes no mismatch here:
    `Compactification.quasiCompact_openImmersion_iff` applies since f is quasi-compact
    (all opens of the Noetherian relative line are quasi-compact). Thus its c's are
    precisely the compactifications intended by this node. The initial paragraph of
    the node defines notation for general h; it does not assert a separate theorem.
11. The chosen bounded-below shriek: the actual upstream
    `rightDerivedLowerShriekOfCompactificationPlus (ModuleCat Λ) c`.
    I opened its body: it is derived exact extension by zero followed by bounded-below
    right-derived direct image, not the right-derived functor of their composite.
    I also read `openImmersionLowerShriek` and `lowerStar` in their recorded modules.
12. Every integer degree: `q : ℤ`. No lower or upper bound is imposed.
13. Cohomology sheaf: `DerivedCategory.Plus.homologyFunctor ... q` on the above image.
    Its body is Plus inclusion followed by `DerivedCategory.homologyFunctor`, whose
    factorization through complexes is the cohomology object. Exact.
14. Constructible on the base: `Scheme.IsConstructibleEtaleModuleSheaf` of that
    cohomology sheaf. I read the definition in the dependency module: it chooses a
    finite locally closed scheme stratification with constructible parts and finite
    module-valued etale trivializations of each inverse image. This is exactly the
    definition node's conclusion. The stratification and inverse-image constructions
    are reused, with no private copy.

Edge cases: U may be empty, or all of the relative line. R may be the zero ring
(empty base), Λ may be the zero ring, and L may be zero; no `Nontrivial` or `Nonempty`
instance is assumed. An empty trivializing cover is possible precisely when its
surjectivity allows it, including the empty scheme. Covers are not required to have
finitely many members. Negative degrees, q = 0, and every positive degree remain in
scope. There is no integer n in this signature and no n > 0 restriction to audit;
in particular coefficient characteristic and characteristic-primary torsion remain
unrestricted. Universe u is explicitly bound; the lifted one-variable index lies in
Type u and modules live in Type (u + 1), as required by the shared small-etale
framework. Finite rings and finite trivializing modules can be represented at these
universes. There are no unbound variables, extra algebra instances or test-universe
quantifications.

Independent searches, using different wording from the worker:

- LeanFinder via msearch: `finite locally constant etale sheaf compact support open
  affine line constructible cohomology`. Eight hits, all affine/qcqs sections or
  limit lemmas; none has this statement.
- Loogle via msearch: `"constructible", "cohomology"`. Zero hits.
- Mathlib grep via msearch: `shriek.*[Cc]onstructible|[Cc]onstructible.*shriek`.
  Zero hits.
- LeanSearch via msearch: `compactly supported etale direct image finite locally
  constant modules open affine line has constructible cohomology`.
  Service returned Internal Server Error; recorded as unavailable, not a no-match.
- Direct rg over upstream WeilConjectures and project lean/Sheaf for
  `constructible.*shriek|shriek.*constructible|lisse.*(line|constructib)` and the
  Stacks source label. I inspected the strongest candidate,
  `Etale.boundedConstructible_rightDerivedLowerShriek` in
  SixFunctors/Etale/Derived/Finiteness/DirectImage.lean, including its signature:
  it assumes schemes over a field and `HasInvertibleExponent Λ X`. It does not
  cover finite-type integer bases or characteristic-primary coefficients.
  The pro-etale/adic and lisse Weil-sheaf hits concern other coefficients/sites;
  open-immersion extension-by-zero stability hits omit the proper derived image.
  No exact duplicate was found. Exact source-label and declaration-name rg found
  no existing matching declaration in either source tree.

No mathematical or signature mismatch was found. I changed only this report, adding
the independent reading; the Lean module and node record are retained verbatim.
There are no new definition nodes, dependency replacement modules, hollow definitions,
or statement corrections to review. The one theorem retains only `sorry`; its docstring
records all five proof steps, including primary decomposition, trace retract,
constant-filtration induction, and principal-open Mayer--Vietoris. Source and blueprint
markers are present, and every Lean line fits 100 characters. A direct extraction
verified `lean.statement` equals the file's theorem signature verbatim.

Second-reader validation: server scompile succeeded cleanly for the delivered module
(1.8 seconds), with its side-only import overlay compiled separately (9.3 seconds),
nice 19, two threads, and 60 seconds per file. The delivery dry run printed
`OK (dry run)` and passed preflight and server compilation. No local compiler or
library build was used.
