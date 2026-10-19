## Worker report

The module `Sheaf.Paper.StrictPerfectCoefficientPackage` states the entire coefficient-package
node, including local perfectness and constant sheaf transport. The main recorded declaration is
`SheafOfModules.StrictPerfectCoefficientRepresentation`; all component declarations are listed
in `lean.declarations`. Definitions contain actual data; all new theorems have whole-proof
`sorry` and their docstrings give the elementary proof. No statement correction or disputed
statement. No new nodes or dependency modules.

Clause-by-clause correspondence:

- The size convention is rendered by explicit universe `u`, `C : Type u`, `Category.{u} C`,
  coefficient rings and module carriers in `Type u`, and derived morphism universe `w`.
  This is the stipulated small-site convention, with no auxiliary smaller test universe.
- A commutative ringed site is `J : GrothendieckTopology C` and
  `R : Sheaf J CommRingCat.{u}`. Its underlying ring sheaf uses Mathlib's `sheafCompose`
  and `forget₂ CommRingCat RingCat`, preserving the given ring operations.
- Localization at `U : C` is Mathlib `R₀.over U` on `J.over U`. Restriction of modules
  and complexes is the recorded `SheafOfModules.overFunctor` and `mapHomologicalComplex`.
- The local `Q` is in `DerivedCategory (SheafOfModules (R₀.over U))` with explicit
  `HasDerivedCategory.{w}`. Representation is `represents : Q ≅ DerivedCategory.Q.obj F`.
- `F` is an integer-indexed `CochainComplex`; `bounded` states existence of `a b : ℤ`
  with `IsZero (F.X r)` whenever `r < a ∨ b < r`. This is strict termwise boundedness,
  not just bounded cohomology.
- `SheafOfModules.StrictPerfectCoefficientPackage R F` has exactly `N : ℤ → ℕ`, the
  sheaf-module morphisms `i r` and `p r`, and `splitting r : i r ≫ p r = 𝟙 _`.
  The finite free sheaf is `∏ᶜ fun _ : Fin (N r) => SheafOfModules.unit R`; finite products
  of module sheaves are computed sectionwise, so sections are the required finite tuples.
  A finite product equals the finite direct sum in this additive category. No use of
  categorical projectivity of sheaves replaces the explicitly stated retraction condition.
- The `package` field of the localized representation gives those splittings in every degree;
  hence every term is finite projective in precisely the sheaf sense of the node. No separate
  existential splitting assumption is added to chosen splitting data.
- `e r := p r ≫ i r`, in diagrammatic composition order. Both sheaf and ring versions have
  `.identities`, whose three conjuncts render `e²=e`, `p∘e=p`, and `e∘i=i` in that order.
  There is no complex structure on the ambient tuple objects and no chain-map condition.
- `IsLocallyStrictPerfectComplex R K` quantifies over every `V : C` and a covering sieve
  `S ∈ J V`. For every arrow `f : U ⟶ V` in the sieve it requires a bounded complex `F`,
  `Nonempty (StrictPerfectCoefficientPackage _ F)`, and a map `α : F ⟶ K|_U` with
  `QuasiIso α`. Covers as covering sieves are the Grothendieck-site formulation of the
  node's covering families; passing from a family to its generated sieve uses restriction
  of each model. Each member chooses its own bounds and ranks. A map into the restriction,
  not merely an isomorphism of derived objects, is required.
- `IsPerfectOnRingedSite R E` is existence of such a complex `K` and
  `Nonempty (E ≅ DerivedCategory.Q.obj K)`.
- The coefficient-ring version uses `Λ : Type u`, `[CommRing Λ]`, `ModuleCat Λ`, and
  `DerivedCategory.IsPerfect Q` in the representation parameter `hQ`. Its `F`, `bounded`,
  `finite_projective`, `represents`, and `package` render the chosen bounded representative
  of finitely generated projective modules with its splitting data. The plain package
  remains data for a fixed complex; boundedness belongs to the representation.
- Ring-package free modules are `ModuleCat.of Λ (Fin (N r) → Λ)`, the standard finite tuple
  modules, whose standard basis is Mathlib's coordinate basis. Maps are ordinary Λ-linear
  maps bundled as `ModuleCat` morphisms.
- `strictPerfectConstantPresheaf` gives constant module objects and identity restriction maps.
  `strictPerfectConstantSheaf` composes this with Mathlib module sheafification along
  `toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))`. Its coefficient ring is exactly
  `(constantSheaf J RingCat).obj (RingCat.of Λ)`, not a constant ring presheaf.
- `strictPerfectConstantComplex` maps the entire complex by this functor, including all
  differentials. The package `.constant` maps `i` and `p` by this same functor, then uses
  `strictPerfectConstantFiniteFreeComparison` and its inverse. The comparison is an explicit
  `Pi.lift` of coordinates given by the sheafified scalar-unit maps. Its invertibility is
  the finite-product preservation assertion; the inverse is uniquely determined, not data
  chosen from an undetermined existence theorem. `strictPerfectConstant_splitting` supplies
  the proof of the transported splitting.

Dependency declarations read and reused:

- `def-weil-size-convention` is metatheoretic and has no declaration; universes above render it.
- `def-weil-sheaf-of-modules-category`: the general-site `mathlib_match` is `SheafOfModules`
  in `Mathlib.Algebra.Category.ModuleCat.Sheaf`, with its sectionwise linear morphisms.
  The record's scheme specialization is not used for a general site, as its note instructs.
- `def-pur-localized-ringed-site`: `Sheaf.over`, `GrothendieckTopology.over` in
  `Mathlib.CategoryTheory.Sites.Over`, and `SheafOfModules.overFunctor` in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`, and
  `DerivedCategory.Q` in `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `def-pc-cochain-complex-modules`: `CochainComplex` and complex morphisms from
  `Mathlib.Algebra.Homology.HomologicalComplex`.
- `def-pc-perfect-ring-complex`: `DerivedCategory.IsPerfect` from
  `WeilConjectures.CategoryTheory.DerivedCategory.Perfect` (full definition read).
- `def-weil-finitely-generated-module`: `Module.Finite` from
  `Mathlib.RingTheory.Finiteness.Defs`.
- `def-weil-pbc-projective-module`: `Module.Projective` from
  `Mathlib.Algebra.Module.Projective`.
- `def-weil-pbc-free-module`: `Module.Free` from
  `Mathlib.LinearAlgebra.FreeModule.Basic`, realized here by standard finite tuples,
  rather than selecting an arbitrary free-module basis.
- `def-weil-pbc-constant-sheaf`: `CategoryTheory.constantSheaf` from
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`.
- `def-weil-pbc-sheafification`: `presheafToSheaf`, `toSheafify`, and
  `sheafificationAdjunction` from `Mathlib.CategoryTheory.Sites.Sheafification`, with
  the module-valued specialization `PresheafOfModules.sheafification` and its Hom
  equivalence in `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.
- `lem-weil-pbc-sheafification-sets-exact`: finite-limit preservation of sheafification
  from the same Mathlib sheafification module and `Sites.LeftExact`. Module sheafification
  uses the underlying abelian-group sheafification; its finite-product preservation is
  the corresponding structured version.
- Added the already landed node `lem-pur-rhom-into-kinjective-local` to `stmt_deps` to reuse
  `CategoryTheory.module_overFunctor_preservesZero` from
  `Sheaf.Algebra.Homology.RhomIntoKInjectiveLocal`, as required by the general-site
  restriction convention. Read its full signature, docstring and node. Its theorem is
  registered as a global instance here, avoiding both a duplicate theorem and file-local
  instance notation in statements.

Edge cases checked before writing: rank zero is `Fin 0` and the empty product (the zero
module sheaf), so the zero complex is permitted. Empty sites have vacuous local-cover
quantifiers. Covering objects have independent bounds, with no global boundedness imposed
on `K`. Nontrivial and zero coefficient rings are both permitted. Arbitrary negative
integer degrees are included. A reversed interval forces every term zero and causes no
exclusion. The identities follow equally for zero and nonzero ranks. Constant-ring
sheafification may send the coefficient ring to zero on empty objects; no equality of
constant-presheaf sections and sheaf sections is assumed.

Searches for reuse (2026-10-15; exact remote-search results are in sandbox searches.jsonl):

- `msearch.py leanfinder`: “Bounded complex of finite projective sheaves with chosen degreewise
  finite free splittings strict perfect coefficient package”: eight results on K-projective
  complexes and projective resolutions, none defining the complete package.
- `msearch.py loogle`: `Module.Projective, Module.Finite`: twelve results, including
  `Module.Finite.exists_comp_eq_id_of_projective`; these give individual ring-module
  retractions but no sheaf/local/constant package definition.
- `msearch.py grep`: `StrictPerfect|strictPerfect|strictlyPerfect|StrictlyPerfect`: zero Mathlib
  hits. `rg` on upstream `WeilConjectures` for the same pattern and the exact blueprint ID:
  no hits. `rg` on `lean/Sheaf`: scheme-only `Scheme.IsStrictlyPerfect` and its users,
  no general-site package. Read the scheme definition: it is a Prop on a localized
  scheme complex, with existential rather than chosen splitting data.
- `msearch.py leansearch`: “Strict perfect coefficient package chosen finite free retractions
  for bounded complexes of sheaves”: service unavailable, Internal Server Error.
- Further `rg` on Mathlib module sheaves found `SheafOfModules.free`, `unit`, limits,
  restrictions, and `PresheafOfModules.sheafification`. Read these declarations to use
  their existing interfaces. A finite product of `unit` gives the explicitly requested
  sectionwise tuple carrier without introducing a duplicate finite-free definition.
- `rg` on Mathlib, upstream, and `lean/Sheaf` for all proposed package names found no match.

Source read: the node's blueprint definition 1263, the twelve dependency nodes with their
records and declaration docstrings/signatures, and the Stacks perfect-complex definition.
All data constructions are explicit; no substitute coefficient object or target weakening.

## Earlier second reading (a previous round; superseded)

Independently read the sandbox node and the entire module against blueprint definition
1263 and Stacks `sites-cohomology.tex`, Definitions 08FL (lines 11717–11733) and 08G5
(lines 12735–12745). These passages assume a ringed site, not a Noetherian scheme,
a field, or a quasi-compact topos. The warning immediately after 08G5 confirms that
perfect objects need not be globally bounded. The original blueprint paragraph and
the expanded DAG statement agree on the package and its local/global uses.

Object, hypothesis, and conclusion checklist (all verdicts: matches):

1. Small site and commutative coefficient sheaf: `C : Type u`, `[Category.{u} C]`,
   `J : GrothendieckTopology C`, `R : Sheaf J CommRingCat.{u}`. The passage to
   `RingCat` is the forgetful functor, not a replacement coefficient ring.
2. Localization at any object: `U : C`, `R₀.over U`, and the actual Mathlib
   `SheafOfModules.overFunctor R₀ U`. Read `GrothendieckTopology.over`,
   `Sheaf.over`, `overFunctor`, `overMap`, and `overFunctorMap` signatures.
3. Local derived object and its chosen representative: the sheaf representation's
   `Q : DerivedCategory ...`, `F`, `represents : Q ≅ DerivedCategory.Q.obj F`, and
   `bounded : ∃ a b : ℤ, ∀ r, r < a ∨ b < r → IsZero (F.X r)`.
   `HasDerivedCategory.{w}` chooses the localization size and adds no geometric
   hypothesis. Read `DerivedCategory`, `Q`, and `HasDerivedCategory` in Mathlib.
4. Finite projectivity in exactly the sheaf sense stated: `package` contains
   `N : ℤ → ℕ`, `i r : F.X r ⟶ ∏ᶜ ... unit ...`, the reverse map `p r`, and
   `splitting r : i r ≫ p r = 𝟙 _`. Read `SheafOfModules`, its morphisms, `unit`,
   and its limits interface: these are sheaf-linear maps and finite sectionwise
   tuples. No categorical-projectivity assumption is substituted. The package
   for a fixed complex is usable without boundedness; the representation record
   supplies boundedness, exactly separating the data from the context.
5. Idempotent and all three identities: `.e` is `p r ≫ i r`, hence mathematical
   `i_r ∘ p_r`; `.identities` asserts `e ≫ e = e`, `e ≫ p = p`, and `i ≫ e = i`.
   The same check applies to the `ModuleCat` version. Neither package introduces
   a differential on the finite free terms or imposes a chain-map condition.
6. Local perfectness: `IsLocallyStrictPerfectComplex` quantifies first over every
   `V`, then a covering sieve, then its arrows, then a bounded `F`, a package,
   and `α : F ⟶ K|_U` with `QuasiIso α`. This matches 08G5's direction of the
   quasi-isomorphism. A covering family generates a covering sieve; restriction
   of a model along a factorization preserves its bounds, splittings, and
   quasi-isomorphism. Conversely, all arrows of a covering sieve give a covering
   family. Thus the sieve formulation introduces no stronger condition.
7. Perfect derived objects: `IsPerfectOnRingedSite` existentially quantifies `K`,
   its local perfectness, and `Nonempty (E ≅ DerivedCategory.Q.obj K)`. It does
   not assert one global interval for `K`.
8. Ordinary coefficient ring: `[CommRing Λ]`, `Q`, and `hQ : DerivedCategory.IsPerfect Q`
   in the ring representation, with fields `F`, `bounded`, `finite_projective`,
   `represents`, `package`. Read the upstream `IsPerfect` definition: bounded
   finitely generated projective representatives, with no Noetherian assumption.
   `Module.Finite` and `Module.Projective` are the recorded Mathlib notions.
9. Standard finite free modules: `ModuleCat.of Λ (Fin (N r) → Λ)` with ordinary
   module morphisms. This is the standard coordinate free module, not a chosen
   unrelated free object. Read `Module.Free` and the finite-projective splitting
   search result; neither already defines the package.
10. Constant sheaf transport: `strictPerfectConstantPresheaf` has constant objects
    and identity restrictions; `strictPerfectConstantSheaf` applies the existing
    `PresheafOfModules.sheafification` along `toSheafify` of the ring presheaf.
    Its target ring is exactly `(constantSheaf J RingCat).obj (RingCat.of Λ)`.
    Read both sheafification signatures, its Hom equivalence, and `constantSheaf`.
11. Differentials and splitting maps: `strictPerfectConstantComplex` uses
    `mapHomologicalComplex`; `.constant` maps `i` and `p` through the same functor.
    `strictPerfectConstantCoordinateComponent`, its sheafified coordinate, and
    `Pi.lift` explicitly construct the canonical finite-product comparison.
    The stated `IsIso` theorem permits its uniquely determined inverse; the
    splitting theorem supplies only a proof, not unspecified data.

Edge cases: `Fin 0` includes zero rank and the empty product (zero module).
The zero ring and zero complex are allowed; no characteristic restriction exists.
All integer degrees, including negative degrees, are bound. A reversed bounding
interval simply forces the zero complex. Empty sites make the local condition
vacuous; empty covering sieves are permitted exactly when the topology permits
an empty cover. Bounds and ranks can vary by cover member. `u` is arbitrary and
is shared by the small site and section carriers as stipulated; `w` handles local
derived morphism size. The ring case uses the universe of the upstream recorded
`IsPerfect` and does not introduce an independent smaller test universe.

Independent reuse searches:

- LeanFinder: “A cochain complex on a ringed site with chosen retractions onto
  finite powers of the unit sheaf”; eight hits, including `SheafOfModules.unit`
  and local generators, none for this package or local-perfect predicate.
- Loogle: `Module.Finite.exists_comp_eq_id_of_projective`; one exact hit giving
  individual ordinary-module splittings, not the package or its sheaf transport.
- Mathlib grep through msearch: `coefficientPackage|CoefficientPackage|LocallyStrictPerfect|PerfectOnRingedSite`;
  no hits. Independent `rg` on upstream and project sources also used
  `finite.free.*retract` and `constant.*[Ss]plitting`. Results concern scheme
  perfect complexes, stalk constructions, or unrelated category splittings.
- Opened `Scheme.IsStrictlyPerfect` in `Sheaf.AlgebraicGeometry.PerfectComplex`:
  it is a predicate on a scheme's localized complex, not chosen package data on
  an arbitrary ringed site. It cannot replace this definition. Upstream
  `DerivedCategory.IsPerfect` is reused for the ring case, not redefined.

No new nodes, dependency modules, statement correction, or disputed statement
are present. The extra recorded dependency `lem-pur-rhom-into-kinjective-local`
provides the already proved general-ring theorem
`CategoryTheory.module_overFunctor_preservesZero`, whose signature and proof
were opened; registering it globally permits restriction of complexes without
introducing another declaration. It does not restrict the site or coefficient ring.
Every definition has explicit data, every new theorem has whole-proof `sorry`,
and the theorem docstrings explain the elementary construction or identity.
The node's recorded main signature matches the file verbatim up to whitespace.

Statement mismatches found: none. A dependency-record update was found on the final
check: `def-weil-sheaf-of-modules-category` now records the landed general-site
`CategoryTheory.ringedSiteModules` in `Sheaf.CategoryTheory.RingedSiteModules`, not
the older scheme specialization described in the worker report above. Opened the
new declaration: it is exactly the transparent abbreviation `SheafOfModules.{v} R`
with arbitrary site and ring universes. Replaced the direct Abelian import with
this recorded dependency module, which publicly imports that same Mathlib file.
The category in every signature is therefore definitionally the recorded category;
no signature or node statement changed. No new dependency module was written.
The initial server compile passed cleanly in 8.7 seconds; the final import update
is checked again by scompile and both delivery runs, with nice 19, two threads,
and a 60-second limit.

## Repair of returned delivery (H6)

The independent review of immutable head `f93bc4e62c5e` returned one point:
linearity was proved inside `strictPerfectConstantCoordinateComponent`.
Extracted the additive and scalar compatibility obligations into the named theorems
`SheafOfModules.strictPerfectConstantCoordinateComponent_map_add` and
`SheafOfModules.strictPerfectConstantCoordinateComponent_map_smul`, each with a whole-proof
`sorry`, the source/blueprint citation, and a complete natural-language proof in its docstring.
The component definition now references these theorems directly in `map_add'` and `map_smul'`.
Both declarations are recorded in the node's `lean.declarations`; its statement, dependencies,
and main signature are unchanged. These are proof obligations for the existing explicit data,
not new notions requiring new definition nodes. The rank-zero case remains vacuous because
there is no `k : Fin 0`. Sums and scalar actions on tuples are pointwise, including over the
zero ring. Exact-name searches with `rg` in Mathlib, upstream `WeilConjectures`, and project
`lean` found no existing declaration with either extracted name.

Repair validation: `scompile.py` compiled the delivered module cleanly in 9.6 seconds
(nice 19, two threads, 60 seconds per file), with no errors or warnings.

## Second reading by NC

Fresh independent reading of the repaired delivery, 2026-10-15. Opened the complete
sandbox node and Lean module, the original blueprint definition 1263, and Stacks
`sites-cohomology.tex`, strictly perfect complexes (Tag 08FL, lines 11717–11733)
and perfect complexes (Tag 08G5, lines 12735–12757). These source passages assume
only a ringed site; no field, Noetherian, quasi-compactness, or characteristic
hypothesis is implicit. The warning following 08G5 explicitly permits globally
unbounded perfect complexes.

Object/hypothesis/conclusion checklist, each with its Lean rendering and verdict:

1. Chosen small site and commutative coefficient sheaf: `C : Type u`,
   `[Category.{u} C]`, `J : GrothendieckTopology C`, and
   `R : Sheaf J CommRingCat.{u}`. Matches the stipulated small-site convention.
   The forgetful `sheafCompose` keeps the ring and its operations; it does not
   replace the coefficient object. The arbitrary `u` covers each chosen bound.
2. Modules and localization at every `U : C`: `SheafOfModules.{u} R₀`,
   `R₀.over U`, and `SheafOfModules.overFunctor R₀ U`. Matches sectionwise
   restriction on `J.over U`. Opened the recorded dependency abbreviation
   `CategoryTheory.ringedSiteModules`: it is transparently `SheafOfModules R`,
   with no extra structure. Also read `over`, `overFunctor`, `overMap`, and
   `overFunctorMap` signatures and their sectionwise implementations.
3. Local derived object and bounded representative:
   `StrictPerfectCoefficientRepresentation R U Q` has `F`,
   `bounded : ∃ a b : ℤ, ∀ r, r < a ∨ b < r → IsZero (F.X r)`, and
   `represents : Q ≅ DerivedCategory.Q.obj F`. Matches strict termwise
   boundedness, rather than merely bounded cohomology. `HasDerivedCategory.{w}`
   specifies localization size, as the dependency requires. Read Mathlib's
   `HasDerivedCategory`, `DerivedCategory`, `Q`, and integer cochain-complex
   declarations; these are the recorded dependency notions.
4. Finite projectivity in the node's sheaf sense and chosen package:
   `package : StrictPerfectCoefficientPackage _ F` supplies `N : ℤ → ℕ`,
   `i r : F.X r ⟶ ∏ᶜ fun _ : Fin (N r) => unit R₀`, reverse `p r`, and
   `splitting r : i r ≫ p r = 𝟙 _`. Matches a chosen finite-free retraction.
   Read `SheafOfModules.Hom`, `unit`, and evaluation-preserves-finite-limits:
   the maps are sheaf-linear and the finite products have the required tuple
   sections. No categorical projectivity of sheaf objects is imposed.
5. Idempotent and three equations: `.e r := p r ≫ i r`; `.identities` asserts
   `e ≫ e = e`, `e ≫ p = p`, and `i ≫ e = i`. In diagrammatic order these
   are exactly the three displayed equations. Matches in both namespaces.
   There is no ambient free complex or chain-map condition on `i` and `p`.
6. Local condition on a given `K`: `IsLocallyStrictPerfectComplex` quantifies
   over each `V`, then a covering sieve, then every arrow `U ⟶ V` in it,
   then a bounded `F`, its package, and `α : F ⟶ K|_U` with `QuasiIso α`.
   Matches 08G5, including direction and quantifier order. A covering family
   generates a covering sieve: restrict its models along factorizations,
   preserving splittings, bounds, and quasi-isomorphisms. Conversely the
   arrows of a covering sieve are a covering family. Ranks and bounds are
   chosen independently for each member.
7. Derived perfectness: `IsPerfectOnRingedSite R E` is existence of `K` with
   the preceding local condition and `Nonempty (E ≅ Q.obj K)`. Matches;
   there is no global bound on `K`.
8. Ring coefficient variant: `[CommRing Λ]`, `Q`, and
   `hQ : DerivedCategory.IsPerfect Q`; the ring representation supplies `F`,
   `bounded`, `finite_projective`, `represents`, and `package`. Matches the
   chosen bounded finitely generated projective representative. Opened the
   upstream `DerivedCategory.IsPerfect`: precisely existence of such a
   representative, with the same module and localization universes. Read
   `Module.Finite`, `Module.Projective`, and `Module.Free` themselves.
9. Standard finite free ring modules: `ModuleCat.of Λ (Fin (N r) → Λ)` and
   ordinary module morphisms. Matches the finite standard coordinate basis,
   including rank zero; no unrelated basis or coefficient ring is selected.
10. Associated constant sheaves: `strictPerfectConstantPresheaf` has constant
    objects and identity restrictions; `strictPerfectConstantSheaf` applies
    `PresheafOfModules.sheafification` along `toSheafify` of the constant
    ring presheaf. The target coefficient ring is exactly
    `(constantSheaf J RingCat).obj (RingCat.of Λ)`. Matches. Opened the
    recorded constant-sheaf, sheafification/unit/adjunction, module-valued
    sheafification and Hom-equivalence declarations.
11. Transport of all differentials and splitting maps:
    `strictPerfectConstantComplex` uses `mapHomologicalComplex`; `.constant`
    applies the same functor to `i` and `p`. The comparison is explicitly
    `Pi.lift` of sheafified coordinate projections; its inverse comes from
    the named `IsIso` assertion. Matches the canonical finite-product
    identification. Its inverse is uniquely determined, not an arbitrary
    object chosen from a sorry-backed existence statement. The named
    splitting theorem supplies only the proof obligation.

Edge cases: empty sites make the object quantifier vacuous; empty covering
sieves are admitted exactly when covering in `J`. `Fin 0` gives the empty
product, hence the zero module sheaf, and rank zero and the zero complex are
allowed. Negative degrees, degree zero, and reversed bounding intervals are
covered. The zero ring and every characteristic are allowed. No scheme or
nonempty-space hypothesis occurs, so empty scheme sites are covered. Explicit
universes and binders are bound throughout; there is no smaller independent
universe of test objects. The ring specialization follows the recorded
upstream perfectness universe rather than redefining it.

Independent searches in this reading:

- LeanFinder via `msearch.py`: “Chosen degreewise finite tuple retractions of
  complexes on ringed sites with constant sheaf transport”; eight hits about
  K-projective complexes, factorization, and maps to single complexes, none
  defining this package or its constant transport.
- Loogle via `msearch.py`: `Module.Finite.exists_comp_eq_id_of_projective`;
  one hit giving individual ordinary-module retractions, not this package.
- Mathlib grep via `msearch.py`:
  `CoefficientPackage|LocallyStrictPerfect|PerfectOnRingedSite|finiteFreeComparison`;
  zero hits.
- Independent `rg` on Mathlib, upstream `WeilConjectures`, and project
  `lean/Sheaf` used `finite.?free.*(retract|summand)` as well as the package
  and local-perfect names. Project hits concern scheme perfect-complex
  lemmas. Opened `Scheme.IsStrictlyPerfect` and `Scheme.IsPerfect` in
  `Sheaf.AlgebraicGeometry.PerfectComplex`: scheme/open-specific predicates,
  not chosen data or perfectness on an arbitrary ringed site. The ordinary
  ring perfectness definition is already reused from upstream.

No new node or dependency module is in this delivery; no statement correction
or disputed statement is present. The added existing dependency
`lem-pur-rhom-into-kinjective-local` provides the exact general-site zero-map
preservation theorem; opened its full signature and proof. Its registration
as a global instance introduces no hypothesis or second definition.

Mismatch review: none remains. In particular the returned H6 defect is repaired:
`strictPerfectConstantCoordinateComponent_map_add` and `_map_smul` are named
whole-proof-sorry theorems, and the coordinate definition refers to them rather
than proving linearity. Their docstrings explain pointwise addition/scalar
multiplication and preservation by the ring unit. All other new theorems also
have whole-proof `sorry`; data definitions are explicit. Source and blueprint
citations and natural-language proofs are present. No Lean or node text needed
rewriting in this second reading; the report is the only new change.

Validation for this reading: `scompile.py` passed with no diagnostics; the item
compiled in 10.1 seconds and its side import overlay in 1.0 second, nice 19,
two threads, 60 seconds per file. The main recorded signature agrees with the
source signature modulo formatting whitespace. `deliver2.py --no-push` printed
OK: preflight and server compilation both passed, with only the report, item
node, and item module staged. No repository git command or local compiler was
run by this reader.
