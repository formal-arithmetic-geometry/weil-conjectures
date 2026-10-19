## Worker report

Module `Sheaf.Paper.FiniteFreeEtaleLocalActual` states
`AlgebraicGeometry.finiteFree_etale_local_actual`, with its sole theorem proof `sorry`.
The source is Stacks Project, sites-cohomology.tex, Tag 08FR (lemma-local-actual),
assertions (1) and (2), read in full. No statement correction or new notion is needed.

Hypotheses and conclusions, in the node's order:

- The scheme is `U : Scheme.{u}`; its site is `U.smallEtaleTopology` on `U.Etale`.
- The commutative coefficient ring is `B : Type (u + 1)` with `[CommRing B]`.
  The larger coefficient universe is the project's size convention, so the small
  étale site admits sheafification and a derived category. There is no cardinality,
  characteristic, nonzero-ring, or finiteness assumption on B.
- The source complex is `P : CochainComplex (ModuleCat.{u + 1} B) ℤ`.
  `hbounded` states that there is a finite interval outside which every term is
  categorically zero. `hfree` states for EVERY integer n that there exists a natural
  rank r and an isomorphism `P.X n ≅ ModuleCat.of B (Fin r → B)`.
  Thus finite freeness is not replaced by finite generation or local freeness.
- The arbitrary target is
  `F : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ`.
  No boundedness condition on F is imposed.
- The termwise constant complex is the image of P by
  `(constantSheaf U.smallEtaleTopology (ModuleCat B)).mapHomologicalComplex (.up ℤ)`.
  This sheafifies the actual constant presheaf, including its differentials.
- Q is exactly `DerivedCategory.Q`, localization at quasi-isomorphisms.
- Assertion (1) is the first conjunct, quantified over every derived morphism φ.
  It produces `𝒰 : Scheme.Cover.{u} etalePrecoverage U` and an actual complex map
  α on EVERY member. A Cover includes joint surjectivity, and membership in the
  étale precoverage requires every structure map to be étale. These are actual
  covering families, not an arbitrary collection or a single open neighborhood.
  Each α has source and target obtained by `Etale.upperStar ... (𝒰.f j)` applied
  termwise. Its localization is required to equal the restriction of φ, transported
  by `mapDerivedCategoryFactors.inv.app` on the source and `.hom.app` on the target.
  This direction follows the signature Q ⋙ D(R) ≅ R(complexes) ⋙ Q; the equation is
  not mere existence of a map between the two restricted complexes.
- Assertion (2) is the second conjunct: every actual map α whose `Q.map α = 0`
  admits an étale cover and `Nonempty (Homotopy (restriction.map α) 0)` on every
  member. Mathlib `Homotopy.hom i j` vanishes unless j+1=i. Its `comm` field reads
  α^i = d_P^i ≫ h^(i+1) + h^i ≫ d_F^(i-1) + 0 (diagrammatic composition).
  Commutativity of addition gives exactly the node's equation
  α^i = d_F^(i-1) h^i + h^(i+1) d_P^i in ordinary composition order.
  A single Homotopy supplies all components simultaneously.

Constant-ring modules and restriction:
`Sheaf J (ModuleCat B)` is the project's established constant-coefficient encoding,
used, for example, in `Sheaf.Paper.LisseModuleSheaves` and the upstream six-functor
API. It means a sheaf with B-linear restrictions. It equivalently carries the action
of the constant RING SHEAF B: local constant scalars act locally and glue uniquely;
conversely constant sections restrict such an action to B-linear sections. Thus this
uses exactly the node's constant-ring-module objects, without replacing B by a
variable coefficient ring or weakening linearity. The general dependency's
`CategoryTheory.ringedSiteModules` is imported; it transparently aliases Mathlib
`SheafOfModules` for variable ring sheaves. No private replacement is defined here.
For étale maps the exact upstream comparison
`Etale.upperStarIsoLocalizationRestriction` identifies the chosen inverse image with
literal restriction to the cover member's small étale site; no flatness or properness
hypothesis is added. The comparison's signature and docstring were read.

Dependency declarations used/read:

- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, with
  `Scheme.Etale` from Morphisms.Etale and covering families described by
  `Scheme.ofArrows_mem_smallEtaleTopology_iff`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the general ringed-site category underlying the constant-coefficient specialization.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`;
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `Functor.mapDerivedCategoryFactors`.
- `Mathlib.Algebra.Homology.Homotopy`: `Homotopy`, whose full fields were read.

All stated project proof dependencies are imported without `public`; Mathlib proof
leaves are available through the imports. The size-convention dependency has no
module because it is metatheoretic. The six-step proof is carried into the theorem
comment, including exact internal Hom, K-injective resolution, exact sheafification,
local bijectivity, exact site restriction, and the two homotopy-class arguments.

Edge cases checked: zero P (all ranks zero), rank-zero terms among nonzero terms,
zero coefficient ring, arbitrary characteristic, empty U and empty covering family,
complexes supported in one degree, and an unbounded target. None is excluded.
Finite interval support need not have nonzero endpoints. Covers may be infinite;
no finite covering hypothesis is imposed. The u-sized cover convention suffices
since schemes have u-sized underlying spaces and any jointly surjective covering
family has a u-sized subfamily, one member and preimage chosen per point.

Searches made before writing:

- `msearch.py leanfinder`: "bounded finite free constant complex sheaves derived
  morphism locally chain map null homotopy": eight hits. Homotopy factorization,
  K-injective/K-projective null-homotopy and derived single-object vanishing;
  none is the local finite-free-source statement for arbitrary targets.
- `msearch.py loogle`: `"constantSheaf"`: twelve hits, including the constant
  sheaf functor, its adjunction, additive instance and comparison isomorphisms;
  reused constantSheaf, no theorem matching both conclusions.
- `msearch.py grep`: `localActual|local_actual|constantModule`: five unrelated
  condensed-module hits, no match.
- `msearch.py leansearch`: "bounded finite free complex sheaves locally actual
  chain map derived category": UNAVAILABLE, Internal Server Error.
- `rg` over Mathlib's ModuleCat/Sheaf, upstream WeilConjectures, and lean/Sheaf
  for constant modules, localActual/local_actual and étale restriction found
  constantSheaf and the exact inverse-image/restriction comparison; no whole-item
  theorem. `rg` for the node id and proposed full declaration in upstream sources,
  project sources and dag/lean_names_upstream.json found no existing declaration.

Validation: `scompile.py NG lem-weil-pbc-finite-free-etale-local-actual` compiles
this module cleanly on the server (2.2 seconds; nice 19, two threads, 60-second
per-file limit). No local compilation or lake build was run. No disputed statement.


## Second reading by NG

Independent second reader, 2026-10-15. Read the node, its four statement-dependency
nodes and recorded source declarations, the delivered module, Stacks
sites-cohomology.tex lemma-local-actual (Tag 08FR), and the preceding definition of
strictly perfect complexes. The source assumes only a ringed site, an object of
that site, a strictly perfect source, and an arbitrary target complex. This node
explicitly specializes it to finite free constant terms on the small etale site;
a finite free term is a direct summand of itself, as required by the source.
There is no hidden Noetherian, separated, nonempty, characteristic or bounded-target
assumption. No statement correction is needed.

Object/hypothesis/conclusion checklist, in node order:

1. Scheme U and its small etale site: `U : Scheme.{u}` and
   `Sheaf U.smallEtaleTopology ...`. PASS. Read `Scheme.Etale` in
   Morphisms.Etale and `Scheme.smallEtaleTopology` in Sites.Etale: objects are
   etale schemes over U and the topology is joint surjectivity, by
   `Scheme.ofArrows_mem_smallEtaleTopology_iff`.
2. Commutative coefficient ring: `(B : Type (u + 1)) [CommRing B]`. PASS.
   This is a ring, not a field or a finite/nonzero ring. The module-section universe
   and coefficient universe are the larger site universe used by the project's
   constant-coefficient sheaf API. No independent smaller test universe occurs.
   Smaller rings can be lifted to this universe; larger schemes and rings are
   covered by increasing u. This is the existing size convention, not a geometric
   hypothesis.
3. Cochain complex P of B-modules: `P : CochainComplex (ModuleCat.{u + 1} B) ℤ`.
   PASS. Its differential is part of P, not independently chosen sheaf maps.
4. Bounded terms: `hbounded : ∃ a b : ℤ, ∀ n : ℤ,
   n < a ∨ b < n → IsZero (P.X n)`. PASS. Finite interval support is equivalent
   to finitely many nonzero terms on integer degrees; neither endpoint must be
   nonzero, and a greater than b simply permits the zero complex.
5. Every term finite free: `hfree : ∀ n : ℤ, ∃ r : ℕ,
   Nonempty (P.X n ≅ ModuleCat.of B (Fin r → B))`. PASS. A ModuleCat isomorphism
   is B-linear and Fin r gives precisely finite rank, including rank zero.
   Ranks may depend on n; this does not assume a chosen compatible basis or
   impose any condition on the differentials.
6. Arbitrary complex F of constant-ring-module sheaves:
   `F : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ`.
   PASS. For a constant ring sheaf, a sheaf of B-modules has the unique action
   of locally constant B-valued scalars obtained locally from its B-action and
   glued. Conversely an underline-B-module sheaf restricts to B-actions via
   constant sections. The morphisms correspond too: B-linearity implies local
   underline-B-linearity and hence global underline-B-linearity by the sheaf
   condition. Thus the established constant-coefficient encoding has exactly
   the objects and maps of the node, including for the zero ring and empty U.
   The general dependency `ringedSiteModules` was opened: it aliases Mathlib's
   `SheafOfModules`, not a different or scheme-only category. No new/private
   module-category definition is introduced here.
7. Termwise constant complex: each occurrence of
   `(constantSheaf U.smallEtaleTopology (ModuleCat B)).mapHomologicalComplex
   (ComplexShape.up ℤ)` applied to P. PASS. Read `constantSheaf`: it is
   `Functor.const Cᵒᵖ ⋙ presheafToSheaf J D`, so it sheafifies the constant
   presheaf and maps the actual differentials. This uses the dependency's
   exact declaration rather than constant presheaves without sheafification.
8. Localization Q: `DerivedCategory.Q.obj` and `.map`. PASS. Opened
   DerivedCategory.Basic: Q is localization of cochain complexes at
   `HomologicalComplex.quasiIso`, as required. Grothendieck/derived-category
   instances are supplied by the imported ModuleCat and sheaf APIs rather
   than extra hypotheses in the theorem.
9. Conclusion (1), for EVERY derived map: the first conjunct begins `∀ φ` with
   exactly source Q(underline P) and target Q(F). It gives `∃ 𝒰 :
   Cover.{u} etalePrecoverage U, ∀ j : 𝒰.I₀, ∃ α : ...`. PASS. Read Cover's
   ZeroHypercover alias and `Cover.exists_eq`: membership in this precoverage
   requires etale maps and joint surjectivity. No finite-cover condition or
   nonempty-index assumption is added. Each alpha is a morphism of the two
   termwise restricted complexes, not merely maps of their graded objects.
10. Conclusion (1), representing the GIVEN map: `DerivedCategory.Q.map α =`
    source `mapDerivedCategoryFactors.inv.app` followed by
    `mapDerivedCategory.map φ` followed by target `.hom.app`. PASS. Read the
    comparison signature in DerivedCategory.ExactFunctor:
    `Q ⋙ D(restriction) ≅ restriction(complexes) ⋙ Q`; the two transport
    directions in the delivered equation are correct.
11. The restriction in both conclusions: `Etale.upperStar ... (𝒰.f j)`.
    PASS. Opened its construction and exactness instances, and independently
    opened `Etale.localizationRestriction` and
    `Etale.upperStarIsoLocalizationRestriction` in the upstream etale
    LowerShriek/OpenImmersion/Defs module. Despite that module's name, this
    comparison is outside the Mono section: it requires only etaleness.
    Localization restriction evaluates a sheaf at the composite T → V_j → U,
    precisely restriction to V_j's small etale site.
12. Conclusion (2), hypothesis and quantifiers: the second conjunct is
    `∀ α : underline P ⟶ F, DerivedCategory.Q.map α = 0 → ∃ 𝒰, ∀ j, ...`.
    PASS. The covering can depend on alpha, and no boundedness on F is added.
13. Conclusion (2), the simultaneous homotopy equation:
    `Nonempty (Homotopy (restriction.map α) 0)`. PASS. Opened the Homotopy
    structure: `hom i j` is zero unless j+1=i, and `comm` says alpha equals
    dNext hom + prevD hom + zero. For cochain complexes these are h^(i+1)
    composed with d_P^i and d_F^(i-1) composed with h^i, in diagrammatic order.
    Reordering the sum gives precisely the node's equation for every i.
    One Homotopy contains all degree components simultaneously, so there is
    no illicit separate cover chosen for each degree.

Edge cases: the empty scheme permits an empty etale cover, and the theorem never
requires a cover index to be inhabited. Nonempty schemes cannot be covered by an
empty family because Cover includes joint surjectivity. A u-sized index is enough:
choose a covering member and a preimage per point of U, giving a subfamily indexed
by U's u-sized space. This preserves every local conclusion. Zero P, rank-zero
terms, empty finite bases, complexes in a single degree, zero B, arbitrary
characteristic and unbounded F all remain allowed. The universe parameter u is
bound; every other variable is explicitly bound, with no extra section assumptions.

Independent H4 searches: `msearch.py leanfinder` for "locally represent morphisms
derived category finite free sheaves complexes homotopy" returned eight hits,
including `IsKProjective.Qh_map_bijective`, `IsKInjective.Qh_map_bijective`,
`DerivedCategory.left_fac` and sheaf finite-presentation predicates. None states
local representatives and local null-homotopies for this source and arbitrary F.
`msearch.py loogle` for `"Homotopy"` returned generic ShortComplex homotopy APIs,
not this statement. `msearch.py leansearch` for "bounded complex finite free module
sheaves derived morphisms locally chain maps null homotopic" reported UNAVAILABLE
(Internal Server Error); no negative-search verdict is inferred from that failure.
Direct rg searches in Mathlib's homology/module-sheaf files, upstream
WeilConjectures, project lean/Sheaf and the upstream name inventory used
`local.{0,25}(representative|homotopy|chain map)`, the proposed declaration and
blueprint id. They found restriction comparisons and Hom-complex facts but no
whole-item theorem. Opened the nearby project LocalizedHomComplexHomology module:
it concerns the comparison of Hom-complex cohomology with homotopy classes,
not either local-existence conclusion here. Existing notions are reused.

H5-H9: the only declaration is the named theorem with whole proof `sorry`; there
are no definitions, auxiliary proved facts, private aliases or local notation.
The source/blueprint docstrings and all six node proof steps are present. The
statement uses the recorded dependency notions via their established encodings;
there are no new nodes or dependency modules in this delivery. Lines are at most
100 characters. Checked by direct string comparison that `lean.statement` equals
the theorem signature verbatim, excluding its proof.

Mismatches found: none. Changes: appended this independent second-reading section;
kept the correct Lean module and node record unchanged. Validation: scompile.py
compiled FiniteFreeEtaleLocalActual on the server in 2.4 seconds with no warnings
or errors (nice 19, two threads, 60 seconds per file). Its required side-only
RingedSiteModules overlay also compiled separately in 1.0 second. No local
compiler or global build was run.
