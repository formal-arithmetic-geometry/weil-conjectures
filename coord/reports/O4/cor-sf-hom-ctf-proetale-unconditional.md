## Worker report

Item: `cor-sf-hom-ctf-proetale-unconditional`.
Module: `Sheaf.Paper.ProEtalePerfectHomTorAmplitude`.
Main declaration:
`AlgebraicGeometry.Scheme.finiteCoefficientComparisonRHom_boundedConstructible_torAmplitude`.
The only theorem introduced has proof `sorry`. The helper
`AlgebraicGeometry.Scheme.finiteCoefficientComparisonRHom` has real data: it applies the
recorded universe-general derived internal Hom to the two recorded intrinsic comparison
inverse images. No arbitrary functor, map, resolution, or equivalence is hypothesized.

The original blueprint corollary and its unit were read in the launcher's read-only
literature copy: `sec-six-functors/sk-thm-sf-hom-ctf/` and its corollary of order 2200.
The source proof is the etale sharp Hom bound, canonical Hom comparison, and preservation
of Tor amplitude under comparison. The node's expanded four-step proof, including the
finite dimension check, is reproduced in the theorem docstring. No statement correction
is necessary and there is no statement dispute.

Hypotheses and clauses, individually:

- The fixed global finite-field datum is `D : WeilConjectures.FiniteFieldDatum.{u}`.
  Its fields give p prime, q a positive power of p, the finite field k0 of cardinality q,
  and the fixed algebraic closure `D.k`. Thus this is exactly the inherited k of the node.
- The coefficient prime and its difference from the characteristic are
  `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`.
- The finite extension E/Q_l is `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`.
- The positive level is `(n : ℕ) (hn : 1 ≤ n)`.
- The ring A is always `Padic.coefficientExtensionRing l E n`, the recorded quotient
  of the recorded integer ring by the power of its chosen uniformizer ideal. Etale
  sheaves use its canonical `ULift.{u + 1}` ring, not a different coefficient ring.
  Finiteness is supplied explicitly by `Padic.finite_coefficientExtensionRing l E n hn`
  and `Equiv.ulift.finite_iff`. There is no extra finite-ring hypothesis.
- The finite-type k-scheme is `(X : Scheme.{u}) [X.Over (Spec (CommRingCat.of D.k))]`
  together with `LocallyOfFiniteType` and `QuasiCompact` on its structure morphism.
  No separatedness, admissibility, dimension bound, or nonemptiness is added.
- The comparison morphism is the prescribed one: the helper uses
  `ProEtale.finiteCoefficientIntrinsicDerivedComparison X A`, whose source was read
  locally and confirmed by `scompile.py --source`. This functor is
  `comparisonUpperStar` followed by canonical module sheafification along the
  constant-scalar unit, applied termwise and localized. It realizes exactly the
  comparison of `proEtaleSiteComparisonModules`, in the constant-ring presentation
  used by the recorded Tor and constructibility predicates.
- The four integer endpoints are `(a b c d : ℤ)`, with `_hab : a ≤ b` and `_hcd : c ≤ d`.
- K' and M' are `K M : Etale.DerivedCategoryModule (ULift A) X`, with `_hK` and `_hM`
  asserting the recorded `Etale.DerivedCategory.isBoundedConstructible` separately.
  These test finite-value constructibility of every cohomology sheaf and one finite
  cohomological interval. The upstream alternative constructibility notion is not used.
- The respective Tor hypotheses are `_hKt` and `_hMt`, using the existing
  `Etale.DerivedCategory.hasTorAmplitudeIn (ULift A) X a b K` and the same expression
  at `c d M`. Its full signature and definition in the upstream Coefficients module
  were read: every etale module sheaf in degree zero is tested by derived tensor.
  Together with bounded constructibility these express D^b_ctf without an extra binder.
- Site-perfectness is `_hPerfect`. An etale cover `𝒰 : X.Cover.{u} etalePrecoverage`
  is chosen; for every member j, a complex P on `(𝒰.X j).smallEtaleTopology` is chosen.
  Its boundedness is an ordered integer interval r,s with `IsZero (P.X q)` outside it.
  Every term is a retract of the constant module sheaf on `Fin m → ULift A`:
  maps i and p satisfy `i ≫ p = 𝟙 (P.X q)`. This is precisely a direct summand of
  a finite sum of the constant coefficient ring sheaf (finite tuples and finite sums
  agree). The final `Nonempty` is an isomorphism between the actual etale restriction
  `(Etale.upperStar ... (𝒰.f j)).mapDerivedCategory.obj K` and `DerivedCategory.Q.obj P`.
  Bounds, ranks, and splittings may vary with the cover member and degree. This is
  local strict perfectness, with no demand for a global perfect representative.
- The required internal Hom is `finiteCoefficientComparisonRHom X A hA K M`.
  Its definition uses `derivedInternalHomOfUniverses` at site object universe u+1,
  site morphism universe u, coefficient/module universe u+1 and standard localization
  universe u+2. It is the recorded K-injective internal Hom of the actual pullbacks.
- Bounded constructibility of this object is the first conclusion,
  `intrinsicFiniteTorsionConstructible l E n hn X (...)`. Its definition was read:
  finitely many nonzero cohomology sheaves and constructibility of every one of them.
- The second conclusion is `HasProEtaleTorAmplitude X A (...) (c - b) (d - a)`.
  Its definition was read: the ordered interval and vanishing after tensoring with
  every pro-etale module sheaf in degree zero, using all K-flat resolutions of all
  representatives. It includes all test sheaves, not only comparison inverse images.

Recorded dependencies used (module and declaration):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public construction
  import: `Padic.finite_coefficientExtensionRing`, `Padic.coefficientExtensionRing`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and QuasiCompact (via the finite-field
  module): `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`;
  both full signatures and docstrings were read.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `AlgebraicGeometry.Scheme.proEtaleSiteComparisonModules`, whose canonical inverse
  image is used by the intrinsic comparison interface below.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude` and its public upstream imports:
  `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`:
  `AlgebraicGeometry.Scheme.HasProEtaleTorAmplitude`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`:
  `AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicDerivedComparison`.
  The already-landed node `def-weil-pbc-proetale-modules` is added to stmt_deps for
  this interface. The already-landed `def-kun-tor-amplitude` is added for etale Tor
  amplitude. The additions follow the rule allowing already-landed statement nodes.
- Proof-only import `Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`:
  `AlgebraicGeometry.exists_fibre_dimension_bound`. The three other proof-dependency
  nodes have no Lean record yet, so they cannot currently supply imports. Their
  mathematical uses remain explicitly named in the proof docstring.

Edge cases checked before writing:

- Empty X is permitted, as are empty covering families covering the empty scheme;
  there is no nonempty-cover or nonempty-scheme hypothesis.
- K=0 or M=0 is permitted. Rank m=0 is permitted for a zero term. The bounded zero
  complex satisfies the local model condition without an artificial nonzero term.
- The intervals may be singletons and may contain any negative endpoints. The node's
  a≤b and c≤d imply c-b≤d-a, matching the ordered output predicate.
- n=1 is included, including ramified extensions E; n=0 is excluded exactly as the node
  requires. No field assumption is imposed on the non-field finite quotient ring.
- No global common local-model bound or rank is imposed; the source only requires
  boundedness locally. All pro-etale sheaves are tested by the output Tor predicate.
- The site retains its distinct object/morphism universes; no equality between u+1 and u
  is imposed. The coefficient lift and the comparison realization preserve coefficients.

Searches made, with results:

- `msearch.py ... leansearch "pro etale internal Hom of constructible complexes perfect
  first variable finite Tor amplitude"`: service unavailable, Internal Server Error.
- `msearch.py ... leanfinder "pro etale derived internal Hom of bounded constructible
  etale complexes with site perfect first argument has Tor amplitude c-b d-a"`: eight
  hits, on derived t-structure support and projective single complexes; no match.
- `msearch.py ... loogle '"derivedHom"'`: zero hits.
- `msearch.py ... grep 'Has.*TorAmplitude|sitePerfect|SitePerfect'`: zero Mathlib hits.
- `rg` in Mathlib ElladicCohomology for `hasTorAmplitudeIn` and bounded-constructible
  derived Hom: no matching declaration.
- `rg` for site-perfectness, etale Tor amplitude, comparison Hom and finite-projective
  interfaces in the project's Sheaf sources and upstream WeilConjectures sources found
  the interfaces listed above, including intrinsic comparison, and the strict-perfect
  coefficient package. The latter identifies site object and morphism universes and
  operates in ringed-site modules; it is not substituted for the local etale hypothesis.
- Searching the exact node id in upstream WeilConjectures found
  `SixFunctors/Etale/Derived/Stability/Matrix.lean:330` and its theorem
  `AlgebraicGeometry.ProEtale.DerivedCategory.
  boundedConstructible_derivedHom_mapDerivedCategory_of_isDualizable`.
  Its full signature/docstring and surrounding declarations were read. It uses the
  upstream constructibility notion and a dualizability hypothesis; the present DAG
  deliberately records finite-value constructibility and explicit local bounded
  finite-projective models instead. It therefore cannot directly be attached as the
  current node's statement. No copy of its proof or its predicates is introduced.
- `rg` for the two new declaration names in the project's Sheaf sources and upstream
  WeilConjectures found no existing declaration with either name.

Validation: `scompile.py N4 cor-sf-hom-ctf-proetale-unconditional` compiled this module
successfully, both its sandbox check and its library module check; no warnings or errors.
The main signature is copied verbatim into lean.statement. All universes and variables
are explicit, and the module sets `autoImplicit false`. Every line is at most 100 columns.
There are no new nodes, dependency repairs, or changes to the mathematical statement.

## Second reading by N4

I read the sandbox node, module, and worker report independently, then opened the
source corollary and its parent `_section.md` in
`/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/sec-six-functors/`.
The parent introduces the finite coefficient ring and finite-type geometric-base scheme;
it explicitly imposes no admissibility datum. Its perfect case uses bounded local
finite-projective models. I also read Stacks `sites-cohomology.tex`, the definitions
`definition-tor-amplitude` and `definition-perfect`, the final-object covering criterion
`lemma-perfect-independent-representative`, and `section-internal-hom`. Their ambient
assumption is a ringed site, not an extra Noetherian or nonempty assumption.

Here is my object/hypothesis/conclusion inventory and its match with the final Lean.

1. The fixed finite-field datum and geometric field of characteristic p are
   `D : WeilConjectures.FiniteFieldDatum.{u}` and `D.k`. I opened
   `Sheaf.Paper.FiniteFieldFiber`: its prime, positive exponent, cardinality, finite
   base field and algebraic closure fields give precisely the inherited datum. PASS.
2. The prime ell different from p is `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`.
   There is no assumption of positive characteristic on the coefficient quotient. PASS.
3. A finite extension E/Q_l is `E : Type u`, `Field E`, `Algebra (Padic l) E`,
   and `FiniteDimensional (Padic l) E`. The positive level is `n : ℕ`, `hn : 1 ≤ n`.
   No chosen norm or additional topology is assumed. PASS.
4. A is `Padic.coefficientExtensionRing l E n`. I opened the construction and its
   finiteness module: it is the integer ring modulo the nth power of the chosen
   uniformizer ideal. The canonical `ULift.{u+1}` is the same coefficient ring in
   the etale module universe. The explicit `finite_coefficientExtensionRing` and
   `Equiv.ulift.finite_iff` supply finiteness rather than assuming it. PASS.
5. The finite-type k-scheme is `X : Scheme.{u}`, its `Over (Spec (CommRingCat.of D.k))`
   instance, and `LocallyOfFiniteType` plus `QuasiCompact` on the structure map.
   I read both Mathlib class signatures: this is exactly the recorded finite-type
   convention, without separatedness, properness, a dimension bound, or admissibility.
   PASS.
6. The comparison is canonical, not an extra arbitrary functor. I opened
   `proEtaleSiteComparisonModules` and all of
   `ProEtaleFiniteModuleIntrinsicComparison`: `finiteCoefficientIntrinsicComparison`
   is `comparisonUpperStar` followed by module-presheaf sheafification along the
   constant-scalar unit, and `finiteCoefficientIntrinsicDerivedComparison` is its
   `mapDerivedCategory`. This is the fixed inverse image in the presentation needed
   by the recorded intrinsic constructibility predicate. PASS.
7. The endpoints are `(a b c d : ℤ)`, `_hab : a ≤ b`, `_hcd : c ≤ d`. The complexes
   are `K M : Etale.DerivedCategoryModule (ULift A) X`; I read its upstream abbreviation
   as the full derived category of etale module sheaves. PASS.
8. The separate hypotheses `_hK` and `_hM` use the recorded
   `Etale.DerivedCategory.isBoundedConstructible`. I opened that definition:
   each cohomology sheaf satisfies `IsConstructibleEtaleModuleSheaf`, and a single
   finite ordered interval bounds the cohomology. Thus both are in the node's D^b_c.
   The upstream finitely-generated-stalk predicate is not silently substituted. PASS.
9. The two Tor bounds are `_hKt : ...hasTorAmplitudeIn ... X a b K` and
   `_hMt : ...hasTorAmplitudeIn ... X c d M`. I opened the upstream Coefficients
   declaration reexported by the recorded EtaleTorAmplitude module: it tests every
   module sheaf in degree zero with derived tensor, not just constant sheaves.
   These hypotheses with item 8 express exactly D^b_ctf and its specified bounds. PASS.
10. Site-perfectness is now `_hPerfect : Etale.DerivedCategory.IsSitePerfect K`.
    I found and read the exact existing declaration in the current shared upstream
    `WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect`, and confirmed it
    with `scompile.py --source`. It quantifies over an etale cover and, independently
    on each member, a bounded complex whose every term is a retract of the constant
    finite tuple module. Its final isomorphism identifies that complex with the actual
    derived restriction of K. These are exactly the node's local finite-projective
    models. Strict upper/lower term bounds express boundedness; their order is not
    an extra condition and a zero complex is included. PASS after H4 repair.
11. The output object is `finiteCoefficientComparisonRHom X A hA K M`.
    I read `derivedInternalHomOfUniverses` and its representative comparison statements:
    it uses the Hom complex and functorial K-injective replacement in its second
    variable, then localization. The helper applies it to the actual two comparison
    inverse images in the prescribed order `(op (nu* K), nu* M)`. Its data are real
    constructions; the only `sorry` in this delivery is the named main theorem. PASS.
12. The first conclusion is `intrinsicFiniteTorsionConstructible l E n hn X (...)`.
    I read that definition and its constructible-sheaf dependency: finitely many
    nonzero cohomology sheaves, each admitting the finite constructible stratification
    with locally constant finite module stalks. The ring and derived category coincide
    with item 11; this is the intrinsic pro-etale conclusion, not merely membership
    in an etale-image category. PASS.
13. The second conclusion is `HasProEtaleTorAmplitude X A (...) (c - b) (d - a)`.
    I opened its full definition: it requires the ordered interval and vanishing
    after tensor with every degree-zero pro-etale module sheaf, across all K-flat
    resolutions of all representatives. The input inequalities imply the required
    output order. The endpoints and subtraction order match the node exactly. PASS.

Edge cases: X may be empty; an empty covering is allowed when it covers the empty
scheme, and otherwise the covering condition enforces joint surjectivity. Zero K or M
and rank-zero terms are admitted. Local ranks and bounds may vary with the cover member;
no global complex or rank is required. Singleton intervals and arbitrary negative
integer endpoints are included. n=1 is included, n=0 is excluded exactly by `hn`.
Ramified E and non-field quotient rings are included. No nonzero or domain instance
is imposed on A. Universes remain site objects u+1, site arrows u, module coefficients
u+1, standard derived localization u+2; the upstream perfectness predicate has exactly
the needed `Scheme.{u}` and `ModuleCat.{u+1}` universes. No equality of site universes
or additional universe instance was introduced.

Independent searches used different vocabulary:

- `msearch.py ... leansearch "Perfect complex of etale module sheaves derived Hom is
  bounded constructible with sharp Tor amplitude"`: Internal Server Error, recorded
  unavailable; no conclusion drawn from that outage.
- `msearch.py ... leanfinder "derived sheaf Hom finite locally projective first argument
  sharp cohomological tensor amplitude"`: eight hits on light-condensed internally
  projective objects and projective Tor vanishing; none is this statement.
- `msearch.py ... loogle '"Sheaf", "projective"'`: twelve Proj structure-sheaf hits;
  none supplies this statement or coefficient-site perfectness.
- `msearch.py ... grep 'IsSitePerfect|derived.*Hom.*[Aa]mplitude|[Aa]mplitude.*derived.*Hom'
  AlgebraicGeometry`: zero Mathlib hits.
- Direct `rg` in Mathlib, project `lean/Sheaf`, the older slopmaster2 source, and the
  current shared `lean/WeilConjectures` found the exact upstream `IsSitePerfect`
  definition. This finding repairs the first worker's expanded private rendering.
  The ringed-site strict-perfect interfaces and `Scheme.IsStrictlyPerfect` concern
  other coefficient categories; they are not substitutes for this etale predicate.
- I opened the exact upstream corollary
  `ProEtale.DerivedCategory.boundedConstructible_derivedHom_mapDerivedCategory_of_isDualizable`
  in the older source and current shared Matrix module. Its signature uses upstream
  constructibility, derived Hom and pro-etale finite-coefficient presentations, and
  dualizability. It is not the exact statement in this DAG's recorded notions, so
  an `existing: true` attachment of the whole item would change its statement.
  The 51-module framework's `CondensedRing.derivedHom` was also opened: it is on
  condensed ring module objects and does not replace this finite constant-ring object.

Mismatch found and repaired: H4, the explicit local perfectness hypothesis repeated
an exact existing upstream predicate. Added its public import, replaced the expanded
hypothesis by `Etale.DerivedCategory.IsSitePerfect K`, and updated the explanatory
module/theorem docstrings and the node's `lean.statement` and `lean.note`. The old
hypothesis was mathematically equivalent, so no mathematical statement correction or
citer audit is needed. The similarly named DAG node `def-weil-site-perfect-complex`
was read: it concerns four coefficient stages on the pro-etale site and has no Lean
record; it is not an exact owner for this existing etale-only predicate. No duplicate
node, new definition, dependency repair, or added assumption is introduced.
The worker report above remains as the record of the initial version; this section
supersedes its assertion that the local perfectness hypothesis must be expanded.

All recorded statement dependencies were opened and their signatures checked as
listed above. The source-based four-step proof is retained in the theorem docstring:
finite dimension bound, etale sharp Hom bound, canonical Hom comparison, and comparison
preservation of constructibility and Tor amplitude against all pro-etale test sheaves.
No proof was filled. `autoImplicit false` binds every variable and universe; the final
recorded signature is verbatim the file signature. Every Lean line is at most 100 columns.

Validation of the revised file: `scompile.py N4 cor-sf-hom-ctf-proetale-unconditional`
with its absolute Lean path passed both the sandbox compilation (36.5 seconds) and the
library module compilation (8.5 seconds), with no diagnostics. An initial invocation
used a relative path from the read-only repository and found no sandbox file; rerunning
with the absolute sandbox path resolved that invocation error without source changes.
