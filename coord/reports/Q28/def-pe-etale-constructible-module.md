## Worker report

The module `Sheaf.AlgebraicGeometry.ConstructibleNoetherianEtaleModules` defines the
constructible etale modules of `def-pe-etale-constructible-module` and their bounded
constructible derived category. All six declarations are recorded. Every definition has
real data; there are no new theorems, axioms or sorry terms. No statement correction,
dependency replacement, or new node is needed.

The sandbox initially contained dispatcher markers only. The previous attempt's statement
that NP had reviewed the item refers to its stage-1 split. The current node has no `lean`
record. This delivery supplies that missing stage-2 record and its Lean module, rather than
redelivering an unchanged stage-1 node.

### Hypotheses and clauses

- Arbitrary scheme: `X : Scheme.{u}`. No quasi-compactness, quasi-separatedness,
  Noetherian-space, separatedness, or finite-type hypothesis is added.
- Arbitrary discrete commutative Noetherian coefficient ring: `Λ : Type (u + 1)` with
  `[CommRing Λ] [IsNoetherianRing Λ]`. Discrete coefficients are algebraic coefficients
  in `ModuleCat`; no topological-ring or completeness structure occurs.
- Size convention and small etale site: `X.smallEtaleTopology` on `X.Etale`, with module
  values in `ModuleCat.{u + 1} Λ`. Scheme and site universes follow the recorded framework.
  The derived localization uses the larger `u + 2` universe via the existing standard
  localization construction. No equality of site object and morphism universes is assumed.
- Constant ring: exactly `(constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj
  (RingCat.of Λ)`. The ambient module category is the recorded
  `ringedSiteModules.{u + 1}` of this ring sheaf, hence Mathlib's `SheafOfModules` with
  sectionwise semilinear restrictions and linear morphisms.
- Testing local constancy uses `Scheme.etaleConstantModuleRestrictionFunctor X Λ`.
  This is the existing restriction along the constant-ring sheafification unit. The
  existing constant-scalar equivalence shows that this changes the encoding, preserving
  all objects up to canonical isomorphism and all linear morphisms. It introduces no
  arbitrary map, chosen equivalence, or extra assumption. The node gains the already-landed
  dependency `lem-weil-pbc-etale-constant-ring-module-equivalence` for this construction;
  its node file is not changed.
- Every affine open: `∀ U : X.Opens, IsAffineOpen U → ...`. The chosen stratification
  is allowed to depend on U; there is no single global finite stratification.
- Finite partition with schemes and immersions: `∃ S :
  Scheme.LocallyClosedStratification U.toScheme`. Its `n : ℕ`, `stratum : Fin S.n → Set _`,
  `isLocallyClosed_stratum`, `pairwise_disjoint_stratum`, `iUnion_stratum_eq_univ`,
  `domain`, `immersion`, `isImmersion`, and `range_immersion` give exactly the node's
  finite, locally closed, disjoint, covering, immersed scheme pieces.
- Constructible in U, not merely locally closed: the separate clause
  `∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)` is in `U.toScheme`.
- Each inclusion into X: `S.immersion a ≫ U.ι`, used in the recorded
  `Etale.upperStar (ModuleCat.{u + 1} Λ)` inverse image.
- Etale covering of each stratum: `∃ V : Scheme.Cover.{u} Scheme.etalePrecoverage
  (S.domain a)`. Its maps are etale and jointly surjective by the existing cover
  definition. Its index need not be finite. Universe-u covers suffice: from any cover
  of a universe-u scheme one can select a member and a preimage for each point.
- Local constant module models: for every `b : V.I₀`, `∃ M : ModuleCat.{u + 1} Λ,
  Module.Finite Λ M ∧ Nonempty (...)`. `Module.Finite`, rather than `Finite M`, is exactly
  finite generation over Λ; the module can vary with the cover member.
- Restriction and its isomorphism: `.over (MorphismProperty.Over.mk ⊤ (V.f b)
  (V.map_prop b))` localizes the stratum sheaf at that etale object. The right side is
  `constantSheaf` with value M on the localized site. Localizing the small etale site
  at `V_b → Z_a` is the small etale site of `V_b`; this is the existing module-valued
  restriction encoding, also used by the recorded framework. Both sides and the
  isomorphism are in sheaves valued in `ModuleCat Λ`, so linearity is retained. Under
  the constant-scalar equivalence this is the induced constant-ring module structure.
- Constructible module category: `ConstructibleNoetherianModuleCategory` is
  `(constructibleNoetherianModules X Λ).FullSubcategory`. Thus all module-sheaf morphisms,
  identities and composition are inherited, without a new morphism restriction.
- Ambient derived category: `DerivedCategory` of the very same `ringedSiteModules`,
  using its inherited abelian structure. The named noncomputable instance simply supplies
  `HasDerivedCategory.standard _`; it is actual localization data, not a postponed theorem.
- Constructible cohomology in every integer degree:
  `∀ q : ℤ, constructibleNoetherianModules X Λ
  ((DerivedCategory.homologyFunctor _ q).obj K)`.
- Globally bounded cohomology: `∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ,
  (q < a ∨ b < q) → IsZero ((DerivedCategory.homologyFunctor _ q).obj K)`.
  A single finite interval applies to the whole complex. Requiring a ≤ b excludes no
  object, since the zero complex also admits a nonempty interval of bounds.
- Full bounded constructible derived category:
  `BoundedConstructibleNoetherianModuleCategory` is the `FullSubcategory` of that object
  property. All ambient derived morphisms, identities and compositions are retained.
  No derived completeness, Tor-amplitude, or perfectness condition occurs.

### Dependency declarations inspected and used

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, `Scheme.Etale`;
  covers are the existing `Scheme.etalePrecoverage` covers.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Topology.Constructible`: `Topology.IsConstructible`.
- `Mathlib.Topology.Defs.Basic`: `IsLocallyClosed`, through the recorded stratification.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory.standard`; its `HomologySequence` module gives `homologyFunctor`.
- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`:
  `Scheme.LocallyClosedStratification`, including the recorded `Topology.Stratification`.
- Added landed dependency, `Sheaf.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`:
  `Scheme.etaleConstantModuleRestrictionFunctor` and its existing canonical equivalence.
  The exact current published source was also read with `scompile.py --source`.
- `def-weil-size-convention` is recorded as a metatheoretic convention, so its content is
  rendered by the explicit universes rather than a nonexistent declaration.

### Source and edge checks

Read the paragraph before Stacks `etale-cohomology.tex` definition-constructible and
clause (3), and `proetale.tex` lemma-compare-constructible-derived, including the definition
of D_c; the bounded restriction is the node's blueprint scope. The source imposes no
Noetherian hypothesis on X and no finiteness condition on the underlying coefficient set.

The empty scheme permits n = 0 and empty covers. Empty strata are harmless; no positivity
or nonemptiness clause is imposed. The zero module and zero coefficient ring are allowed.
At a separably closed point with Λ = Z, the constant module Z is finitely generated although
its set is infinite, and is allowed. Non-quasi-compact schemes use independent finite
partitions on their affine opens. A non-quasi-compact open piece of an affine scheme is
locally closed but fails the explicit constructibility clause. An unbounded complex with
nonzero cohomology in arbitrarily large degrees fails the global finite-interval condition.
All relevant universes and variables are explicitly bound; no auto-implicit is used.

### Duplicate searches

- `msearch.py ... leansearch`: “Constructible sheaves of finitely generated modules on the
  small etale site, affine locally on finite constructible stratifications.” Eight hits:
  general `SheafOfModules` and finite-type generating sections, plus structure-sheaf modules;
  no etale constructibility or bounded constructible category definition.
- `msearch.py ... leanfinder`: “A constructible etale sheaf of modules over a Noetherian
  ring: every affine open has a finite constructible locally closed stratification with
  locally constant finitely generated module restrictions.” Eight hits, all general
  `SheafOfModules` finite type/presentation or local generator notions; no match.
- `msearch.py ... loogle`: `IsConstructibleSheaf, Module.Finite, LocallyConstantDatum`.
  No hits; unknown identifier `IsConstructibleSheaf` in the search index.
- `msearch.py ... grep`: `IsConstructibleSheaf|Constructible.*Module|constructible.*sheaf`
  in Mathlib/AlgebraicGeometry. No hits.
- `rg` over `WeilConjectures/ConstructibleSheaf`, the source's derived constructible
  category, and the shared `lean/Sheaf` found the global-stratification
  `Scheme.IsConstructibleSheaf`, finite-coefficient `Scheme.IsConstructibleEtaleModuleSheaf`,
  `Etale.DerivedCategory.isBoundedConstructible`, and the qcqs affine-local criterion.
  Read their definitions/signatures and docstrings. None is the arbitrary-scheme,
  affine-local Noetherian-coefficient notion of this node. The qcqs criterion is a theorem
  under extra hypotheses, not a definition usable here. Generic locally constant
  finite-type module predicates do not supply the affine-local stratification or either
  full category. Those local clauses stay inline, as in the node.
- Exact node-id search in the source tree: no hits. Exact new declaration-name searches
  in Mathlib, the source tree, and shared `lean/Sheaf`: no competing declaration.

Validation: prescribed `scompile.py Q28 def-pe-etale-constructible-module` compiled the
single delivery module without errors or warnings (sandbox 4.0 seconds, library 3.5 seconds).
The required `deliver2.py --no-push` result is recorded after the final dry run.

Final dry run: `deliver2.py Q28 def-pe-etale-constructible-module --no-push` printed
`OK (dry run): commit 73ef8da280 compiles and passes the preflight except for the second
reading, which the second reader writes; nothing pushed.` No second-reading section was
written by the author; the independent reader supplies it and delivers.

## Second reading by Q28

I independently reread the node statement, its Stacks source places, every recorded
statement dependency, and the six declarations in
`Sheaf.AlgebraicGeometry.ConstructibleNoetherianEtaleModules`.

The node's objects and clauses render as follows. (1) An arbitrary `X : Scheme.{u}` is
the first argument of `constructibleNoetherianModules` and of the derived-category
properties; no quasi-compact, quasi-separated, Noetherian-space, separated, or
finite-type instance is present. (2) `Λ : Type (u + 1)` with `[CommRing Λ]`
and `[IsNoetherianRing Λ]` is explicit on each constructible and bounded definition;
the coefficient is therefore a discrete commutative Noetherian ring, with no topology
or completeness hypothesis. (3) The small site and coefficient encoding are exactly
`X.smallEtaleTopology`, `ModuleCat.{u + 1} Λ`, and
`(constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of Λ)` inside
`ringedSiteModules.{u + 1}`. The only translation is the recorded
`Scheme.etaleConstantModuleRestrictionFunctor`, whose existing equivalence preserves
the module-sheaf notion and is cited by the dependency list. (4) For every
`U : X.Opens` with `IsAffineOpen U`, the definition supplies one finite
`Scheme.LocallyClosedStratification U.toScheme`; its `Fin S.n` strata, local-closed
scheme immersions, pairwise disjointness, and covering are inherited from
`LocallyClosedStratification`, while
`Topology.IsConstructible (S.stratum a)` is stated separately for every stratum.
Thus the partition may depend on `U` and there is no global finite partition. (5) For
each stratum, `S.immersion a ≫ U.ι` is the inclusion into `X`, and the clause uses the
recorded `Etale.upperStar (ModuleCat.{u + 1} Λ)` inverse-image functor. (6) For each
stratum there is an arbitrary universe-`u` etale cover
`V : Scheme.Cover.{u} Scheme.etalePrecoverage (S.domain a)`; for each `b : V.I₀`
the module model is `M : ModuleCat.{u + 1} Λ` with `Module.Finite Λ M`, followed by
`Nonempty` of an isomorphism between the localized inverse image and the localized
constant sheaf with value `M`. This is finite generation of modules, not finiteness of
the underlying set, and keeps linear morphisms. (7) The constructible category is
`(constructibleNoetherianModules X Λ).FullSubcategory`, so it retains exactly all
ambient module-sheaf morphisms. (8) The ambient derived category is
`DerivedCategory (ringedSiteModules ...)`; `noetherianEtaleModulesHasDerivedCategory`
selects `HasDerivedCategory.standard`, genuine localization data rather than a
hypothesis. (9) `boundedConstructibleNoetherianModules` requires constructibility of
`(_root_.DerivedCategory.homologyFunctor _ q).obj K` for every `q : ℤ`, and supplies
`∃ a b : ℤ, a ≤ b ∧ ∀ q, (q < a ∨ b < q) → IsZero (...)`. This is one finite
cohomological interval for the whole complex. (10) The bounded category is the full
subcategory of that property, retaining all ambient derived morphisms and imposing no
completeness, Tor-amplitude, or perfectness clause.

Verdict: every object, hypothesis, quantifier, and conclusion clause agrees with the
node. I found no mismatch and made no Lean change. In particular, the `Nonempty`
wrapper only expresses existence of the required canonical local isomorphism; it does
not choose an arbitrary map, and the cover itself remains the source's etale local
constancy condition.

Edge cases checked independently: `Fin S.n` permits `n = 0`, so the empty scheme and
empty finite partition remain available; no positivity or nonemptiness assumption was
introduced. The zero module and zero coefficient ring satisfy the stated algebraic
classes where available. `Λ = ℤ` with model `ℤ` is permitted although its underlying
set is infinite, confirming that `Module.Finite` is the intended condition. A
non-quasi-compact scheme is handled affine-open by affine-open, with no hidden global
finite cover. The bounded condition permits the zero complex (choose any `a ≤ b`) and
rejects complexes with nonzero cohomology outside every finite interval. All site,
coefficient, and derived universes are explicit; no universe equality or auto-implicit
variable remains.

I repeated the duplicate-definition search using `msearch.py` LeanSearch, LeanFinder,
and Loogle queries for constructible etale module sheaves; `rg` searches over Mathlib,
`WeilConjectures/`, and `lean/Sheaf`; and exact declaration-name searches. Hits were
general `SheafOfModules` finite-type/presentation predicates, condensed locally constant
functors, and unrelated global or finite-coefficient constructibility definitions.
None has this arbitrary-scheme, affine-local, Noetherian-coefficient statement together
with its bounded derived full subcategory. The recorded dependency declarations were
opened, including `Scheme.LocallyClosedStratification`, `Etale.upperStar`,
`ringedSiteModules`, `constantSheaf`, `Module.Finite`, `DerivedCategory`, and the
constant-ring module equivalence; each supplies exactly the interface used here.

The repaired sandbox module compiles cleanly with the prescribed `scompile.py` wrapper
(Lean file and library compile, 3--4 seconds each, no errors or warnings). No statement
correction, dependency repair, or new node was needed.
