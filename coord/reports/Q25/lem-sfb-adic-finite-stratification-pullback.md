## Worker report

This is the stage-2 statement of `lem-sfb-adic-finite-stratification-pullback` in
`Sheaf.AlgebraicGeometry.AdicFiniteStratificationPullback`, with principal declaration
`AlgebraicGeometry.Scheme.adic_finite_stratification_pullback`. All theorem proofs are
`sorry`. Definitions contain real data. The module's helper declarations package the
objects and canonical maps explicitly required by this same node, and all 34 are
listed in `lean.declarations`.

The previous attempt confused the stage-1 N1 landing with a stage-2 completion.
Reading the current node shows `reviewed` by N1, but no `lean` or `reviewed_lean`.
The N1 report describes a DAG split, not a Lean statement. This delivery therefore
adds a genuine Lean record and a new module rather than resubmitting an unchanged
node. No natural-language statement, proof plan or dependency list was changed.

Source read: `literature/stacks-project/sites-modules.tex`,
`lemma-pullback-locally-constant` (Tag 093R), including its explicit fixed-ring-module
case. The node expands this omitted proof by its eight reviewed proof steps; those
steps, not a weaker abstract preservation lemma, are transcribed in the theorem
docstring. Scheme fibre products use Mathlib's actual cone and limit definitions.

Hypothesis and conclusion correspondence:

- Scheme X: `(X : Scheme.{u})`. There is no quasi-compactness, quasi-separatedness,
  reducedness, finite-type or Noetherian hypothesis on X.
- Arbitrary commutative ring R: `(R : Type (u + 1)) [CommRing R]` in the usual larger
  coefficient universe. There is no `[Finite R]`, `[Fintype R]`, finite-presentation
  or Noetherian assumption.
- Choice of the small etale or small pro-etale sites for all schemes: `pro : Bool`,
  uniformly false for etale and true for pro-etale. `adicStratificationSite`,
  `adicStratificationTopology` and `adicStratificationBaseChange` select precisely the
  existing categories, topologies and base-change functors. Their original site
  object universe is u+1 and their original arrow universe is u.
- Small-model transport: `adicStratificationModel` is `AsSmall.{u+1}` of that site,
  with the topology induced by `AsSmall.down`. It retains every object and enlarges
  Hom types by `ULift`. This is an equivalence, not an assumption equating the two
  original universes, a small subsite, or a restriction on schemes. It makes the
  already recorded small-site finite-type predicate applicable directly.
- Constant-ring module sheaves: `adicStratificationModules` abbreviates the recorded
  `CategoryTheory.ringedSiteModules` of the recorded `CategoryTheory.constantSheaf`
  with value `RingCat.of R`. There is no alternative sheaf category or private
  definition of locally constant modules.
- Finite family: `r : ℕ` and `D.sheaf : Fin r → adicStratificationModules pro X R`.
  The family can be empty or have repetitions.
- A given open cover for each sheaf: `D.coverIndex : Fin r → Type v`,
  `D.opens j : D.coverIndex j → X.Opens`, and `D.covers j`, asserting that the
  supremum of those opens is top. The index universe v is independent and the
  covers need not be finite. Bundling choices of covers and partitions is exactly
  supplying witnesses of the node's hypotheses, without an extra property.
- Given finite constructible locally closed scheme stratifications on each input
  open: `D.strata j a : Scheme.LocallyClosedStratification (D.opens j a).toScheme`.
  This uses the dependency's recorded declaration. Its currently imported parent
  `Topology.Stratification` includes `isConstructible_stratum`, in addition to
  locally closedness, pairwise disjointness and the covering equation. Thus the
  explicit constructibility requirement of this item is retained even though the
  dependency's older record note describes a parent without that field.
- Each input restriction is locally constant of finite type: `D.locallyConstant`
  applies exactly the recorded `SheafOfModules.IsFiniteTypeLocallyConstant` to the
  pullback of `D.sheaf j` along the composite of the stratum immersion with the open
  immersion into X. This uses finite generation of the module, not finiteness of
  its underlying set or finite presentation.
- Exactly the intersection cover: `D.commonOpen p` is `⨅ j, D.opens j (p j)` for
  every tuple p of input cover indices. The theorem's first conjunct states that
  the supremum of all these intersections is top. Its second conjunct supplies a
  `CommonRefinement` for every such intersection, including empty intersections.
- A finite disjoint covering by constructible locally closed scheme strata:
  `CommonRefinement.strata` is the same recorded scheme stratification type, now
  over `D.commonOpen p`. Its inherited fields give finiteness, local closedness,
  constructibility, pairwise disjoint images and union equal to the whole open.
- Actual finite fibre products of the input strata restricted to U:
  `factor k j` chooses one input stratum for each j. `productFactors` consists of U
  and those original strata, all mapped to X by `productArrows`.
  `cone k` and `isLimit k` assert their genuine universal property; `point k` ties
  the cone point to `strata.domain k`, and `toOpen k` identifies its U-projection
  with the stratum immersion. Taking this product over X with the U-factor is
  equivalently the finite product over U of the base-changed input strata. This
  formulation retains the original projections without arbitrary choices of
  factorization through their set-theoretic images.
- Exactly the nonempty products for r>0: `nonempty` discards empty domains. The
  partition covers U and is pairwise disjoint, so no nonempty combination can be
  omitted or duplicated: any point of that product lies in exactly one common
  stratum, and disjointness of each input partition forces all its factor indices.
- Actual morphisms to original strata: `projection k j`, `projection_eq k j` and
  `projection_comp k j` give the cone projection, its equality with the limiting
  projection, and the required equality of composites to X.
- Simultaneous finite-type local constancy: `CommonRefinement.locallyConstant`
  applies the identical existing predicate to every j on every common stratum.
- Every chosen trivializing covering pulls back: `CommonRefinement.coverings`
  quantifies over every covering sieve S of every original site object W and uses
  precisely `S.functorPushforward` along the scheme base-change functor. This is
  the sieve generated by the actual base-changed arrows. In particular, a cover
  of the original final object becomes a cover of the target final object, up to
  its canonical final-object isomorphism. The formulation also includes all slice
  covers used by the recorded finite-type predicate.
- Every chosen trivialization, with the same model M:
  `CommonRefinement.trivializations` quantifies over any original site object V,
  any `M : ModuleCat R` with `Module.Finite R M`, and every given local isomorphism
  e. It asserts `AdicStratificationTrivializationCompatibility`, whose output d
  identifies the refined restriction with the constant sheaf of that exact same M
  on the base-changed V. Together with `coverings` this applies member by member
  to every chosen trivializing covering, allowing different models on members.
- Canonical constant-ring identification: `adicStratificationRho` is constructed
  by sheafification of the constant-section map, and `adicStratificationRingMap`
  is its adjoint. `adicStratificationRingMap_isIso` states its invertibility for
  arbitrary R. Module pullback is Mathlib's `SheafOfModules.pullback` for rho,
  namely the sheafified module Kan extension, canonically the ringed-topos module
  inverse image with extension along that adjunct. The given pro-etale and etale
  inverse-image constructions are therefore used on their equivalent small models.
- Canonical constant-module identification: `adicStratificationConstantMap` is
  chosen from an existence-and-UNIQUENESS theorem specifying its adjunct on each
  constant generator m. This determines the actual map, rather than choosing data
  from a bare existence theorem. `adicStratificationConstantMap_isIso` states its
  invertibility. There is no unknown module or arbitrary comparison object.
- Compatibility with inverse-image composition: the sectionwise fibre-product
  pasting uniquely determines `adicStratificationPushforwardComp`; its adjunction
  mate defines `adicStratificationPullbackComp`.
  `adicStratificationConstantMap_comp` gives the actual equality of constant-module
  comparisons under this mate. `adicStratificationProjectionComparison` then uses
  the actual equation `projection_comp` to identify the common restriction with
  the two successive inverse images. The normalization equation in
  `AdicStratificationTrivializationCompatibility` uses its inverse, the module
  adjunction unit, the given e and the canonical constant map. Thus d is specified
  by this commuting square, not merely asserted to exist as some isomorphism.
- Empty family: `emptyFamily` requires one stratum and an isomorphism immersion
  when r=0. In that case `commonOpen` is the empty infimum, hence all X; the cone
  has just the U-factor and realizes the identity partition even for empty X.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale` and `smallEtaleTopology`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: the reexported `Scheme.ProEt`
  and `Scheme.ProEt.topology`. The node also records an ordinary derived category;
  no derived category is needed in the present underived statement.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `Etale.upperStar`, its module-compatible inverse-image adjunction and
  `Etale.isContinuous_overPullback`. Using the existing continuity instance as a
  term also resolves the opaque `smallEtaleTopology` wrapper, which is definitionally
  its `smallGrothendieckTopology`; no topology-changing assumption was added.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport` reexports the arbitrary
  inverse-image construction in `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
  In particular `proEtaleBaseChange`, its continuity, and the AsSmall transport in
  that module supply the pattern used uniformly here. Its finite-coefficient
  realization helpers are not used and impose no finiteness assumption.
- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`:
  `Scheme.LocallyClosedStratification` with the existing `Topology.Stratification`.
- `Sheaf.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf`:
  `SheafOfModules.IsFiniteTypeLocallyConstant`, and its reexported
  `strictPerfectConstantSheaf` / `strictPerfectConstantPresheaf` from
  `Sheaf.Paper.StrictPerfectCoefficientPackage`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: actual scheme
  pullbacks; `WidePullbackCone` and `IsLimit` give the finite universal property.
- `Mathlib.Topology.Constructible`: `Topology.IsConstructible`, via the inherited
  stratum field. The source signature, docstring and Boolean closure lemmas were read.

Proof-only imports include the already recorded stratification pullback, constructible
preimage, immersion composition, the upstream etale algebraic-structure inverse image,
and `Sheaf.Paper.LocalizeRingedSiteMorphism.localize_ringed_site_morphism` (in namespace
`SheafOfModules`). The two general geometric constant-module proof nodes currently
have no Lean record. They are proof dependencies only; this module supplies the
scheme-site canonical comparisons needed in its own statement as uniquely normalized
helpers with the source and proof steps in their docstrings. It does not rebind either
general-site node to a scheme-only specialization.

Edge cases checked before writing and rechecked against the final fields: r=0;
X empty with either empty input covers or one empty cover member; empty intersections
for r>0 (zero common strata allowed); a zero coefficient ring; zero or repeated sheaves;
infinite rings such as the integers; finitely generated modules over non-Noetherian
rings that need not be finitely presented; nonreduced input strata (actual cones and
projections are retained); arbitrarily indexed input covers; and the distinct original
site object/Hom universes. No `STATEMENT-DISPUTED` issue or statement correction remains.

Searches actually executed with the prescribed msearch wrapper:

- LeanFinder: “Finite families of constructible module sheaves on schemes admit a
  common finite fibre product stratification preserving chosen locally constant
  trivializations”. Eight hits about finite module presentations, generators and
  scheme-limit morphisms; no common-strata theorem.
- Loogle: `"Sheaf", "LocallyConstant"`. Twelve condensed and locally constant
  presheaf hits; no theorem on simultaneous scheme strata or fixed-ring modules.
- Mathlib grep: `stratification|locallyConstant.*pullback|locallyConstant.*inverseImage`
  in CategoryTheory. No hits.
- LeanSearch: “Common finite constructible stratification for finitely many sheaves
  of modules over a constant ring, compatible with pullback of chosen trivializations”.
  Eight hits including `SheafOfModules`, its finite-type predicates, and pullback of
  free sheaves; no simultaneous stratification theorem.
- `rg` on upstream WeilConjectures for the same concepts found stratification
  definitions and etale constructible-sheaf pullback, not this two-site arbitrary-ring
  chosen-trivialization statement. Searching the item id in upstream gave no hit.
- `rg` on the project's `lean/Sheaf` for common stratification and pullback found
  references in adic reconstruction and coefficient modules, but no declaration of
  this reviewed statement. Reading the present node confirmed it had no Lean record.

Validation is performed only through `scompile.py` and `deliver2.py`. Each delivered
module is compiled separately under the fixed 60-second limit. No global build,
source-checkout mutation or direct Git command is used.

## Dependency modules

`def-weil-proetale-inverse-image` is repaired under §1(B) by an `existing: true`
record for `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`, whose complete source was
read both locally and through `scompile.py --source`. The return uses the earlier
name `def-weil-pbc-proetale-inverse-image`; the current item's dependency list and
current DAG use `def-weil-proetale-inverse-image`. Its current recorded primary
`AlgebraicGeometry.ProEtale.finiteModuleAdjunction` requires `[Finite A]` and
`[DiscreteTopology A]`, so it cannot be the arbitrary-ring interface of this node.
The new `lean.note` records this defect and the exact replacement. No definition
is copied, and no dependency field outside `lean` is changed.

The replacement lists all 25 declarations of the existing module. The node's
clauses match them as follows: `proEtaleBaseChange` is the actual scheme pullback
functor on objects and arrows; its continuity, cover preservation and finite-limit
instances give the morphism of sites. `proEtaleInverseImageIndex` is the stated
category of pairs, and `proEtaleSheafInverseImage` is the sheafified left Kan
extension. `proEtaleSheafDirectImage` is precomposition and
`proEtaleSheafAdjunction` gives the unit and counit. The generic value category
includes sets, abelian groups, rings and commutative rings.
`proEtaleConstantDirectImageMap` extends constant sections and
`proEtaleConstantInverseImageMap` is its specified adjoint.
`proEtaleModuleInverseImage` supplies the induced module action over the inverse
image ring. The constant-ring, coefficient rho/c, constant-module direct image,
tensor pullback and map declarations specialize these constructions to every
commutative ring, with no finiteness or topology assumption. The `ULift` coefficient
presentation and `AsSmall` site transport preserve the original two site universes.
The consumer already imports and uses this exact module; its arbitrary
`R : Type (u+1)` construction on the small model remains unchanged.

## Second reading by Q25

Repair self-check: reread the current item node, the retained Lean file, the
returned H13 diagnostic, the current finite-coefficient dependency record and all
of `ProEtaleInverseImage.lean`. This is a self-check; no additional agent was
started, as the repair brief prohibits that. The item's natural statement,
proof plan and dependency list agree with current main outside its added `lean`
record. The retained item signature and all its substantive clauses remain as
reported above; no Lean source change is needed. The mismatch found is precisely
the dependency's finite-coefficient binding, now repaired with the existing
general interface and an explicit explanation in `lean.note`.

In particular, rechecked that `proEtaleConstantModulePullback` binds only
`(A : Type u) [CommRing A]`, not `[Finite A]`; hence infinite coefficient rings,
including the integers, are covered. The generic constant-ring comparison also
accepts rings in the larger coefficient universe used by the consumer. Neither
empty schemes, the empty family, the zero ring nor non-Noetherian rings are
excluded by this repair. No source-based statement correction or new node is
necessary. The original item module was retained and its compile is rerun through
`scompile.py`, followed by the required full delivery dry run.
