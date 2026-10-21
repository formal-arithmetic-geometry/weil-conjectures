## Worker report

The module `Sheaf.Paper.FiniteDiscreteConstructibleModel` states
`AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscrete_boundedConstructible_iff_classicalModel`.
Its whole proof is `sorry`. It introduces no definitions, helper theorems, new nodes, or
changes to the mathematical node. The node copy changes only `lean`.

The statement is the equivalence in the node, with a literally bounded cochain complex
as the classical model. The coefficient identification and sectionwise equivalence are
explicit inputs to the already recorded common encoding, rather than an arbitrary
replacement equivalence. They are exactly the data required by that dependency.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Finite discrete commutative ring T | `B : Type`, `[CommRing B]`, `[TopologicalSpace B]`, `[IsTopologicalRing B]`, `[Finite B]`, `[DiscreteTopology B]`. The name B avoids collision with scheme parameters. |
| Noetherian scheme Z, explicitly quasi-compact and locally Noetherian | `(Z : Scheme.{u}) [CompactSpace Z] [IsLocallyNoetherian Z]`. No separation hypothesis is added. |
| The continuous-function condensed ring and its pullback T_Z^c | `Profinite.continuousMapRingObj.{u} B` and `condensedRingObj (Profinite.continuousMapRingObj.{u} B) Z`, respectively. The latter is the strong monoidal pullback from the point, as in `coefficientRing`. |
| The explicitly constructed common exact encoding with its finite-discrete constant-ring identification | `finiteDiscreteCoefficientEquivalence B eR G hG Z`. `eR` is the specified isomorphism from the sheafified constant ring to the continuous-function ring, with `[IsMonHom eR.hom]`. `G`, `[G.IsEquivalence]`, and `hG` are the dependency's fixed internal-abelian-group module equivalence and literal forgetful-functor equality. The theorem quantifies over this supplied encoding data. |
| K in the ordinary internal-module derived category | `(K : DerivedCategory (FiniteDiscreteInternalModules B Z))`. Expanding the abbreviation gives precisely `DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u+1}) T_Z^c)`. |
| (i) Bounded constructible in the general ring-object sense | `boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj.{u} B) Z) K`. This is the existing general predicate, not the finite-constant-model predicate or the separate discrete-site presentation. Its definition is t-boundedness and `IsConstructibleModuleObject` for each cohomology module. That definition uses finite strata and locally finitely presented modules with unrestricted presentation maps. |
| (i) and (ii) are equivalent | The main connective is `↔`. |
| (ii) There exists a bounded complex L of ordinary etale B-modules | The existential is over `L : CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u+1} (ULift.{u+1} B))) ℤ`, followed by `a b : ℤ`, `a ≤ b`, `L.IsStrictlyGE a`, and `L.IsStrictlyLE b`. These mean terms vanish outside a finite interval; no projectivity or termwise constructibility is imposed. |
| L as an object of D(Z_et,T) | `DerivedCategory.Q.obj L`, using the ordinary localization and the coefficient encoding of the recorded `def-weil-pbc-derived-categories`. |
| Classical constructible cohomology locally on affine opens | `∀ (q : ℤ) (U : Z.Opens), IsAffineOpen U → Scheme.IsConstructibleSheaf ((Etale.upperStar (ModuleCat ...) U.ι).obj (L.homology q))`. This spells out the affine-open condition rather than replacing it with a potentially stronger global predicate. On each U, `IsConstructibleSheaf` means a finite constructible locally closed stratification with finite locally constant restrictions. `IsFiniteSheaf` is finite generation of module stalks, which for finite B is equivalent to finite underlying sets of the local constant module values. |
| The actual site comparison nu_Z^* | `comparisonUpperStar (ModuleCat.{u+1} (ULift.{u+1} B)) Z`, the module left Kan extension followed by sheafification appearing in `proEtaleSiteComparisonModules`. |
| K is isomorphic to E_Z nu_Z^* L in the ordinary derived category | `Nonempty (K ≅ E.functor.mapDerivedCategory.obj (nu.mapDerivedCategory.obj (DerivedCategory.Q.obj L)))`, with E and nu expanded explicitly in the signature. Both are the existing exact functor localization construction; there is no arbitrary functor or mere equivalence in place of the specified construction. |
| The zero ring is allowed | No `Nontrivial B`, field, characteristic, prime, or invertibility assumption occurs. |
| No Tor amplitude | Neither predicate nor existential mentions Tor amplitude, flatness, perfectness, completion, or a completed category. |

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, publicly retaining
  `Profinite.continuousMapRingObj` from the continuous-coefficient construction.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `coefficientRing_X`, and
  `condensedRingObj`; these give the existing pulled-back ring, not a copied definition.
- `Sheaf.Paper.FiniteDiscreteCoefficientEncoding`:
  `AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteCoefficientEquivalence`.
  Its full eR/G/hG interface is retained verbatim. The publicly imported
  `FiniteDiscreteRealizationFunctor` supplies `FiniteDiscreteInternalModules`,
  `FiniteDiscreteProEtaleSheaves`, and `finiteDiscreteEncoding_additive`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `AlgebraicGeometry.Scheme.proEtaleSiteComparisonModules`, expressed using the already
  defined `AlgebraicGeometry.ProEtale.comparisonUpperStar` in
  `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the recorded
  general-derived-category convention interface; the category itself is Mathlib's
  `DerivedCategory`, and the exact localization here is `Functor.mapDerivedCategory`.
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`: publicly retains
  `AlgebraicGeometry.ProEtale.boundedConstructible` from the source
  `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`. Its general
  `IsConstructibleModuleObject` is in the source `ProEtaleModule.Def`.
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`:
  `AlgebraicGeometry.ProEtale.constructibleComparison`, the recorded discrete comparison
  interface. For the actual classical sheaf predicate on the original etale site, use
  the existing `AlgebraicGeometry.Scheme.IsConstructibleSheaf`, `Stratification`, and
  `IsFiniteLocallyConstantSheaf` from `WeilConjectures.ConstructibleSheaf.Defs`; these
  notions are not redefined in this delivery.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`; `Mathlib.AlgebraicGeometry.Noetherian`:
  `AlgebraicGeometry.IsLocallyNoetherian`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: reexports
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, `DerivedCategory.Q`, the cohomology
  functor, and the ordinary derived-category conventions. Q(L) uses that exact category.

All already stated proof-dependency modules are imported without `public` unless they
are already a statement-dependency import. The Mathlib exact-functor localization and
cohomology comparison, bounded representative, finite-presentation, and general
constructibility modules are available through these imports. The docstring follows
all seven proof steps, including the finite presentation over a finite ring, affine
refinement and globalization, compatibility with restrictions, rank-one normalization,
and preservation of every vanishing interval. No proof is filled in this delivery.

Edge cases checked before writing:

- B = 0: all module categories have only zero modules up to isomorphism; finite
  presentations and the supplied encoding still make sense. No nonzero coefficient is
  required.
- Z empty: the constructibility predicates permit the empty stratification and the
  zero complex supplies a model; no point, inhabited cover, or nonempty stratum is bound.
- K zero: choose the zero cochain complex and bounds a = b = 0. Both strict bounds and
  all affine-local constructibility conditions apply.
- Nonregular finite coefficient ring, for example B = Z/4 with the degree-zero constant
  module Z/2: this is included despite infinite projective dimension. No finite-Tor
  predicate is accidentally inherited from the source's separate ctf interfaces.
- Bounds may be any integers, including negative ones and a = b. No fixed interval is
  imposed. Existentially ordering bounds does not discard zero objects.
- The scalar convention is exactly the recorded common encoding: finite rings are
  represented by a small carrier `B : Type`, then `ULift.{u+1} B`; schemes have arbitrary
  universe u. Every finite ring has such a small presentation, and coefficient/module
  values are not forced into the scheme universe. No extra equality of site universes
  or countability restriction is used.

Searches made (2026-10-21):

- `msearch.py ... leanfinder "Bounded constructible internal modules over a finite
  discrete condensed ring are exactly bounded constructible etale module complexes"`:
  eight hits, including `CondensedMod.isDiscrete_tfae`, `Condensed.finFree`, and light
  condensed variants. None is the scheme/internal derived statement.
- `msearch.py ... loogle '"Sheaf", "Constructible"'`: zero hits.
- `msearch.py ... grep '(constructible|Constructible).*(Condensed|Proetale|ProEtale)|(Condensed|Proetale|ProEtale).*(constructible|Constructible)'`:
  zero Mathlib hits.
- `msearch.py ... leansearch "Finite discrete coefficient encoding identifies bounded
  stratified locally finitely presented internal proetale modules with constructible
  etale complexes"`: eight hits, including condensed discreteness, constant module
  functors, and `SheafOfModules.isFinitePresentation`; none gives the stated equivalence.
- `rg` of the corresponding constructibility/finite-discrete patterns in
  `lean/WeilConjectures` and `lean/Sheaf`: finds the recorded encoding and its one-way
  sheaf constructibility theorem, plus ordinary/ctf comparison interfaces. The latter
  use different coefficient equivalences or impose finite Tor amplitude, so cannot be
  rebound as this statement.
- `rg -n 'lem-sfb-finite-discrete-constructible-model' lean/WeilConjectures`: no hit.
  `rg` for the proposed declaration names in both source roots, Mathlib, and the
  upstream-name index: no collision.

Sources checked: local Bhatt--Scholze PDF, Sections 5.1 and 5.4; local Stacks
`proetale.tex`, `lemma-compare-constructible` and `lemma-compare-constructible-derived`
(Tags 09AK and 09AL); `etale-cohomology.tex`,
`lemma-constructible-quasi-compact-quasi-separated` (Tag 095E). These use ordinary
Noetherian coefficients without a characteristic or finite-Tor restriction.
The prescribed compact-object example is now withdrawn; its node points to the same
source example under `WeilConjectures.CategoryTheory.CompactObject`, which was read for
the current module/header conventions.

Validation: prescribed `scompile.py Q12 lem-sfb-finite-discrete-constructible-model ...`
passed for both sandbox (5.4 s) and library module name (8.8 s), without errors or
warnings. No local compiler, global build, repository edit, or direct Git command was run.
No statement dispute or node fault was found.

## Second reading by Q12

This is the worker's second reading with the node and completed module open. No other
agent was started, as the dispatcher brief prohibits that; the independent review is
the maintainer's delivery review.

Rechecked every binder against the node: B is finite discrete commutative, eR/G/hG are
exactly the recorded construction's inputs, Z has precisely compactness and local
Noetherianity, and K is in the internal ordinary derived category. Rechecked both sides
of the iff: the left calls the general ring-object predicate; the right quantifies a
bounded complex of the original etale-site fixed-module sheaves, tests its cohomology
on every affine open, and uses the specified exact comparison and encoding to form its
image. In particular, the cohomology condition concerns H^q(L), not the terms of L,
and the two functors are applied in the order nu^*, then E. The isomorphism is ambient,
with no change to the source or target derived category. No finite-Tor, regularity,
nontriviality, separation, or completion condition was added. No mismatch was found;
no statement correction or dependency repair was needed.
