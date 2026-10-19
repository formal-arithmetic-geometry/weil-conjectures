## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.ExceptionalBaseChangeReducesToProper`.
Its theorem `AlgebraicGeometry.Scheme.exceptionalBaseChangeReducesToProper` has
exactly one postponed proof, `sorry`. All helper definitions contain actual data.
The dependency module `Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction`
constructs the finite constant-coefficient open adjunction without a postponed proof.
No new nodes or natural-language statement corrections are included.

The hypotheses and clauses are rendered as follows.

- The prime and finite extension are `l`, `[Fact l.Prime]`, `E`, `[Field E]`,
  `[Algebra (Padic l) E]`, and `[FiniteDimensional (Padic l) E]`.
  `exceptionalCoefficientRing l E n` is the existing coefficient quotient at
  level `n+1`, representing every positive level; the existing construction fixes
  a uniformizer, whose choice does not change its defining ideal. The named
  instance obtains finiteness from `Padic.finite_coefficientExtensionRing`.
- The schemes and maps are the explicit scheme binders, `f`, and arbitrary `g`.
  `[IsSeparated f]`, `[LocallyOfFiniteType f]`, `[QuasiCompact f]`, `_hX`, and
  `_hY` give exactly separated finite type and invertibility of ell on X and Y.
- `c : Compactification f` and `c' : Compactification f'` specify the chosen
  open/proper factorizations, including their factorization equations.
  `X'`, `g'`, `f'`, `overlineG`, and `hsq`, `hbar`, `hopen` express all three
  Cartesian squares. Their universal-property formulation allows every choice
  of the fibre products. No extra finite-type assumption on g is imposed.
- `proEtaleDerivedCategory` is the ordinary unbounded derived category of
  intrinsic constant-ring modules. `exceptionalModulePullback` transports
  the existing exact site inverse image using `sfIntrinsicModuleEquivalence`;
  `exceptionalDerivedPullback` applies `mapDerivedCategory`. No arbitrary
  operations or constructible subcategories replace these categories.
- `ambient` and `ambient'` supply the optional ambient exceptional right-adjoint
  data. Their `adjunction c` and `adjunction c'` have the specified compact-support
  functors as left adjoints; the theorem asserts no existence of these data.
- `Q`, `Q'`, `adjP`, and `adjP'` specify the proper right adjoints and adjunctions.
  `deltaP` has the reverse proper direct-image comparison type. `betaP` has the
  proper exceptional comparison type and `hbetaP` fixes it as the mate of
  `deltaP` under these very adjunctions, using Mathlib `mateEquiv`.
- `exceptionalDerivedOpenSquare` constructs canonical alpha using
  `ProEtale.upperStarCompIso` for `hopen.w`, the canonical equivalence unit,
  and derived termwise/composition isomorphisms. The inverse of `mateEquiv`
  for the two constructed `exceptionalOpenAdjunction` values gives gamma.
- `whiskerRight ... (proEtaleConstantDerivedDirectImage c'.g ...)` is
  Rp'_* gamma; `whiskerLeft (derivedOpenExtension c.i ...) deltaP` is
  deltaP j_!. Their composite is exactly delta_f. The final mate uses the
  supplied ambient adjunctions, and `IsIso betaP → IsIso (...)` is precisely
  the asserted conditional invertibility of beta_f.

Dependency declarations used include `Padic.finite_coefficientExtensionRing`
(`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`),
`AlgebraicGeometry.Compactification` and its refinement category
(`WeilConjectures.Compactification.Refinement`), Mathlib `IsPullback`,
`SfAmbientExceptionalRightAdjointDatum`
(`Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint`),
`ProEtale.upperStar` and `ProEtale.upperStarCompIso`
(`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso`),
`ProEtale.openImmersionLowerShriekUpperStarAdjunction`
(`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`),
`sfIntrinsicModuleEquivalence` and `sfIntrinsicExtensionByZero`
(`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`),
`CategoryTheory.mateEquiv` and its pasting laws (Mathlib Mates),
`Adjunction.rightAdjointUniq` (Mathlib Unique), `Adjunction.mapHomologicalComplex`
(`WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`), and
`Adjunction.localization` (Mathlib Localization.Adjunction).
The stated composition dependency is imported from
`Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition`; the finite constant
case is constructed directly from the existing canonical exact site comparison.

Edge cases checked: final `n=0` denotes coefficient level 1, and all positive
levels occur. Empty schemes, empty opens, zero complexes, and identity and
arbitrary base-change maps are included. Ell-invertibility on the base-changed
schemes follows from that on X and Y. No nonempty, boundedness, constructibility,
finite-Tor, or extra characteristic condition is imposed. The scheme universe u
is arbitrary, and the small pro-etale site's object and morphism universes are
not identified.

Searches already recorded in `searches.jsonl` and independently described in the
second reading below found no exact existing item theorem: LeanFinder for
exceptional base change reducing to the proper part, Loogle for
`CategoryTheory.mateEquiv`, and grep/rg for the item id, exceptional base change,
mate pasting, and adjoint uniqueness across Mathlib, the upstream project, and
`lean/Sheaf`. The exact source declarations and their docstrings were read.
The repair additionally traced the delivered modules' imports, inspected the
finite-coefficient open and pullback APIs and the general derived/complex APIs,
and read the current composition source using `scompile.py --source`.

## Returned delivery repair: L

The returned immutable head e63076fc5b0c failed on simultaneous imports of legacy
`ProEtale.UpperLowerStar.Defs` and
`ProEtale.FiniteCoefficient.UpperLowerStar.Defs`.
The supplied sandbox already used the finite-coefficient site operations and
constructed the open derived adjunction instead of importing the legacy derived
open-adjunction module. Rechecking that baseline against the current dependencies
passed, so the historical failure is not reproducible with the current published
import closure.

The concrete Lean repair narrows `IntrinsicDerivedOpenAdjunction` to the explicit
`FiniteCoefficient.LowerShriek.Open.Defs` API and the general complex-adjunction
API. It removes the unnecessary larger derived-composition import and redundant
localization import from that dependency module. The consumer now directly imports
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, which
provides the derived isomorphisms its square construction uses. Neither delivered
module imports the legacy ProEtale operation paths. No declaration's mathematical
signature or constructed data changed. Both node lean notes record this repair;
all other node fields remain unchanged.

Repair validation: `scompile.py Q01 cor-exc-base-change-reduces-to-proper`
compiled both revised modules separately in dependency order, including sandbox
and final module checks, with no compiler errors or warnings.

## Earlier second reading (a previous round; superseded)

I read the current DAG statement, all four proof steps, the blueprint source
at sec-smooth-purity/sk-prop-sf-existence/cor-exc-base-change-reduces-to-proper.md,
and the actual dependency signatures. The blueprint source is a Markdown node,
not a Stacks statement. Its unconditional final sentence has already been
replaced in the reviewed DAG by the explicit conditional ambient-datum version;
this delivery preserves that reviewed statement. There is no statement_change
in the item copy and I made no natural-language statement correction.
The earlier report above describes the first worker's superseded implementation.

The object/hypothesis/conclusion checklist, matched to the final Lean, is:

1. Prime ell, finite extension E/Q_ell, chosen integers/uniformizer, positive
   coefficient level and A=O_E/(varpi^level): `l`, `[Fact l.Prime]`, `E`,
   `[Field E]`, `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]`,
   and `n : ℕ`, with `exceptionalCoefficientRing l E n` the existing
   `Padic.coefficientExtensionRing l E (n+1)`. Every positive integer is of
   this form. The uniformizer is the existing coefficient construction's
   choice; the defining ideal is independent of it. Finiteness is supplied
   by `exceptionalCoefficientRing_finite` from the recorded
   `Padic.finite_coefficientExtensionRing`, not an extra hypothesis. PASS.
2. Schemes X,Y and separated finite-type f, with ell invertible: the scheme
   binders, `f`, `[IsSeparated f]`, `[LocallyOfFiniteType f]`,
   `[QuasiCompact f]`, `_hX`, and `_hY` give exactly these assumptions.
   There is no Noetherian, base-field, smoothness, properness of f, or
   finite-type assumption on g or Y. PASS.
3. A compactification X --j--> Z --p--> Y: `c : Compactification f`.
   I opened Compactification/Defs and Refinement: its `i` is open, `g` is
   proper, and `comm : f = i ≫ g`. Its lack of an explicit quasi-compact
   field for i is harmless here because f is quasi-compact (the source
   documents this equivalence). No density assumption is added. PASS.
4. Arbitrary g and the Cartesian changes: `g : Y' ⟶ Y`, `X'`, `g'`, `f'`,
   `c'`, `overlineG`, and `hsq`, `hbar`, `hopen : IsPullback ...` encode
   the lower, proper, and open Cartesian squares. The universal-property
   form permits every chosen fibre product, not just Mathlib's chosen one.
   `c'.comm` gives f'=p'j'. The removed finite-type/separated assumptions
   on f' and ell-invertibility on X',Y' follow by base change/pullback;
   they are not further input. PASS.
5. Ordinary unbounded constant A-module categories and operations:
   `proEtaleDerivedCategory` is the dependency's existing intrinsic
   constant-ring category, not a constructible, completed or bounded category.
   `exceptionalModulePullback` transports the existing exact `ProEtale.upperStar`
   using the existing `sfIntrinsicModuleEquivalence`; `exceptionalDerivedPullback`
   descends that functor termwise. The equivalence's functor is the canonical
   constant-scalar realization, whose inverse is fixed by equivalence units
   and counits. This is the permitted equivalent coefficient presentation,
   with no arbitrary pullback functor as input. PASS.
6. Supplied ambient data at c and c', over Y and Y': `ambient`, `ambient'`
   have type `SfAmbientExceptionalRightAdjointDatum A f c` and its primed
   version. I read that structure: it includes FullCD for the specified
   proper part, adjunctions for every compactification, and coherent
   refinement comparisons with unit/counit equations. Its `adjunction c`
   has precisely `sfAmbientCompactSupportCandidate A c = j_! ⋙ Rp_*`
   as left adjoint. No existence of ambient data is asserted. PASS.
7. Specified proper adjunctions: `Q`, `Q'`, `adjP`, `adjP'` give exactly
   Rp_* ⊣ Rp^times and Rp'_* ⊣ Rp'^times on the same ordinary categories.
   The direct-image declaration is the existing sectionwise canonical
   constant-coefficient direct image derived by K-injectives. PASS.
8. Reverse proper comparison and its mate: `deltaP`, `betaP`, `hbetaP`
   state the displayed types and the equality using Mathlib `mateEquiv`.
   I checked TwoSquare and mateEquiv's actual directions: G ⋙ L2 -> L1 ⋙ H
   maps to R1 ⋙ G -> H ⋙ R2. Thus these are precisely delta_p and beta_p;
   no invertibility of deltaP is required. The source explicitly permits
   specifying either map via the inverse mate bijection. PASS.
9. Canonical alpha and its open inverse mate: these are now constructions,
   not extra binders. `exceptionalPullbackCancellation` uses the inverse
   of the middle equivalence's unit. `exceptionalDerivedOpenSquare` then
   transports `ProEtale.upperStarCompIso ... hopen.w` and descends it through
   `mapDerivedCategoryNatIso` and the two derived composition comparisons.
   `exceptionalOpenAdjunction` composes the equivalence adjunctions with
   `ProEtale.openImmersionLowerShriekUpperStarAdjunction` and localizes
   the termwise complex adjunction. This avoids the monoidal assumptions
   of an unnecessarily specialized derived-adjunction API. The inverse
   of `mateEquiv` applied to alpha is exactly gamma. PASS.
10. delta_f and the conditional conclusion: the displayed `whiskerRight`
    applies Rp'_* to gamma, and `whiskerLeft` applies deltaP after j_!.
    Their composite is delta_f. The final `mateEquiv` uses exactly the two
    supplied `ambient.adjunction` values. `IsIso betaP → IsIso (...)`
    is exactly invertibility of beta_p implying invertibility of beta_f.
    No identification of just endpoints replaces the specified map. PASS.

Mismatches found and repaired:

- H3/H4: `DerivedPullbackTensorHomData` had unconstrained functor fields;
  a comment calling them derived operations did not characterize them.
  It also replaced the completed integral, rationalized, and common-stage
  operations in its dependency node by ordinary constant-ring categories.
  The node is an existing DAG node (not a new definition node), and the
  supplied module stated only a different, much weaker interface. I removed
  both its delivered node copy and its module. This item needs only the
  finite inverse image, which already exists as the exact fixed-scalar site
  pullback and is now canonically transported; no new definition node or
  module for the broad operation node is needed. The broad dependency node is not re-recorded
  as though all its finite/integral/rational/closed clauses were implemented.
- H3: alpha and the open adjunctions were arbitrary supplied data, despite
  the node specifying the canonical site comparison and open adjunctions.
  I constructed them from the existing operations and equivalence instead.
- H3: the first theorem requested a separate `Finite A` instance despite
  the recorded theorem giving it. Positive levels are now n+1 and a named
  instance applies that theorem. Redundant assumptions on the base change
  have also been removed.
- H4/H9: the private mate wrappers duplicated Mathlib `mateEquiv` and its
  inverse and forced all four generic categories into the same object/Hom
  universe. I removed them and use Mathlib directly at its full universes.
- H8: all remaining helpers now have source/blueprint docstrings. The theorem
  docstring spells out all four DAG proof steps, including unit/counit
  compatibility, the canonical alpha, mate pasting, and the explicit
  inverse-of-a-composite argument. Its proof remains exactly `sorry`.

Edge cases: the theorem has no index family or nonempty assumption. Empty
schemes and zero complexes are included by the existing sheaf categories and
functors. Positive level 1 is `n=0` in the final signature; level zero is
outside the node's scope. Identity and arbitrary base-change morphisms are
both included. No characteristic assumption beyond ell being invertible on
X,Y occurs; it pulls back to all other schemes as needed. The scheme universe
is arbitrary u; the original small site's objects remain in u+1 and its
morphisms in u. The coefficient values use the recorded `ULift.{u+1,u}` and
ModuleCat in u+1, without identifying the two site universes. All functor
transports are between these existing categories and use the same chosen
unbounded localization. Every variable and universe is explicitly bound.

Independent searches (recorded by msearch.py in searches.jsonl):

- LeanFinder: "exceptional inverse image base change follows from proper part
  and open immersion adjunction mates": eight hits, concerning ordinary
  scheme-module restriction/pullback and open immersions, no matching theorem.
- Loogle: `CategoryTheory.mateEquiv`: found the exact mate bijection and
  `mateEquiv_hcomp`, `mateEquiv_vcomp`, and conjugation laws; I opened Mates.lean
  and use the bijection directly rather than defining it again.
- grep: `mateEquiv_hcomp|rightAdjointUniq` in Mathlib/CategoryTheory/Adjunction:
  found the pasting and canonical adjoint-uniqueness tools. I opened Unique.lean,
  including its unit and counit normalization statements.
- LeanSearch: "mates of natural transformations commute with pasting
  adjunctions": the service returned Internal Server Error (unavailable).
- Independent rg over Mathlib, upstream WeilConjectures, project lean/Sheaf,
  and dag/lean_names_upstream.json, using exceptional/base-change/proper,
  rightDerivedUpperShriek, the item id, and final declaration names: no exact
  exceptional base-change reduction theorem. The nearby
  SmoothExceptionalBaseChange.lean is etale, smooth, and uses different
  exceptional adjoints; I opened it and it is not this statement.
- Read the precise existing finite-coefficient UpperLowerStar/Iso and
  LowerShriek/Open/Defs declarations, the canonical intrinsic realization,
  ProEtaleDerivedCategory, AmbientExceptionalRightAdjoint, the coefficient
  finiteness theorem, ProEtaleOperations and its normalized adjunction module,
  and ProEtaleDerivedPullbackComposition. These supply the actual finite
  operations; none justifies the withdrawn arbitrary-operation structure.

No new nodes remain in the delivery. The open adjunction and its coefficient
transport helpers now belong to the repaired `prop-exc-open-adjoint` dependency
module described below; the square comparison and coefficient-level helpers
belong to the item. All are listed in their owning lean.declarations and contain
real categorical data. No additional theorem or untracked sorry
was introduced. The natural-language node statement and proof are unchanged.


## Dependency modules

`prop-exc-open-adjoint` is repaired under §1(B) in
`Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction`. The first clean
standalone compile used our constructed exact adjunction, but adding the
recorded proof-dependency module exposed an old/new module-path collision:
`WeilConjectures.SixFunctors.ProEtale.Derived.OpenImmersionLowerShriek`
imports `ProEtale.UpperLowerStar.Defs`, while the landed intrinsic extension
by zero imports `ProEtale.FiniteCoefficient.UpperLowerStar.Defs`. Lean
reported an existing `AlgebraicGeometry.ProEtale` notation declaration from
the other path. The imported upstream derived-adjunction API also requires
monoidal/K-flat structures on an intrinsic category despite both functors
being exact. I did not add such assumptions or alter upstream sources.

The dependency module states precisely the dependency node's adjunction:
for every finite commutative A and open j:U->V,
`derivedOpenExtension j A ⊣ exceptionalDerivedPullback j A`
on the full ordinary unbounded `proEtaleDerivedCategory` categories. It
contains only actual definitions/instances, with no new postponed theorem.
Its left functor is exactly the existing
`sfIntrinsicExtensionByZero j A |>.mapDerivedCategory`. Its right functor
is the canonical site inverse image transported through the already recorded
intrinsic module equivalences and descended termwise. `exceptionalOpenAdjunction`
composes the canonical equivalence adjunctions and the existing underived
open adjunction, applies `mapHomologicalComplex`, and applies Mathlib
`Adjunction.localization` with the existing `mapDerivedCategoryFactors`.
This fixes its units and counits, rather than merely giving an arbitrary
adjunction witness. It covers empty opens, zero complexes, and every finite
ring, including the zero ring; it adds no boundedness, constructibility,
finite-Tor or characteristic condition. I checked each clause of the
unchanged dependency node against this signature and these constructions:
all clauses match. The dependency node changes only in lean, with lean.note
recording the unusable old import/interface. Its source/blueprint docstrings
use `prop-exc-open-adjoint`; the item imports this module publicly and the
composition proof dependency non-publicly.

Validation: both delivered modules were compiled separately in dependency order
using scompile.py with the required 60-second limits. The only intermediate
warning was a doubled final newline in the theorem docstring; it was removed
before the final delivery checks. No natural-language node field changed.

## Second reading by Q01

This is a fresh independent reading of the current two-module delivery. I opened
both sandbox node records and both complete Lean files, the reviewed shared DAG
node and its dependencies, and the blueprint source files in the launcher's
literature mirror. The item's source is blueprint Markdown, not a Stacks lemma.
The reviewed DAG already makes the ambient adjunction claim conditional; its
stage-1 review explicitly records why the source's unconditional final sentence
was not retained. This delivery changes no natural-language statement and has
no statement_change. I checked the Lean against that reviewed conditional node.

Object, hypothesis, and conclusion checklist:

1. Prime ell: `(l : ℕ) [Fact l.Prime]`. Finite extension E/Q_ell:
   `(E : Type u) [Field E] [Algebra (Padic l) E]` and
   `[FiniteDimensional (Padic l) E]`. These are the specified field and extension,
   with no additional topology or characteristic assumption. PASS.
2. Positive level and coefficient ring: `(n : ℕ)` and
   `exceptionalCoefficientRing l E n = Padic.coefficientExtensionRing l E (n+1)`.
   I read CoefficientExtension and CoefficientExtensionFinite: the ring is the
   integers of the spectral extension absolute value modulo the power of the
   principal uniformizer ideal. Changing uniformizer does not change that ideal.
   Every positive level occurs, and `exceptionalCoefficientRing_finite` uses the
   recorded finiteness theorem, rather than assuming finiteness separately. PASS.
3. Schemes X,Y and separated finite-type f with ell invertible: the explicit
   scheme binders and `f : X ⟶ Y`, `[IsSeparated f]`,
   `[LocallyOfFiniteType f]`, `[QuasiCompact f]`, `_hX`, `_hY` give exactly
   these hypotheses. Finite type is locally finite type plus quasi-compactness;
   invertibility is tested in all local rings. No Noetherian assumption. PASS.
4. Chosen compactification: `c : Compactification f`. I read upstream Defs and
   Refinement, including `Z`, `i`, `g`, `comm`, and the open/proper instances.
   Thus j_0 is c.i, p is c.g, and f = j_0 followed by p. The open immersion is
   automatically quasi-compact because f is; no density condition is added. PASS.
5. Arbitrary base change and its compactification: `g : Y' ⟶ Y`, `X'`, `g'`,
   `f'`, `c'`, `overlineG`, and `hsq`, `hbar`, `hopen : IsPullback ...` specify
   the total, proper, and open Cartesian squares. I checked the IsPullback
   convention against the displayed arrows: in particular hopen.w is
   g' followed by c.i = c'.i followed by overlineG. The compactification equation
   gives f' = j_0' followed by p'. No property of g is imposed. PASS.
6. Full ordinary derived categories and their specified operations:
   `proEtaleDerivedCategory`, `proEtaleConstantDerivedDirectImage`,
   `derivedOpenExtension`, and `exceptionalDerivedPullback` have precisely the
   finite constant-ring module categories of the node. I read their definitions:
   unbounded localization, sectionwise canonical direct image derived with
   K-injectives, and exact termwise extension by zero and inverse image.
   The latter is transported through sfIntrinsicModuleEquivalence; its functor
   is the existing fixed-scalar realization and its inverse is determined by
   that equivalence. There is no freely supplied replacement operation. PASS.
7. Ambient exceptional data: `ambient` and `ambient'` are the recorded
   `SfAmbientExceptionalRightAdjointDatum` at f,c and f',c'. I read every field:
   the datum supplies full cohomological dimension for the chosen proper part,
   right adjoints at all compactifications, their adjunctions, and coherent
   refinement comparisons preserving units and counits. Its left functor
   sfAmbientCompactSupportCandidate is exactly j_! followed by Rp_*.
   Using the structure directly over Y and Y' asserts no existence theorem
   and adds no separate restrictions on the arbitrary morphism g. PASS.
8. Specified proper adjunctions and comparisons: `Q`, `Q'`, `adjP`, `adjP'`,
   `deltaP`, `betaP`, and `hbetaP` encode Rp_* ⊣ Q and Rp'_* ⊣ Q',
   delta_p : Rp'_* Lgbar^* -> Lg^* Rp_*, and
   beta_p : Lgbar^* Q -> Q' Lg^*. I read Mathlib mateEquiv and its inverse:
   hbetaP is exactly the mate equality for these adjunctions. There is no
   assumption that deltaP is invertible. PASS.
9. Canonical alpha and gamma: `exceptionalDerivedOpenSquare` cancels the
   intermediate realization equivalence using its unit inverse, applies
   ProEtale.upperStarCompIso to hopen.w, and descends this isomorphism through
   the exact derived functors. I opened that upstream construction: it is
   inverse composition, congruence, composition, in the order in the node.
   Applying `(mateEquiv ... ...).symm` with the constructed open adjunctions
   therefore gives exactly the specified gamma, not an arbitrary square. PASS.
10. Pasted delta_f and its ambient mate: `Functor.whiskerRight` applies Rp'_*
    to gamma; `Functor.whiskerLeft (derivedOpenExtension c.i ...) deltaP`
    applies deltaP after j_!. Their composite is the node's delta_f.
    The outer mateEquiv uses ambient.adjunction c and ambient'.adjunction c'.
    `IsIso betaP → IsIso (...)` is precisely the sole conclusion, with the
    same supplied adjunctions and quantified maps. No extra comparison clause
    or existence conclusion is asserted. PASS.

Dependency-module reading (H13): prop-exc-open-adjoint is the only dependency
node re-recorded. I read its blueprint source, the old upstream derived open
adjunction signature/imports, and the replacement IntrinsicDerivedOpenAdjunction.
The old path uses the legacy UpperLowerStar modules, while intrinsic extension
by zero imports the FiniteCoefficient paths; the prior returned delivery records
the resulting declaration collision. The replacement uses the exact existing
finite-coefficient open site adjunction, composes the two canonical equivalence
adjunctions, applies Adjunction.mapHomologicalComplex, and localizes at
quasi-isomorphisms with the specified derived-factor isomorphisms. I opened these
APIs, including the localization unit and counit formulas. Thus it supplies the
same canonical open adjunction on the full ordinary categories for every finite
commutative ring, without a monoidal, constructibility or finite-Tor hypothesis.
Its definitions contain actual categorical data; it introduces no postponed
proof. The repair is justified by its lean.note. There are no new nodes to audit.

Edge cases: empty schemes and the empty open immersion are allowed; zero
complexes and the zero ring in the open-adjunction dependency are included.
There is no index family or nonemptiness assumption. n=0 represents coefficient
level 1; coefficient level zero is outside the item's scope. Identity and arbitrary
base-change maps are covered. Ell-invertibility on X',Y' follows by pullback.
Scheme universe u is arbitrary; the site still has object universe u+1 and
morphism universe u, and coefficient modules use the recorded ULift into u+1.
No equality of these two site universes is imposed. All variables/universes are
bound explicitly with autoImplicit false.

Independent searches in this reading, recorded in searches.jsonl:

- LeanFinder: "exceptional inverse image isomorphism obtained by pasting
  adjunction mates for open immersion and proper direct image" returned eight
  unrelated scheme-module restriction/open-immersion results, no exact theorem.
- Loogle: CategoryTheory.mateEquiv returned the actual mate bijection, its
  unit/counit laws, horizontal/vertical pasting and conjugation lemmas. I opened
  Mates.lean and Unique.lean; they supply tools, not this geometric statement.
- msearch grep: exceptionalBaseChangeReducesToProper, mateEquiv_hcomp and
  rightAdjointUniq found the Mathlib categorical tools, no existing item theorem.
- Independent rg across Mathlib, upstream WeilConjectures and lean/Sheaf used
  exceptional/base-change in both orders and the helper names. The nearby
  SmoothExceptionalBaseChange is etale and smooth and uses different adjoints;
  I opened its comparison declaration and it is not the present theorem.
- I read the finite-coefficient site operations in the shared 51-module framework
  and fetched the current ProEtaleDerivedPullbackComposition with
  scompile.py --source. For the cited Stacks background I read Tags 03DI/03DJ
  in sites-modules.tex, 09AE in proetale.tex, and 0D6D in sites-cohomology.tex:
  these add no missing finiteness or boundedness hypotheses to this finite case.

Findings and changes in this reading: no further mathematical, signature, or
construction mismatch was found. I preserved both Lean files and both node
records and appended this fresh review. The prior return's import repair is
present: the dependency imports the finite-coefficient open API and general
complex adjunction; the consumer directly imports the derived-composition API.
Both lean.statement strings were mechanically compared to normalized signatures
and are verbatim identical. Both files have lines at most 100 characters.
The only direct sorry is the named item theorem, whose docstring gives all four
DAG proof steps, including preservation of units/counits and the explicit pasted
mate equation. No data definition is hollow and no theorem was proved here.

Validation in this reading: scompile.py compiled both delivered files separately
in dependency order, including sandbox and final module checks. All five checks
finished within 60 seconds each (maximum 32.1 seconds), without errors or warnings.


## Maintainer landing repair (2026-10-16)

Independent immutable review found H4 overlap with the recorded operations dependency.
`ProEtaleIntrinsicFiniteOperations` already defines exactly the transported module
pullback and its exact termwise derived pullback. The complete replacement modules
reuse `sfIntrinsicPullback A f` and `sfIntrinsicDerivedPullback A f` directly, and
remove the redundant additive instance. The open adjunction still composes the same
site adjunction with the same equivalence adjunctions and localizes termwise. The
square comparison and the final mate use precisely the same functors and maps.
Both lean records have updated verbatim signatures and declaration lists. No node
statement or mathematical hypothesis/conclusion changed. The remaining helpers
construct the positive coefficient level and the square comparison, rather than
new operations. See the independent review.md for replacement compilation evidence.

The independent search also found `ProEtaleOpenSquareExchange` helpers for the
underived intrinsic open adjunction, derived open extension, and square pullback
comparison. The final replacements import that module and use these helpers
directly (`sfIntrinsicOpenAdjunction`, `sfIntrinsicDerivedOpen`, and
`sfIntrinsicDerivedSquarePullback`), removing the duplicate cancellation/square
and extension abbreviations. Only the derived adjunction localization is new in
the dependency module. No theorem from the exchange module is used as a premise.

Final maintainer replacement validation: both complete replacement modules passed
`scompile.py Q01 cor-exc-base-change-reduces-to-proper` together, separately in
dependency order, with exit 0 and no diagnostics. Library-path checks took 6.8
and 6.6 seconds. The unchanged wrapper used its standard 60-second invocation
limits. Its five reported wall intervals were 43.9, 17.0, 6.8, 72.6 and 6.6
seconds (wall intervals can include wrapper/slot overhead). Merge-tool
`refit_record` and `check_lean_text` accept the final modules and records.
