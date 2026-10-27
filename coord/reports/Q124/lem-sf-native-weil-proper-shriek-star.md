## Worker report

Existing declaration, with no new Lean module:
`AlgebraicGeometry.WeilComplex.derivedLowerShriekIsoDerivedLowerStar` in
`WeilConjectures.WeilSheaf.LowerShriekFunctoriality`, source lines 109–144.
The node itself names this exact declaration as its Lean candidate. I read its
section variables, declaration, docstring and construction, including the
object-level comparison at lines 72–105. The delivery changes only `lean`.
No new nodes, dependency repairs, statement corrections or proofs are supplied.

The signature recorded in `lean.statement` is copied verbatim from the existing
source (including `noncomputable def`); its inherited binders are described below.
This is a data-valued natural isomorphism already constructed upstream, not a
new definition with postponed data.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Finite field k₀: the shared variable declaration at line 56 is
  `{k₀ : Type u} [Field k₀] [Finite k₀]`.
- Prime ℓ different from the characteristic: the same line supplies
  `{l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]`.
- Ω = algebraic closure of the ℓ-adic numbers: the coefficient is the framework's
  `PadicAlgCl l`, used by `ProEtale.AdicSheaf` and therefore by `WeilComplex`.
  Ω is not an additional freely chosen ring or coefficient package.
- V and W are k₀-schemes: lines 64–65 bind `{X Y : Scheme.{u}}`,
  `[X.Over (Spec (CommRingCat.of k₀))]` and
  `[Y.Over (Spec (CommRingCat.of k₀))]`. The dictionary is V = X, W = Y.
- The k₀-morphism h: lines 65–66 bind `(f : X ⟶ Y)` and
  `[f.IsOver (Spec (CommRingCat.of k₀))]`; h = f.
- Properness: line 66 has `[IsProper f]`. In Mathlib this extends separated,
  universally closed and locally finite type, and universally closed supplies
  quasi-compactness, giving exactly the node's properness definition.
- W locally of finite type: line 66 has
  `[LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]`.
- W quasi-compact and quasi-separated: lines 67–68 have
  `[QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]` and
  `[QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]`.
  Over a field these express the scheme properties in the node; separatedness
  of Y over k₀ is not assumed. There is no independent restriction on X.
- The requested functors are literally `derivedLowerShriek k₀ l f` and
  `derivedLowerStar f` of the recorded native framework. The declaration's
  conclusion is their `≅` in the functor category, thus includes an invertible
  natural transformation, its inverse and naturality for all morphisms. It is
  not merely a family of object isomorphisms or cohomology comparisons.
- The source and target are exactly `WeilComplex k₀ l X` and
  `WeilComplex k₀ l Y`. The former is the full subcategory cut out by
  `WeilComplex.objectProperty`, the intersection of boundedness with the
  cohomology property induced by `WeilSheaf.objectProperty`. The ambient
  category is `DerivedCategory (ProEtaleWeilSheaf k₀ l X)`, and
  `ProEtaleWeilSheaf` is `IsoAlgebra (WeilSheaf.frobeniusPullback k₀ l X)`.
  This retains Frobenius structures at the sheaf level before derivation.

Dependency declarations read and used to interpret this exact match:

- `def-sf-native-weil-derived-framework`: its recorded entry module is
  `WeilConjectures.WeilSheaf.LowerShriek` and primary declaration is
  `AlgebraicGeometry.WeilComplex.derivedLowerShriek` (lines 146–160).
  Its actual data is `liftFullSubcategory` of
  `ProEtaleWeilSheaf.rightDerivedLowerShriek` for the Nagata compactification
  `HasCompactification.compactification`. The ambient functor is degreewise
  `ProEtaleWeilSheaf.extensionByZero` followed by the total right derived
  functor of `ProEtaleWeilSheaf.lowerStar`. I also read the recorded declarations
  in `WeilConjectures.WeilSheaf.Category`, `.LowerStar`, `.OpenImmersion`, and
  `WeilConjectures.SixFunctors.ProEtale.Adic.Module`, `.ConstantSheaf`, and
  `.Constructible`: `WeilComplex`, `WeilComplex.objectProperty`,
  `ProEtaleWeilSheaf`, `WeilSheaf.frobeniusPullback`,
  `WeilSheaf.objectProperty`, `ProEtale.AdicSheaf`,
  `ProEtale.adicConstantSheaf`, `PadicAlgCl.locallyFiniteFunctions`,
  `ProEtale.IsAdicLisseSheaf`, `ProEtale.IsAdicStratifiedLisseSheaf`,
  `ProEtale.IsAdicConstructibleSheaf`, `ProEtaleWeilSheaf.upperStar`,
  `ProEtaleWeilSheaf.lowerStar`, `ProEtaleWeilSheaf.extensionByZero`,
  `ProEtaleWeilSheaf.rightDerivedLowerShriek`, `WeilComplex.upperStar`,
  and `WeilComplex.derivedLowerStar` (all in namespace `AlgebraicGeometry`
  except the recorded `PadicAlgCl` declaration). Locally finite functions use
  the whole underlying space; lisse rank is existential inside the covering
  member quantifier, as in the dependency's current text.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper`, module
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`, class at line 42.
- `def-weil-quasi-separated-morphism`: `AlgebraicGeometry.QuasiSeparated`,
  module `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`, class at line 50;
  its field is quasi-compactness of the diagonal.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  module `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, class at line 43;
  and `AlgebraicGeometry.QuasiCompact` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, class at line 43.
  Finite type means these two conditions together, with quasi-compactness
  already supplied by properness here.

The construction in the source makes the open factor of the chosen
compactification proper and therefore clopen. It compares extension by zero
with direct image, derives the comparison and composes direct images, then
uses the fully faithful inclusion of the full Weil-complex subcategory to lift
the ambient natural isomorphism. I checked that the last step constructs a
functor isomorphism, not only the preceding object comparison. The absence of
local `sorry` in this particular construction is not a transitive axiom audit;
closure of its dependencies remains for the maintainer.

Edge cases checked by reading the statement and construction: empty source,
empty target (then the source is empty), identity morphisms, clopen component
immersions, and the zero complex are not excluded. Properness supplies the
finite-type and separated hypotheses required by compact support and the
quasi-separated hypothesis required by direct image. No smoothness, dimension,
connectedness, nonemptiness or separatedness of W is added. The non-quasi-compact
target counterexamples to boundedness are excluded by the node's own explicit
quasi-compactness hypothesis. The prime equal to the characteristic is excluded
exactly as in the node. The source declares universe u explicitly and imposes
no additional site/coefficient universe equality beyond the recorded framework.

Searches actually run through `/home/ubuntu/weil-launcher-all/batch2/msearch.py`:

- LeanFinder: `For a proper morphism of schemes the derived direct image with
  compact support of Weil sheaves is naturally isomorphic to the derived direct
  image`, and `proper pushforward agrees with derived direct image with compact
  support for Weil sheaves`. The latter returned eight generic sheaf-pushforward
  hits (including `SheafOfModules.pushforwardNatIso`), none the native comparison.
- Loogle: `"LowerShriek"`, returned `OK 0 hit(s)`.
- Mathlib grep: `proper.*shriek|shriek.*proper|derivedLowerShriekIsoDerivedLowerStar`
  and `derivedLowerShriekIsoDerivedLowerStar`, returned `OK 0 hit(s)`.
- Direct `rg -n` in the read-only project's `lean/WeilConjectures` and
  `lean/Sheaf` for `derivedLowerShriekIsoDerivedLowerStar` found the exact
  declaration at `WeilConjectures/WeilSheaf/LowerShriekFunctoriality.lean:109`.
  Other matches include its consumers in `VerdierDualLocalization.lean` and
  the weaker existence wrapper in `LowerShriekPackage.lean`. The direct
  data-valued natural isomorphism is the closest exact match.
- Direct `grep -rn` for this node id in `lean/WeilConjectures` found no occurrence;
  its existing docstring instead cites `prop-functor-package`, clause 3.
- `rg` of `dag/lean_names_upstream.json` for the exact name found no occurrence;
  that older index does not override the declaration read in the actual source.

No statement dispute or node fault found. Because this delivery attaches an
existing declaration, the brief's existing-match rule requires no new module;
there is no delivered Lean file to compile. The prescribed delivery dry run
checks the attachment on the current server base.

## Second reading by Q124

I made a second reading of the node and source after preparing the attachment.
This is a second pass by the same dispatcher worker, not a claimed independent
agent review; the dispatcher explicitly prohibits starting other agents. The
maintainer's independent delivery review is still required.

I compared the entire binder context at lines 56 and 64–68 to the node: finite
field, prime, unequal characteristic, two schemes over that field, over-base
morphism, properness, and all three target conditions agree. In particular there
is no assumption that Y is separated over the field and no additional assumption
on the source. I compared the conclusion at lines 109–110 to the node: it is
`derivedLowerShriek k₀ l f ≅ derivedLowerStar f` between the native restricted
functors, so the inverse and all naturality identities are included. Reading
the definitions confirms both functors act on the full bounded constructible
subcategory of the derived fixed-pair sheaf category stipulated in the node.
The pointwise declaration at line 72 alone would not suffice; the attachment
uses the functor declaration at line 109. No mismatch was found and no statement
or dependency field was changed.
