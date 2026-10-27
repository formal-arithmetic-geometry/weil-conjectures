## Worker report

The module `Sheaf.SixFunctors.AmbientUnderivedClopenPasting` states
`AlgebraicGeometry.ProEtale.AmbientClopen.UnderivedPasting.ambientUnderivedClopenPasting`.
Its only theorem has proof `sorry`. The accompanying transparent predicates expand every
clause; identity isomorphisms are constructed by the specified adjoint-uniqueness maps.
The H2 return is repaired by a new existing:true definition owner for the published
ordinary clopen constructions; see the repair and new-node sections below. No
mathematical statement correction or dependency Lean module is needed.

Hypothesis and clause correspondence:

- `F : FiniteFieldDatum.{u}` fixes the prime-power finite field and its fixed algebraic
  closure `F.k`. `[Fact l.Prime]` and `_hl : l ≠ F.p` express the coefficient prime and
  its distinction from the characteristic. `E : Type u`, `[Field E]`,
  `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` express the finite extension.
  `scalarRings l E n` is the existing common lift of the quotient at positive level
  `n+1`; `scalarTransitions` is the actual adjacent quotient homomorphism. Thus `n : ℕ`
  covers exactly every level ≥1, with no missing first level or zero-level case added.
- In all six predicates, each scheme has its own `Over (Spec (.of F.k))`,
  `LocallyOfFiniteType` and `QuasiCompact` structure morphism. Together these are finite
  type over k. Every named arrow has `IsOver` for that base. No separatedness of a
  structure morphism is assumed, and the schemes need not descend to the finite field.
- Ordinary objects are the actual `Sheaf (Scheme.ProEt.topology T) (ModuleCat Λ)`.
  System objects are `VaryingRing.Modules C τ T`, modules on the vertical ringed
  sequence site, carrying exactly the compatible semilinear transitions. The functors
  are the actual `upperStar`/`openImmersionLowerShriek` and `VaryingRing.pull`/`extension`.
  The inherited ordinary derived categories and specified derived adjunctions remain
  available through the imported dependencies; the conclusions here are before deriving.
- The intrinsic arrows are `AmbientClopen.alpha` and `VaryingRing.moduleAlpha`.
  Their source definitions were read: beta for the fibre product, the clopen projector
  of `squareLift`, open composition, and pullback composition, in that order. They
  use `pullback.fst`, `pullback.snd`, and `pullback.lift`; no arbitrary comparison map
  or replacement coefficient category appears here.
- `Ordinary.Vertical` and `Systems.Vertical` bind the three quasi-compact open rows
  and four proper verticals exactly as in the node. `h₁` and `h₂` are the two square
  equalities. `h` is the resulting outer equality, a propositionally determined proof,
  not an additional geometric restriction (associativity and h₁,h₂ imply it).
  Their first conjunct is equality of natural transformations: whisker alpha₂ on
  the right by p₁*, then whisker alpha₁ on the left by r₂*. The other side is the
  intrinsic outer alpha transported by the inverse p-compositor and forward
  r-compositor. The associators only parenthesize these exact source/target functors.
- Each Vertical predicate's second conjunct is the restriction of p₁*alpha₂ along
  j₀: starting at r₁*r₂*M, insert the j₂ unit and the two square pullback comparisons;
  restriction of the factor equals insertion of the j₁ unit and first-square
  comparison. The third conjunct applies the restricted alpha₁ at r₂*M and obtains
  the j₀ unit. These explicit endpoint identifications are precisely identity on
  r₁*r₂*M; no faithfulness of restriction is assumed as a hypothesis.
- `Ordinary.Horizontal` and `Systems.Horizontal` bind k₁,k₂,i₁,i₂ as quasi-compact
  opens, r,p,q as proper, and both square commutativities. The resulting outer
  commutativity `h` again only supplies a proof of an already implied equality.
  The first conjunct is equality of natural transformations with source
  `(i₁! ⋙ i₂!) ⋙ q*` and target `(r* ⋙ k₁!) ⋙ k₂!`: the two factors on one side,
  the intrinsic outer alpha conjugated by both canonical open compositors on the other.
- Each Horizontal predicate's second conjunct restricts alpha₂ at i₁!M first by k₂*
  and then by k₁*, with the i₂ unit and both square identifications, giving the
  k₂ unit at p*i₁!M. The third conjunct restricts k₂!alpha₁: naturality of the
  k₂ unit and the first-square restriction give the successive k₁ and k₂ units
  at r*M. These are identity on r*M after the specified identifications. Successive
  restriction is identified with restriction along k₁≫k₂ by the canonical pullback
  compositor; the open compositor is adjunction-normalized, so its unit is exactly
  the composite of these units.
- `Ordinary.Identities` and `Systems.Identities` have two universal clauses. Identity
  verticals give the canonical word from k! followed by identity pullback to identity
  pullback followed by k!, using pullback identity compositors and functor unitors.
  Identity horizontals give the analogous word using `openIdentity` and unitors.
  The comparison uses the actual intrinsic alpha even in these specializations.
- The main theorem conjoins all three predicates for every finite level and all
  three for the actual simultaneous system of positive quotients. No Cartesian,
  boundedness, constructibility, flat-transition, or normalized-system assumptions
  occur. The maps are ordinary natural transformations, so equality is not inferred
  from evaluation on derived morphisms.

Dependency declarations read and used:

- `Sheaf.SixFunctors.AmbientExactClopenComparison`: `AmbientClopen.alpha`,
  `beta`, `projector`, `openComp`, `openCongr`, `Normalized`, `Systems.Normalized`,
  and `ambientExactClopenComparisonLocalizes` (proof normalization). The plain
  constructions are owned in stmt_deps by the new definition node
  `def-sf-ambient-underived-clopen-comparison`; the localization theorem stays
  in proof_deps only. Its `localize` and `localizeSquare` show the derived backdrop;
  no new localization is constructed here.
- `Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows`: `VaryingRing.moduleAlpha`,
  `moduleSquareG`, and their defining beta/projector words. Added the existing
  definition owner `def-sp-varying-ring-proper-open-arrows` to stmt_deps.
- `Sheaf.AlgebraicGeometry.VaryingRingOperations`: `Modules`, `pull`, `extension`,
  `moduleAdj`, `moduleJAdj`, `moduleGComp`, `moduleJComp`, `modulePId`.
  Added its existing owner `def-sp-varying-ring-operations` to stmt_deps.
- `Sheaf.SixFunctors.IntegralSystemCanonicalBridge`: `scalarRings`, `scalarTransitions`;
  `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`. Added those
  existing definition owners to stmt_deps. These are existing constructions with existing definition owners.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and the imported actual coefficient data.
  The published `AmbientClopen.finiteScalarRing` supplies the lifted finite instance.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules` is the
  general ringed-site presentation, retained by dependency import; ordinary finite
  coefficients use the existing ModuleCat-valued presentation of this family.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; ordinary unbounded backdrop, no completed replacement.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `Scheme.proEtaleConstantRingDerivedPullback` and the arbitrary-ring operations,
  read as the recorded dependency; the underived finite presentation used here is
  already the presentation of the recorded alpha owner.
- `Sheaf.Paper.SemilinearDerivedSections`:
  `WeilConjectures.SemilinearSections.SemilinearDerivedSectionsData`,
  `semilinearDerivedSections`, and its simultaneous ringed-site operations.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`; the existing semilinear system category implements
  those scalar-restricted transition maps.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`:
  `SheafOfModules.localizedSystemExact`, `localizedSystemAdjunction`; the real
  direct-sum/sheafification extension and restriction are retained by imports.
- `Sheaf.SixFunctors.OpenTensorNormalization`: `SheafOfModules.openTensorNormalization`;
  it fixes the canonical open-unit comparison used by the alpha owner.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.lift`, already in the alpha construction.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.comp`, `Adjunction.id`;
  their unit/counit formulas were read; `Adjunction.leftAdjointIdIso` constructs the
  identity compositors. `ProEtale.upperStarId` is used for ordinary inverse images.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: proper-composition instance, imported
  for the proof plan. The clopen uniqueness and pullback/tensor coherence proof nodes
  currently have no Lean binding, so there is no module for those proof-only imports.
  No missing notion is needed to state this item: all maps and normalization data
  already have published owners.

Edge cases checked before drafting: empty U or W, zero sheaves/systems, Cartesian
squares (clopen lift an isomorphism), non-Cartesian squares with an extra clopen
component, both identity orientations, lowest positive quotient A₁, arbitrary
unbounded inputs in the inherited derived backdrop, and non-flat coefficient
transitions. The ordinary equations use the unique zero-object maps for empty opens;
no Nonempty or surjectivity condition excludes them. Scheme/site and coefficient
universes follow the published u / u+1 convention without identifying site object
and morphism universes.

Searches (2026-10-23):

- msearch.py leanfinder: "Underived clopen proper open comparison natural
  transformations satisfy horizontal and vertical pasting" returned eight general
  condensed-set naturality/site-composition results, none this geometric statement.
- msearch.py loogle: "CategoryTheory.mateEquiv_vcomp, SheafOfModules.pullbackComp"
  returned zero hits.
- msearch.py grep: `clopen.*(pasting|compose)|properOpen.*pasting` returned zero hits.
- rg in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  underived/clopen pasting and proper-open names: no exact declaration. The exact
  item id has no upstream Lean occurrence.
- Read `Sheaf.AlgebraicGeometry.ProperOpenAlphaPasting`: covers ordinary constant
  coefficients and constant towers, also derived/complex clauses, but not this
  varying-ring semilinear statement, both factor restrictions, and identity cases.
- Read `Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting.moduleAlpha_vertical`
  and `.moduleAlpha_horizontal`: actual semilinear pasting, but neither includes the
  two factor restrictions and ordinary identity clauses of this complete item.
  Accordingly neither is an exact existing:true binding for the requested node.
- Read Stacks `more-etale.tex` at `lemma-shriek-proper-and-open-compose` and
  `lemma-shriek-proper-and-open-compose-horizontal`: their vertical/horizontal
  rectangles agree with the node's underived mate formulation and orientation.

Validation: scompile.py Q71 lem-sf-ambient-underived-clopen-pasting compiled the
sandbox and library module cleanly (9.9s and 5.4s); no errors or unexpected warnings.

## Second reading by Q71

Author's second pass, as required by this direct-delivery dispatcher; independent
review is left to the maintainer. Reopened the node and complete generated Lean file.
Checked every scheme/base/finite-type binder, prime and coefficient datum, each
of the six assertion predicates, and both actual alpha definitions against the
node. In the vertical equation the functor composition order is opposite to
geometric notation: i! then p*, and r₂* then r₁* then j₀!. In the horizontal equation
the final inverse top-open compositor is necessary to match the two separate
extensions; it is present. Checked that every displayed restriction equation has
common starting object r₁*r₂*M or r*M and its right endpoint is the appropriate
open-unit identification, with no arbitrary identification assumed. Both identity
clauses use canonical adjunction-normalized compositors, not existence of some
isomorphism. The only additional proof binders `h` assert outer commutativity already
forced by the two square equalities. No source hypothesis or conclusion changed.
All variables and universes are explicit (`autoImplicit false`); no local notation,
private declaration, new axiom, or proof other than the sole theorem's `sorry`.

## New nodes

`def-sf-ambient-underived-clopen-comparison` is the definition owner of the already
published `AlgebraicGeometry.ProEtale.AmbientClopen.beta`, `projector`, `openComp`,
`openCongr`, `alpha`, and `finiteScalarRing`, all in
`Sheaf.SixFunctors.AmbientExactClopenComparison`. Its record is `existing: true`:
no new module or duplicate definition is introduced. Its source is the ordinary
clopen/open-adjunction formulation of Stacks Tag 0F7B underlying 0F7C and 0F7D,
with the coefficient lift from the existing canonical bridge. Each hypothesis and
construction is read off the published definitions: finite commutative coefficients
in universe u+1, schemes in u, cartesian beta with two open maps, projector with
open and closed s, openComp with two composable opens, openCongr with equality of
opens, alpha with two quasi-compact opens, two proper verticals and commutativity,
and the finiteScalarRing instance for prime l, a finite extension E/Q_l and every
natural n (the actual quotient index is n+1). The node states these constructions,
not their localization or their pasting properties. Its stmt_deps are precisely
the definition nodes cited in its statement.

The new-node searches are recorded verbatim as the msearch JSON results in
mathlib_searches: LeanSearch returned eight general open-map/clopen results;
LeanFinder returned eight general topological/condensed-category results; Mathlib
grep returned four unrelated algebraic-geometry clopen occurrences. DAG/project
grep found the exact helpers listed under the localization theorem but no definition
node owning them. Blueprint search for "clopen comparison" found zero blueprint
nodes. Accordingly the existing helpers are reused and given the missing definition
owner, exactly as the return requests.

## Returned H2 repair

Return on immutable head `841d56bd590a`: the item had used the localization theorem
as the owner of plain definitions. Added the new existing:true definition node above
and replaced `lem-sf-ambient-exact-clopen-comparison-localization` in the item's
stmt_deps with that definition node. The theorem remains in proof_deps, and the
module import still supplies both the definitions and the proof dependency.
The delivered Lean module and main mathematical statement are unchanged. The
initial saved-packet dry run passed (aaaeb4e82f9); that mechanical pass did not
resolve the independent review's ownership fault, which this metadata repair fixes.

Second reading of the repair by Q71: reopened the six complete published signatures
and bodies and checked them against the new definition statement. beta is the
inverse of the conjugate baseChangeMap isomorphism; projector is the direct-image
unit followed by the inverted open-to-direct-image map; openComp/openCongr are
fixed by adjoint uniqueness; alpha is exactly their beta/projector/compositor word.
finiteScalarRing uses actual positive-quotient finiteness and the existing lift.
None is a choice from the localization theorem. The new node's principal signature
is copied verbatim from def alpha up to :=; lean.declarations names all six.
The item's proof_deps, original statement, proof and Lean file are untouched.
Empty opens, zero coefficients, identity maps and the first positive quotient
remain included. No new theorem, axiom or sorry is introduced.

Repair validation: scompile.py compiled the unchanged item as sandbox and library
modules cleanly (9.9s and 5.4s), with no errors or unexpected warnings.
