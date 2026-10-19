## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison` states
`AlgebraicGeometry.ProEtale.openImmersionLowerShriekComparison_coherence`, with
one postponed proof, and constructs the canonical pro-etale extension composition
isomorphism `proEtaleOpenExtensionComp` with real data. Nothing is proved here.
The already existing `openImmersionLowerShriekComparisonUpperStarIso` supplies
the canonical comparison and its naturality; it does not state the composition
or identity equations, so an existing-only attachment would omit a clause.

Sources read: the full blueprint node at
`sec-smooth-purity/sk-prop-sf-cbc/lem-cbc-proetale-extension-zero-comparison.md`,
its DAG statement and all eight expanded proof steps; Stacks `proetale.tex`,
Tag 09AF (`lemma-jshriek-comparison`, lines 5075–5090), and the surrounding
extension-by-zero discussion. The source identifies right adjoints by actual
restriction, then identifies left adjoints by their adjunctions.

Hypothesis and clause matching:

- A scheme and the comparison morphism: all schemes are `Scheme.{u}`, and
  `comparisonUpperStar (ModuleCat.{u + 1} Λ) X` is the inverse image of the
  recorded `Scheme.proEtaleSiteComparisonModules X Λ` adjunction. Its right
  adjoint is restriction along `Scheme.toProEt X`.
- An arbitrary open immersion: `j : U ⟶ X` with `[IsOpenImmersion j]`;
  the second clause uses arbitrary `k : V ⟶ U` and `j : U ⟶ X` with both
  open-immersion instances. No quasi-compactness or constructibility is assumed.
- A finite commutative ring: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  This is the larger coefficient universe used by the recorded etale extension
  and site comparison, with no equality imposed on site object/morphism universes.
- Every module sheaf: `F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)`
  (or on `V` for composition). This is the same fixed-coefficient encoding as
  the recorded etale extension and comparison; sectionwise Λ-actions extend
  uniquely to actions of the sheafification of the constant ring presheaf.
- The displayed arrow in the displayed direction is
  `(openImmersionLowerShriekComparisonUpperStarIso (ModuleCat Λ) j).hom.app F`.
  The upstream definition is the inverse adjunction conjugate of the
  identity-on-sections right-adjoint identification, exactly α in steps 4–5.
- Isomorphism for every F is the first universal conjunct `IsIso (...)`.
- Naturality in F is part of the existing **natural** isomorphism: both its hom
  and inverse are natural transformations. This is not an existential choice
  of unrelated component isomorphisms.
- Compatibility with composition is the second conjunct: apply ν_X^* to the
  etale composite-to-iterated extension map, then α_j, then j_! applied to α_k,
  then the pro-etale iterated-to-composite map. The resulting arrow equals
  α_(k ≫ j). This is the equation of node step 8, with Lean's left-to-right `≫`.
- The third conjunct spells out the identity case under the canonical unit
  identifications `Adjunction.leftAdjointIdIso` on each site. It says α_id
  becomes the identity after identifying both identity extensions with F.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `AlgebraicGeometry.Scheme.proEtaleSiteComparisonModules`; its underlying
  functors and canonical adjunction are those in upstream
  `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`, its restriction and
  adjunction; `Comp` supplies `Etale.openImmersionLowerShriekComp`.
- `def-weil-extension-by-zero` is repaired as described below, using upstream
  `ProEtale.openImmersionLowerShriek` and its specified adjunction.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`; its imports provide the
  small `Scheme.ProEt` site and `Scheme.ProEt.topology`. No new site is defined.
- `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `AlgebraicGeometry.IsOpenImmersion` (signature and docstring read).
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, transparently `SheafOfModules`; the
  Mathlib definition and morphisms were read. Fixed-coefficient modules are
  the existing presentation already used by the comparison dependency.
- Upstream `Derived.LowerShriekComparison`:
  `ProEtale.comparisonLowerStarOpenImmersionRestrictionIso` is `Iso.refl _`,
  and `openImmersionLowerShriekComparisonUpperStarIso` is its canonical mate.
  Upstream pro-etale `UpperLowerStar.Coherence` supplies the canonical
  `upperStarComp` used in constructing the composition helper.

The stated proof-dependency modules are imported, including the landed etale
composition coherence, pro-etale localization and extension adjunction. Mathlib
imports for etale composition/cancellation and ringed-site localization are
included as proof imports. The helper belongs to the comparison node's own
step 7; it needs no independent new definition node and contains no sorry.

Edge cases checked before writing: empty schemes and empty open subschemes
are allowed; there is no nonempty scheme assumption. The zero finite ring is
allowed, and no nontriviality assumption is made. Arbitrary module sheaves,
including zero sheaves and those without constructible support, are quantified.
Identity immersions are explicitly covered by the third equation. All schemes
use the site's size convention, and coefficients inhabit the common larger
universe; no geometric-stalk conservativity is asserted. There is no statement
correction and no disputed mathematical assertion.

Searches actually run:

- msearch LeanFinder: `pullback from etale to proetale commutes with extension
  by zero along open immersion`; 8 unrelated hits on open-immersion pullbacks
  and scheme module pullback composition, no full comparison/coherence match.
- msearch Loogle: `"lowerShriek", "comparison"`; 0 hits.
- msearch grep: `shriek|extensionByZero|extension_by_zero`; 0 Mathlib hits.
- msearch LeanSearch: `extension by zero commutes with comparison of etale and
  proetale sites`; service unavailable (Internal Server Error), not a no-match.
- rg of upstream WeilConjectures for comparison/shriek combinations found
  `ProEtale.openImmersionLowerShriekComparisonUpperStarIso`; its full signature,
  docstring and implementation were read. It gives invertibility/naturality,
  but no equation for composable open immersions.
- rg of upstream for the exact node id and of `dag/lean_names_upstream.json`
  found no node-id attachment. rg of project `lean/Sheaf` found the comparison
  adjunction, localized extension, localization theorem, and etale composition
  coherence, but no etale/pro-etale extension comparison coherence theorem.
- rg of Mathlib and `lean/Sheaf` for `openImmersionLowerShriekComparison` and
  `proEtaleOpenExtensionComp` found no conflicting declarations. Upstream
  `openImmersionLowerShriekComp` search found only the etale definition; its
  pro-etale canonical adjunction counterpart is the helper constructed here.

Validation: `scompile.py NK lem-cbc-proetale-extension-zero-comparison` passed
for the module with no errors or warnings. The required delivery dry run is
performed after these records and this report are complete.

## Dependency modules

`def-weil-extension-by-zero`: lean-only repair to an **existing** upstream
module, `WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs`.
The previous `Scheme.proEtaleExtensionByZero` interface accepts modules over
`A_X.over U` on `X.ProEt/U`. It cannot compose with the recorded site comparison,
whose codomain is module-valued sheaves on the independently formed `U.ProEt`.
The replacement primary record is `ProEtale.openImmersionLowerShriek`,
specialized at use to `ModuleCat.{u + 1} Λ`. This is the same mathematical
construction, not an arbitrary left adjoint: `localizationLowerShriek_eq` shows
it is the actual left Kan extension along localization, followed by
sheafification. For a monic open immersion the indexing category is empty or
has the unique factorization as terminal object, so its value is exactly the
module F(V → U) or zero, with the specified restriction and scalar maps.
`openImmersionLowerShriekAdjunction` is the adjunction of that construction.
The source file's implementation notes (lines 73–88), actual construction
(lines 108–116), presheaf formula (lines 223–245), and open-immersion wrapper
(lines 296–317) were read. Only the node's lean record changes; the definition,
source, statement dependencies and all other fields are untouched. No extra
module is needed because this exact upstream construction already exists.

## Second reading by NK

I independently read the node, its eight proof steps, the blueprint source at
order 1584, Stacks `proetale.tex` Tag 09AF and the preceding Tag 09AE module
clause. Tag 09AF assumes an etale morphism of arbitrary schemes and an arbitrary
abelian sheaf; there is no ambient noetherian, quasi-compact, separated or
nonempty hypothesis. The node specializes this to open immersions and finite
commutative coefficients. The scalar-linear version follows from the same
restriction adjunction, not from a restriction to constructible sheaves.

Object/hypothesis/conclusion checklist (each verdict: matches):

1. Arbitrary schemes X and U: `{U X : Scheme.{u}}`; a third arbitrary scheme V
   is introduced only for the composition clause.
2. The specified site comparison: `comparisonUpperStar (ModuleCat.{u + 1} Λ) X`
   is definitionally the left adjoint in the dependency's
   `Scheme.proEtaleSiteComparisonModules`. I opened that declaration and the
   upstream `comparisonUpperStar`, `comparisonLowerStar`, `comparisonAdjunction`:
   they use left Kan extension/sheafification and restriction along `toProEt`.
3. Open immersion j: `(j : U ⟶ X) [IsOpenImmersion j]`, the recorded Mathlib
   notion. Composition has exactly the corresponding assumptions on k and j.
4. Finite commutative ring: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
   No nontriviality, characteristic, invertibility or field assumption appears.
5. Every module sheaf F on U_et: `F : Sheaf U.smallEtaleTopology
   (ModuleCat.{u + 1} Λ)`. This is the fixed-coefficient presentation used by
   the recorded etale extension and site comparison; it is equivalent to
   modules over the sheafified constant ring, through extension of scalar
   actions by sheafification. It does not replace modules by sets.
6. The two specified extensions: `Etale.openImmersionLowerShriek` and
   `ProEtale.openImmersionLowerShriek`, at `ModuleCat Λ`. I opened their
   definitions and restriction adjunctions. Both are the actual localization
   left Kan extension followed by sheafification, giving F(V→U) or zero for a
   monic j. The repaired dependency `def-weil-extension-by-zero` therefore
   supplies precisely the node's construction in this presentation.
7. Canonical displayed arrow: the hom component of
   `openImmersionLowerShriekComparisonUpperStarIso`. I read its implementation
   in both the upstream source and the group's read-only framework: it is the
   inverse conjugate of `comparisonLowerStarOpenImmersionRestrictionIso`,
   whose body is `Iso.refl _`. Thus this is the node's section-identity mate,
   not an arbitrary isomorphism or an added comparison hypothesis.
8. Isomorphism for every F: the first conjunct is exactly `IsIso` of that
   component. Naturality is supplied by this fixed natural isomorphism's
   existing natural transformations, so it is part of the specified map.
9. Composition compatibility: the second conjunct first applies ν_X^* to
   `Etale.openImmersionLowerShriekComp.hom`, then α_j at k_!F, then j_!(α_k),
   then `proEtaleOpenExtensionComp.inv`; it equals α_(k≫j). This is precisely
   the last formula of proof step 8 in Lean's left-to-right composition order.
   I opened the etale composition definition and the pro-etale pullback
   coherence. The helper uses the same `leftAdjointUniq` prescription as the
   etale dependency, transporting the composite adjunction by `upperStarComp`.
   It contains real data and introduces no extra axiom or premise.
10. Identity normalization: the last conjunct identifies α_id with the
    identity using the canonical `Adjunction.leftAdjointIdIso` maps on both
    sites. This spells out the identity part of the node's canonical,
    composition-compatible comparison and its proof step 8.

I opened all six statement dependency records and their recorded source
signatures, including `proEtaleDerivedCategory` (which supplies the existing
small pro-etale site), `IsOpenImmersion`, and `ringedSiteModules`. The old
extension-by-zero interface and its replacement are different presentations
of the same construction; the lean-only dependency repair is justified under
§1(B), with no change to that node's mathematical statement. There are no new
nodes or dependency source modules to review. I also read
`coord/pefw-upstream-framework.md`; none of the condensed-module framework
objects is substituted for the fixed finite-coefficient sheaf category here.

Edge cases: empty schemes and empty opens are allowed by all binders; zero
sheaves and the zero finite ring are allowed. Identity immersions are included
explicitly. There is no index set or cohomological degree, so empty indexing
and n=0 add no cases. All characteristics are admitted. `u` is arbitrary;
site objects retain universe u+1 and morphisms u, and ModuleCat uses the
common larger coefficient universe required by the existing dependency
interfaces. No equality of the site's two universes is assumed. Smaller
finite rings fit this presentation by universe lifting, as in the dependencies.

Independent searches used different wording from the worker: LeanFinder
`canonical mate of restriction comparison commutes with composite extension
by zero` returned eight unrelated scalar-extension/complex hits; Loogle
`"comparisonUpperStar"` returned zero. LeanSearch `Naturality and composition
coherence of etale proetale comparison with extension by zero` was unavailable
(Internal Server Error), not evidence of absence. Direct rg over Mathlib,
upstream WeilConjectures, the group's WeilConjectures framework and project
lean/Sheaf for `jshriek-comparison`, `Comparison_coherence`,
`proEtaleOpenExtensionComp`, and comparison/shriek word combinations found the
existing canonical comparison but no full composition/identity theorem or
existing pro-etale extension composition helper. Thus dropping the module
would lose the coherence clause. Searches are recorded by msearch as well.

No mathematical, signature, docstring or dependency-record mismatch was found;
I left the correct Lean and node copies unchanged. The module and declaration
docstrings cite the source and blueprint, and the theorem docstring carries
all eight proof steps. The only postponed proof is the named node theorem;
there is no hollow definition, file-local notation, private construction or
unbound variable/universe. The node's `lean.statement` equals the signature
verbatim. I compiled the sole delivered Lean file with the required
`scompile.py NK lem-cbc-proetale-extension-zero-comparison` wrapper: success,
no errors or warnings. Second reading changes only this report.
