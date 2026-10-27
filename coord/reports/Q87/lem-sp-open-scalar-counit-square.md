## Worker report

The delivery states lem-sp-open-scalar-counit-square in
`Sheaf.Paper.OpenScalarCounitSquare`, namespace `AlgebraicGeometry.ProEtale`.
The main declaration is `openScalarCounitSquare`; its three companion theorems
record the unit/restriction and identity clauses. All four theorem proofs are `sorry`.
The two helper definitions contain real constructions from published adjunctions:
`openScalarCounitAdjunction` transports the canonical open adjunction by the
unit-preserving `reductionOpenModel`, and `openScalarCounitScalarUnitor` is the
left-adjoint uniqueness comparison over the published identity scalar-restriction
unitor. Neither chooses an arbitrary map or natural isomorphism.

Hypothesis and clause correspondence:

- Schemes X, Z and open immersion j are `{X Z : Scheme.{u}}`, `(j : X ⟶ Z)`
  and `[IsOpenImmersion j]`. The coefficient map is `(φ : A →+* B)`, with
  `[CommRing A] [CommRing B] [Finite A] [Finite B]`. RingHom includes preservation
  of 1; the zero ring is allowed. The unit and identity results use the same
  hypotheses with a coefficient ring named R.
- Ordinary uncompleted unbounded D(W_proet,R) is exactly the recorded intrinsic
  constant-ring category `Scheme.proEtaleDerivedCategory W R`. Its objects are
  localizations of integer-indexed cochain complexes of sheaves of modules over
  `proEtaleConstantRing W R`, with the standard derived-category instance. The
  dependency's continuous-function presentation is already related to these
  intrinsic constant coefficients by its published canonical realization.
  No completed, bounded or constructible subcategory occurs here.
- T_W is `scalarExtensionFunctor φ W`, the published K-flat-derived change of
  rings. r_W is `scalarRestriction φ W`, the exact termwise restriction functor.
  The counit is specifically
  `(proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap φ)).counit`.
  This is the universal-counit-normalized scalar adjunction, not an arbitrary
  adjunction on the same pair of functors.
- J_R is precisely `(sfIntrinsicExtensionByZero j R).mapDerivedCategory`, the
  recorded sheafified extension presheaf descended termwise. Its adjunction with
  `constantPullback` is `openScalarCounitAdjunction R j`. Its construction uses
  `reductionOpenModel`, which preserves the specified ordinary open units.
- The scalar comparison a is the existing natural isomorphism
  `sfOpenRestrictionDerived j φ`. Its hom has orientation J_A r_X → r_Z J_B.
  This is exact termwise localization of the sectionwise normalized comparison
  `sfOpenRestriction`, not a newly selected comparison.
- E is the existing natural isomorphism `reductionOpenScalarIso φ j`, with
  orientation T_Z J_A → J_B T_X, including both `reductionOpenModel` coordinate
  changes around the common-right-adjoint open tensor comparison.
- The first conjunct of `openScalarCounitUnit` equates the open unit, after the
  canonical `openSquareDerivedPullbackModel`, with the independently specified
  `sfIntrinsicDerivedOpenUnit`. That unit is descended from the sectionwise
  extension adjunction in the realization coordinates. Thus it fixes the actual
  section-normalized unit rather than just asserting existence of an isomorphism.
  The second conjunct says this unit is invertible. Together these express that
  the unit becomes identity under the canonical sectionwise open identification.
  The final conjunct says restriction on arrows J_R M → N is injective for every
  M and N. It makes no assertion of faithfulness on all ambient arrows.
- The first equation of `openScalarCounitRestriction` writes
  η_A(r_X L); u_A(a_L); ρ_(J_B L) = r_X(η_B L), where ρ is
  `(OpenScalarTensor.rightSquare φ j).inv`. This is the identity of the restricted
  scalar comparison under the two open units and the canonical scalar square.
- Its second equation writes η_B(T_X M); u_B(E_M inverse) =
  T_X(η_A M); λ_(J_A M) inverse, using `tensorPullbackIso`. Since both units are
  invertible, this is precisely the requested identity restriction of E, expressed
  in inverse orientation without a second tensor comparison.
- `openScalarCounitSquare` is an equality of natural transformations.
  Its left component at L is T_Z(a_L) followed by ε_Z(J_B L). Its right component
  is E_(r_X L) followed by J_B(ε_X L). Lean's `≫` composes left to right,
  whereas the displayed mathematical equation uses right-to-left `∘`.
- Naturality in every derived argument is part of the types: a and E are NatIso,
  the counits are NatTrans, and the square is a NatTrans equality. Consequently
  it includes the component equation for every L and all its naturality squares.
- `openScalarCounitIdentity` first states that a for `RingHom.id R` becomes identity
  after `sfOpenDerivedCoefficientRestrictionId`; its second equation says E becomes
  identity after `openScalarCounitScalarUnitor`. Its third identifies the scalar
  counit with these scalar unitors. The general square therefore specializes to
  the identity equation as the node requests.
- No additional hypothesis mentions flatness, boundedness, constructibility,
  K-flatness of L or r_X L, or Tor amplitude. Their full absence is visible in
  the signatures. The unit statement quantifies over all finite R, including
  both coefficient rings of the square.

Dependency declarations used (all signatures and source docstrings inspected):

- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `AlgebraicGeometry.ProEtale.FiniteCoefficientModules` and the intrinsic
  coefficient realization used by `sfIntrinsicModuleEquivalence`; the actual
  category is `Scheme.proEtaleDerivedCategory` from the published operations.
- `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `AlgebraicGeometry.IsOpenImmersion`.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction` provides the named
  representative normalization used in the proof plan. The published specialized
  pair is `Scheme.proEtaleRingDerivedExtensionAdjunction` (FourCorners).
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `Scheme.sfIntrinsicExtensionByZero` and `sfIntrinsicModuleEquivalence`.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`:
  `ProEtale.proEtale_extension_by_zero`, `openExtensionScalarMap` and its
  sectionwise mate normalization, already transported by the intrinsic interface.
- `Sheaf.SecSmoothPurity.ReductionDirectImageComparison`:
  `ProEtale.reductionOpenModel`, `reductionOpenScalarIso`.
- `Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionCoherence`:
  `Scheme.sfOpenRestrictionDerived`, `sfOpenDerivedCoefficientRestrictionId`,
  and the ordinary comparison's unit characterization
  `SfOpenRestrictionNormalized` / `sfOpenRestriction_normalized_unique`.
- `Sheaf.SixFunctors.OpenScalarTensorData`:
  `ProEtale.OpenScalarTensor.openAdj`, `rightSquare`; the existing
  `ProEtale.tensorPullbackIso` is reexported by the scalar operations.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange`:
  `Scheme.openSquareDerivedPullbackModel`, with
  `Scheme.sfIntrinsicDerivedOpenUnit` from ProEtaleOpenSquareExchange.
- Proof imports are the recorded `openTensorNormalization`,
  `open_scalar_tensor_normalization`, `kflat_scalar_comparison_normalization`.
  The recorded Mathlib mate is `CategoryTheory.mateEquiv` and its transpose lemma
  `mateEquiv_counit_symm` in Mathlib.CategoryTheory.Adjunction.Mates.
  Module-presheaf sheafification is the recorded Mathlib declaration, used through
  the existing extension construction.

The repaired item records the canonical interfaces under definition owners:
def-sp-open-scalar-tensor-data, the new existing-declaration node
def-sp-open-scalar-restriction-comparison, def-coef-scalar-restriction-identity,
def-trf-finite-pullback-coordinate-comparison, def-sp-finite-intrinsic-open-square,
and def-sp-proetale-constant-coefficient-ring-map. The two theorem dependencies
lem-sf-open-extension-scalar-restriction-coherence and lem-trf-open-square-exchange
added by the returned delivery have been removed from stmt_deps. The new node owns
only the already defined scalar-restriction comparison a; it has no theorem conclusion.
The item's mathematical statement, proof and proof_deps are unchanged. No new Lean
module or dependency replacement module is needed.

Edge cases checked before writing and on rereading:

- Empty X: the extension source is zero and restriction is to the zero category;
  the specified source-restricted Hom injection remains valid.
- Whole open and j = identity: the section-unit and transported tensor equations
  reduce to the corresponding canonical identity functor comparisons.
- Zero complexes: all displayed arrows have the stipulated zero source or target.
- Identity coefficient homomorphism: explicitly retained by the identity theorem;
  neither extension nor restriction is silently replaced by definitional identity.
- Nonflat coefficient maps, e.g. Z/4 → Z/2: neither L nor its restricted complex
  needs to be K-flat; the statement uses the derived normalized counit rather than
  underived multiplication on an arbitrary representative.
- Unbounded complexes and arbitrary finite commutative rings, including the zero
  ring, remain admissible. The site has objects in u+1 and morphisms in u; no equality
  of those universes is imposed.

Searches (2026-10-24 UTC):

- msearch.py leansearch: "Open extension by zero is compatible with the derived
  scalar adjunction counit on unbounded module sheaves" returned 8 hits, including
  ModuleCat.RestrictionCoextensionAdj.counit', PresheafOfModules.sheafificationAdjunction,
  and Scheme.Modules.restrictAdjunction. None states this derived pro-etale square.
- msearch.py leanfinder: "Extension by zero preserves derived scalar restriction
  counit, with identity restriction on the open" returned 8 ordinary ModuleCat
  scalar adjunction/counit/unit hits. These fix familiar formulas, but do not
  identify these geometric comparisons or their unbounded restriction laws.
- msearch.py loogle: "CategoryTheory.mateEquiv, CategoryTheory.conjugateEquiv_counit"
  returned 0 hits. Direct source reading of Mathlib's Adjunction/Mates.lean confirms
  mateEquiv_counit_symm is the generic transpose identity used by the proof plan,
  not the requested geometric statement.
- msearch.py grep: `(extensionByZero|lowerShriek|openExtension).*(scalar|Scalar|counit)|
  (scalar|Scalar).*(extensionByZero|lowerShriek|openExtension)` returned 0 Mathlib hits.
- rg of the same notions in lean/WeilConjectures and lean/Sheaf found the existing
  extension adjunction, sfOpenRestrictionDerived, OpenScalarTensor.rightSquare,
  and reductionOpenScalarIso. These are reused above. No complete theorem with
  the item's square and unit/identity clauses was found.
- rg for `openScalarCounit|OpenScalarCounitSquare` in lean/WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json returned no declarations. The
  prescribed grep for the item id in lean/WeilConjectures returned no hits.

Source check: read sites-modules.tex lemma-j-shriek-and-tensor (0E8I),
sites-cohomology.tex lemma-adjoint (07A6), and the current blueprint's
sk-prop-sp-tower-geometric-gluing.proof.md, Levels paragraph. The node makes
explicit the open/scalar compatibility needed by its canonical coefficient
comparisons. No statement fault or STATEMENT-DISPUTED issue was found.

Validation: scompile.py compiled the initial complete module with no diagnostics
once Functor.whiskerLeft/Right were fully qualified. The final unit-normalization
refinement also compiled cleanly in both sandbox and library module modes using
scompile.py; the delivery dry run repeats the prescribed checks. All variables
and universe parameters are explicit, every line is at most 100 characters, and
all postponed theorem proofs are whole `by sorry` bodies with source/proof docstrings.

## Second reading by Q87

This dispatcher assignment forbids other agents; the maintainer supplies the
independent review. I reopened the node and the module for a separate self-rereading.
I checked each binder, the ambient unbounded categories, both directions of each
comparison, the order of composition, and the absence of hidden flatness/Tor
assumptions. The main square has exactly source T_Z J_A r_X and target J_B. I
checked the restriction comparison uses rightSquare.inv, whereas the inverse
open-tensor adjunct uses tensorPullbackIso.inv. The identity comparison targets
use the published restriction unitor, not bare equality of different functors.
This reading added the explicit equality with sfIntrinsicDerivedOpenUnit, so that
unit invertibility is accompanied by its prescribed section normalization. No
mathematical statement correction was needed. The only compilation repair was
fully qualifying the four Functor whiskering operations.


## Repair of immutable head 2d2128af2ba5

H2 is repaired as requested:

1. Removed `lem-sf-open-extension-scalar-restriction-coherence` and
   `lem-trf-open-square-exchange` from the delivery's added statement dependencies.
   The current main node still has its original six statement dependencies; all six
   are retained. This is a replacement of the returned delivery's two additions,
   not a deletion of any accepted base dependency.
2. Added `def-sp-open-scalar-restriction-comparison`, `existing: true`, owning
   `Scheme.sfOpenRestriction` (ordinary comparison) and
   `Scheme.sfOpenRestrictionDerived` (its exact derived localization). The node
   describes exactly their published construction and records the source signatures.
   The latter is the primary declaration; the former is in the publicly imported
   `Sheaf.Paper.SfCompactSupportRestrictionOfScalars` module. No second definition,
   module, coherence assertion, or normalization theorem is introduced.
3. Cited the three requested existing definition owners:
   `def-coef-scalar-restriction-identity` owns the ordinary and derived scalar
   restriction identity unitors; `def-trf-finite-pullback-coordinate-comparison`
   owns `openSquarePullbackModel` and `openSquareDerivedPullbackModel`;
   `def-sp-finite-intrinsic-open-square` owns the intrinsic open extension/adjunction
   coordinates used for `sfIntrinsicDerivedOpenUnit`. The definitions and docstrings
   of all these interfaces were read again. Also cited
   `def-sp-proetale-constant-coefficient-ring-map`, which owns the coefficient map
   named directly in the statement and used in the new definition node.
4. Kept the accepted Lean module byte-for-byte unchanged. Its SHA-256 is
   `155db2cbf43a15965f60c5ba9fdecd98932880e37f191d132942abf01a594aac`.
   Against the current main node the only modified fields are `lean` and
   `stmt_deps`. The prescribed delivery wrapper handles refreshing the current
   base and building the new one-commit delivery; no direct Git operation was run
   in the shared read-only repository.

The review's accepted mathematical findings are preserved: the scalar and open
comparison orientations, composition order, unit/Hom injection, both restriction
identities and all identity-map clauses are the same. Every proof is still `sorry`;
no hypothesis, definition body, signature, docstring or import was changed.

## New nodes

`def-sp-open-scalar-restriction-comparison` attaches definition ownership to the
published ordinary isomorphism `sfOpenRestriction` and its canonical exact derived
localization `sfOpenRestrictionDerived`. For finite commutative A, B, a unital map
A → B, and an arbitrary open immersion j, its source is r_U followed by J_A and
its target is J_B followed by r_Z. The ordinary construction transports the
fixed-scalar left-adjoint uniqueness isomorphism through the canonical realization
comparisons. The derived construction is exactly
`Functor.mapDerivedCategorySquareIso (sfOpenRestriction j φ)`. The source is the
sheafified extension presheaf and its scalar action in Stacks Tags 03DI and 03CY,
and exact localization (015F). This new node asserts no coefficient cocycle or
normalization theorem. It uses precisely the existing definitions in the module
already imported by the accepted item.

The new node's own statement explicitly cites open immersions, pro-etale constant
module categories, the coefficient ring map, scalar restriction, sheafified open
extension and the abstract derived category. Those six definition nodes are exactly
its stmt_deps. The source construction covers empty opens, whole opens, zero rings,
zero complexes and nonflat coefficient maps, with no quasi-compactness, boundedness,
constructibility or Tor hypothesis. Its import_flags is [] because the target reaches
it through this item; its blueprint ancestor is det-sp-tower-gluing, confirmed by
`tools/blueprint_refs.py ancestor lem-sp-open-scalar-counit-square`.

Fresh searches for this ownership node are recorded verbatim as results in its
mathlib_searches. LeanSearch's canonical open/scalar comparison query returned eight
scalar-restriction declarations (ModuleCat, PresheafOfModules, SheafOfModules), but
none is this geometric comparison. LeanFinder returned eight ordinary module
adjunction declarations, also no geometric comparison. The Mathlib regex search
returned zero hits. The upstream regex search found only the compact-support
Frobenius/scalar theorem; the project search found exactly the published ordinary
and derived definitions reused here. A search of all definition-kind DAG lean
records found no owner of sfOpenRestriction or sfOpenRestrictionDerived, while
`blueprint_refs.py search 'open scalar restriction'` returned zero blueprint nodes.
Thus the new definition node is needed for ownership, not to replace an existing
construction. The three existing owners named by L are cited and are not duplicated.

Repair rereading by Q87: reopened the new node, accepted module, current item node,
three required existing definition records and their actual Lean definitions. Checked
that the two rejected theorem additions are absent, that the comparison a has the
same existing declaration as before, and that each added dependency now describes
data used in the signature. The accepted original clause-by-clause reading above
still applies because the Lean bytes are unchanged. The maintainer's independent
reading on immutable head 2d2128af2ba5 accepted those mathematical clauses; this
repair changes only dependency ownership and the delivery report.

Repair validation: scompile.py passed the unchanged module in both sandbox and
library modes. deliver2.py --no-push then passed preflight and all compiler checks,
including the existing-declaration check for the new definition node. Its staged
set is exactly the accepted Lean module, the repaired item record, the new
existing-definition record and this report.
