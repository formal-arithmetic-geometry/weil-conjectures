## Worker report

The module `Sheaf.AlgebraicGeometry.ZariskiEtalePseudoCoherentRHom` states
`AlgebraicGeometry.Scheme.Modules.zariski_etale_pseudoCoherent_rhom`. The sole
postponed theorem has the complete seven-step proof in its docstring. Definitions
have real data; the theorem returns witnesses with normalization equations, rather
than selecting an unspecified map or an unspecified natural isomorphism.

Source read: `literature/stacks-project/spaces-perfect.tex`, equation-epsilon,
lemma-epsilon-flat (08H8), and lemma-descend-RHom (08JP), including its proof of
case (1). The source assumes only a scheme, pseudo-coherent first input and a
bounded-below second input. It expressly uses exact epsilon pullback and finite
Hom products degreewise. No Noetherian or quasi-coherence hypothesis is present.
The additional representative normalization in the DAG is implemented explicitly.

Hypotheses and clauses, matched against the Lean:

* Scheme: `X : Scheme.{u}`. No geometric finiteness, separation, characteristic,
  nonemptiness, or Noetherian assumption is imposed.
* Canonical ringed-site epsilon: `c : ZariskiEtaleModuleContext X` supplies only
  continuity and right-adjointness proofs. `c.extension` is the recorded actual
  tensor pullback along `zariskiEtaleOpenRingMap X`, not arbitrary functor data.
  `zariskiEtaleRHomExtension c` is its composite with actual affine-basis
  restriction. Exactness is supplied in the theorem's result by `extension_limits`
  and `extension_colimits`, with `extension_additive`; it is not a new hypothesis.
* Ordinary unbounded derived categories: `schemeDerivedCategory X` and
  `DerivedCategory (ZariskiEtaleRHomModules X)`. The HasDerivedCategory binders
  select localization morphism sizes `w`, including those of the open restrictions
  required by the recorded `Scheme.IsPseudoCoherent`. No bounded derived-category
  replacement or restriction to D_QCoh occurs.
* Inputs: the `isIso` field quantifies over all `K L : schemeDerivedCategory X`.
  Its first hypothesis is exactly `X.IsPseudoCoherent K`. Its second is
  `∃ a : ℤ, ∀ i : ℤ, i < a → IsZero ((DerivedCategory.homologyFunctor _ i).obj L)`.
  Thus the bound is a cohomology bound, not a bound on arbitrarily chosen complex
  terms. There is no quasi-coherence assumption on L.
* Derived internal Hom: `zariskiRHom X` and `smallEtaleRHom X` are abbreviations
  of the recorded `derivedInternalHomOfUniverses`, without a new Hom construction.
  Their ordinary models use the recorded `homComplex` and `homComplexπ`.
* The displayed comparison is the field `comparison`, a natural transformation
  from `zariskiRHom X ⋙ extension.mapDerivedCategory` to
  `(extension.mapDerivedCategory.op.prod extension.mapDerivedCategory) ⋙ smallEtaleRHom X`.
  This gives contravariant naturality in K and covariant naturality in L on the
  entire two-variable domains. `isIso` says its components are invertible under
  precisely the two input hypotheses; restricting a natural transformation with
  invertible components gives the stated natural isomorphism.
* Canonical ordinary map on local sections: `ordinary_sections` says that the
  image of a local linear map φ, evaluated on a pulled-back local section m, is
  the pulled-back section φ(m). It is quantified over every affine chart, every
  refinement and every open lying under that chart, with the commuting square
  `_hk`. Linearity then specifies the map on all local scalar multiples and sums.
* Degree-n product comparison: `complex_projections` says that postcomposition
  with the p-th Hom-product projection is pullback of the source projection
  followed by `ordinary (A.X p) (B.X q)`, where `p+n=q`. `complex` is a genuine
  complex morphism, so it includes compatibility with the signed differential.
  No preservation of infinite products is asserted.
* Fixed replacements: the theorem’s representative equation uses exactly
  `WeilConjectures.coefficientHomResolution`, `ringedSiteHomAugmentation` and
  `coefficientHomResolutionIso`. Its right side applies the Zariski fixed
  factorization, the exact pullback factorization, the chain comparison to
  Hom(A,I(B)), and postcomposition with TI(B) → I(TI(B)). Its left side takes the
  claimed derived comparison and identifies its target using the pulled-back
  augmentation TB → TI(B) and the same etale fixed resolution. Hence the equation
  normalizes the actual derived morphism rather than merely its endpoints.

Universe transport is explicit. The raw site `X.Etale` has object universe u+1,
whereas its modules in the recorded epsilon interface have section universe u.
The recorded `homComplex` on this presentation returns section universe u+1 and
cannot be fed back into that interface. Use Mathlib's essentially-small affine
etale basis `X.AffineEtale` and `SmallModel.{u}`, with the actual inclusion
`(equivSmallModel X.AffineEtale).inverse ⋙ AffineEtale.Spec X`. Topology and
commutative regular-function sheaf are pulled back along this inclusion.
`zariskiEtaleRHomRestriction` is literal module restriction with identity ring map.
The theorem's `restriction_equivalence` field identifies this with the given
module topos. This is the same D(O_et), using an equivalent small site as the node
requires. Coefficients and section sizes stay u. No equality of the original site
object and morphism universes is imposed. These are helpers for this node's
canonical comparison, not independent replacement definitions of epsilon or RHom.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
* `Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence`:
  `DerivedEtaleZariskiEquivalenceData`, `DerivedEtaleZariskiSystem`, and the theorem
  `AlgebraicGeometry.Scheme.Modules.derived_etale_zariski_equivalence`; its public
  context `ZariskiEtaleModuleContext` and canonical `extension` / `adjunction`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, and its cohomology functors.
* `WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsPseudoCoherent`, exactly its local finite-free model.
* `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` publicly reexports
  `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses` and its fixed K-injective
  localization. The ordinary ModuleCat abbreviation is not used for sheaves.
* `WeilConjectures.Algebra.Homology.HomComplex`: `CategoryTheory.homComplex` and
  `homComplexFunctor`, with `HomComplexComponents.homComplexπ` used for projections.
* `Sheaf.CategoryTheory.RingedSiteOrdinaryHomComparison`:
  `CategoryTheory.ringedSiteHomAugmentation`; its public representative module
  supplies the fixed `coefficientHomResolution` and `coefficientHomResolutionIso`.
* Mathlib `Scheme.AffineEtale`, its `EssentiallySmall.{u}` instance, `AffineEtale.Spec`,
  `SmallModel`, `equivSmallModel`, `Functor.inducedTopology`, module pushforward,
  and `Functor.mapDerivedCategory` with `mapDerivedCategoryFactors`.
* Available proof dependencies are imported privately: bounded-free RHom model and
  quasi-isomorphism, exact restriction, K-injective slice restriction. Other proof
  dependency modules are public transitive imports of the statement dependencies.

Edge cases: the empty scheme is allowed (the affine site and restriction comparison
still exist); K=0 or L=0 is allowed; arbitrary positive and negative bounds a and
arbitrary shifts are allowed; finite-free rank zero is allowed; the degree-n finite
interval [a-n,b] may be empty. L need not have bounded terms or quasi-coherent
cohomology. K need not be globally bounded above or have globally chosen ranks.
All module and site universes are explicitly bound, with autoImplicit disabled.

Searches actually run for this item:

* msearch LeanFinder: "Zariski to etale pullback preserves derived internal Hom from
  pseudo coherent complexes to bounded below complexes" — eight ordinary scheme
  module-pullback and categorical-pullback hits; no matching theorem.
* msearch Loogle: `"RHom", "pullback"` — eleven unrelated pullback/Over tensor hits.
* msearch grep: `(RHom|internalHom|internal_hom).*(etale|zariski)|(etale|zariski).*(RHom|internalHom|internal_hom)`
  — zero Mathlib hits.
* msearch LeanSearch: "Zariski etale derived internal Hom pseudocoherent bounded
  below" — eight scheme-Hom, topology, ring-etale, prestack-Hom, locality and Ext
  size hits; none is the comparison theorem.
* `rg` of `lean/WeilConjectures` and `lean/Sheaf` for Hom/pullback/etale patterns:
  ordinary constant-coefficient etale Hom pullback exists in
  `Sheaf.SixFunctors.EtaleHomComplexPullback`, but it has another ring and another
  morphism of sites. Existing scheme RHom quasi-coherence theorems do not state
  the Zariski-etale comparison. Algebraic-space small affine models demonstrate
  the size transport convention but have a different chart category.
* `grep -rn lem-sfb-zariski-etale-pseudocoherent-rhom lean/WeilConjectures`: no hit.
  The target has no previously recorded Lean declaration.

No statement correction, dependency re-recording or new definition node is needed.
The node's statement and all dependency fields are preserved.

## Second reading by Q72

A separate in-session rereading (no other agents are permitted by this assignment)
compared the original node, Tag 08JP(1), and the full module. The arbitrary scheme,
pseudo-coherent source, existential lower cohomology bound, absence of Noetherian
and L-quasi-coherence assumptions, and ordinary unbounded categories match the
`isIso` field. The variance is encoded by the actual product functors and natural
transformation. The section equation evaluates at every refinement over each open;
the projection equation uses all n,p,q with p+n=q. The representative equation
uses the specified successive K-injective replacements and their augmentations,
so the theorem cannot choose another isomorphism of the endpoints. The raw-site
universe mismatch was resolved with actual affine-site restriction and its
asserted equivalence, without restricting X or identifying original universes.
No mathematical mismatch or statement change was found. Compiler and delivery
results are recorded after the final checks below.

## Verification

The prescribed `scompile.py Q72 lem-sfb-zariski-etale-pseudocoherent-rhom`
compiled the delivered module cleanly in both sandbox and library modes, with no
errors or warnings (2026-10-24 UTC). The named helper definitions
`complexExtension`, `derivedExtension`, and `derivedFactors` use the exact
functor's explicit structural proofs. `representativeTarget`,
`targetIdentification`, and `sourceIdentification` give the two sides of the
final normalization equation real terms; no helper is chosen from an existence
theorem or filled with `sorry`. The theorem quantifies that equation over all
complex representatives, in addition to the naturality and isomorphism clauses
in its data record.

The prescribed `deliver2.py --no-push` returned `OK (dry run)` at
`aeffeb40ad1`: the maintainer preflight and per-file compilation passed.
