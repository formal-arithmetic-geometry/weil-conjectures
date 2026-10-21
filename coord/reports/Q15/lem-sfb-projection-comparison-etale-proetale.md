## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleProEtale` states
`AlgebraicGeometry.ProEtale.projection_comparison_etale_proetale`, with its proof `sorry`.
The statement and all dependency lists of the DAG node are unchanged. Three real-data
helper definitions name the admissible pairs and the common source and target functors.
They introduce no second derived category, tensor product, comparison map or projection map.
There are no new nodes, dependency repairs or statement corrections.

Hypothesis and clause correspondence:

- A finite discrete commutative ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  ModuleCat sheaves encode discrete constant coefficients; no topological ring is supplied.
- Schemes and their qcqs morphism are `{X Y : Scheme.{u}} (p : X ⟶ Y)
  [QuasiCompact p] [QuasiSeparated p]`. There is no properness assumption.
- The fixed common universe is explicit `universe u`, with the existing small etale site
  and `Scheme.ProEt.topology` and coefficient objects `ModuleCat.{u + 1} A`.
  These are exactly the published size convention and fixed-coefficient presentation.
  The pro-etale site's object universe is u+1 and its Hom universe u: neither is changed.
- The pair's objects are `B.obj.1 : Etale.DerivedCategoryModule A X` and
  `B.obj.2 : Etale.DerivedCategoryModule A Y`. These are the existing unbounded categories.
- `sfbProjectionComparisonAdmissible` requires `∃ n : ℤ, K.IsGE n` and the same condition
  for `((Etale.derivedTensor ... X).obj K).obj
  ((Etale.upperStar ... p).leftDerivedFunctor.obj N)`. These render precisely K in D+
  and L = K tensor uN in D+. `B.property.1` and `.2` supply these two proofs.
  There is no bound on N, on R_e K tensor N, or on its comparison pullback.
- F_T is `(comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory`.
  u and v are the existing `.leftDerivedFunctor` of etale and pro-etale `upperStar`;
  exactness identifies these with the exact termwise derived inverse images.
  R_e and R_p are `.rightDerivedFunctor` of their existing `lowerStar` functors.
  These are ordinary uncompleted operations, with no constructibility or Tor condition.
- The specified a is `comparisonOpenDerivedPullbackIso A p`. Despite the historical
  name, its full signature has an arbitrary scheme morphism p, with no open-immersion
  binder. Its body localizes the recorded `supportSiteComparisonCoefficientPullbackIso`
  and inserts the canonical L-upperStar / termwise-upperStar isomorphisms.
- t_T is `derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso` evaluated at
  the two inputs. Its body is the canonical strong-monoidal derived tensor comparison,
  transported through the exact comparison functor's L ≅ D identification. This is the
  K-flat representative comparison specified by the ringed-topos tensor node.
- h is `(comparisonOpenTensorIso A p K N).hom`. Its definition first applies t_X
  at (K,uN), then maps a_N by tensoring with F_X K. Again there is no open-immersion
  restriction in its signature.
- b_B is written as five arrows: F_Y applied to the inverse of the right-derived
  D+ compatibility; the inverse of the exact F_Y D+ compatibility; D+ inclusion
  applied to `fixedComparisonDirectImageMatePlus`; the right-derived pro-etale
  D+ compatibility; and R_p applied to the exact F_X D+ compatibility. These are
  precisely the components of the published included comparison, with the two
  inverse arrows at its source and two forward arrows at its target. The middle
  arrow is the recorded normalized mate, without any choice of endpoint map.
  The constructor is `⟨B.obj.1, B.property.1⟩` at K and the displayed L with
  `B.property.2` at L. These are the only boundedness requirements.
- pi_e and pi_p are the components of the existing etale and pro-etale
  `rightDerivedLowerStarProjectionMap`. Their bodies are
  `derivedUpperStarLowerStarAdjunction.rightAdjointProjectionMap` applied to the
  canonical pullback tensor comparison. Their documented transpose is exactly
  that comparison followed by counit tensor identity.
- The first component formula in the theorem is, in Lean's left-to-right composition
  order, `F_Y.map pi_e ≫ b_L.hom ≫ R_p.map h.hom`. This is the displayed left route.
- The second formula is `t_Y.hom ≫ (derivedTensor.map b_K.hom).app (F_Y.obj N) ≫ pi_p`.
  The middle map is exactly b_K tensor identity by the bifunctor action.
- The source helper is the uncurry of `Etale.derivedTensorRightDerivedLowerStar`,
  followed by F_Y, restricted to admissible pairs: F_Y(R_e K tensor N).
  The target helper first applies F_X and F_Y, then the uncurry of
  `rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar`: R_p(F_X K tensor v F_Y N).
- `∃ alpha : source ⟶ target, ∀ B, alpha.app B = firstRoute ∧ alpha.app B = secondRoute`
  states exactly that the displayed routes agree naturally in both inputs.
  A natural transformation includes its naturality equation for EVERY arrow in the
  full subcategory of admissible pairs. Those arrows are arbitrary pairs of maps
  K → K', N → N' between admissible objects. Conversely, the node's common natural
  route gives precisely this alpha. No extra isomorphism assertion is made about pi.

Dependency declarations and full source signatures/docstrings read:

- `def-weil-size-convention`: metatheoretic convention; its record explicitly has no
  declaration, and the universes above implement it.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, `DerivedCategory`,
  `DerivedCategory.Plus`, and `DerivedCategory.TStructure.t.plus` / `IsGE`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `Scheme.proEtaleConstantRingDerivedPullback` and the reexported intrinsic finite
  interface; the fixed ModuleCat presentation here is the published finite-coefficient
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar`.
  Its documentation explicitly identifies exact termwise D(p*) with L(p*), and its
  ordinary K-injective right-derived operation and adjunction are the ones used here.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `supportSiteComparisonCoefficientPullbackIso` and
  `supportSiteComparison_pullback_coherent`; the former occurs in the localized a.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`
  and `ringedTopoiCanonicalDerivedTensorComparison`, with their unique K-flat
  representative square and ordinary unit normalization. The ModuleCat specialization
  used here is the existing framework tensor comparison, not a second definition.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `fixedComparisonPullbackPlus`, `fixedComparisonDirectImageMatePlus`,
  `isIso_fixedComparisonDirectImageMatePlus`, and
  `fixedComparisonDirectImageMatePlus_counit`.
  `Functor.rightDerivedFunctorPlusCompatibility` and
  `Functor.mapDerivedCategoryPlusCompatibility` supply its inclusion into the
  unbounded categories. The five inclusion arrows are written directly, so no
  second definition is introduced and no exceptional-inverse-image theorem is imported.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`:
  `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap` and its transpose lemmas.
  The pro-etale counterpart is in the finite-coefficient `Derived.LowerStarProjection`.
- `Sheaf.Paper.ProjectionMateExact`: `SheafOfModules.ringedProjectionMateExact`;
  `Sheaf.Paper.RingedExchangeTensorCoherence`:
  `SheafOfModules.ringedExchangeTensorCoherence`. These are proof-only imports,
  along with the recorded ringed-topos and constant-ring-map proof prerequisites.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `CategoryTheory.mateEquiv`, the
  `mathlib_match` of the adjunction-mate dependency; its unit/counit formula was read.
- `Sheaf.SixFunctors.ComparisonOpenTensorCoherence`:
  `comparisonOpenDerivedPullbackIso`, `comparisonOpenTensorIso`. Both full signatures
  apply to arbitrary scheme morphisms; their canonical construction bodies were read.

Source reading: `literature/stacks-project/proetale.tex`,
`lemma-morphism-comparison` (09A6), including the preceding pullback square;
`sites-cohomology.tex`, `lemma-pullback-tensor-product` (07A4) and
`remark-compatible-with-diagram` (0E48); current blueprint
`main-20261015/blueprint/sec-six-functors-basics/sk-thm-sfb-proper-base-change/`
`sk-thm-sfb-proper-base-change-finite.proof.md`, paragraph (3).
The theorem docstring reproduces the node's four proof steps, with the inverse
orientation theta = a inverse and the normalized mates at K and L.

Edge cases checked by reading the definitions and signatures:
identity p and tensor-unit N; zero K and arbitrary unbounded N (K=L=0 is admissible);
zero N; empty X or Y; zero coefficient ring; nonproper qcqs p; finite nonreduced
coefficient rings such as Z/4, with no Tor-amplitude restriction. No Nontrivial,
nonempty scheme, bounded N, properness, projection-isomorphism, or flatness binder
excludes these cases. The full subcategory retains every pair of maps between its
objects and therefore does not weaken naturality.

Searches actually run for this item, using the prescribed msearch wrapper:

- LeanFinder: "The canonical projection formula map commutes with etale to proetale
  comparison and the counit normalized derived direct image mate". Eight results,
  including Condensed.profiniteSolidCounit and ordinary adjunction counits; no match.
- Loogle: `CategoryTheory.Adjunction, "projection"`. Zero hits.
- Mathlib grep: `projection.*[Cc]omparison|[Cc]omparison.*projection|rightAdjointProjectionMap`
  in CategoryTheory. Zero hits.
- LeanSearch: "The projection formula morphism commutes with etale to proetale
  comparison of derived direct images". Eight results on product comparisons,
  projective resolutions and stability of etale maps; no match.
- Local rg in `lean/WeilConjectures` and `lean/Sheaf` for the item id: no declaration.
  Searches for projection/comparison and derived mates found and led to reading the
  modules above. In particular upstream `Derived.LowerStarProjComparison` states
  invertibility transport conditional on invertibility of the etale projection,
  not the node's specified equality with the included normalized b. Its generic
  tensor/mate coherence helps prove the item, but is not this statement. The existing
  `SpDirectImageEtaleMate` specializes to constant B_Y and is not the arbitrary N
  statement. Its canonical included form is expanded using the recorded D+ mate
  and existing compatibility maps. Open tensor coherence treats open
  extension rather than R_p projection, but its unrestricted helper is reused.

Historical validation of the original packet: prescribed scompile.py compiled it both as
sandbox module and at its actual library module name, 7.9 s each, with no errors
or warnings. `autoImplicit false` is set; the only universe is explicitly bound u.
Every definition contains real data; the only sorry is the named main theorem.

## Second reading by Q15

A fresh pass compared the final node statement with the final module. The admissible
property contains exactly the two D+ hypotheses; the theorem's binders contain exactly
the finite commutative ring and qcqs assumptions. The first route ends in R_p(h),
and the second applies t_Y before b_K tensor identity and pi_p. The orientations of
h and the tensor/pullback comparisons agree with the displayed target. The source
and target functors unfold to the two endpoints in the node. Replacing a bare
pointwise equality by a common natural transformation records the final naturality
clause for arbitrary pair maps. No mismatch or statement correction was found.
The helper with "Open" in its name was checked at its signature and construction:
it has no open-immersion hypothesis. The included direct-image comparison was checked
at its middle arrow: exactly the recorded normalized D+ mate. In this repair,
the five arrows of that inclusion are expanded in both formulas. Their source
and target orientations agree with the original convenience wrapper, and the
underlying normalized mate is unchanged. This is a second
reading by the assigned worker; the maintainer's independent review follows delivery.
No other agent was started, as required by the dispatcher brief. The three
new characterizations were then checked against the bodies of their definitions:
conjunction order, both tensor arguments, and both direct-image endpoints match
verbatim. The definitions still contain the original real data.

## Returned-delivery repair, 2026-10-21

The saved packet was inspected first and the required initial `deliver2.py --no-push`
was run before editing. The earlier missing-Mathlib failure and subsequent upstream
cohomology timeouts did not recur on the current published server build. That dry run
reached the item and gave concrete errors: the etale projection bifunctor and projection
map were not imported, and `no_expose` prevented projections of the admissibility
conjunction. Adding the exact recorded owning import
`WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection` repairs the missing names.
A first compile using the admissibility characterization then diagnosed the hidden
source and target endpoint definitions. The final repair removes `no_expose` from all
three helper definitions, retaining their bodies and the three characterization
statements. These exposed interfaces let the main statement elaborate definitionally.
No upstream repair is included or needed, and no launcher tool was changed.

This is a substantive import/interface repair of the saved packet, not an unchanged
re-push. The natural-language statement, stmt_deps, proof, and proof_deps remain verbatim
from the current shared node. Only its lean record changes. There are no new nodes or
dependency modules. The complete included normalized mate at K and L remains unchanged;
all four theorems have stage-2 sorry proofs, and all three definitions have real data.

Prescribed `scompile.py Q15 lem-sfb-projection-comparison-etale-proetale
lean/Sheaf/AlgebraicGeometry/ProjectionComparisonEtaleProEtale.lean` passed cleanly as
both `Sheaf.Stage2.Sandbox0` (20.3 seconds) and the actual library module (24.5 seconds).
The final node signature was extracted verbatim from the theorem through its type,
before `:=`, and all seven declarations remain recorded. No local/global build,
shared-source edit, or direct Git command was used.

Fresh second reading of the repaired module against the current node: A is finite
commutative; p is qcqs with arbitrary X and Y; K and K tensor uN are exactly the two
bounded-below objects; N is arbitrary unbounded. The source is F_Y(R_e K tensor N),
and the target is R_p(F_X K tensor v F_Y N). The two formulas retain F_Y(pi_e), b_L,
and R_p(h) in the first route, and t_Y, b_K tensor identity, and pi_p in the second.
The helper definitions expand to these exact endpoints. A common natural transformation
on the full subcategory retains all morphisms of admissible pairs. Neither the added
import nor restoring exposure adds any mathematical assumption, changes a canonical
map, or excludes identity, zero, empty-scheme, zero-ring, or nonproper qcqs cases.
The previous report's compact no_expose interface was the elaboration defect; exposure
is restored in this repair. The compiler verifies that both routes now have the exact
source and target of alpha.app B.

Final prescribed dry run: `deliver2.py Q15
lem-sfb-projection-comparison-etale-proetale --no-push` printed
`OK (dry run): commit 42c12dc475f passes the preflight and compiles; nothing pushed`.
Static checks confirmed zero changes outside lean in the node, the exact recorded
signature, all seven declarations, and no Lean line over 100 characters.
A fresh project-source search for the theorem and helper names found no duplicate.
