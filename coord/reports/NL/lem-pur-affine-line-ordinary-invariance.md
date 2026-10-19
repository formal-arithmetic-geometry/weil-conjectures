## Worker report

This delivery repairs the already published module
`Sheaf.Paper.AffineLineOrdinaryInvariance` in place. Its statement is
`WeilConjectures.PurityFiniteSetting.affineLineOrdinaryInvariance`, previously
reviewed and landed by Q124 on 2026-10-17. The dispatch overlaps that earlier work.
No declaration, definition, theorem signature, docstring, or mathematical statement
is changed. The existing main theorem retains its stage-2 `sorry`.

The required existing-declaration dry run exposed a real import failure:
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso` and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso`
both declare `AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv`.
The published `FixedComparisonDirectImageMate` imports the FiniteCoefficient
branch, while this module's GlobalSections and Coherence imports used the other
branch. I read the current server source of both replacements with
`scompile.py --source`. They provide the same required declarations and signatures.
The only two source changes are these import replacements:

- `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.GlobalSections` becomes
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections`.
- `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Coherence` becomes
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence`.

This follows the launcher's explicit duplicate-import repair instruction and keeps
one owning module and the exact existing canonical constructions. The node changes
only in `lean` (attribution, verbatim signature formatting and repair note).
The resolved repair note concerns stage-1 proof splitting, explicitly retaining
this Lean statement; it withdraws no stage-2 interface.

Hypothesis and clause correspondence:

- Finite datum, k, ell distinct from p, the fixed finite extension, and positive n:
  `P : PurityFiniteSetting.{u}`. Its field, coefficients, extension and positive level
  are precisely the recorded datum; `P.Coefficient` is ULift of O_E/(varpi_E^n).
- Arbitrary k-scheme: `X : Scheme.{u}` with `[X.Over (Spec (.of P.field.k))]`.
  The structure map passed to the conclusion is `X ↘ Spec (.of P.field.k)`.
  There is no finite-type, separated, noetherian, quasi-compact or smooth hypothesis.
- The relative dimension-one projection: `a1OrdinaryProjection X`, literally
  `AffineSpace (ULift.{u} (Fin 1)) X ↘ X`, the Mathlib definition recorded in
  `def-sbc-affine-space`.
- Every signed twist: `r : ℤ`; `a1OrdinaryBaseModuleComplex P r` uses the existing
  `Scheme.finiteEtaleTateSheaf` on Spec k in degree zero. The annihilator is
  `ringChar P.Coefficient`, with `CharP.cast_eq_zero`, not the older exponent
  ell^(n/e). A nonzero finite residue ring has positive characteristic a power of
  ell, hence invertible on k. Exponent-change in the recorded finite-twist theorem
  identifies this realization with the specified finite twist. Thus no e | n
  restriction has entered. Exact pullback gives the twist on each k-scheme;
  pro-etale realization is the actual comparison inverse image.
- The actual module-valued etale and pro-etale derived units are the two `IsIso`
  clauses using `(upperStarLowerStarAdjunction (ModuleCat P.Coefficient) p).derivedPlus.unit`.
  The target is Rp_* p^* A(r)_X, canonically Rp_* A(r)_(A1_X) by the recorded finite
  twist pullback. It is not an existential isomorphism between endpoints.
- The corresponding underlying abelian units are also explicitly invertible in
  `A1OrdinaryInvarianceAt`. They use the same adjunctions with `AddCommGrpCat.{u+1}`.
  Keeping both records the coefficient-forgetting part of proof step 5 rather
  than silently identifying the two derived coefficient categories.
- Ordinary cohomology in every integer degree: `q : ℤ`; `a1OrdinaryEtaleH` and
  `a1OrdinaryProEtaleH` apply `DerivedCategory.Plus.homologyFunctor` in degree q to
  the right-derived ordinary global-sections functor. The inputs are sheaves in
  degree zero, so this is ordinary sheaf cohomology and is zero for q < 0.
  Bounded-below injective resolutions compute the stated unbounded ordinary
  operations on these inputs; no coefficient completion is used.
- Canonical pullback is the unit followed by the canonical Leray isomorphism,
  then the canonical composition transport of the twist. The two `IsIso` clauses
  on `a1OrdinaryEtaleProjection` and `a1OrdinaryProEtaleProjection` are precisely
  p^*:H^q(X,A(r)) -> H^q(A1_X,A(r)). Leray uses the published equality of sections
  of a direct image and the exact inverse-image adjunction preserving injectives.
- Naturality in X: the final universally quantified clause ranges over every
  `X' : Scheme.{u}` and `v : X' ⟶ X`; the induced k-structure is v followed by a.
  `a1OrdinaryProjectionSquare` is Mathlib's actual affine-space base-change square.
  In both topologies, `a1OrdinaryUnitNatural` is exactly the unit/exchange equation
  of proof step 8, using the counit mate `a1OrdinaryExchange` of the specified
  inverse-image square. `a1OrdinaryEtaleBaseNatural` and its pro-etale counterpart
  state the commuting square on ordinary cohomology with all four canonical edges.
- Naturality in finite coefficient maps: the global pullbacks and projection maps
  are `NatTrans`, on the whole base derived abelian-sheaf category before evaluation
  at `P.a1OrdinaryBaseComplex r`. Their type therefore includes the naturality
  equation for every base coefficient morphism. This covers the underlying maps
  of finite coefficient extensions/reductions, including different rings and
  levels, without restricting to A-linear endomorphisms or choosing generators.
  The module units are likewise the published natural adjunction units. Ring
  actions may be forgotten for cohomology and its naturality; the module unit
  invertibility and comparison are separately retained above.
- Canonical comparison: `A1OrdinaryModuleUnitsCompared` uses the recorded
  `fixedComparisonDirectImageMatePlus` and `fixedComparisonPullbackPlus`, and
  equates their composite with the actual pro-etale module unit. The underlying
  abelian version is `a1OrdinaryUnitsCompared`, using the same underived canonical
  mate and right-derived base-change construction. On cohomology the displayed
  equation says p_et^* followed by comparison equals comparison followed by
  p_proet^*. Both comparison edges are explicitly isomorphisms. The comparison
  map is the derived comparison adjunction unit followed by Leray for its actual
  restriction functor, never a chosen map between isomorphic groups.

Dependency declarations read and checked:

- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`, `WeilConjectures.PurityFiniteSetting`.
- `def-coefficient-twists-detailed`: `Sheaf.Paper.IntrinsicCoefficientTwists`, `WeilConjectures.intrinsicQbarComplexTwistFunctor`.
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`, `AlgebraicGeometry.Scheme.smallEtaleTopology`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-pbc-sites-and-cohomology`: `Sheaf.CategoryTheory.SiteCoveringAxioms`, `CategoryTheory.Precoverage.IsSiteForCoverings`.
- `def-weil-pbc-direct-image`: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, `AlgebraicGeometry.Etale.lowerStar`.
- `def-weil-derived-direct-image`: `Sheaf.Paper.SfDerivedDirectImage`, `WeilConjectures.SfIntegralDirectImage`.
- `def-sbc-affine-space`: `Mathlib/AlgebraicGeometry/AffineSpace.lean`, `AlgebraicGeometry.AffineSpace`.
- `lem-asd-etale-finite-twist-pullback`: `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`, `AlgebraicGeometry.Scheme.etaleFiniteTwistPullback`.
- `def-weil-pbc-inverse-image`: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, `AlgebraicGeometry.Etale.upperStar`.
- `def-weil-pbc-proetale-operations`: `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`, `AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback`.

The recorded intrinsic coefficient-twist module publicly imports
`CoefficientTwistsDetailed`, retaining its finite signed root-line constructions.
The existing affine-line statement uses these finite realizations through
`Scheme.finiteEtaleTateSheaf`. Its two `ModuleCat` units retain the scalar actions;
the abelian-group functors retain coefficient naturality across rings. The pro-etale
operations are the published fixed-coefficient `upperStar`/`lowerStar` adjunctions
in the ordinary sheaf model. The intrinsic constant-ring presentation's construction
and source docstrings were also read; no coefficient identification is chosen here.
The existing source's proof docstring contains all eight proof steps of the item.

Edge cases checked: arbitrary X (including empty, nonseparated and non-quasi-compact),
level n=1, levels not divisible by the ramification index, r=0 and r<0, q=0 and q<0,
identity and arbitrary base maps, and zero coefficient morphisms. The existing theorem
has no finite-type, noetherian or separation hypothesis. Its root-line annihilator is
`ringChar P.Coefficient`, so it avoids the divisibility hypothesis of the older
`P.twistEtale`. Small-site object and morphism universes remain u+1 and u.

Searches made in this session:

- `msearch.py leanfinder`: "ordinary affine line homotopy invariance finite twists derived
  direct image etale proetale"; eight etale-site/morphism hits, no exact theorem.
- `msearch.py leansearch`: "affine line homotopy invariance finite etale sheaf cohomology";
  eight hits on topological affine homotopy, etale stability and cotangent cohomology,
  with no exact theorem.
- `msearch.py loogle`: `"AffineSpace", "rightDerived"`; zero hits.
- `msearch.py grep`: `affine.*line|homotopy` in AlgebraicGeometry; one unrelated
  elliptic-curve affine-point hit.
- `rg` for `affineLineOrdinaryInvariance|a1Ordinary|lem-pur-affine-line-ordinary-invariance`
  in upstream WeilConjectures, the project's Sheaf library and upstream name index:
  the exact declaration is in the project's existing affine-line module. Upstream has
  no exact declaration with these names. The supported affine-line result is a consumer.
- Read the current blueprint's sk-prop-a1-kummer unit and lem-pur-a1-direct-image proof.
  The unit's finite-type assertion is a special case of the item's explicitly documented
  arbitrary-base refinement; the strict-local stalk argument supports this scope.

Validation: an unchanged source copy passed scompile.py in sandbox and library
positions, but the required existing-declaration import probe then found the
cross-branch duplicate described above. The final repaired module is compiled
through scompile.py in both positions, and the prescribed deliver2.py dry run
checks the server preflight. The repaired source passed sandbox and library checks with no errors or warnings
(11.2 s and 23.4 s). An additional consumer import probe checks the compiled
module for the duplicate-environment failure that the original source showed.
That probe also passed in sandbox and library positions (49.7 s and 8.5 s),
printing the full expected theorem signature with no errors or warnings.
The prescribed dry run returned `OK`: commit cd02e2882c passes the preflight
and compiles. No global build or live source edit is performed.

No new nodes, dependency modules, statement correction, or STATEMENT-DISPUTED finding.

## Second reading by NL

No independent worker was started: the dispatcher expressly prohibits other agents.
I reread the existing theorem and unfolded `A1OrdinaryInvarianceAt`: the positive
finite datum, both module units, both abelian units, both ordinary pullbacks,
comparison equality and invertibility, and the four base-naturality clauses match
the informal statement. Coefficient naturality follows from the displayed natural
transformations before evaluation at the finite twist. Only the two import paths change; all declaration bodies and signatures remain
byte-identical. The maintainer provides the independent review.
