## Worker report

The module `Sheaf.Targets.EtaleSmooth` states
`AlgebraicGeometry.Etale.isIso_baseChange_of_smooth` with proof `sorry`.
Source read: literature/upstream-master-20261014/WeilConjectures/SixFunctors/Etale/
BaseChangeTheorems/Smooth.lean, declaration at lines 55–59, together with the complete
node statement and its two proof steps. The source's `Ab` is the present `AddCommGrpCat`.
No ring coefficient binder is added: the original source's section variable Λ is not
used by this theorem.

Hypothesis and conclusion correspondence:
- X, Y, X′, Y′ are `{X Y X' Y' : Scheme.{u}}`; f, g, f′, g′ are explicitly bound
  morphisms with exactly the displayed sources and targets.
- f quasi-compact and quasi-separated: `[QuasiCompact f] [QuasiSeparated f]`.
- g smooth: `[Smooth g]`.
- The cartesian square: `sq : IsPullback g' f' f g`. In particular its commutativity
  is `g' ≫ f = f' ≫ g`; no choice of fibre product is imposed.
- K in the bounded below derived category of abelian sheaves on X_et:
  `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`.
- Homology torsion orders invertible on Y: `hK` quantifies over every integer q,
  separably closed field Ω in the scheme universe, geometric point s : Spec Ω → X,
  and element x in the geometric stalk of the degree-q homology sheaf of K, and
  requires `IsUnit (addOrderOf x : Γ(Y, ⊤))`. This is the literal expansion supplied
  by the node's proof step 1 of its named `orderInvertibleOnHomology f K` condition.
  That old upstream predicate is absent from the current published TorsionSheaf
  module (read using scompile.py --source), whose available predicates concern
  module sheaves instead. A raw-source request for that historical TorsionSheaf
  file at the source commit returned HTTP 404. This delivery relies on the explicit
  expansion in the reviewed node, and does not invent a replacement definition.
- The component at K of the canonical derived base-change transformation is an
  isomorphism: `IsIso ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K)`.
  This is the canonical map recorded by def-weil-pbc-derived-exchange. The source
  uses its equivalent monoidal mate presentation `baseChange`. That presentation
  requires MonoidalCategory and functorial flat resolutions on the coefficient
  category, which AddCommGrpCat does not carry in this library. The recorded
  derivedBaseChangeMapPlus is constructed directly by the universal property of
  the right derived functor; its formula on injective resolutions is the underived
  exchange followed by the derived unit. This gives the same canonical exchange,
  without any added tensor-structure assumption. No statement correction is needed.

Dependency declarations read and used:
- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Mathlib.CategoryTheory.Sites.Point.Basic: Point.sheafFiber; with
  Mathlib.AlgebraicGeometry.Sites.EtalePoint: Scheme.pointSmallEtale. These compute
  the stalk by the colimit over the opposite category of pointed etale neighbourhoods.
- WeilConjectures.SixFunctors.BaseChange.Derived: Etale.derivedBaseChangeMapPlus;
  Also read (not imported, because its monoidal interface is unused)
  WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs:
  Etale.baseChange, baseChangeUnitStep, pullbackSquareComparison,
  baseChangeSquareStep and baseChangeCounitStep. These give the source mate formula.
- Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories:
  allowableTorsionSheafProperty, allowableTorsionPlusProperty and
  AbelianDerivedCategoryPlusTorsionOfPrimes (proof input).
- Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange:
  Etale.boundedBelow_derived_smooth_baseChange (proof input).
- WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem:
  Etale.isIso_baseChangeHomologyMap_of_smooth (proof input).
- Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets:
  Etale.abelianDerivedBaseChangeArrow (proof input).
All recorded statement-dependency modules are imported. Modules needed only for the
proof are ordinary imports. The docstring includes both node proof steps, including
relabelling and the identification of the actual unit-square-counit map.

Edge cases: the empty scheme and zero complex are allowed. If Y is empty then X is
empty; the stalk condition is vacuous as it should be. No degree is excluded, and
no uniform lower bound or annihilator is added. The additive order of zero is 1.
An element of infinite additive order has order 0; at a geometric point its being
a unit in Γ(Y,⊤) contradicts the induced ring map to Ω. All characteristics remain
allowed, with precisely the invertible-order restriction. Site points use Type u,
coefficients use u+1, matching the source and the dependency's size convention.

Searches performed:
- msearch.py leanfinder: "smooth base change bounded below derived etale abelian
  sheaves torsion invertible order": eight hits, on ring-theoretic etale and Kahler
  differential results; no exact theorem.
- msearch.py loogle: "AlgebraicGeometry.Etale.isIso_baseChange_of_smooth": zero hits,
  unknown identifier.
- msearch.py grep: "isIso_baseChange.*smooth|orderInvertibleOnHomology": zero hits.
- msearch.py leansearch: "smooth base change derived etale sheaves torsion invertible
  order": service unavailable, Internal Server Error; not counted as a negative hit.
- rg of the same theorem/predicate names in slopmaster2/WeilConjectures and lean/Sheaf:
  no exact theorem or predicate; the ring-order target sibling is a different statement.
- rg of the item id in slopmaster2/WeilConjectures: no hits.
- Read the published TorsionSheaf module using scompile.py --source: module-sheaf
  invertible-order and prime-torsion conditions exist, but no abelian
  orderInvertibleOnHomology predicate. The hypothesis is a logical combination of
  existing homology, geometric stalk, additive order and unit definitions.

No new nodes, dependency repairs, statement corrections or disputed statements.

## Second reading by NO

I independently read the complete node and Lean module, the archived target source
`literature/upstream-master-20261014/WeilConjectures/SixFunctors/Etale/BaseChangeTheorems/Smooth.lean`,
Stacks `etale-cohomology.tex`, theorem-smooth-base-change and
lemma-smooth-base-change-general, and every statement-dependency node and its recorded
interface. The source section's coefficient ring variable is unused in the abelian
statement; the source adds no field, Noetherian, separatedness, or finite-type assumption.

Object, hypothesis and conclusion checklist (all pass):
- Schemes X, Y, X', Y': `{X Y X' Y' : Scheme.{u}}`; all four arrows are bound
  with exactly the node's domains and codomains. No additional structure on a scheme.
- The given f is qcqs: `[QuasiCompact f] [QuasiSeparated f]`, exactly these two
  assumptions. Smoothness is on the given g: `[Smooth g]`, not f or g'.
- The arbitrary cartesian square is `sq : IsPullback g' f' f g`; its equality is
  `g' ≫ f = f' ≫ g`. No chosen-pullback equality or additional square property.
- The bounded-below abelian sheaf complex on X is
  `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`.
  This is the source's Ab encoding under its current name, not module coefficients.
- Torsion orders invertible on Y: hK quantifies, in order, over q : ℤ, a separably
  closed field Ω : Type u, s : Spec Ω → X, and each element of the stalk of H^q(K).
  `Plus.homologyFunctor ... q` is the cohomology sheaf; `pointSmallEtale s` followed
  by `sheafFiber` is precisely the recorded geometric stalk. Its element's
  `addOrderOf` is required to be a unit in `Γ(Y, ⊤)`, not merely in a residue field
  or on X. This matches the explicit expansion in the node's first proof step.
- The sole conclusion is IsIso of the component at this K of
  `Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq`.
  I read BaseChange/Derived.lean, including the definition by rightDerivedDesc and
  its resolution formula, and MorphismDefs.lean, including upperStarPlusComp,
  pullbackSquareComparison, and all three steps. The source mate inserts the f'
  unit, uses the inverse composition comparison for f' then g and the forward
  comparison for g' then f, and contracts the f counit. This is the canonical
  exchange recorded by def-weil-pbc-derived-exchange with the required endpoints.
  It is not an arbitrary arrow with those endpoints. The alternative interface
  removes no hypothesis; it avoids the monoidal-only coefficient interface.

Dependency inspection: Scheme is Mathlib's scheme category. Mathlib's
pointSmallEtale has fibre the lifts of s to an etale neighbourhood; Point.sheafFiber
is the sheaf restriction of the colimit over the opposite elements category.
The allowable-torsion definitions use the same fields, points and abelian universe,
with a positive annihilator whose prime divisors lie in P. The bounded-below smooth
base-change theorem uses that full subcategory and the unbounded abelian exchange;
I read its signature and the canonical unit/composition/counit construction of
abelianDerivedBaseChangeArrow in BaseChangeMapAbelianAndSets.lean. The published
smooth-base-change theorem is the module-coefficient, degreewise proof ingredient,
not an existing copy of this target. There are no new nodes or dependency modules
in this delivery, and no statement_change to audit.

Edge cases: empty X and empty Y are allowed; Y empty forces X empty and makes hK
vacuous. The zero complex is allowed (zero has additive order 1). No index-set or
natural-degree parameter occurs. All integers q, including zero and negative
integers, are tested. Infinite additive order means addOrderOf = 0; a geometric
point would send its claimed global unit zero into a nonzero field, so it cannot
occur. No characteristic is excluded except by the required invertibility itself.
There is no uniform annihilator or extra lower-bound binder. The scheme and field
universe is u and the abelian coefficient universe is u+1, matching the source and
geometric-stalk dependency; residue separable closures in Type u give a conservative
family, so this field universe does not create a vacuous small-field condition.

Independent searches: msearch leanfinder query "etale smooth base change derived
direct image stalk torsion" returned eight ring-theoretic etale hits, none this
statement. Loogle query "IsIso (AlgebraicGeometry.Etale.derivedBaseChangeMapPlus _ _)"
returned unknown identifier IsIso, so I do not count it as negative evidence.
Direct rg of Mathlib, slopmaster2/WeilConjectures and lean/Sheaf for
isIso_baseChange_of_smooth and orderInvertibleOnHomology found only the distinct
ring-order target sibling. Broader rg for smooth/base-change and torsion/order
found the degreewise module theorem and the bounded-below allowable-torsion theorem
already inspected above, not this statement. The historical target is reference
material, not a published current declaration. The wrapper's source request for
BaseChangeTheorems.Smooth confirms it is unavailable in the current library.

No mismatch found; no Lean or node changes. The module contains one named theorem
with whole proof sorry, no definition or local notation/instance, and a source and
blueprint docstring carrying both proof steps. All binders and universe variables
are bound. The node's lean.statement is verbatim the file signature.
Validation: scompile.py NO nt-target-etale-smooth
lean/Sheaf/Targets/EtaleSmooth.lean completed cleanly (sandbox and library passes).
