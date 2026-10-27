## Worker report

The module Sheaf.Paper.OpenSquareSupportScalarCounit states the complete node as
AlgebraicGeometry.ProEtale.CondensedRing.openSquare_support_scalar_counit.
Its only postponed proof is this theorem. The helper definitions construct the
specified arrows or expand the clauses of this same node; none contains sorry.
The node statement, statement dependencies, proof and proof dependencies are unchanged.

Hypotheses and objects, clause by clause:

- The universe u is explicitly declared. The small pro-etale sites are
  Scheme.ProEt.topology T, with Ab.{u+1} as in the recorded framework. No equality
  of object and morphism universes is imposed.
- An arbitrary commutative condensed ring is R : Sheaf (coherentTopology
  Profinite.{u}) Ab.{u+1}, with MonObj R and IsCommMonObj R. The coefficient on T
  is exactly condensedRingObj R T. Modules are the recorded internal Mod category.
- The ordinary derived category is DerivedCategory of those modules; M ranges
  over DerivedCategory.Plus and M.obj is its actual unbounded inclusion. This
  includes arbitrary bounded-below objects, rather than only bounded complexes.
- Noetherian Y is [IsLocallyNoetherian Y] [CompactSpace Y]. The maps j and c carry
  [IsOpenImmersion j] and [IsOpenImmersion c]. W is the chosen pullback j c,
  b = pullback.fst j c and a = pullback.snd j c. Their open-immersion instances
  follow from base change; they are not extra hypotheses.
- The reduced closed complement is i : Z to Y with [IsClosedImmersion i],
  [IsReduced Z] and hcomplement : Set.range i = (Set.range c)ᶜ. This parameterizes
  exactly the reduced closed complement, independently of its isomorphic presentation.
- openSquareB is the exact, termwise b_! followed by the recorded actual
  moduleObjectDerivedPushforward R j. openSquareA is Ra_* followed by exact c_!.
- openSquareOpenUnitIso is asIso of the actual derived open unit; the existing
  full-faithfulness theorem and derived-unit instance justify it without sorry.
- openSquareRho is the recorded derivedDirectImageOpenRestriction for jb=ca,
  whiskered by b_!, followed by Ra_* of that unit's inverse. OpenSquareRhoFamily
  is the type of isomorphisms with these endpoints on D^+(W,R), and the first
  conjunct of OpenSquareCounitAssertions pins every hom to this exact map.
  Thus the existential family introduces no arbitrary comparison or data choice.
- openSquareCounit applies the inverse Hom bijection of the published actual
  derivedOpenImmersionLowerShriekUpperStarAdjunction to rho.inv. The second
  conjunct states exactly c_!(rho.inv) followed by the actual counit.
- The next two conjuncts explicitly state naturality of rho and of this e for
  every morphism in D^+(W,R), using mu.hom for its unbounded image.
- The last conjunct is IsZero of actual exact closed restriction of B implies
  IsIso e. This is the only occurrence of a support hypothesis.
- A scalar map is arbitrary phi : R to R' with IsMonHom phi; no flatness,
  finiteness or admissibility is assumed. openSquareRes is termwise derived
  Mod.comap of coefficientMap phi T. This is the internal-module realization of
  the same sectionwise restriction-of-scalars notion as SheafOfModules.restrictScalars.
- openSquarePushScalar is a real mate construction from the existing
  derivedComapUpperStarIso and the exact-left actual derived geometric
  adjunctions. It does not use the older flat-only derivedComapLowerStarIso.
  OpenSquareScalarAssertions supplies isomorphisms hj and ha whose homs are
  exactly these canonical maps. They are conclusions, never added assumptions.
- openSquareShriekScalar derives the existing comapOpenImmersionLowerShriekIso
  using canonical derived-composite comparisons. This is the identical underlying
  open-extension comparison, not a chosen isomorphism between endpoints.
- OpenSquareScalarUnderivedOpenAdjunction writes out both ordinary unit and
  counit preservation equations for b and c. OpenSquareScalarOpenAdjunction
  writes out their derived versions using the same actual adjunctions.
- The rho scalar equation uses the existing inverse-image scalar comparison,
  openSquareBScalar, and the specified rho map on Res M'. No unspecified transport
  is hidden in this equation.
- For every M, M' in their respective D^+ categories and every unbounded derived
  arrow mu : M.obj to Res_W M'.obj, the final equality is
  A_R(mu); ASscalar.inv; Res_Y(e_R'); BScalar.hom = e_R; B_R(mu).
  Here openSquareAScalar and openSquareBScalar are exactly the composites of ha,
  hj and the canonical open-extension comparisons. This is precisely the node's
  mixed equation with all endpoint comparisons inserted. There is no support
  premise and no scalar-extension/direct-image assertion.

Recorded statement dependencies used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme, Scheme.Hom.
- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt and Scheme.ProEt.topology.
- Sheaf.Topology.ProfiniteCondensedRing: Profinite.CondensedRing, with its unbundled
  commutative ring-object representation used here.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic: coefficientRing,
  condensedRingObj and its commutative monoid-object instances.
- Mathlib.CategoryTheory.Monoidal.Mod: CategoryTheory.Mod.
- Sheaf.Paper.CondensedModuleDerivedPushpull: moduleObjectDerivedPushforward;
  inverse image uses the existing exact mapDerivedCategory realization, with its
  canonical identification with moduleObjectDerivedPullback publicly available.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs:
  openImmersionLowerShriek and its exactness instances.
- Mathlib.AlgebraicGeometry.OpenImmersion: AlgebraicGeometry.IsOpenImmersion.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: AlgebraicGeometry.IsClosedImmersion.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: pullback, fst, snd.
- Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings:
  SheafOfModules.restrictScalars; its internal realization is Mod.comap, preserving
  the underlying abelian sheaf and changing only its action.
- Mathlib.AlgebraicGeometry.Noetherian: AlgebraicGeometry.IsLocallyNoetherian.
- Mathlib.Topology.Defs.Filter: CompactSpace.
- Sheaf.Paper.DerivedDirectImageOpenCoherence: derivedDirectImageOpenRestriction,
  the actual mate defined by def-sfb-open-square-restriction-mates.

Additional canonical constructions are from the existing upstream
ModuleObject.ChangeOfCoefficients (coefficientMap, comapUpperStarIso,
derivedComapUpperStarIso, comapOpenImmersionLowerShriekIso),
Derived.OpenImmersionLowerShriek (actual derived open adjunction),
Derived.OpenImmersionEssImage (full faithfulness), and RightDerivedFunctor.Adjunction
(the exact-left derived geometric adjunction). Stated proof dependency modules
are imported privately, including section normalization, scalar-adjunction
transport, ringed open/closed, ring-sheaf change adjunction and mate pasting.
No upstream or shared file is changed.

Edge cases checked before finalizing: O=Y gives the identity-open counit;
O empty forces B=0 in the supported conclusion; V or W empty and M=0 give the
zero maps and their expected invertibility when applicable. The scalar parameter
admits identity maps and nonflat maps such as Z to Z/n. In particular no
PreservesFiniteLimits of scalar extension or preservation of K-injectives by
restriction appears. Arbitrary mu is retained, including zero and identity.

Searches made:

- msearch.py leanfinder: "For an open square of pro-etale module sheaves the
  extension by zero counit is invertible on supported objects and commutes with
  restriction of scalars". Eight hits, including Scheme.Modules Zariski
  restriction counits and ordinary ModuleCat scalar counits, none this statement.
- msearch.py loogle: "CategoryTheory.Adjunction.counit, CategoryTheory.Mod.comap".
  Zero hits.
- msearch.py grep: "(openImmersion|extensionByZero).*(counit|restrictScalars)|restrictScalars.*counit".
  Eight hits, ordinary algebraic scalar counits, no matching pro-etale theorem.
- rg in WeilConjectures and Sheaf for this exact node id, OpenSquareRhoFamily,
  openSquarePushScalar and openSquare_support_scalar_counit: no declaration.
- rg for open/support/counit and scalar compatibility, and inspection of the
  complete ChangeOfCoefficients interface: the ordinary comparisons are already
  present; the derived direct-image comparison there assumes flat coefficients,
  and neither it nor the open-base-change counit results states this node.

Source checked: the current blueprint paragraph (3), the node's complete nine-step
proof, and the recorded dependency declarations and docstrings. No statement
correction, new independent notion, dependency replacement or disputed statement
is needed. The previous stage-1 refusal does not forbid a stage-2 Lean attachment:
this delivery preserves the reviewed Q143 split verbatim.

Validation: scompile.py compiled both the sandbox probe and the actual library module
cleanly (14.4 seconds and 11.9 seconds respectively); no extra warnings.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
