## Worker report

The module states `CategoryTheory.derivedInternalHom_restrict_open`, with `sorry` only.
The statement is Stacks Cohomology Lemma 20.42.3, Tag 08DL
(https://stacks.math.columbia.edu/tag/08DL), opened online because the local
literature/stacks-project/cohomology.tex is absent. No statement correction is needed.

Hypothesis and clause mapping:
- A ringed space (X,O_X) is `X : RingedSpace.{u}`; this is Mathlib's
  `SheafedSpace CommRingCat`, with sheaf `X.sheaf`, not a locally ringed hypothesis.
- The open subset is `U : Opens X`, including the empty and whole open.
- The module category is `SheafOfModules.{u} (moduleRings X)`;
  `moduleRings` is the shared forgetful image of the structure sheaf.
- The two objects are `K L : DerivedCategory (SheafOfModules.{u} (moduleRings X))`.
  Both `HasDerivedCategory.{w}` binders specify the localization/morphism-size
  choices for X and the open; they impose no geometric or boundedness condition.
- Termwise restrictions are `(SheafOfModules.overFunctor (moduleRings X) U).
  mapDerivedCategory.obj K` and the same for L. `mapDerivedCategoryFactors`
  identifies these with termwise restriction on representatives.
- The left side is `derivedInternalHom` on `(Opens.grothendieckTopology X).over U`
  with commutative sheaf `X.sheaf.over U`, applied to the two restricted objects.
  This localized site is the site of opens contained in U, equivalently opens of U.
- The right side is `mapDerivedCategory.obj` of
  `(derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj (op K,L)`.
- `Nonempty (left ≅ right)` asserts the isomorphism in D(O_U). The docstring
  records the canonical construction by restriction of sheaf Hom complexes.
  The explicit instance `hU` supplies the SAME derived category to the left side:
  forgetting to rings after restriction and restricting after forgetting have
  definitionally equal sheaf objects (checked by a scratch `rfl` on the server),
  though typeclass search does not unfold them automatically.

Dependency declarations inspected and used:
- Mathlib.Geometry.RingedSpace.Basic: `AlgebraicGeometry.RingedSpace`;
  Mathlib.Geometry.RingedSpace.LocallyRingedSpace: `LocallyRingedSpace.Hom`
  (the dependency also supplies the ringed-space notion, no morphism is needed).
- Mathlib.Algebra.Category.ModuleCat.Sheaf: `SheafOfModules`, its `Hom` and category;
  this is the dependency's general-site mathlib_match, as its lean note permits.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, and its localization instance.
- Sheaf.Algebra.Homology.DerivedInternalHom: `CategoryTheory.derivedInternalHom`;
  full signature and its computation/representative-independence docstrings read.
- Sheaf.Paper.DerivedHomMayerVietoris: `AlgebraicGeometry.moduleRings` and shared
  `moduleOverFunctor_additive`, `moduleOverFunctor_limits`, `moduleOverFunctor_colimits`.
- Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous:
  `SheafOfModules.overFunctor`, restriction on the localized site.
- Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor: `Functor.mapDerivedCategory`.

Edge cases: U empty, U whole, X empty, K or L zero, and arbitrary unbounded
complexes are all admitted. No finite-type, scheme, perfectness, boundedness,
nonempty, or locality hypotheses occur. The universes u and w are explicitly bound.

Searches (2026-10-11):
- msearch leanfinder: "derived internal Hom sheaves of modules commutes with
  restriction to an open subset": 8 hits (unitHomEquiv, LightCondensed.ihom,
  restrictScalars and Tilde restriction), none stating this result.
- msearch loogle: "SheafOfModules.overFunctor, CategoryTheory.derivedInternalHom":
  zero hits; derivedInternalHom unknown to the public index.
- msearch leansearch: "derived internal Hom commutes with restriction to an open
  subset": service unavailable (Internal Server Error).
- msearch grep: "derivedInternalHom|RHom|internalHom.*restrict": 25 unrelated
  matches such as congrHom and Over.tensorHom; no match.
- Direct rg in Mathlib/Algebra/Homology for derivedInternalHom or RHom restriction:
  no hits. Direct rg in WeilConjectures for the item id or proposed declaration:
  no hits. Direct rg in lean/Sheaf for derivedInternalHom and restriction:
  the existing definition and object-computation theorem, but no open-restriction theorem.

The server single-file compilation is clean. No new notion or dependency module
was needed, and no statement fault or disputed statement was found.

## Earlier second reading (a previous round; superseded)

Read the sandbox node and module, each of the four statement-dependency nodes,
and the declarations they record. The local Stacks checkout is absent. I fetched
the actual `cohomology.tex` into this item's scratchpad from
https://raw.githubusercontent.com/stacks/stacks-project/master/cohomology.tex
and read lines 10543--10651 (the section's standing assumptions, construction,
and `lemma-restriction-RHom-to-U`) and 7840--7855 (the K-injective restriction
input). I also checked https://stacks.math.columbia.edu/tag/08DL. The source
assumes an arbitrary ringed space and arbitrary objects of its unbounded derived
category, with no further geometric, finiteness, or boundedness hypothesis.
There is no statement correction in this delivery.

Object, hypothesis, and conclusion checklist:

1. A topological space with a sheaf of commutative rings: `X : RingedSpace.{u}`.
   Verdict: matches. `RingedSpace` in Mathlib's `Geometry/RingedSpace/Basic.lean`
   is `SheafedSpace CommRingCat`, the ringed-space clause of
   `def-weil-locally-ringed-space-morphism`. I opened that node and
   `LocallyRingedSpace.Hom`; its stalk-locality field is not imposed here.
2. Sheaves of O_X-modules: `SheafOfModules.{u} (moduleRings X)`.
   Verdict: matches. The dependency's lean note explicitly permits the general
   site `SheafOfModules` carrier in its mathlib_match, rather than forcing the
   scheme-only `Scheme.Modules` abbreviation. I read `SheafOfModules`, `Hom`,
   and the category instance: module-valued presheaves whose underlying abelian
   presheaf is a sheaf, with sectionwise linear morphisms. The shared
   `moduleRings` only forgets commutativity of X's actual structure sheaf.
3. Two arbitrary derived objects: `K L : DerivedCategory (SheafOfModules.{u}
   (moduleRings X))`. Verdict: matches. `DerivedCategory` localizes all
   Z-indexed cochain complexes at quasi-isomorphisms. There is no D-plus,
   quasi-coherence, perfectness, or scheme restriction.
4. An arbitrary open U: `U : Opens X`. Verdict: matches. No nonemptiness,
   affine, compactness, or proper-open condition is present. Its position before
   K and L among universal binders does not change the quantification.
5. The two termwise restrictions: each occurrence of
   `(SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory.obj`.
   Verdict: matches. I read `overFunctor` in PushforwardContinuous and
   `mapDerivedCategory` and `mapDerivedCategoryFactors` in ExactFunctor.
   The former precomposes sections with `Over.forget U`; the latter is the
   localization of its degreewise complex functor. The shared additive,
   finite-limit and finite-colimit instances in DerivedHomMayerVietoris supply
   exactness, without an extra hypothesis or a duplicate restriction definition.
6. O_U and D(O_U): `(X.sheaf.over U)` on
   `(Opens.grothendieckTopology X).over U`, and its module derived category.
   Verdict: matches. An object of `Over U` is precisely an open V of X contained
   in U; its coverings are the original coverings of V, as checked in
   `GrothendieckTopology.over` in Sites/Over.lean. This is the open-subspace site
   of U. Forgetting commutativity after `over` and doing so before `over` give
   the same ring sheaf; explicit `@derivedInternalHom ... hU` uses the same
   derived-category instance as the right side, rather than another localization.
7. Size choices: the two `HasDerivedCategory.{w}` binders.
   Verdict: matches the abstract-derived-category dependency's chosen-universe
   convention. I read `HasDerivedCategory`, `standard`, `DerivedCategory`, and Q.
   These choose localizations and impose no property on X, U, K, or L. Both
   sites and module carriers can be raised to a common universe; u and w are
   explicitly bound and no finite universe is fixed.
8. Left side: `(@derivedInternalHom ... (X.sheaf.over U) hU).obj
   (op (restriction.obj K), restriction.obj L)`.
   Verdict: exactly R-sheaf-Hom on U, contravariant in K and covariant in L.
   I read the shared definition, its localization construction, comparison
   statement and object-computation statement; it is not global derived Hom.
9. Right side: `restriction.obj ((derivedInternalHom ... X.sheaf).obj (op K,L))`.
   Verdict: exactly the restriction of R-sheaf-Hom on X. Both sides are objects
   of the same D(O_U), and the isomorphism has the node's orientation.
10. Conclusion: `Nonempty (left ≅ right)`.
    Verdict: the asserted object isomorphism, using the project's proposition
    encoding of isomorphisms. Its canonical construction is the restriction of
    the Hom complex, spelled out in the docstring, not a claim that every
    isomorphism between these objects is equal. The source states this as an
    object identification, with no separately quantified coherence condition.

Edge cases: U = bottom, U = top, and X empty all remain available; the empty
open still has its localized open site. Either derived object can be zero.
All integer cochain degrees, including zero and negative degrees, are allowed;
there is no n binder or positive-degree restriction. All characteristics and
the zero structure ring are admitted. There is no finite-index assumption;
the Hom complex's Z-indexed products come from the shared definition. Universe
levels are explicit, and no unbound variables or file-local notation occur.

Independent searches, using wording different from the first reader:

- `msearch leanfinder`: "R sheaf Hom localized site open subset derived category
  isomorphism" returned eight dense-subsite/sheaf-Hom equivalence hits, none
  computing derived internal Hom under open restriction.
- `msearch leansearch`: "restriction of derived sheaf Hom to open subsets"
  was unavailable (Internal Server Error); no negative mathematical verdict
  is inferred from that outage.
- `msearch loogle`: "SheafOfModules.overFunctor" returned the restriction
  functor, its composition isomorphism, and the scheme open-equivalence
  comparison. These confirm the existing restriction carrier, not this theorem.
- Direct `rg` for `RHom`, `derivedInternalHom`, and both orders of derived Hom
  and restriction across Mathlib/Algebra/Homology, WeilConjectures, and
  lean/Sheaf found the shared definition and related scheme/etale material.
  In particular I opened upstream
  `nonempty_iso_mapDerivedCategory_upperStar_derivedHom` in
  WeilConjectures/SixFunctors/Etale/Derived/Stability.lean: it concerns sheaves
  on a scheme's small etale site with coefficient-category hypotheses and an
  open scheme immersion. It does not state this arbitrary-ringed-space,
  structure-sheaf-module result, so `existing: true` would be incorrect.

H5--H9: the delivered module introduces no definitions or instances, and its
only theorem proof is `sorry`. Both imports are used: DerivedInternalHom gives
the existing bifunctor, and DerivedHomMayerVietoris gives moduleRings and the
shared exactness instances. Module and declaration docstrings name 08DL and
the blueprint id. The four proof paragraphs track the node's four proof steps:
K-injective replacement, its preservation and quasi-isomorphism after exact
restriction, termwise Hom/product/differential comparison, and passage to the
localization with representative independence. All lines satisfy the length
convention. No new definition nodes or dependency modules need review.

Mismatches and changes: none found in the node or Lean statement. I preserved
the correct module and lean record and appended this independent reading.
The node's `lean.statement` agrees verbatim with the module signature.
The prescribed server single-file compile succeeded in 2.5 seconds with no
errors or warnings. The first compile invocation used a relative filename
from the read-only repository and therefore could not open the sandbox module;
rerunning with its absolute sandbox path succeeded.

Delivery gate: three subsequent `deliver2.py ... --no-push` attempts failed
in the server compile before preflight, including a retry after 30 seconds.
The server reported that
`local/build/H1/Sheaf/Algebra/Homology/DerivedInternalHom.olean` does not exist.
This differs from the successful standalone compile immediately beforehand.
No dependency source was copied or restated to bypass the missing build
artifact; no branch was pushed. Delivery is blocked by that server artifact.

## Second reading by H1

I independently opened the item node, its module, all four statement-dependency
nodes and their recorded declarations. I read the actual Stacks cohomology.tex
in this sandbox's scratchpad: the standing assumptions and construction in
section-internal-hom, lemma-restriction-RHom-to-U (08DL), and
lemma-restrict-K-injective-to-open (08BS). No statement correction is present
or required. There are no new definition nodes or dependency modules.

Objects, hypotheses and conclusion, matched individually:

1. Ringed space (X,O_X): `X : RingedSpace.{u}`. PASS. Basic.lean defines
   RingedSpace as SheafedSpace CommRingCat. The dependency node includes this
   notion; no locally-ringed stalk condition is assumed by this theorem.
2. Sheaves of O_X-modules: `SheafOfModules.{u} (moduleRings X)`. PASS.
   I read SheafOfModules and Hom in Mathlib: module-valued presheaves with the
   abelian sheaf condition and sectionwise linear morphisms. The dependency's
   lean.note expressly selects this carrier for general ringed spaces.
   `moduleRings` in DerivedHomMayerVietoris forgets only commutativity of X.sheaf.
3. K,L in unbounded D(O_X): the `K L : DerivedCategory ...` binder. PASS.
   Basic.lean localizes integer cochain complexes at quasi-isomorphisms, with
   no boundedness, coherence, finiteness or perfectness restriction.
4. Any open U: `U : Opens X`. PASS. No nonemptiness or compactness binder.
   Reordering universal U before K,L does not alter their quantification.
5. Termwise restrictions K|_U,L|_U: the two overFunctor.mapDerivedCategory.obj
   terms. PASS. I opened overFunctor in PushforwardContinuous.lean and
   mapDerivedCategory and mapDerivedCategoryFactors in ExactFunctor.lean:
   they restrict sections to Over U and descend the degreewise exact functor.
   Shared moduleOverFunctor additive/limits/colimits instances supply exactness.
6. Structure sheaf on U and its derived category: `X.sheaf.over U` on
   `(Opens.grothendieckTopology X).over U`. PASS. Over U consists of opens
   contained in U. Forgetting commutativity and restricting commute; explicit
   `hU` supplies the same localization instance to both sides of the iso.
7. Derived internal Hom: the shared `derivedInternalHom` on each site. PASS.
   I read its definition and comparison/obj_iso signatures. It descends the
   sheaf Hom complex with functorial K-injective replacement, contravariant
   in K and covariant in L. It is internal sheaf Hom, not global Hom.
8. Conclusion on U: `Nonempty (restricted-site derivedInternalHom.obj ... ≅
   restriction.obj (derivedInternalHom.obj (op K,L)))`. PASS. Orientation and
   both arguments match 08DL. Nonempty is the proposition expressing the
   object identification; the docstring records the canonical construction
   from restriction of local maps and its naturality/independence.
9. Size hypotheses: both HasDerivedCategory.{w} instances. PASS. I read
   HasDerivedCategory.standard and Q: these choose the localization in the
   node's chosen morphism universe, without a geometric assumption. u,w
   are bound explicitly; every space, ring and module family fits after a
   common universe enlargement.

Edge cases: empty X, U = bottom or top, zero K or L, arbitrary negative and
zero cochain degrees, all ring characteristics, and the zero ring are allowed.
There is no index-set or n hypothesis. No unbound variable or universe remains.

Independent searches this reading:
- msearch leanfinder: "internal sheaf Hom derived localization to an open
  subspace" returned eight ordinary sheafHom/sheafOver hits, no derived result.
- msearch loogle: "SheafOfModules.overFunctor" returned the shared restriction
  functor, overFunctorMap, and the scheme overFunctorEquiv; no exact theorem.
- msearch leansearch: "derived sheaf Hom and restriction to an open subspace"
  returned service unavailable (Internal Server Error), not a no-match verdict.
- Direct rg for derivedInternalHom, RHom and the upstream open-restriction
  declaration across Mathlib/Algebra/Homology, WeilConjectures and lean/Sheaf
  found the shared definition and related scheme/etale statements, no match.
  I opened Etale/Derived/Stability/Basic.lean's
  nonempty_iso_mapDerivedCategory_upperStar_derivedHom: its small-etale scheme
  and coefficient-category assumptions differ from arbitrary O_X-modules on
  a ringed space, so it cannot replace this module as an existing declaration.

H5-H9: no new data definition, private copy, local notation or local instance;
only one theorem, with sorry proof. Both imports are used. Source and blueprint
appear in both docstrings; the four proof steps include K-injective replacement,
exact restriction preserving that resolution, Hom-complex products/differentials,
and localization with canonical independence. No line exceeds 100 characters.
The node lean.statement was compared programmatically with the complete literal
signature and is identical. No mismatch found; the Lean and node are preserved.
Only this report section was appended. The prescribed scompile invocation with
an absolute sandbox filename passed in 2.5 seconds, exit 0, without warnings.
