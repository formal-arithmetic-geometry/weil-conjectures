## Worker report

The module [PurLisseMorphismRigidity.lean](lean/Sheaf/Paper/PurLisseMorphismRigidity.lean)
introduces the canonical terminal-object coefficient type, the underlying fixed-coefficient
module sheaf and its map, the induced geometric-stalk map, and the underlying ordinary
internal Hom.  `PurityFiniteLisse` renders “locally constant with finite geometric stalks”
using `IsLocallyConstantProEtaleFixedModuleSheaf` and
`proEtaleGeometricFixedModuleStalk`.  `PurityVanishingAtComponent` packages one geometric
point whose image lies in the connected component of a chosen point.  The main theorem has
`sorry` as required for stage 2.

The theorem hypotheses render the finite coefficient setting by `P : PurityFiniteSetting`,
`T` as a scheme over `Spec P.field.k` by `[T.Over ...]`, separatedness by
`[IsSeparated (T ↘ Spec ...)]`, and finite type by the locally-finite-type and quasi-compact
instances.  `L` and `M` are modules in
`proEtaleRingModules T (proEtaleConstantRing T P.Ring)`, and `hL`, `hM` state finite local
constancy and finite geometric stalks.

Clause (1) is `PurityFiniteLisse P T (SheafOfModules.homObj (R :=
proEtaleConstantRing T P.Ring) L M)`.  The underlying sheaf is obtained by the canonical
`SheafOfModules.forgetToSheafModuleCat` at the terminal pro-etale object, and the Hom is
`SheafOfModules.homObj`, matching the ordinary sheaf Hom dependency.

Clause (2) is the conjunction whose first part says that every `f : L ⟶ M` with
`PurityVanishingAtComponent P T L M f x` for every `x : T` is zero.  The component predicate
uses `connectedComponent x`, the range of the underlying topological map of a geometric
point, and `purityProEtaleStalkMap ... f = 0`.  Its second part states the connected-case
corollary: under `ConnectedSpace T`, two maps whose stalk maps agree at one geometric point
are equal.

Recorded dependency declarations used:

- `WeilConjectures.PurityFiniteSetting` from `Sheaf.Paper.PurityFiniteSetting`.
- `AlgebraicGeometry.Scheme.proEtaleDerivedCategory` from
  `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` (the pro-etale site/coefficient setup).
- `AlgebraicGeometry.Scheme.IsLocallyConstantProEtaleFixedModuleSheaf` from
  `Sheaf.Paper.ProEtaleFixedModuleLocalConstancy`.
- `AlgebraicGeometry.Scheme.proEtaleGeometricStalk` and its neighbourhood/stalk declarations
  from `Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk`.
- `SheafOfModules.homObj` from
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`.
- `ConnectedSpace` and `connectedComponent` from Mathlib topology.
- `AlgebraicGeometry.IsProper`, `LocallyOfFiniteType`, and `QuasiCompact` are the recorded
  Mathlib morphism declarations; the theorem uses the separated and finite-type instances
  explicitly, as the node’s “separated finite-type” wording requires.
- `Padic.finite_coefficientExtensionRing` is supplied by the recorded l-adic dependency
  module through the finite setting imports.

Edge cases checked in the statement: the empty scheme makes the component quantifier
vacuous; `connectedComponent` is Mathlib’s nonempty maximal connected subset (so the empty
space is not treated as connected); no nonempty or connected hypothesis is imposed for clause
(1); and the geometric-point and finite-stalk quantifiers retain the source universe `Type u`.
The zero morphism and zero stalk map are the categorical zeroes in the module categories.

Searches made:

- `msearch.py ... leanfinder` for internal Hom of finite locally constant module sheaves:
  condensed and free-module Hom results only; no matching theorem.
- `msearch.py ... loogle` for `CategoryTheory.Sheaf`, `CategoryTheory.MonoidalClosed`,
  and `CategoryTheory.constantSheaf, ModuleCat`: no matching arbitrary-site rigidity theorem.
- `msearch.py ... grep` for locally-constant/Hom and constant-sheaf Hom patterns in Mathlib:
  no matching declaration.
- `rg` over `WeilConjectures/` and `lean/Sheaf/` for lisse, pro-etale stalk, internal Hom,
  and rigidity names: found the recorded site/stalk/Hom infrastructure, but no statement of
  this node.
- DAG grep for `lem-pur-lisse-morphism-rigidity`: found only this split node and its proof
  references; no existing Lean declaration.

## Earlier second reading (a previous round; superseded)

The statement was checked against the source node clause by clause. The finite coefficient
setting is represented by `PurityFiniteSetting`; separated finite-type hypotheses are the
explicit separated, locally-finite-type, and quasi-compact instances on the structure map.
The internal Hom is `SheafOfModules.homObj` on the ordinary module-sheaf category, and
finite local constancy is exactly local constancy plus finite geometric stalks. The vanishing
condition quantifies one geometric point in each connected component, and the connected
corollary compares two maps at one stalk. No extra connectedness, nonemptiness, or derived
category hypothesis was added.

## Second reading by Q29

I independently read the current DAG node, its seven proof steps, the sandbox module,
all nine statement dependency records, and their actual declarations. This section
supersedes the first worker's description of terminal-object coefficients above.
The natural-language statement and its dependency lists needed no correction.
There are no new nodes or dependency modules in this delivery.

Source reading: the restored master blueprint node is the separated finite-type
rigidity lemma, with both ordinary Hom and morphism conclusions. I read the local
Stacks sources in the launcher's literature mirror: `sites-modules.tex`, Tags 093S
and 093T, and Tag 0E8H (restriction of internal Hom); `proetale.tex`, Tag 099Y;
`etale-cohomology.tex`, Tags 03PR, 03PT and 03Q1; and `morphisms.tex`, Tag 03WT.
093T assumes a site, a ring, and finite presentation of the source module; 093S(3)
assumes a final object and finite type of the source. 099Y compares finitely
presented locally constant module sheaves for any scheme and ring. No freeness,
properness, or extra characteristic assumption is implicit in these source lemmas.
Over the node's finite coefficient ring a finite module is finitely presented,
by the finite free presentation and finite kernel argument recorded in the DAG.
03PT is the exactness/sheafification-stalk lemma, rather than a separately named
constant-stalk theorem; its sheafification clause supplies that computation.

Object, hypothesis, and conclusion list, matched to the final Lean:

| Node item | Lean rendering and verdict |
|---|---|
| Fixed finite field datum and finite coefficients A = O_E/(varpi_E^n), n >= 1, ell different from p | `P : PurityFiniteSetting.{u}`. I opened its structure, `FiniteFieldDatum`, `CoefficientDatum`, and `PurityFiniteSetting.Ring`: these bundle the actual finite field and algebraic closure, prime ell different from p, finite subextension of the fixed coefficient closure, and positive level. `P.Ring` is the existing quotient construction. Exact. |
| A k-scheme T | `(T : Scheme.{u}) [T.Over (Spec (CommRingCat.of P.field.k))]`. This is the chosen structure map to the specified k. Exact. |
| T separated | `[IsSeparated (T ↘ Spec (CommRingCat.of P.field.k))]`. I read `IsSeparated` in Mathlib: its diagonal is a closed immersion. No properness is assumed. Exact. |
| T finite type | The `LocallyOfFiniteType` and `QuasiCompact` instances on that same structure map. I read both Mathlib classes and the dependency record; together these are precisely finite type. Exact. |
| Small pro-etale site and constant coefficient ring sheaf | `proEtaleRingModules T (proEtaleConstantRing T P.Ring)`. I opened `proEtaleRingModules`, `ringedSiteModules`, `proEtaleConstantRing`, and `proEtaleDerivedCategory`: this is ordinary `SheafOfModules` over the sheafified constant `CommRingCat` ring, with the standard ULift of P.Ring. Exact, without a derived-category hypothesis. |
| Two ordinary module sheaves L and M | `(L M : proEtaleRingModules T (proEtaleConstantRing T P.Ring))`. Morphisms are sectionwise linear natural maps in this ordinary category. Exact. |
| Both locally constant as modules over A_T | `hL`, `hM`, through the first conjunct of `PurityFiniteLisse`: `IsLocallyConstantProEtaleModuleSheaf T P.Ring F`. I opened the public ringed-site predicate retained by the recorded fixed-module dependency: it requires a pro-etale cover and module-sheaf isomorphisms of localized restrictions with the sheafified constant modules. This is exactly the dependency node, without a rank or freeness restriction. Repaired. |
| Finite underlying sets at every geometric stalk | The second conjunct of `PurityFiniteLisse`: for all `Ω : Type u`, `[Field Ω]`, `[IsAlgClosed Ω]`, and `y : Spec (.of Ω) ⟶ T`, `Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing T P.Ring) F)`. I opened the stalk definition: it restricts the existing module presheaf to pointed weakly etale neighbourhoods and takes the existing module colimit over their opposite category. This is finiteness of the underlying set, not finite generation or finite rank. Exact. |
| Clause (1), ordinary internal Hom is finite locally constant | `PurityFiniteLisse P T (SheafOfModules.homObj (R := proEtaleConstantRing T P.Ring) L M)`. I opened the upstream `homObj`: its values are linear sheaf maps on the localized ringed site, with the usual scalar action. Both local constancy and stalk finiteness are asserted. Exact. |
| Clause (2), vanishing at one geometric point of every component implies zero | For every `f : L ⟶ M`, `(∀ x : T, PurityVanishingAtComponent P T L M f x) → f = 0`. The component predicate existentially binds an algebraically closed field and a geometric point whose image lies in `connectedComponent x`, and requires the induced stalk map to be zero. Spec of a field has one nonempty underlying point, so this says that each component contains a vanishing geometric point. Quantifying over x is equivalent to quantifying over components: the witness can be reused for every x in that component. Exact. |
| Clause (2), connected corollary for any two maps agreeing at one geometric point | `ConnectedSpace T → ∀ f g Ω ... y, purityProEtaleStalkMap P T y f = purityProEtaleStalkMap P T y g → f = g`. I opened `ConnectedSpace` and `connectedComponent`: the former includes nonemptiness and the latter is the union of connected subsets through x, hence the maximal connected subset. The one specified point and both arbitrary maps occur in the correct order. Exact. |

The canonical `purityProEtaleStalkMap` now applies the same
`PresheafOfModules.colimitFunctor` as `proEtaleGeometricModuleStalk` to the
sectionwise map after `pushforward₀` along the pointed-neighbourhood forgetful
functor. Its source and target are those precise module stalks over the stalk
ring. There is no arbitrary map, chosen comparison isomorphism, or hollow data.

Edge cases checked: empty T is allowed in (1) and in the first implication of
(2), where the component quantifier is empty; the empty-cover sheaf axiom handles
its morphisms. The connected corollary has the dependency's nonempty notion of
connectedness. Zero modules and zero morphisms are allowed, and `Finite` does not
exclude singleton zero stalks. Neither a nonempty cover index nor a positive rank
is required. All n >= 1 are included; n = 0 is excluded by the stated purity
conventions themselves, not by a new Lean assumption. The characteristic data
are exactly those in P; no new invertibility hypothesis was added. Scheme and
geometric-point fields remain in the chosen bound u, while the site objects and
module values use u+1 and site morphisms use u. The module-stalk construction
already handles these different universes, so no equality of site universes or
extra smallness assumption was imposed. Every binder and universe is explicit
with `autoImplicit false`.

Independent searches (in addition to the first worker's logged searches):

- `msearch.py ... leansearch` for a morphism of locally constant finite sheaves
  determined by one stalk per connected component: service returned Internal
  Server Error, recorded as unavailable; no negative mathematical verdict inferred.
- `msearch.py ... leanfinder` for the sheaf of linear morphisms between finite
  locally constant module sheaves: eight results about condensed locally constant
  module functors and condensed realization, not this theorem or its category.
- `msearch.py ... grep` for local-constancy/lisse plus Hom/rigidity patterns:
  results concern rank functions and locally constant functions on spaces, not
  this pro-etale ringed-module statement.
- Independent `rg` over Mathlib, `WeilConjectures`, this project's `lean/Sheaf`,
  `dag/lean_names_upstream.json`, and DAG nodes with finite-lisse, rigidity,
  component, Hom, and geometric-stalk terms. I opened the relevant hits:
  upstream `ProEtale.IsFiniteLocallyConstant` and the project's
  `IsLisseProEtaleFixedModuleSheaf` take fixed-coefficient module-valued sheaves,
  not the ringed-module objects in this statement; the ringed local-constancy
  predicate is already available and is reused directly. Upstream
  `Etale.isClopen_stalkZeroLocus` is an etale zero-object statement, and
  `upperStar_map_injective_of_isPreconnected` concerns restriction to a closed
  immersion meeting connected pieces. `injective_upperStar_map_of_isFiniteLocallyConstantSheaf`
  in the purity affine-line module is likewise a special etale restriction
  theorem. None contains both clauses of this node. The already existing
  `SheafOfModules.homObj` and geometric module-stalk construction are used,
  not duplicated.

Mismatches found and repairs:

1. The previous `PurityFiniteLisse` tested local constancy after forgetting to
   modules over A_T(T), the terminal object's section ring. On disconnected T
   this ring need not be A. That is not the dependency node's local-constancy
   predicate, and obscures the coefficient ring in the statement. I replaced
   it with the existing ringed-site predicate on the original object.
2. I removed the now-unneeded terminal coefficient type, its instance,
   underlying fixed-module sheaf/map, and redundant internal-Hom underlying
   wrapper. Stalk finiteness and the induced map now use the dependency's
   ringed module stalk directly. This also removes the need for a coefficient
   transport or a separate equivalence argument in the statement.
3. Several helper docstrings lacked a source/owning-blueprint tag; the remaining
   three helpers all now have them. The compressed proof sketch omitted the
   detailed etale descent, unit/counit calculation, finite-presentation argument,
   local constancy of the morphism, and empty-scheme reasoning. I expanded it
   to all seven DAG steps, naming the dependencies at each step. The theorem's
   only proof is still `sorry`; no theorem was proved.
4. I added the recorded statement/proof imports, keeping proof-only imports
   non-public. `lem-pur-site-constant-module-hom` is still unstated and has no
   module to import. One published proof module cannot be imported alongside
   this statement's existing dependencies: `Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence`
   imports the reorganized FiniteCoefficient UpperLowerStar definitions,
   whereas PurityFiniteSetting imports the original UpperLowerStar definitions.
   Both local compilation and server confirmation failed with the duplicate
   declaration `AlgebraicGeometry.ProEtale.«term(_)_*[_]»`. I omitted only this
   incompatible proof-only import, retaining its mathematical step in the
   proof docstring. Its own node's `lean.note` records the same incompatibility.
   This is an import-interface issue for the maintainer, not a change to the
   rigidity statement. All other stated proof dependencies are imported.
5. I updated `lean.declarations` to the surviving four declarations and copied
   the final theorem signature verbatim into `lean.statement`. No mathematical
   node field, dependency node, target, or source-library file was changed.

Validation: the repaired ringed-module statement passed scompile.py cleanly
before the proof-import pass. Final compilation and delivery preflight results
are recorded below after running them on the complete delivery.

Final `scompile.py Q29 lem-pur-lisse-morphism-rigidity` passed for the sole
module, both as a sandbox import (14.3 s) and as its library module (8.6 s),
with no errors or warnings. All four declared names are bound, no Lean line
exceeds 100 characters, and the recorded signature equals the source verbatim.

`deliver2.py Q29 lem-pur-lisse-morphism-rigidity --no-push` printed OK:
the full delivery compiles and passes the stage-2 preflight.
