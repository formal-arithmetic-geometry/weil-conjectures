## Worker report

Record an existing definition; no new Lean module or theorem is introduced.
The exact declaration is
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`
in `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`.
The published source was read using `scompile.py --source`, since this module
is absent from the older local upstream checkout. Its full signature and
construction, and the definitions of `derivedPlusFormalism`, `pfBaseChange`,
`shriekBaseChange`, and `shriekBaseChangeOfIsPullback`, were inspected.

Clause-by-clause correspondence:

- The four schemes have universe `u`; the four morphisms are implicit parameters,
  and `sq : IsPullback g' f' f g` expresses precisely the cartesian square.
  There is no condition on `g`. The given separated finite-type `f` is allowed:
  the construction works for every supplied compactification, without needing
  separatedness or finite type to construct the map. These ambient assumptions
  are not strengthened, and the definition restricts directly to the stated case.
- The coefficient parameter is `Λ : Type (u + 1)` with `[CommRing Λ]` and
  `[Finite Λ]`, exactly finite commutative module coefficients, in the existing
  small-etale size convention.
- `c : Compactification f` supplies the open immersion `c.i`, proper `c.g`,
  ambient scheme `c.Z` and factorization equation. Its base change is
  `c.ofIsPullback sq`; its ambient scheme is `pullback c.g g`, with ambient
  projection `pullback.fst c.g g`. The initial S-structures do not enter any
  sheaf functor; all these constructions preserve the induced S-structures.
- `derivedPlusFormalism.obj X` is
  `DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
  Its `pb` is exact inverse image induced on D+, `pf` is the bounded below
  right derived direct image, `sh` is degreewise exact extension by zero
  induced on D+, and `adj` is the derived inverse-image/direct-image adjunction.
- `derivedPlusFormalism_shriek` identifies its compactification-relative shriek
  with `Rf_!(c)[ModuleCat.{u + 1} Λ]+`, namely `D+(j_!) ⋙ R+(p_*)`.
  This realizes both displayed definitions of `Rf_!^c` and `Rf′_!^{c′}`.
- `derivedPlusFormalism_pfBaseChange_eq_mateEquiv` identifies the proper-square
  exchange with the mate of the square comparison for these module adjunctions.
  `derivedPlusFormalism_pfBaseChange` identifies it with the dependency's
  `derivedBaseChangeMapPlus`. Thus its component is the specified
  unit–square-isomorphism–counit composite at `M = j_!K`.
- `CompactSupportFormalism.shriekBaseChange` horizontally composes this proper
  exchange with the inverse open-immersion base-change transformation. Its
  component is therefore `Ex_{*,p}(j_!K)` followed by `Rp′_*(β_K)`.
  The inverse open comparison is exactly the canonical extension-by-zero
  identification: it uses the derived extension-by-zero adjunction and square
  comparison, the same canonical mate localized degreewise in the recorded
  `extensionZeroBaseChangeDerivedPlusIso`. No arbitrary comparison is supplied.
- `shriekBaseChangeOfIsPullback sq c` inserts the upper and lower pullback
  squares furnished by the dependency's base-change compactification.
  The recorded definition is its `.natTrans` in the etale D+ formalism.
  Its component at every `K` is the required map, with exactly source
  `g^{-1}Rf_!^cK` and target `Rf′_!^{c′}g′^{-1}K`; its naturality comes from
  being a natural transformation. The notation refers to these chosen
  compactifications, rather than comparing them to unrelated chosen ones.

Dependency declarations inspected:

- `WeilConjectures.Compactification.BaseChange`:
  `AlgebraicGeometry.Compactification.baseChange`, `ofIsPullback`,
  `isPullback_i_ofIsPullback`, `isPullback_g_ofIsPullback`.
- `Sheaf.AlgebraicGeometry.DerivedCategories` and its upstream coefficient import:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`; Mathlib `DerivedCategory.Plus`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriek` and
  `preservesFiniteLimits_openImmersionLowerShriek` (with its additive and
  left-adjoint structures, giving exactness).
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`:
  `AlgebraicGeometry.Etale.exchange_forget_coefficients`, whose statement
  uses the same module `derivedBaseChangeMapPlus`.
- `WeilConjectures.SixFunctors.BaseChange.Derived`:
  `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`.
- `Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange`:
  `AlgebraicGeometry.Etale.extensionZeroBaseChangeDerivedPlusIso` and
  `derivedExtensionZeroBaseChange`.

Edge cases: no nonempty scheme, nonzero coefficient ring, invertible torsion,
characteristic, or bounded-above assumption is present. Empty schemes, the
zero ring, zero complexes, identity base change, and arbitrary base change all
remain admitted. A supplied compactification avoids any extra compactification
existence hypothesis. All coefficient sheaves and derived categories use the
same `u + 1` convention as the dependencies. No node fault or statement dispute.

Searches (2026-10-15):

- `msearch.py leansearch`: “Compactly supported etale derived base change exchange
  map using a compactification”; unavailable, Internal Server Error.
- `msearch.py leanfinder`: “Compact support exchange map on bounded below etale
  derived categories along a chosen compactification”; eight results on generic
  boundedness/localization, none the requested construction.
- `msearch.py loogle`: `CategoryTheory.mateEquiv`; twelve generic mate results.
- `msearch.py grep`: `shriekBaseChange|compact.*support.*exchange` in Mathlib
  CategoryTheory; zero hits.
- `rg` in upstream WeilConjectures and side Sheaf for `lowerShriekBaseChange`,
  `rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`, and
  `def-cbc-exchange-map`: no local source match for this newer module.
  The prescribed item-id grep likewise has no local upstream match.
- `dag/lean_names_upstream.json` names the canonical plus exchange and abstract
  lowerShriekBaseChange. Reading their current published module through
  `scompile.py --source` revealed the exact compactification-relative declaration
  selected here, avoiding the extra canonical-compactification comparisons.

Validation: the prescribed deliver2.py dry run checks the existing declaration
through scompile.py and runs the current server preflight. No delivery is pushed;
the independent second reading remains for the second worker.

## Second reading by NA

Independent second reader, 2026-10-15. Read the node and original blueprint
`sec-smooth-purity/sk-prop-sf-cbc/def-cbc-exchange-map.md`, the square's source,
all seven dependency nodes and their recorded signatures. Read current published
upstream sources with `scompile.py --source`, including LowerShriekPlusBaseChange,
LowerShriekFormalism, Formalism.BaseChange, Compactification.BaseChange and
BaseChange.Derived; read the side DerivedCategories, ExchangeForgetCoefficients
and DerivedExtensionZeroBaseChange modules, and upstream open-shriek definitions.
Stacks 03S6 (lemma-shriek-base-change), 0F70 (lemma-jshriek-open) and 015F
(lemma-right-derived-exact-functor) give the relevant underived comparison,
open extension and exact-functor descent. The node's own source is the blueprint,
not a Stacks statement of this compactification formula.

Object/hypothesis/conclusion checklist and verdicts:

1. Four schemes and the four indicated arrows, cartesian over a base S:
   implicit `{X Y X' Y' : Scheme.{u}}` and `{f f' g g'}`, with
   `sq : IsPullback g' f' f g`. PASS. Forgetting S does not change any
   operation; the ambient compactification has its S-map induced through Y.
2. Separated finite-type f and unrestricted g: the existing definition takes
   any `c : Compactification f` and no instance on g. PASS as a direct
   specialization of the existing construction. No existence theorem or
   stronger geometric hypothesis is required; the given f is admitted.
3. Finite commutative coefficients: surrounding `Λ : Type (u + 1)` and
   `[CommRing Λ]`, followed by `[Finite Λ]`. PASS. This is the recorded
   small-etale module coefficient convention, not pro-etale coefficients.
4. Chosen c=(j,p), and its base change c': `Compactification f` with `c.i`,
   `c.g`, `c.Z`, and `c.ofIsPullback sq`. The latter has ambient scheme
   `pullback c.g g` and ambient horizontal arrow `pullback.fst c.g g`.
   Read `isPullback_i_ofIsPullback` and `isPullback_g_ofIsPullback`; the
   latter is flipped at the call site. PASS, including arbitrary chosen
   pullback squares, not only a literal fibre product.
5. Every category is D+ of small-etale module sheaves: `derivedPlusFormalism`
   has `obj X := DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)`;
   specialize A to `ModuleCat.{u + 1} Λ`. PASS. `pb` is `D+(f^*)`, `pf`
   is `R+(f_*)`, and `sh` is `D+(j_!open)`; exact extension is the same
   recorded `openImmersionLowerShriek`, not a replacement functor.
6. Both compactification-relative direct images Rp_*j_!: checked
   `derivedPlusFormalism_shriek`, whose equality to `Rf_!(c)[A]+` is rfl.
   The source and target of the recorded signature use c and exactly its
   base change. PASS; no comparison to independently chosen compactifications.
7. Proper exchange at M=j_!K with unit, square isomorphism, counit:
   `derivedPlusFormalism_adj`, `derivedPlusFormalism_sqIso` and
   `derivedPlusFormalism_pfBaseChange_eq_mateEquiv` identify all factors.
   `derivedPlusFormalism_pfBaseChange` identifies this with the recorded
   module `derivedBaseChangeMapPlus`. PASS; this is a fixed mate, not an
   arbitrary natural transformation between the endpoints.
8. Canonical beta and composite: `shriekBaseChange` uses
   `inv (F.baseChange ...).natTrans` horizontally composed with
   `F.pfBaseChange ...`. Read Mathlib `TwoSquare.hComp`: its first
   component is the proper exchange after j_!, followed by p'_* of the
   inverse open comparison, in exactly the node's order. The formalism's
   open comparison uses the derived open adjunction and square comparison;
   the dependency's `extensionZeroBaseChangeDerivedPlusIso` is the same
   inverse mate localized degreewise, with the functor-composition
   comparisons inserted. PASS: canonical beta, not an unspecified iso.
9. For each K and naturality: the declaration returns a natural
   transformation; its `.app K` has exactly the displayed source and
   target and preceding formula. PASS. It asserts no additional theorem
   about independence or invertibility as part of this definition.

Edge cases: empty schemes/open subschemes, zero coefficient ring, zero
complex, identity/arbitrary g and complexes with any cohomological lower
bound are admitted. There is no characteristic, invertibility, nonempty,
Noetherian, bounded-above or nonzero assumption. There is no numerical n
or index set in this definition. The scheme universe u is arbitrary;
finite rings can be represented at the dependencies' u+1 coefficient size,
and no extra universe equality is imposed. No unbound variable remains:
read the surrounding `universe u' u`, coefficient variables and four
scheme/morphism binders of the existing source.

Independent searches: ran `msearch.py leanfinder` for “étale lower shriek
compactification exchange natural transformation”: eight restriction/site
results, no requested exchange. Ran `msearch.py loogle` for
`CategoryTheory.TwoSquare.hComp`: eleven generic square/mate results,
including hComp. Ran rg for `shriekBaseChange`,
`LowerShriekOfCompactification`, compactification base change and the
blueprint id across Mathlib, upstream WeilConjectures and side Sheaf.
The local upstream has related unbounded constructions; the published
source has the exact D+ compactification-relative construction selected
by the worker. Reuse is correct and a new module would duplicate it.

No mismatch found; no Lean or node change. Retained the existing signature
verbatim, including its implicit context as checked above. No new nodes,
dependency modules, hollow data, private notions or proofs were introduced.
The item's definition has no proof steps requiring a postponed theorem
docstring. No stage-2 statement correction or citer audit is needed.
Validation follows through the prescribed deliver2.py existing-declaration
check and server preflight; there is no new Lean file to compile.
