## Worker report

The module `Sheaf.SixFunctors.GeometricCoefficientSquareTransport` states
`SheafOfModules.RingedCoefficientProjection.GeometricSquare.geometricCoefficientSquareTransport`.
Its only theorem has proof `sorry`; every helper has actual data. The node's TeX,
source, accepted proof and proof dependencies are unchanged. Three already landed
definition records are added to statement dependencies to cite the interfaces used:
`def-pur-ringed-coefficient-projection-data`,
`def-weil-pbc-successive-derived-quotient-data`, and
`def-coef-semilinear-system-models`. There are no new nodes or dependency repairs.

Source read: the CURRENT `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3).
It states preservation through compactification, not this subsidiary scalar calculation;
the node explicitly records this as an agent refinement. I also read the local Stacks
`sites-cohomology.tex`: `lemma-adjoint` (07A6),
`lemma-derived-pullback-composition` (0D6D),
`lemma-derived-pushforward-composition` (0D6E), and
`lemma-adjoints-push-pull-compatibility` (0FPI). These give the canonical adjunction,
composition and representative normalization used here.

Hypothesis and clause matching:

| Node | Lean rendering |
| --- | --- |
| Morphism of topoi presented by small sites | `C`, `X`, `J`, `K`, `uInv`, `uPush`, `adj`, `[PreservesFiniteLimits uInv]`, and the existing normalized `Geometry uInv uPush adj`; no functor between the presenting sites is required. |
| Size convention | Explicit universes `c v r`, independent site object/morphism levels, `[EssentiallySmall.{r} C]` and `[EssentiallySmall.{r} X]`; standard localizations in `max c v (r+1)` from the recorded `D`, with no equality between site object and morphism universes. |
| Sheaves A -> R -> S on Y | `A R S : Sheaf J CommRingCat.{r}`, `a : A ⟶ R`, `c : R ⟶ S`. |
| Their inverse images on X, induced coefficient maps | `g.rings.obj A/R/S` and `g.rings.map a/c`; the existing Geometry fields `inverse`, `rings_naturality`, `pushUnderlying`, `unit_underlying` identify these as the algebraic inverse images and induced module adjunctions. |
| Ordinary unbounded module derived categories | `D J R`, `D K (g.rings.obj A)` are transparent abbreviations for the standard `DerivedCategory` of the actual `SheafOfModules` categories. |
| K-flat scalar extension and K-injective direct image | `pY`, `pX : Scalars`, their `Presentation` universal counits and `nY/nX : Normalization`; `g.right A/R/S = (g.push _).rightDerivedFunctor`. Geometry uses actual exact inverse-image module functors and K-injective resolutions. |
| Canonical adjunctions | `g.adjunction`, `nY.adjunction`, `nX.adjunction`, normalized by ordinary scalar insertion and K-flat computation; no independent arbitrary adjunctions substituted. |
| V, V_R, V_S | `V : D K (g.rings.obj A)`, `(pX (g.rings.map a)).derived.obj V`, `(pX (g.rings.map (a ≫ c))).derived.obj V`. |
| Comparison with exact scalar restriction | `theta`: right-adjoint conjugation of `e.derived a` using the two composite canonical adjunctions. The existing `Comparisons.ordinary_insertion` and `.representative` fix e; the right conjugate is the canonical normalized restriction comparison by adjoint uniqueness. |
| beta_R and beta_S specified by scalar transpose | `beta`: inverse of the functor-category scalar Hom bijection at `G_A` and `L_a,X ⋙ G_R`, applied to whiskering `G_A` with the X scalar unit, then theta. Thus the beta family is a natural transformation from construction, rather than objectwise maps with naturality assumed. |
| m and gamma send r tensor x to c(r) tensor x | `unitArrow` inserts the c scalar adjunction unit and follows with the normalized scalar associator. `gamma nY a c` uses `nY.derived a c`; `m g nX a c` uses `targetAssociator` including `g.rings.map_comp`. On flat-term K-flat representatives these are `1 tensor (r tensor x)` followed by the multiplication formula `c(r) tensor x` in the existing Normalization record. |
| kappa = G_R(m), then restriction comparison | `kappa` is `whiskerRight (m ...) (g.right R)` followed by whiskering theta_c, with functor associators. |
| Equality in D(R) | First equality after the binders `a c V`: gamma followed by `(nY.right c).map beta_S` equals beta_R followed by kappa. All four endpoints lie in D(J,R); no equality detection by faithful restriction is used. |
| Natural in V, all transformations | beta, gamma, m, kappa, theta are `NatTrans`/`NatIso`, constructed by whiskering, adjunction and composition. Their naturality is part of their type. The equality is universally quantified in V. |
| Canonical integer shifts | First conjunct `Nonempty (Shifts g nY nX e)`. The record supplies coherent scalar/restriction shifts; `canonicalY/X` fix scalar shifts by the universal counits; `restrictionY/X` fix the localization-factor shifts; `adjunctionY/X` give both unit and counit compatibility; every specified transformation has `NatTrans.CommShift ... ℤ`. Geometry's right shifts are the existing K-injective right-derived shifts. |
| Restriction to A | Second equality is the first square mapped by `nY.right a`, retaining the actual D(A) arrows. |
| Exact equivalences compatible with adjunction units/counits and restriction comparisons | `AdjunctTransport` explicitly quantifies equivalences of source and target categories, comparison isomorphisms of left/right functors, and both unit and counit compatibility equations. It concludes the equality between the transported arrow and the primed adjunction transpose. The theorem asserts it for the Y and X scalar adjunctions and geometric adjunctions. Applying this to the scalar-unit and beta words identifies the transported specified arrows; whiskering/composition yields m, gamma and kappa. No equality of transported beta is assumed. |
| Equality carried to equivalent presentations | Last clause quantifies `E : D J R ≌ T` with coherent shift and triangulated exactness and arbitrary endpoint isomorphisms `i₀` through `i₃`. It explicitly asserts equality of the composites of the four transported arrows `i_source.inv ≫ E.functor.map arrow ≫ i_target.hom`. AdjunctTransport supplies their identification with specified primed arrows under the stated normalization compatibilities. |
| No invertibility of projection, flatness or boundedness | No `IsIso beta`, coefficient flatness, finite Tor dimension, boundedness, properness, or characteristic hypothesis occurs. |

Dependencies read and used:

- `Sheaf.Paper.RingedCoefficientProjectionData`: `Scalars`, `Geometry`,
  `Geometry.right`, `Geometry.adjunction`, `Comparisons`, `targetAssociator`;
  the underlying categories `WeilConjectures.SemilinearSections.Mod` and `.D`
  from `Sheaf.Paper.SemilinearSystemModels`.
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientData`:
  `Presentation`, `Normalization`, scalar adjunction units, normalized
  ordinary/derived associators and exact restriction factors.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`.
  The geometric interface presents exactly its generalized-element module functors.
- `Sheaf.Paper.ProjectionMateExact`: `SheafOfModules.ringedProjectionMateExact`,
  the canonical derived adjunction/shift theorem already re-exported by the public data module.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` publicly retains
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `nonempty_derivedChangeOfRingsCochainModel`: the generic ringed-site portion
  of the recorded dependency, rather than its ordinary ModuleCat specialization.
- Proof imports: `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`
  (`sheafRingDerivedCoefficientAdjunction`),
  `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
  (`CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons`),
  `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
  (`CategoryTheory.ringedToposDerivedPushforwardComposition`),
  `Sheaf.Paper.DerivedAdjunctionShift`
  (`CategoryTheory.derivedAdjunctionShiftCompatible`), Mathlib KInjective shifts.
- Mathlib `Adjunction.comp`/`id`, `conjugateIsoEquiv`,
  `Adjunction.whiskerRight`, `Adjunction.homEquiv`, and `NatTrans.CommShift`.
  I read their signatures and normalization docstrings; the composite adjunction
  Hom bijection and its explicit unit/counit formulas implement proof step 1.

Edge cases checked mathematically: identity geometry and identity coefficient maps
reduce to the scalar unit law; V=0 gives zero arrows without assuming beta invertible;
the point topos with Z -> Z/4 -> Z/2 retains all Tor terms, so nonflatness is allowed;
an unbounded V and any positive/negative/zero shift are admitted by the actual
unbounded DerivedCategory and integer CommShift structures. Empty/degenerate sites
are not excluded by any nonemptiness assumption. The transport formulas include
identity equivalences and arbitrary endpoint identifications.

Searches actually run (logged in sandbox searches.jsonl):

- msearch LeanSearch: `Derived direct image scalar extension coefficient unit square commutes`:
  eight hits on underived scalar units, PUnit actions, and cochain unit scalar identities;
  no derived geometric square.
- msearch LeanFinder: `Successive derived scalar extension units commute with derived direct image coefficient projection square`:
  eight cotangent/extension functoriality hits; no exact match.
- msearch Loogle: `"Adjunction", "unit"`: twelve general adjunction constructors and unit declarations;
  used the adjunction API, none states the complete node.
- msearch Mathlib grep: `(derived.*[Rr]estrictScalars|[Rr]estrictScalars.*derived)`:
  zero hits.
- rg on `lean/WeilConjectures` and `lean/Sheaf` for coefficient squares,
  scalar-unit/cocycle/transport patterns and the exact node id; exact-id search
  also in `dag/lean_names_upstream.json`: no declaration attached to this node.
  Nearby `ProEtaleDirectImageScalarCocycle` only treats finite constant coefficients
  and the extension cocycle; `ringedCoefficientProjectionCocycle` gives an extension
  cocycle, not this square in D(R) with successive restriction. Neither is an exact
  existing match. Reused their general normalized interfaces instead of copying them.

Validation: prescribed scompile.py compiled both sandbox and intended library module
with no errors or non-sorry warnings. Initial diagnostics (ambiguous associators,
missing triangulated-category structural binders) were repaired. A first attempt
at transport reused AdjunctionEvaluation, but that existing helper fixes all Hom
and object universes to one level. The final elementary formula spells out its
unit/counit equations directly with independent explicit universe parameters.
No statement correction or STATEMENT-DISPUTED issue was found.

## Second reading by Q128

This is the worker's final self-reading, not a claim of an independent second agent;
the dispatcher brief prohibits starting other agents and reserves independent
review to the maintainer. I reopened the node and final module and checked the
hypotheses and clauses in the table above. The square has source R tensor G_A(V),
intermediate corners Res_c(S tensor G_A(V)) and G_R(V_R), and common target
Res_c G_S(V_S), all in D(R). Its second equation applies Res_a to those same
composites. beta is transposed under the Y scalar adjunction; its input is G_A of
the X scalar unit followed by theta. Thus it has the required orientation.
The X associator retains the functorial equality of inverse-image ring maps.
All naturality is structural, and Shifts covers each named map and the unit/counit
and localization normalizations. The final transport clause was expanded during
this reading: an arbitrary functor image of the square alone would not record
identification with the specified maps, so AdjunctTransport now explicitly
includes both normalization equations and concludes preservation of transposes.
The comparison and normalized presentation notions are imported from landed nodes,
not duplicated. No node statement or accepted proof was changed.
