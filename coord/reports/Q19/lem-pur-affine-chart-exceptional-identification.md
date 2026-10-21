## Worker report

The module `Sheaf.Paper.PurityAffineChartExceptionalIdentification` states the witnessed
adjunction and compactification independence, open restriction, the natural affine-chart
isomorphism, and the two comparisons on bounded constructible inputs. All six theorem
proofs are `sorry`. Definitions contain actual constructions, never postponed data.

The statement is divided into declarations of the same node:

- `exists_liftedAdjunction`: `P : PurityFiniteSetting` retains precisely k, ell, the fixed
  finite coefficient extension, uniformizer convention, and positive level. The source and
  target carry `Over (Spec (.of P.field.k))`; their structure maps have `LocallyOfFiniteType`
  and `QuasiCompact`, precisely finite type. The displayed v has `IsOver`, `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact`. There is no separatedness condition on S or R over k.
  A compactification c is explicitly supplied, as in the statement.
- `C` is an abbreviation for the recorded `EtaleOriginDerivedCategory`, with P.Coefficient
  the recorded size lift of P.Ring and the discrete topology. `forget` abbreviates the
  published `originWitnessFixedAmbient`, the canonical realization of the forgetful functor.
  It keeps all ambient arrows; neither objects nor witnesses are replaced by private copies.
- `LiftedAdjunction.lower` and `.upper` are actual functors between these categories.
  `.lowerUnderlying` and `.upperUnderlying` identify them with exactly compact support and
  transported exceptional image. The fixed-scalar compact support `support` is the published
  `rightDerivedLowerShriekOfCompactification`, canonically identified with the recorded
  intrinsic `sfIntrinsicCompactSupport` by `sfIntrinsicCompactSupportComparison` in
  `SfOpenExceptionalBaseChange`. This is a coefficient realization of the same Rg_* Di_!.
  The exceptional `right` is literally the recorded `sfFiniteExceptionalAt`, with its
  ordinary etale right-adjoint existence supplied by the published theorem.
- `.lowerWitness` and `.upperWitness` give respectively Rv_!,e M_e and v_e^times N_e.
  Each is the underlying object of a `DerivedCategory.Plus` object, so boundedness below
  of BOTH images and BOTH retained witnesses is asserted. `.adj` is an actual Mathlib
  adjunction, hence its Hom equivalences are natural for every witnessed-category arrow.
  `.normalized` states that this equivalence is exactly the chain of compact-support site
  comparison, ordinary etale adjunction, and the comparison-unit witness arrow `rightOrigin`.
- `compactification_independence` quantifies over two compactifications and two lifted
  adjunctions. Its left comparison maps to the published etale-origin compact-support
  comparison `supportComparison`. The right comparison is exactly
  `(D.adj.ofNatIsoLeft e).rightAdjointUniq E.adj`, and the displayed equation asserts
  compatibility of the Hom bijections. Identity/cocycle are the existing canonical support
  comparison and `Adjunction.rightAdjointUniq_refl/trans` equations.
- `exists_openLift` quantifies over EVERY open immersion. `OpenLift.underlying` gives the
  exact derived inverse image; `.witness` is the ordinary etale restriction of K_e.
- `affine_chart` names the local source X and affine target V, the open affine U via j,
  d : Nat, closed i into `AffineSpace (ULift (Fin d)) V`, and the equality
  `j ≫ f = i ≫ (AffineSpace ... V ↘ V)`. This is the local f_V of the node; the local
  theorem therefore applies to X_V in its final assertion. cf, ci, cp are arbitrary chosen
  compactifications. F, I, B, J are the lifts whose existence is stated above. Its conclusion
  is `Nonempty (F.upper ⋙ J.restriction ≅ B.upper ⋙ I.upper)`, a natural isomorphism on C(V).
  It is a derived-category isomorphism, not merely separate homology isomorphisms.
- `constructible_origin` says every intrinsic bounded constructible K has a witnessed
  realization L, related to K by the published intrinsic coefficient equivalence. Thus the
  input L in the last theorem does not silently require an additional origin hypothesis.
- `base_open_chart` names f, the affine open g : V -> Y, X_V=`pullback f g`,
  h=`pullback.fst f g`, f_V=`pullback.snd f g`, the affine open j : U -> X_V, d, i, and
  `j ≫ pullback.snd f g = i ≫ pi`. Ju is restriction along u=`j ≫ pullback.fst f g`.
  `_hL` is EXACTLY the recorded intrinsic finite-torsion constructibility predicate after
  coefficient realization. The first existential b is Lh* G_f L ≅ G_fV Lg* L. Its displayed
  equality identifies its underlying arrow with the specified `baseOpenMap`, including
  the underlying-lift comparison isomorphisms. The second existential t is the canonical
  inverse-image composition comparison for u=hu'. The last z is Lu* G_f L ≅ G_i G_pi Lg* L,
  explicitly equal to t, then the restriction of b, then the chart comparison e.
  None of these declarations assumes constructibility of an exceptional output.

`baseOpenMap` constructs the comparison itself: canonical comparison pullback square,
ordinary etale exceptional mate, exact derived restriction comparison, then canonical
comparison-direct-image restriction. `etaleOpenMate` is `mateEquiv` of the inverse of the
published compact-support base-change map, at the very two specified compactifications.
This avoids an invalid definitional identification of c with the arbitrary compactification
chosen from the Prop-valued `c.hasCompactification` instance.

Dependency declarations used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, `.Ring`, `.Coefficient`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` (via the public dependency imports):
  `Scheme.proEtaleSiteComparisonModules`, and the same `comparisonUpperStar/LowerStar`
  used in its definition and all derived operations here.
- `Sheaf.Paper.EtaleOriginDerivedCategory`: `ProEtale.EtaleOriginDerivedCategory`;
  `Sheaf.Paper.CanonicalOriginCompactSupportComposition`: `originWitnessFixedAmbient`,
  `originWitnessFixed`, the existing canonical coefficient realization of its forgetful functor.
- The scheme-property dependency is explicitly a convention node. Instances `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact`, `IsOpenImmersion`, `IsClosedImmersion`, and `IsOver`
  use the Mathlib notions it collects.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`: `Scheme.sfIntrinsicCompactSupport`;
  the fixed-scalar formula and its published canonical coefficient comparison are explained above.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` publicly supplies the finite
  declaration `sfFiniteExceptionalAt` from `FixedFiniteExceptionalAt`; this is one of the
  recorded dependency declarations, with no additional higher-coefficient datum assumed.
- Mathlib `AlgebraicGeometry.AffineSpace`, `AffineSpace.over`, with coordinate type
  `ULift.{u} (Fin d)`, are the affine-space dependency's recorded match.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`, via `SfIntrinsicRealizationTransport`:
  the same canonical `upperStar` and `sfFixedDerivedPullback` inverse-image constructions.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`, applied to the exact quotient P.Ring.

All recorded proof-dependency modules with declarations are imported, proof-only ones
privately. Mathlib leaves and unrecorded nodes use their existing declarations transitively.

Edge cases checked before and after writing: d=0 uses `Fin 0`, with no positivity binder;
empty schemes and empty affine charts have no nonemptiness premise; positive level is
P.level_pos with no artificial divisibility by ramification index; arbitrary cohomological
lower bounds, with no t-exactness imposed on upper shriek; arbitrary witnessed-category
arrows, with no map of witnesses required; distinct witnesses for the same pro-etale object;
nonseparated X and Y over k; all schemes share universe u while site objects and module
values keep universe u+1. No independent smaller test universe is introduced.

Searches (all performed before finalizing):

- `msearch.py leanfinder`, query “Witnessed etale origin bounded below category compact support
  exceptional adjunction affine chart comparison”: eight unrelated affine transition-limit hits.
- `msearch.py loogle`, query `CategoryTheory.Adjunction.rightAdjointUniq`: found the standard
  uniqueness isomorphism and its counit, unit, identity and transitivity equations; used it.
- `msearch.py grep`, query `EtaleOriginDerivedCategory|affine.*[Ee]xceptional|[Ee]xceptional.*[Cc]hart`,
  subdirectory AlgebraicGeometry: no Mathlib hits.
- `msearch.py leansearch`, query “compact support exceptional adjunction on bounded below etale
  origin complexes”: unrelated compact support of functions, condensed adjunction, and
  supported-complex hits; no exact theorem.
- `rg` in `lean/WeilConjectures`: searched the node ID, etaleOrigin, chart/exceptional names.
  Found published compact-support comparisons, upper shriek, and origin Homology; no statement
  of this entire witnessed affine-chart package. Read the source declarations before use.
- `rg` in `lean/Sheaf`: found the witnessed-category definition, the ordinary etale chart Hom
  chain, the canonical compact-support site comparison, ordinary comparison unit, and the
  open exceptional comparison. These ingredients are reused, not redeclared.

No statement correction, new independent notion node, dependency repair, or disputed
mathematical statement. Helpers belong to this node's specified witness and comparison data.

Validation: required scompile.py compiled the module in both sandbox and library modes,
within 60 seconds per file, with no errors or non-sorry warnings.

## Second reading by Q19

A second local pass read the node and final file clause by clause; no second agent was
started, as the dispatcher's explicit instruction forbids one. The maintainer performs
the independent review. This pass found and repaired: implicit discrete coefficient
topologies; a false definitional identification of a specified compactification with a
compactification chosen from a Prop instance; the missing assertion that every constructible
input admits a retained witness; and the previously unspecified final chart composite.
The final file states the actual ordinary mate at c, retains the specified etale image
witnesses, and equates the final chart arrow to restriction of the base-open arrow followed
by the natural chart comparison. The first theorem covers every separated finite-type
morphism between finite-type k-schemes, the chart theorem covers all C(V), and only the
last comparison restricts the input to bounded constructibility. d=0, empty charts,
nonseparated base schemes, and arbitrary ambient morphisms remain admitted.
