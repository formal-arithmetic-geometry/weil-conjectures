## Worker report

The module `Sheaf.Paper.ProductExchangeCounitCoordinates` states
`AlgebraicGeometry.ProEtale.productExchangeCounitCoordinates`, with one `sorry` proof.
All other declarations are actual coordinate expressions, canonical constructions or
instances obtained from existing theorems. No node statement or dependency list is changed.

Hypotheses, clause by clause:

- The fixed finite-field datum, prime distinct from the characteristic, finite subextension,
  positive level and quotient coefficient ring are the existing `PurityFiniteSetting C`.
  The ordinary scalar ring is `C.Coefficient = ULift C.Ring`. The helper instance
  `productCoordinateRingFinite` uses `Padic.finite_coefficientExtensionRing` and `C.level_pos`;
  finiteness is derived, not added as a hypothesis. The site is `Scheme.ProEt.topology` with
  scheme universe u, site objects u+1 and site morphisms u.
- The k-schemes B,X,Z use `Scheme.Over (Spec (.of C.field.k))`.
  `IsSeparated` on each structure map is separatedness; `LocallyOfFiniteType` and
  `QuasiCompact` together are finite type. The same three classes on f,g, and their
  `IsOver` instances, express exactly separated finite-type k-morphisms.
- `cf : Compactification f`, `cg : Compactification g` retain j,a,k,b and the two
  factorization equations. Their open immersions and proper maps are structure fields.
  No density or reducedness hypothesis is imposed on either compactification.
- M and N are `DerivedCategory.Plus` on the ordinary fixed-scalar module sheaf categories.
  `_wM`, `_wN : Scheme.FixedEtaleOriginWitness ...` retain each actual etale antecedent
  and specified isomorphism. They are not replaced by constructibility or by a mere
  existence assumption. N and its witness are bound although none of the conclusions
  depends on N.
- P is `pullback f g`; C is `pullback cf.g cg.g`; W is `pullback cf.g g`.
  p,q,r,t,v are their `pullback.fst`/`pullback.snd` projections. The first base-changed
  compactification is `cf.baseChange g`; its `.i` is j_q and its `.g` is v.
  `ProductExchangeCoordinates.i` is the unique projection-preserving map W to C.
  `square` records the Cartesian square; `comm` records ti=kv. The h used here is
  q followed by g, canonically equal to p followed by f by the pullback condition.
- `compositeChoice cf cg : Compactification (pullback.snd f g ≫ g)` has precisely
  u=j_q followed by i and c=t followed by b. Its construction supplies the required
  factorization, openness and properness; no existence-only choice is made.

Conclusions, clause by clause:

- `Geometry` explicitly lists proper v,t; open and quasi-compact i,j_q,k,u;
  Noetherian B,X,Z,Xbar,Zbar,P,W,C; and finite type of their eight structure maps.
  The two compactifications are the above actual `Compactification` values.
- H,F,L0 are literal abbreviations for j_!M, P_rH and P_b R_aH.
  E and K occur explicitly as the endpoints of `beta`. The source's J,D,K_D, m and L
  do not contribute extra assertions: J=k_!N, D=P_pM tensor P_qN, K_D=j_q!D,
  m=i_!K and L=R_aH are just named expressions. m and L are expanded where used.
  In particular no bounded-below tensor or finite-Tor assumption on D is added.
- A0 is `derivedBaseChangeMap` at H for the actual square (r,t,a,b).
  B0 is `rightDerivedLowerShriekOfCompactificationBaseChangeMap` at M, preceded by
  the canonical derived pullback compositor P_k P_b=P_g.
  These are the actual finite transformations used by def-exchange-projection,
  not arbitrary arrows of the same types.
- `rho` derives the existing sectionwise `sfProperOpenFixedRestrictionIso` by the
  canonical K-injective composition comparisons. Open pullbacks are compared with
  restriction and with total left derived pullbacks. This is the ordinary fixed-scalar
  expression of the sectionwise restriction underlying the recorded intrinsic rho.
  It is defined independently of `derivedBaseChangeMap`, so their asserted equality
  is not tautological. No new open-restriction notion is introduced.
- `beta` is the existing `properOpenBeta`, with the canonical compositor P_iP_r inserted.
  `chi` is i_!(beta inverse) followed by the existing open-adjunction counit.
  `s` is k_!(B0) followed by the existing `properOpenMate` at K.
- `Equations` first says rho_F=Ex_(t,k,F); second says
  B0=P_k(A0), then rho_F, then R_v(beta); third says
  s, then R_t(chi), equals epsilon_(k,L0), then A0.
  Lean's `≫` composes left to right, the reverse of the source's juxtaposition.
- `lambda` is rho at i_!E followed by R_v of the inverse canonical open unit.
  The fourth conjunct of `Equations` says the actual Gamma_E has adjunct lambda_E inverse
  under `properOpenAdj k`. This is the source's explicit normalization, including its
  independently defined lambda, rather than a definition of Gamma by the required square.
- `CounitIdentities` at F supplies both explicit formulas. In the first formula the
  source suppresses P_k k_! R_vE=R_vE; Lean inserts the unit `eta_k` before
  P_k(R_t(epsilon_i) Gamma_E), then rho_F, obtaining the identity of R_vE.
  The second formula is k_!(rho_F), then Gamma_E, then R_t(epsilon_i), equal to
  epsilon_(k,R_tF). These are equalities of actual morphisms.
- The last universally quantified Q is in D+ and retains `wQ`.
  Its property `plusEtaleOrigin` is obtained directly from `wQ.complex` and `wQ.iso`.
  `alpha` conjugates the existing `originCompositionAmbient` by the existing
  `towerCandidateComparison` for exactly (j_q,v), (k,b), (u,c).
  `compositionRoute` is R_b(Gamma_(j_q!Q)), the inverse
  `finiteDirectImageComposition t b`, then R_c of `properOpenShriekComp j_q i`.
  Naturality of kappa makes this the source's equivalent order of the last two factors.
  Gamma is never inverted; neither proper projection nor general exchange is claimed
  invertible. The only inverses used in the conclusions are the specified open and
  compositor isomorphisms.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, `.Ring`,
  `.Coefficient` and their ring instances.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `.fst`, `.snd`;
  the scheme pullback instances and `IsPullback` calculus are reused.
- `WeilConjectures.Compactification.RefinementCategory`: `Compactification.Refinement`
  and category. The imported `Compactification` and `.baseChange` retain the selected
  compactification data and are the constructions needed by this statement.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`, `.exchange` and
  `.compactExchange` specify the mate formula. The finite API uses the exact existing
  `derivedBaseChangeMap` and `rightDerivedLowerShriekOfCompactificationBaseChangeMap`
  from `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange`.
  The old omnibus ExchangeProjection module is not imported: its recorded repair is
  specifically the supplied-domain extraction, while the underlying finite operations
  themselves remain the canonical published ones.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `WeilConjectures.finiteDerivedPullback`,
  `.finiteIntrinsicDerivedTensor` and the recorded finite operation interface. Here
  the node explicitly requests ordinary module coordinates; `ProperOpenPull` is the
  ordinary total derived pullback, with the canonical exact termwise comparisons.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `Scheme.sfIntrinsicModuleEquivalence`, `.sfIntrinsicExtensionByZero`. Ordinary
  `ProperOpenShriek` is precisely the fixed-scalar middle functor used by that construction.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`: `Scheme.FixedEtaleOriginWitness`.
- `Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction`:
  `Scheme.proEtaleOpenRestrictionComparison`, `.proEtaleOpenRestrictionLambdaInverse`,
  `.proEtaleDerivedOpenRestriction`. Their intrinsic categories require coordinate
  transport here; `rho` uses their existing sectionwise input
  `Scheme.sfProperOpenFixedRestrictionIso` from
  `Sheaf.AlgebraicGeometry.ProEtaleProperOpenSheafComparison` and the same right-derived
  composition construction. No arbitrary equivalence or comparison map is supplied.
- `Sheaf.SixFunctors.OpenTensorNormalization`: `SheafOfModules.openTensorNormalization`,
  with its data and finite compatibility; its actual ordinary beta is reused via
  `properOpenBeta` rather than a private open base-change definition.
- `Sheaf.SixFunctors.ProperOpenProjectionMate`: `ProperOpenDerived`, `ProperOpenPull`,
  `ProperOpenPush`, `ProperOpenShriek`, `properOpenBeta`, `properOpenAdj`,
  `properOpenMate`, `properOpenShriekComp`, and `properOpenProjectionMate`.
- `Sheaf.Paper.FiniteDirectImageComposition`: `finiteDirectImageComposition`.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`: `originCompactSupport` and
  `originCompositionAmbient` (the recorded full-origin composition map).
- Proof imports: `ProperStability.proper_stability`,
  `RelativeCompactSupportPasting` (ordinaryPasting and finite coefficient agreement),
  `ProEtaleCompositionTowerNormalization` (normalization theorem and canonical candidate
  comparison), and Mathlib Noetherianity/finite-type/open-immersion stability interfaces.
  The tower module is public because its canonical comparison is used in the signature's
  coordinate definition. The tensor-product compactification theorem is deliberately not
  imported: it cites this item. Its tiny pullback-compositor expressions are written using
  the underlying published compositor API instead, avoiding an import/dependency cycle.

Edge cases checked before writing and again against the final formula:

- Empty X or Z: pullbacks and opens remain defined; no Nonempty, density, point or
  positive dimension assumption occurs. Zero M,N,Q are permitted.
- Identity/open-identity compactifications: beta, rho and open units have their canonical
  identity normalizations; both counit formulas remain typed, including the inserted eta.
- Zbar=Z (k identity), or Xbar=X (j identity), retain the same formula without cancellation
  by any proper exchange. Arbitrary positive coefficient level is permitted.
- Unbounded ambient F is allowed by all helpers. Only the source's M,N,Q are D+;
  no claim that a tensor of arbitrary D+ inputs is D+ is made.
- Universes are explicit and autoImplicit is false. The standard lift does not equate
  site object and morphism universes.

Searches for an existing complete statement:

1. msearch.py leanfinder: `Derived open restriction exchange along product compactifications
   and extension by zero counit square` returned eight condensed locally-constant counit
   hits, none a scheme product-compactification exchange/counit result.
2. msearch.py loogle: `CategoryTheory.Adjunction.counit_naturality` returned the generic
   naturality theorem and two lifting-adjunction coequalizer hits, not this statement.
3. msearch.py grep: `properOpen|open.*counit|counit.*open`, subdirectory CategoryTheory,
   returned zero hits.
4. msearch.py leansearch: `Derived direct image restriction to an open immersion commutes
   with base change and extension by zero adjunction` returned eight structure-sheaf
   restriction/adjunction hits; none states the ordinary pro-etale product coordinate lemma.
5. rg in `lean/WeilConjectures` for the item id, productExchange, product_exchange,
   properOpen and counit coordinates: no matching item theorem. rg in `lean/Sheaf`
   found the existing proper/open, product geometry and forward-product coordinate
   helpers and the downstream proof citation. Read those interfaces; no existing
   declaration supplies this full geometry plus the six specified-map identities and
   the canonical origin-composition coordinate formula.
6. Checked the upstream declaration-name registry for the item and proposed theorem;
   no collision. No new independent notion/node is needed.

Validation: scompile.py compiled the module in sandbox and library modes in 10.8 and
10.2 seconds, clean apart from the expected sorry declaration. No build or direct git
command was run in the read-only repository. No STATEMENT-DISPUTED flag or source
statement correction is required.

## Second reading by Q83

A separate reading pass by the same dispatched worker compared the node text and final
module in full; no second agent was started, as the dispatcher expressly forbids it.
The maintainer's independent review is still required. This section does not claim an
independent reviewer.

Checked all three product endpoints and projection orders: W is Xbar times_B Z here,
not the other intermediate product X times_B Zbar used in the sibling tensor lemma.
Checked the base-change compactification of q, the actual composite choice of h, and
the precise source and target of every counit formula. The open unit eta_k is explicitly
inserted only where the node suppresses it; lambda includes inverse eta_i. Re-read beta:
P_i P_r is first identified with P_(ri), then the actual normalized open beta is applied.
Re-read B0: the actual compactification-relative exchange is used, with P_kP_b=P_g,
and is not defined by the horizontal factorization being asserted. Re-read Gamma: it is
the existing proper mate; the equation identifying its open adjunct is part of the
assertion. Re-read alpha: it uses the original canonical origin compositor conjugated
by canonical candidate comparisons, not the desired Gamma formula as a definition.

The pass removed an initial import of the downstream finite-product compactification
module to prevent a cycle, replacing its compositor wrappers with their existing base
API. It also replaced an unnecessarily indirect finite-type conjunction with the eight
explicit structure-map conjuncts. All source hypotheses are retained, all conclusions
are represented, and no arbitrary ambient proper/open invertibility was introduced.
