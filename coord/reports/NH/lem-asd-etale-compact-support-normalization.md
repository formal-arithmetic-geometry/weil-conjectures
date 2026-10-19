## Worker report

The delivery states `AlgebraicGeometry.Etale.nonempty_etaleCompactSupportNormalization` in
`Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization`. Its single postponed proof is
`sorry`; all helper definitions have actual data. The theorem asserts existence of a
simultaneous, normalized family, packaged in `EtaleCompactSupportNormalization`. It does
not choose an unspecified isomorphism from a mere existence assertion.

The node is unchanged except for `lean`. No statement correction or disputed statement.
The module and theorem docstrings cite SGA 4 XVII 5.2.2 and 6.2.11 and Stacks Tag 03S6;
the theorem docstring gives all nine proof steps, including the unbounded fibre argument.
Read the local SGA PDF with pdftotext: Proposition 6.2.11 identifies compact support with
the sheafified sum, with trace as adjunction map, and its proof specifies compatibility
with base change. Also read the local Stacks lemma-shriek-base-change and the following
lemma-shriek-into-star-separated-etale, including the graph-extension construction.

Hypotheses and clauses:

- Finite commutative torsion coefficient ring: `(A : Type (u + 1)) [CommRing A] [Finite A]`
  on the theorem. A finite ring is automatically additively torsion; no nontrivial-ring
  or invertibility-of-the-order hypothesis is imposed. The helper package itself is
  defined for any commutative ring, without asserting its existence there.
- Schemes are `U X : Scheme.{u}`. Noetherian is rendered by
  `[IsLocallyNoetherian U] [CompactSpace U]` and the same pair for X, exactly the two
  parents of Mathlib `IsNoetherian`. This means a finite affine cover by Noetherian
  spectra. The intermediate compactification schemes are locally Noetherian and compact
  because their maps to X are proper and thus of finite type. The refinement field
  spells out these inherited instances for d.Z, so they can be supplied using
  `LocallyOfFiniteType.isLocallyNoetherian d.g` and compactness of a proper scheme over X.
- Separated etale finite type: `[Etale f] [IsSeparated f]`. Etale implies locally of
  finite type. Between the indicated Noetherian schemes quasi-compactness is automatic:
  construct `IsNoetherian U` from its two parents, then use its NoetherianSpace instance
  and `quasiCompact_of_noetherianSpace_source`. The base-change and pasting fields retain
  `[QuasiCompact f]` explicitly to make compactness of their fibre products available
  to elaboration. These are the same morphisms as in the node, not a larger geometric
  hypothesis or a restriction on their fibres.
- All derived categories are the ordinary unbounded `DerivedCategoryModule A T`,
  definitionally `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat A))`. The
  constructions never restrict an input to D-plus, bounded, constructible, or finite-Tor
  objects. `HomotopyCategory ... (ComplexShape.up ℤ)` in the normalization quantifies over
  every unbounded cochain complex modulo homotopy.
- The prescribed sum extension is `etaleLowerShriek (ModuleCat A) f inferInstance`.
  Its degreewise descent is `.mapDerivedCategory`. Its adjunction is precisely
  `(etaleLowerShriekUpperStarAdjunction ...).mapDerivedCategoryAdjunction`, whose unit and
  counit are the descended unit and sum/evaluation counit. Inverse image is the recorded
  `upperStar`, descended by the same exact-functor construction.
- The chosen compactification is `c : Compactification f`, with `c.i` open, `c.g` proper,
  and `c.comm : f = c.i ≫ c.g`. Its candidate is the recorded
  `rightDerivedLowerShriekOfCompactification (ModuleCat A) c`, definitionally
  `D(c.i_!open) ⋙ R(c.g_*)`.
- The natural isomorphism in the requested direction is the `comparison` field.
  The `sheafComparison` field has the inverse direction on sheaves. Its
  `sheaf_normalization` equation says that composing with the actual compact-support
  inclusion into direct image gives `etaleLowerShriekToLowerStar`. The latter is the
  published graph-extension/sheafification map: each sheet summand is extended by zero
  off its clopen graph. Thus its inverse sends proper-support sections to their sheet
  components. The compact-support inclusion is explicitly composed from
  `openImmersionLowerShriekToLowerStar` and `lowerStarComp`, with `c.comm`; it is not an
  arbitrary map used as a hypothesis.
- `derived_normalization` identifies `comparison.inv` on EVERY homotopy representative
  with `compactSupportComparisonOnHomotopy`. This helper first uses the exact functor's
  localization comparison, applies the sheaf map degreewise, splits the homotopy
  composite using `mapHomotopyCategoryCompIso`, applies the actual total-right-derived
  unit of `c.g_*`, and returns through the exact open-extension localization comparison.
  In particular the derived isomorphism cannot be changed arbitrarily in higher degrees
  while retaining its sheaf comparison.
- `refinementOpenCompactification r` is the real compactification of d.i given by c.i
  and r.hom, with equation `r.i_hom.symm`. The `refinement` equality constructs the
  comparison using `comparison d.i ... .inv`, whiskers it by R(d.g)_*, and applies
  `rightDerivedFunctorCompIso'` with `lowerStarComp ... r.hom_g.symm`. This is the
  proper-refinement comparison: the same graph normalization makes it identity over U.
  The field asserts `rho ≫ c_c = c_d`. No Cartesian-square restriction is imposed on
  a refinement. Invertibility follows since its factors are natural isomorphisms;
  identity and composition of refinement comparisons follow by cancellation of c.
- For ANY right adjoint R with its chosen `adj : Rf_!^c ⊣ R`, the `adjunction` field
  gives `∃! e : R ≅ D(f^*)` with the explicit counit equality. It first applies c under R,
  then e under derived sum extension, then the specified sum/evaluation counit, and
  equates this to `adj.counit`. Consequently it is the unique adjunction-preserving
  comparison; the node's exceptional adjoint is one such R. It does not assume its
  original choice of counit equals the evaluation counit before transport.
- For arbitrary Noetherian X' and g, use `pullback g f`: its projections are
  `pullback.fst g f` (u') and `pullback.snd g f` (h). Its pulled compactification is
  `c.ofIsPullback (IsPullback.of_hasPullback g f).flip`.
- `exactCompactSupportExchange` is the existing compactification-relative unbounded
  proper exchange followed by inverse open-extension exchange, transported from
  L(g^*) to exact D(g^*) by `leftDerivedUpperStarIsoMapDerivedCategory`. This transport
  is the canonical identification of exact inverse image, so its mate is the exchange
  recorded by def-kun-unbounded-exchange, not an arbitrary base-change isomorphism.
- `exactEtaleSumExchange` is explicitly the degreewise descent of the INVERSE of the
  recorded `etaleLowerShriekBaseChangeMap A g f`, via `asIso` and the exact-functor
  composition isomorphisms. Invertibility comes from the recorded
  `isIso_etaleLowerShriekBaseChangeMap`, not a new hypothesis.
- `base_change` is exactly `C_compact ≫ (h^* c') = (c g^*) ≫ C_sum` as an equality of
  natural transformations. Thus it holds on every unbounded derived object. It includes
  g an identity and arbitrary g, with no flatness or field assumption.
- `identity` fixes c for the trivial compactification of an identity morphism to the
  canonical removal of the derived identity direct image. Together with `refinement`
  this normalizes an identity morphism presented by any compactification. The actual
  exchanges are the named adjunction mates (and beta inverse), so an identity change
  of base is the identity under the canonical identity/pullback identifications.
- `composition` states the same commuting equation for TWO successive changes of base,
  using Mathlib `TwoSquare.vComp` for the exact canonical pasting, including every
  associator and the iterated pulled-back compactification. Proper exchanges and beta
  are formed by mates/conjugacy of the same inverse-image squares; their pasted maps
  are the maps for the composite square under canonical fibre-product identification.
  Thus this is compatibility with composition, with the same c as in `base_change`.

The packaging avoids choosing c from a bare `Nonempty` and then silently imposing
normalizations: the existence theorem supplies the comparison AND all normalization
conditions together. All helper declarations are listed in `lean.declarations`, belong
only to this node, and have source/blueprint docstrings. The one sorry is precisely the
node's assertion. No extra independent mathematical notion or postponed helper theorem
is introduced.

Dependency declarations used (read their recorded signatures and docstrings):

- `Sheaf.AlgebraicGeometry.DerivedCategories`: `DerivedCategoryModule` (via the recorded
  upstream coefficient module), unbounded derived-category conventions.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `upperStar`,
  `upperStarLowerStarAdjunction`, `lowerStar`, `lowerStarComp`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`: `etaleLowerShriek`,
  `etaleLowerShriekUpperStarAdjunction`, `preservesFiniteLimits_etaleLowerShriek`.
- `WeilConjectures.Compactification.Refinement`: `Compactification.Refinement` and its
  properness instance. `Compactification` itself is from its imported Defs module.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification` (the actual unbounded candidate).
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`: `exactDerivedBaseChangeMap` and its
  square/mate normalization, matched by canonical transport of the upstream exchange.
- `Sheaf.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`:
  `etaleLowerShriekBaseChangeMap`; its invertibility is from
  `Sheaf.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules`.
- `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`:
  `isLeftAdjoint_rightDerivedLowerShriekOfCompactification`; the adjunction field covers
  every adjunction to the candidate, including its supplied exceptional adjoint.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`:
  `Adjunction.mapHomotopyCategory`, and the subsequent derived construction in
  `WeilConjectures.CategoryTheory.DerivedCategory.Adjunction`.
- Mathlib `Localization.lift`, `liftNatTrans`, `natTrans_ext` and associated lifting
  isomorphisms (Localization.Predicate) underlie the exact derived functors. The
  localization node is a mathlib leaf and has no missing project declaration.
- Mathlib `Scheme`, `Limits.pullback`, `IsProper`, `IsSeparated`, `Etale`,
  `LocallyOfFiniteType`, `QuasiCompact` supply the remaining dependency notions directly.

Proof-dependency modules that have declarations are imported as non-public imports,
including the unbounded proper-base-change theorem, separably closed-field decomposition,
open-section clopenness, geometric germs, exact derived-functor comparison, and derived
pushforward composition. No dependency module or node record is replaced.

Edge cases checked: zero coefficient ring is admitted (`Finite`, not `Nontrivial`);
empty U and empty geometric fibres give zero sums/products; no fixed nonempty sheet set;
identity f and nontrivial compactifications are covered by identity plus refinement;
identity g is an instance of the actual mate exchange; arbitrary g remains unrestricted;
unbounded complexes have no truncation hypothesis; refinements need not be Cartesian;
finite characteristic equal to residue characteristic is allowed; u can be a non-finite
separated etale open immersion. The coefficient/site universe is the project's standard
ModuleCat.{u+1} encoding and all universes and variables are explicitly bound.

Searches (2026-10-15):

- msearch leanfinder: "For an etale morphism compactly supported derived direct image is
  canonically exact extension by zero with compatible base change" returned eight
  unrelated etale/ring/ordinary module-pushforward results, no statement match.
- msearch loogle: "AlgebraicGeometry.Etale.etaleLowerShriek,
  AlgebraicGeometry.Etale.lowerShriek" returned no hits, unknown project identifier.
- msearch grep: "etaleLowerShriek|compactSupport" in CategoryTheory returned no hits.
- msearch leansearch: "etale morphism derived compact support sum extension base change"
  was unavailable (Internal Server Error). The other searches were used.
- rg of upstream WeilConjectures and side lean/Sheaf for the node id, etaleLowerShriek
  together with compactification/compact support, normalization and sum-extension found
  the component constructions but no comparison with all these normalizations. Upstream
  FiniteEtale supplies the precise graph-normalized sheaf-to-direct-image comparison for
  every separated etale map; the finite etale specialization is already carried by
  def-weil-pbc-etale-shriek-to-star-map. Its existing declaration is used directly.
- DAG searches for clopen, proper-support, sum-stalks and normalization found the existing
  support and geometric-stalk nodes, not another node supplying this normalized derived
  comparison. No new independent definition was needed.

Compilation: use the prescribed scompile.py wrapper only, with this delivered module.
The final verification and deliver2.py --no-push results are recorded below after running.

Verification completed: scompile.py compiled the delivered module cleanly in both sandbox
and library mode (8.5 s / 11.1 s), with no errors or warnings. deliver2.py --no-push
printed `OK (dry run)`; preflight passes except for the second reading, intentionally
reserved for the independent second reader. Nothing was pushed. No second-reading section
has been written by this worker.

## Second reading by NH

I independently read the node and its nine proof steps, the delivered Lean module, the
recorded statement dependencies and their source declarations. I read SGA 4 XVII 5.1.3–5.1.8,
5.2.2, and Proposition 6.2.11 with its proof (printed pp. 430–431), and Stacks
`etale-cohomology.tex`, section Extension by zero, especially
`lemma-shriek-base-change` (03S6) and `lemma-shriek-into-star-separated-etale`.
The Stacks section has no standing field, Noetherian, or invertible-characteristic
hypothesis: its module statement allows a ring. SGA supplies the torsion-coefficient
compact-support formalism, its exact open extension on the whole derived category, and
the trace-normalized identification with sheafified sum extension. The node explicitly
specifies the unbounded extension and its proof, which the Lean retains.

Here is my list of the node's objects, hypotheses, and conclusion clauses, matched with
what the Lean actually quantifies over.

1. **Finite commutative torsion ring A.** The theorem binds
   `(A : Type (u + 1)) [CommRing A] [Finite A]`. Finite additive groups are torsion,
   so no separate torsion assumption is needed. No field or nontriviality instance is
   required. Verdict: exact.
2. **Noetherian schemes U and X.** Each comparison field binds
   `U X : Scheme.{u}` with `[IsLocallyNoetherian U] [CompactSpace U]` and the analogous
   pair for X. I read Mathlib `Noetherian.lean`: `IsNoetherian` has exactly those parents,
   and `isNoetherian_iff_of_finite_affine_openCover` gives the node's finite-affine-cover
   characterization. Verdict: equivalent hypotheses, not merely topological Noetherianity.
3. **Separated etale finite-type f : U → X.** `f : U ⟶ X`, `[Etale f]`,
   `[IsSeparated f]` use the recorded Mathlib notions. Etale supplies locally finite
   presentation and hence locally finite type. Noetherian U supplies `NoetherianSpace U`
   after assembling `IsNoetherian U`, and Mathlib
   `quasiCompact_of_noetherianSpace_source` supplies `QuasiCompact f`. Its explicit binder
   on `base_change` and `composition` is thus derivable, not a restriction. Verdict: exact.
4. **Ordinary unbounded coefficient categories and exact inverse image.**
   `DerivedCategoryModule A T` unfolds to
   `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))`; I read the
   upstream Coefficients declaration and the recorded DerivedCategories module.
   `upperStar` is the recorded left Kan extension/sheafification inverse image, and
   `.mapDerivedCategory` is its exact termwise descent. No plus, bounded, constructible,
   or Tor-amplitude subcategory occurs. Verdict: the same categories and functors.
5. **Exact etale sum extension and its specified adjunction.** The right side of
   `comparison` is `(etaleLowerShriek (ModuleCat A) f inferInstance).mapDerivedCategory`.
   I read EtaleMap: this is sheafification of the sum over lifts, and
   `etaleLowerShriekUpperStarAdjunction` is the sum/restriction adjunction. The
   `adjunction` field uses precisely its `Adjunction.mapDerivedCategoryAdjunction`,
   whose upstream unit/counit normalization descends the original adjunction termwise.
   Verdict: no substitute left adjoint or unspecified evaluation.
6. **Every chosen compactification (j,r) and its candidate.** `c : Compactification f`
   has actual fields `i`, `g`, open/proper instances, and `comm : f = c.i ≫ c.g`.
   `rightDerivedLowerShriekOfCompactification (ModuleCat A) c` unfolds to exact derived
   open extension followed by the unbounded total right derived `lowerStar c.g`.
   This is the recorded def-amb-etale-compact-support construction. Verdict: exact,
   with no Cartesian-refinement or density hypothesis.
7. **Canonical natural isomorphism in the required direction.** `comparison f c`
   is an isomorphism from that candidate to derived sum extension. The theorem asserts
   `Nonempty (EtaleCompactSupportNormalization A)`: the entire simultaneous family
   and its laws exist together, without defining a chosen object from a sorry existence
   theorem. Verdict: all f and all c are covered with the required simultaneous laws.
8. **Degree-zero proper-support-to-sheet-components normalization.**
   `sheafComparison f c` runs in the inverse direction. `sheaf_normalization` says its
   composite with `compactificationSheafToDirectImage A c` is the actual upstream
   `etaleLowerShriekToLowerStar`. I read the latter in FiniteEtale: despite that module's
   name this declaration only needs separated etale f, and is adjoint to extension by
   zero off clopen graphs. The inclusion helper is actual open-extension inclusion
   whiskered by `lowerStar c.g`, followed by `lowerStarComp` using `c.comm`.
   Therefore the inverse comparison recovers sheet components, as the source says.
   `derived_normalization` imposes its degreewise descent on every homotopy
   representative using `mapDerivedCategoryFactorsh` and the total-right-derived unit;
   it cannot silently vary on higher degrees. Verdict: the prescribed normalization.
9. **Agreement under proper refinements normalized over U.** `refinement` quantifies
   over every `r : c.Refinement d`. I read its signature: its two equations express
   exactly a morphism over X compatible with the open immersions; properness is its
   existing derived instance. `refinementOpenCompactification r` has open map `c.i`
   and proper map `r.hom`, and compactifies `d.i` by `r.i_hom.symm`.
   The equality uses the normalized inverse comparison for this compactification,
   whiskers by R(d.g), and applies the actual right-derived composition isomorphism
   with `r.hom_g.symm`. It says `rho ≫ c_c = c_d`. Its normalization is identity on U
   by the same graph and termwise normalization. The extra Noetherian/compact binders
   on d.Z are inherited from proper d.g over Noetherian X. Verdict: all proper
   refinements, including non-Cartesian ones, are covered.
10. **Exceptional adjunction, including sum/evaluation counit and unique comparison.**
    For every `R` and every adjunction from the compact-support candidate to R,
    `adjunction` asserts `∃! e : R ≅ (upperStar ... f).mapDerivedCategory`.
    Its equation first applies `comparison` under R, then e under sum extension,
    then the specified derived evaluation counit, and equates this with `adj.counit`.
    This is precisely preservation of the adjunction; it includes the exceptional
    adjoint supplied by the recorded EtaleExceptionalAdjoint theorem, whose middle
    scheme assumptions are inherited from properness. Verdict: the counit and unique
    adjunction-preserving identification are present, with no preselected-counit premise.
11. **Arbitrary Noetherian X′ and arbitrary g : X′ → X, and pulled compactification.**
    `base_change` binds X′ with the same Noetherian parents and has no property on g.
    `pullback g f`, `pullback.fst g f` and `pullback.snd g f` are U′, u′ and h.
    The candidate uses `c.ofIsPullback (IsPullback.of_hasPullback g f).flip`.
    I read BaseChange: its middle scheme is `pullback c.g g`, proper map the second
    projection, and open map the canonical lift. Verdict: the actual pulled-back
    compactification and every g.
12. **The two specified exchanges, and equality on all complexes.**
    `exactEtaleSumExchange` explicitly descends the inverse of
    `etaleLowerShriekBaseChangeMap A g f`; its invertibility is the recorded theorem,
    not a new premise. I read that map's inverse-conjugate definition and both
    adjunctions. `exactCompactSupportExchange` transports the published
    `rightDerivedLowerShriekOfCompactificationBaseChangeMap` through the canonical
    `leftDerivedUpperStarIsoMapDerivedCategory`. I read its full body: proper exchange
    is the mate of the inverse-image square, followed by the inverse derived open
    exchange. The open map is the same conjugate under the open instance of the etale
    sum adjunction, transported to its specified pullback square. Thus this is the
    node's exchange, not an arbitrary natural isomorphism. `base_change` is equality
    of the resulting natural transformations, in the order `C_compact ≫ h^*c′ =
    g^*c ≫ C_sum`. Verdict: the specified arrows and equality on the entire category.
13. **Identity normalization and composition of base changes.** `identity` fixes the
    identity morphism with its trivial compactification to the canonical removal of
    derived identity direct image. Together with `refinement` it handles other
    compactifications of an identity. `composition` intertwines the actual `TwoSquare.vComp`
    pastings for any two arbitrary changes g,k, with their associators and the iterated
    pullback compactification. The exchanges are the specified mates/conjugates, so their
    identity and composite identifications are the canonical ones, as in proof step 9;
    the field is not a choice of new exchanges. Verdict: identity and pasted compatibility
    use the same normalized family as the single-square equation.

Edge cases: empty U, empty X and empty geometric fibres have not been excluded by any
Nonempty assumption; sums over empty lifts and zero complexes remain allowed. The zero
coefficient ring is allowed. All integer degrees, including degree zero and complexes
unbounded in both directions, occur through `ComplexShape.up ℤ` and unrestricted
`DerivedCategory.Qh` representatives. Characteristic equal to a residue characteristic is
allowed: neither an invertibility nor a prime-to-characteristic assumption appears.
Nonfinite separated etale open immersions are included. Identity f, identity g, arbitrary
g and arbitrary proper refinements are included. The common site/coefficient size is the
recorded six-functor `Scheme.{u}` / `ModuleCat.{u+1}` convention; u is arbitrary, and no
extra equality of site object and morphism universes is imposed. No implicit parameter or
universe is left unbound (`autoImplicit false`, explicit universe u).

Independent searches, with different wording from the worker:

- msearch leanfinder: "The derived extension with proper support of a separated etale
  morphism agrees canonically with its exact left adjoint to restriction" returned eight
  etale-locus, affine restriction, and algebra results, not this statement.
- msearch loogle: `"rightDerivedFunctorIsoMapDerivedCategory"` returned no hits.
- msearch grep: `shriek.*[Nn]ormal|[Cc]ompact.*[Ss]upport.*[Ee]tale|etale.*[Cc]ompact`
  returned only an unrelated local-flat-descent instance.
- msearch leansearch: "compactly supported direct image for an etale morphism is exact
  and left adjoint to restriction" was unavailable (Internal Server Error); no negative
  mathematical verdict is inferred from that failure.
- Direct rg searches in Mathlib, upstream WeilConjectures, side lean/Sheaf and the DAG
  found the component maps and compactification comparisons. Existing upstream unbounded
  refinement comparison requires a Cartesian refinement, and the side
  EtaleCompactSupportComparisons module uses bounded-below derived categories; neither
  states this node. The existing `lowerShriekToLowerStar` uses the globally chosen
  compactification; the helper here accepts each explicit c. No exact existing declaration
  covers this whole normalized family.

Mismatches repaired: the worker's `identityEtaleCompactification` reproduced the existing
`Compactification.ofIsProper (𝟙 X)` field for field, including its factorization proof.
I removed this duplicate definition, used the existing construction at both occurrences,
and removed the deleted name from `lean.declarations`. This changes no mathematical
statement. I also added the direct proof-dependency import
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`, used in proof step 5, so the
proof's conservative-stalk dependency is explicitly available to the later prover.
The node's statement, dependency lists and nine proof steps remain unchanged.

There are no new definition nodes or dependency modules to audit. All retained helpers
belong to this node, have real data and source/blueprint docstrings, and are listed in
`lean.declarations`. The sole postponed theorem is
`nonempty_etaleCompactSupportNormalization`, whose docstring follows all nine node proof
steps. No new theorem is proved. Its `lean.statement` is verbatim the source signature.
The first post-repair scompile.py run was clean in sandbox and library modes (8.5 s and
11.4 s); final compilation after the explicit proof import and delivery checks follow.

Final second-reader verification: scompile.py compiled the final module with no errors or
warnings in sandbox mode (8.7 s) and library mode (11.1 s). deliver2.py --no-push printed
`OK (dry run)` and passed preflight and compilation. The delivery consists only of this
module, this node's Lean record and the report. No statement correction was needed.
