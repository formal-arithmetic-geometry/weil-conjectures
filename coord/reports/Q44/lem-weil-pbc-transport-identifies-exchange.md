## Worker report

Recorded the existing declaration
`AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap` in
`WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`, source lines 141–169.
The upstream docstring explicitly names this blueprint node. No module is delivered:
brief-stage2 §1 and §5 require reuse of an existing statement. Only the item's `lean`
field changes. This is a stage-2 statement attachment, not a proof completion; the
upstream theorem's body is `sorry`.

I read the full upstream module locally and independently retrieved its current server
source with `scompile.py --source`. They agree on the declaration and its comparisons.
The signature in `lean.statement` is copied verbatim from `theorem` up to `:=`;
its preceding section variables are `Λ : Type (u + 1)`, `[CommRing Λ]`, the four schemes,
and the four square arrows. The compilation probe checks the fully quantified type.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node clause | Existing Lean expression |
| --- | --- |
| Finite discrete commutative coefficient ring Λ | Specialize the existing parameter `Λ : Type (u + 1)` with `[CommRing Λ]` to a finite ring. Fixed-ring `ModuleCat Λ` is the discrete coefficient encoding: no topology on Λ is used by these functors. The declaration already states the same transport equation for every commutative coefficient ring, so finiteness is not needed by the equation. No new stronger theorem is introduced. |
| Four schemes and arrows in the chosen cartesian square | The explicit section variables `X' X Y' Y`, `g' f' f g` and `(sq : IsPullback g' f' f g)`. This expresses the universal property of the chosen identification in `ChosenCartesianSquare`; the statement and the named maps use only `sq.toCommSq`. Different choices of the fibre-product identification produce the same commutativity proof and same maps. |
| f and f' quasi-compact and quasi-separated | `[QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']`. There is no condition on g or g'. |
| L belongs to D⁺(X_et,Λ) | `(L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))`. This is the exact fixed-ring encoding of the derived-categories dependency. |
| Precisely the constant ring at each pro-etale corner | The coefficient category is `Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)` throughout. This is the fixed-ring presentation of modules over the constant ring, not modules over a scheme's structure sheaf or condensed coefficients. The recorded `finiteCoefficientRealization T Λ` is the associated-module-sheaf functor from exactly this category to `FiniteCoefficientModules T Λ`, built along `finiteCoefficientScalarMap`. |
| Canonical constant-ring structure maps on all four edges | Fixed scalars act sectionwise; direct image is evaluation after fibre-product base change. Under the constant-preserving ring identifications these are the specified structure maps. Pullback is the same scalar-preserving inverse image. In the ringed presentation its identification with tensor pullback is the node's `m ⊗ r ↦ c⁻¹(r)m`, inverse `m ↦ m ⊗ 1`; it is compatible with restrictions and composites by tensor balancing. This is a change of the existing constant-ring presentation, not an arbitrary map or additional coefficient hypothesis. |
| A_T = ν_T* | `(comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory`; the `Plus.ι` in the equation includes the bounded-below étale object into the unbounded derived category before applying A_T. The recorded ringed comparison `finiteCoefficientDerivedComparison` is termwise comparison followed by the canonical coefficient realization. |
| l_u and r_u | `(Etale.upperStar (ModuleCat Λ) u).mapDerivedCategoryPlus` and `(Etale.lowerStar (ModuleCat Λ) u).rightDerivedFunctorPlus`. |
| p_u and s_u, ordinary uncompleted operations | `(ProEtale.upperStar (ModuleCat Λ) u).leftDerivedFunctor` and `(ProEtale.lowerStar (ModuleCat Λ) u).rightDerivedFunctor`. `leftDerivedUpperStarIsoMapDerivedCategory` identifies p_u with exact termwise pullback. The right derived functor uses K-injectives in all module sheaves; no completion or constructibility is imposed. |
| The specified pullback comparison a_u | `leftDerivedUpperStarComparisonIso u Λ`. Its body derives `(comparisonUpperStarCompUpperStarIso (ModuleCat Λ) u).symm`, then inserts the canonical exact/K-flat derived-functor comparison. The underived iso is the adjunction conjugate of `lowerStarCompComparisonLowerStarIso`, the same specified comparison used by `comparisonCoefficientPullbackIso`. |
| The specified direct-image counit mate b_u | `rightDerivedLowerStarComparisonIso' u (ModuleCat Λ)`. Its bounded-below factor is `asIso (rightDerivedFunctorPlusBaseChange (lowerStarComparisonUpperStarBaseChange u (ModuleCat Λ)))`. The underived map is the mate of the evaluation/restriction identity, not a selected member of `Nonempty`. Its derived map is characterized by compatibility with the derived-functor units, and the derived adjunction is induced from the same module adjunction. Thus its transpose is `A_U(εᵉ) ∘ a⁻¹`; the counit normalization follows by the adjunction transpose identity. The final factors are the fixed Plus/unbounded compatibility isomorphisms. |
| S_L = p_g(b_f,L) ∘ a_g,r_fL | `(baseChangeSourceComparisonIso f g Λ).hom.app L`. Its definition is precisely `isoWhiskerLeft Rf (leftDerivedUpperStarComparisonIso g Λ)` followed by `isoWhiskerRight (rightDerivedLowerStarComparisonIso' f ...) Lg`. Functor composition in Lean runs from left to right. |
| T_L = s_f'(a_g',L) ∘ b_f',l_g'L | `(baseChangeTargetComparisonIso g' f' Λ).hom.app L`. Its definition first applies the f' direct-image comparison at l_g'L, then applies s_f' to the g' pullback comparison. |
| Specified étale module exchange E_L | `(Etale.baseChange (ModuleCat Λ) sq.toCommSq).app L`. `baseChange` is the abbreviation for `derivedBaseChangeMapPlus`, the declaration recorded by the derived-exchange node. The module/abelian compatibility dependency records its identification after forgetting coefficients. |
| Precisely the ambient unit–square–counit exchange | `(ProEtale.derivedBaseChangeMap (ModuleCat Λ) sq.toCommSq).app (A_X.obj (Plus.ι.obj L))`. Its definition is literally `mateEquiv` of `leftDerivedUpperStarSquareIso` under `derivedUpperStarLowerStarAdjunction f` and its f' counterpart. The square iso is the inverse composite comparison, commutativity transport, and forward composite comparison, exactly the ambient-ringed definition under constant-ring identifications. |
| T_L ∘ A_Y'(E_L) = Ex ∘ S_L | The displayed theorem's left side is `D(ν*).map (Plus.ι.map E_L) ≫ T_L.hom` and its right side is `S_L.hom ≫ Ex.app (A_X L)`. These are exactly the two composites in the node. |
| Identification by conjugation | S_L and T_L are declared natural isomorphisms, so the equality is the asserted conjugation identity. Its source and target are the specified inverse-image/direct-image composites, with no degree, stalk, properness, or bounded-constructibility restriction. |

The ringed and fixed-ring presentations here describe the same constant coefficient
objects and canonical operations. In particular the attachment does not claim that
`FiniteCoefficientModules T Λ` is definitionally equal to the fixed-ring sheaf category.
The finite-coefficient definition supplies the canonical sheafification realization;
the constant-ring-map node identifies the coefficient sheaf with the constant sheaf
preserving scalars, including on empty objects. On those identifications the source's
fixed-ring mate is precisely the ambient ringed mate. This is the constant-coefficient
specialization explicitly requested in the node, not a second definition of exchange.

Dependency declarations read:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `ChosenCartesianSquare`, with
  `isoPullback`, `hom_fst`, `hom_snd`, and inherited `CommSq`.
- `Sheaf.AlgebraicGeometry.DerivedCategories` and upstream Etale/Derived/Coefficients:
  `Etale.DerivedCategoryModule`; Mathlib's `DerivedCategory.Plus` and its inclusion.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `finiteCoefficientRingSheaf`,
  `FiniteCoefficientModules`, `FiniteCoefficientDerivedCategory`,
  `finiteCoefficientRealization`, `finiteCoefficientComparison`, and
  `finiteCoefficientDerivedComparison`, including their full docstrings and signatures.
- The constant-ring-map dependency currently has no `lean` record. I inspected the
  Q05 delivered `ProEtaleConstantRingMap` module and its node: the actual map is built
  by fibre-product pullback of continuous functions, sheafification, and adjunction;
  the statement includes invertibility and agreement on constants. This delivery
  does not copy or redefine that dependency, because the item already exists.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `proEtaleSiteComparisonModules`,
  whose two functors and adjunction are the upstream `comparisonUpperStar`,
  `comparisonLowerStar`, `comparisonAdjunction` used by the existing theorem.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage` publicly reexports
  the identified-coefficient `proEtaleRingDerivedPullback`,
  `proEtaleRingDerivedDirectImage`, and normalized `proEtaleRingDerivedAdjunction`.
  I read their full source in `ProEtaleOperations` and
  `ProEtaleOperationsCanonicalAdjunction`, including the tensor-unit normalization.
- `Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence`:
  `comparisonCoefficientPullbackIso` and `comparison_pullback_coherent`; the comparison
  is the conjugate of the same `lowerStarCompComparisonLowerStarIso` used upstream.
- The canonical-mate node has no recorded declaration. Its full statement was read;
  the existing theorem fixes its direct-image maps by the explicit derived base-change
  construction, as described above. No replacement arbitrary iso is supplied.
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`: `isIso_comparisonDirectImagePlus`,
  concerning exactly that `rightDerivedFunctorPlusBaseChange` map. The upstream
  `rightDerivedLowerStarComparisonPlusIso` constructs its isomorphism from the same map.
- `WeilConjectures.SixFunctors.BaseChange.Derived`:
  `Etale.derivedBaseChangeMapPlus` and its `Etale.baseChange` abbreviation.
- `Sheaf.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility`:
  `Etale.moduleAbelianDerivedExchange_compatibility`, with the exact module exchange.
- The ambient-ringed node has no record. I read its whole statement and the NA sandbox
  module `ProEtaleAmbientRingedExchange`; both define the mate of the specified
  derived composition square, as does the upstream fixed-ring `derivedBaseChangeMap`.
- `ProEtaleDerivedPullbackComposition` and upstream ProEtale/Derived/UpperLowerStar:
  the canonical composition and square isomorphisms, and both derived adjunctions.

No dependency module is needed for an existing-declaration attachment. In particular
none of the three currently unrecorded dependencies is silently replaced by a fresh
axiom or extra assumption. Their statements and the node's expanded proof remain the
stage-3 route; the existing theorem already states the resulting transport equality.

The natural-language proof remains the node's five-step proof, rather than being
inferred from the theorem's `sorry`: identify constant-ring tensor pullbacks with
scalar-transported inverse image; use the normalized direct-image counit mate; derive
its unit face by transposing and the triangle identity; use the pullback comparison's
cartesian-square coherence; transpose the two final composites, use naturality and
the two counit equations to identify them, and invoke injectivity of the adjunction
bijection. The upstream proof is still open. No new postponed theorem or data choice
is introduced by this delivery.

Edge cases checked: identity squares, arbitrary g and g', zero complexes, the zero
ring, and empty corner schemes are included. Constant sections on an empty object
are allowed to coincide; nothing assumes an injective map of constants or connected
components being open. All coefficient categories use `ModuleCat.{u + 1} Λ` with
Λ in `Type (u + 1)`, and all schemes use `Scheme.{u}`; the small pro-etale site's
object universe `u + 1` and morphism universe `u` are retained. There is no auxiliary
independent test-scheme universe, and no hypothesis on characteristic.

Searches made with the prescribed wrapper:

- LeanFinder: `canonical etale pro-etale comparison intertwines derived base change
  exchange maps` returned eight algebraic etale/Kähler candidates, no exact match.
- Loogle: `CategoryTheory.mateEquiv` returned twelve generic mate declarations,
  including `mateEquiv`, `mateEquiv_counit` and pasting laws; these are ingredients.
- LeanSearch: `site comparison functor intertwines etale and pro-etale derived base
  change morphisms` returned service unavailable / Internal Server Error. No verdict
  was inferred from that unavailable search.
- Mathlib grep via wrapper: `comparison_derivedBaseChangeMap|transport.*exchange|exchange.*transport`
  in `CategoryTheory` returned zero matches.
- `rg` of the upstream source for the node id located the exact blueprint docstring
  and declaration in ProEtale/BaseChange/SmoothBaseChange. `rg` for the declaration
  and node id in `lean/Sheaf` and the upstream-name index gave no competing definition.
- Checked available delivery branches for the three unrecorded dependencies before
  considering any additions; Q05 has the constant-ring-map delivery. No addition was
  needed once the exact upstream item declaration was found.

The initial sandbox-only exploration copied NA's ambient-exchange module to test the
available interface. It compiled through `scompile.py`, but was removed from `lean/`
in this sandbox once the existing item was found. It is not part of this delivery.

Validation: the scratchpad probe compiled cleanly through `scompile.py`, checking
the theorem and both endpoint comparison signatures. `#print axioms` returned
`[propext, sorryAx, Classical.choice, Quot.sound]`, as expected for the existing
stage-2 statement; this is not a claim of sorry-freeness. The delivery wrapper also
checks the existing declaration through a separate import-and-`#check` probe. No source library file was edited or rebuilt.
No statement correction, new node, dependency-record change, or disputed statement.
The independent second reader will audit this existing-declaration match and deliver.

Process note: during dependency discovery I mistakenly ran read-only `git ls-remote`
and `git show` commands from the shared checkout, despite the brief prohibiting all
direct Git commands there. They made no repository or source changes. Subsequent
validation and delivery bookkeeping use the prescribed wrappers only.

## Earlier second reading (a previous round; superseded)

Independent second reader, 2026-10-16. I read the sandbox node before the
attachment, then the full local upstream `SmoothBaseChange.lean` and its current
source returned by `scompile.py --source`. The theorem is at lines 158–169;
lines 141–157 are its docstring. I also opened the dependency node records and
the declarations discussed below, rather than relying on their names or on the
first reader's correspondence table.

Source check: the blueprint source is available on this machine under
`/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/`, rather
than under the shared clone's unpopulated literature directory. Its statement
identifies the transported exchange with the ambient unit–square–counit map;
its proof expands these maps through the comparison adjunctions. I read that
file, the two module lemmas in `sites-modules.tex` (labels
`lemma-pullback-module` and `lemma-adjoint-push-pull-modules`), and the mate and
composite-counit lemmas in `categories.tex` (labels
`lemma-transformation-between-functors-and-adjoints` and
`lemma-compose-counits`). These assume sites, a geometric morphism, a ring
sheaf, and the relevant adjunctions; there is no standing Noetherian,
properness, characteristic, or smoothness assumption. The smoothness and
invertible-integer assumptions in the upstream module's introduction belong
to its later smooth-base-change theorem, not to this theorem: the fully
quantified compiler output confirms this distinction.

The node's objects, hypotheses and conclusions, in order, and my verdicts:

1. A finite discrete commutative ring Lambda. The section parameters are
   `Λ : Type (u + 1)` and `[CommRing Λ]`. Verdict: usable existing theorem,
   specialized to the node's finite ring. It proves the same equation even
   without finiteness. It introduces no finiteness conclusion or additional
   coefficient hypothesis. Discreteness is encoded by fixed scalar actions,
   not by replacing the coefficient object with a condensed ring.
2. Four schemes, their four arrows, and the chosen Cartesian identification.
   The quantified schemes and arrows have exactly the node's orientation;
   `sq : IsPullback g' f' f g` gives the Cartesian property. I opened
   `ChosenCartesianSquare`: its `isoPullback`, `hom_fst`, `hom_snd`, and
   `toCommSq` give this property by Mathlib's
   `IsPullback.of_iso_pullback`. Conversely `IsPullback.isoPullback` has both
   projection equations. The only use in the displayed maps is `sq.toCommSq`;
   those comparisons factor through the composite-arrow equality. Verdict:
   equivalent presentation, with no lost choice-dependent conclusion.
3. Quasi-compactness and quasi-separatedness of f and f'. These are exactly
   the four explicit class arguments. There are no assumptions on g or g'.
   Verdict: exact.
4. L in the bounded below etale derived category. The binder is
   `DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
   I checked `Etale.DerivedCategoryModule` and the recorded derived-categories
   node: this is its fixed-ring encoding. Verdict: exact, not bounded or
   constructible complexes only.
5. Precisely the constant pro-etale ring at every corner, with the canonical
   structure isomorphisms on all edges. Here the existing theorem is written
   in fixed-ring module sheaves. I opened `ProEtaleFiniteModules`: its
   `finiteCoefficientRingSheaf` is the specified sheafified continuous-function
   presheaf; `finiteCoefficientScalarMap` and `finiteCoefficientRealization`
   give the canonical associated-module-sheaf presentation. I also read the
   delivered Q05 `ProEtaleConstantRingMap` source and its normalized map on
   constants. On a cover where a coefficient section is constant, module
   actions and linear maps are exactly the fixed-Lambda actions and maps;
   sheaf gluing extends them uniquely. Pullback preserves those constants,
   and direct image is evaluation on the fibre product. Thus the fixed-ring
   operations present these particular ringed operations. Verdict: the same
   constant coefficients and maps under the node's specified identifications,
   not a claim of definitional equality of the categories.
6. A_T is the derived site-comparison inverse image. This is
   `(comparisonUpperStar (ModuleCat Λ) T).mapDerivedCategory`; `Plus.ι` merely
   includes its input into D. I read `proEtaleSiteComparisonModules` and
   `finiteCoefficientComparison`/`finiteCoefficientDerivedComparison`:
   the latter apply exactly this functor followed by the canonical
   coefficient realization. Verdict: exact under the preceding presentation.
7. The pairs l_u,r_u and p_u,s_u are the ordinary derived adjoint pairs.
   They are respectively `mapDerivedCategoryPlus`, `rightDerivedFunctorPlus`,
   `leftDerivedFunctor`, and `rightDerivedFunctor` of the corresponding
   `upperStar`/`lowerStar`. I read the arbitrary identified-coefficient
   operations and their canonical adjunction, reexported by the recorded
   `ProEtaleConstantDerivedDirectImage`. Their tensor-unit normalization is
   `m ↦ 1 ⊗ m`; transport by the coefficient isomorphism sends `r ⊗ m` to
   `c.inv(r)m`. This recovers the same inverse-image module adjunction, not
   an arbitrary adjunction on the same functors. Exactness identifies the
   left derived functor with the termwise functor. Verdict: ordinary
   uncompleted operations; no extra completeness assumption.
8. The specified pullback comparison a_u. Its Lean name is
   `leftDerivedUpperStarComparisonIso`. In `LowerStarAcyclic.lean`,
   `comparisonUpperStarCompUpperStarIso` is the adjunction conjugate of
   `lowerStarCompComparisonLowerStarIso`; the derived comparison uses its
   inverse, in the direction A_U l_u to p_u A_V. I compared this with
   `comparisonCoefficientPullbackIso` in the recorded coherent-comparison
   module: the same conjugate and inverse occur. Verdict: the specified map,
   with the correct direction.
9. The counit-mate b_f and b_f'. These are
   `rightDerivedLowerStarComparisonIso'`. Its bounded below factor is
   `asIso (rightDerivedFunctorPlusBaseChange
   (lowerStarComparisonUpperStarBaseChange u (ModuleCat Λ)))`.
   I opened `LowerStar.lean`: the underived map is the mate of the inverse
   restriction comparison. Under the pullback adjunction its transpose is
   a_u inverse followed by the etale counit, as required by the node.
   `PlusBaseChange.lean` constructs the derived map by `rightDerivedDesc`
   from that termwise map followed by the derived unit; its factorization
   fixes this map, rather than choosing some isomorphism. Deriving the same
   adjunction gives the same counit transpose. The remaining factors are
   the canonical Plus/unbounded compatibilities. Verdict: correct canonical
   mate and normalization. The separate canonical-mate node is still an
   obligation to formalize/prove, not an extra assumed isomorphism in this
   attachment.
10. S_L is a_g at r_f L followed by p_g(b_f). Expanding
    `baseChangeSourceComparisonIso` gives precisely the left whiskering of
    a_g followed by the right whiskering of b_f. Verdict: exact order.
11. T_L is b_f' at l_g' L followed by s_f'(a_g'). Expanding
    `baseChangeTargetComparisonIso` gives precisely these two whiskerings.
    Verdict: exact order.
12. The specified module etale exchange E_L. `Etale.baseChange` abbreviates
    `Etale.derivedBaseChangeMapPlus`, the recorded dependency's map. I opened
    that definition and `moduleAbelianDerivedExchange_compatibility` with
    its source and target comparisons: it is this very module map whose
    forgotten map is the specified abelian exchange. Verdict: exact map,
    not a stalkwise or degreewise substitute.
13. Precisely the ambient ringed unit–square–counit exchange at A_X L.
    I opened the now-landed `ProEtaleAmbientRingedExchange`, including the
    normalized composition comparison it selects, and upstream
    `ProEtale.derivedBaseChangeMap`. Both are `mateEquiv` of the inverse
    f',g composition comparison, the commutativity transport, and the
    forward g',f comparison. In constant coefficients, both tensor
    composition identifications multiply the same scalars on pure tensors;
    the tensor-unit-normalized adjunction identifies their units and
    counits. Exact termwise derivation retains that comparison. Verdict:
    this is the ambient map after the constant-ring identifications,
    rather than a newly chosen exchange.
14. The concluding equality is T_L after A_Y'(E_L) equals Ex after S_L.
    Lean composition is written in the opposite textual order from the
    node's function notation: its left side is `A.map (Plus.ι.map E_L) ≫
    T.hom.app L`, and its right side is `S.hom.app L ≫ Ex.app (A.obj L)`.
    Verdict: exactly the displayed equality, with its full source and target.
15. The asserted conjugation identification follows because the endpoint
    comparisons are isomorphisms by their types. The source and target
    of the last map are p_g s_f(A_X L) and s_f' p_g'(A_X L), which become
    the stated inverse-image/direct-image composites in constant
    coefficients. Verdict: every conclusion is retained; there is no
    additional assertion that exchange itself is invertible.

Edge cases: the four scheme parameters may be empty, and the coefficient ring
may be the zero ring. On an empty site object the empty covering gives the
unique section; the constants argument above does not assume distinct
constant sections there. Zero complexes and identity squares are allowed.
There is no index family, degree n, chosen cohomological lower bound,
nonzero characteristic, or invertible integer in the statement. The bound
in `Plus` is existential; the theorem does not fix it. All schemes share
arbitrary universe u; coefficients and module carriers are in u+1. The
small sites retain object universe u+1 and morphism universe u, as do the
recorded dependency interfaces. The elaborated `#check @...` shows no extra
category, flatness, or smallness parameters beyond those supplied canonically
for these module categories.

Independent searches, using different queries from the first reader:

- LeanFinder through `msearch.py`: `derived change of sites conjugation
  compatibility unit counit base change morphism`. Eight results included
  the generic derived-adjunction unit/counit factorization lemmas and
  `sheafComposeNatIso`; none was another exact transport statement.
- Loogle through `msearch.py`: `CategoryTheory.conjugateEquiv`. Twelve
  results give conjugation and its normalization laws, not this theorem.
- LeanSearch through `msearch.py`: `Transport of a derived exchange
  transformation by the canonical comparison from etale to pro etale
  sheaves`. Service unavailable / Internal Server Error; no negative
  mathematical verdict is inferred.
- `rg` on Mathlib CategoryTheory for exchange/transport and comparison/base
  change found no exact statement. `rg` on upstream SixFunctors for
  exchange/comparison, conjugation/base change and the blueprint id found
  the existing `comparison_derivedBaseChangeMap`. Searching `lean/Sheaf`
  found module/abelian and bounded/unbounded exchange comparisons, which
  concern different comparison functors, and the ambient exchange
  definition, not a competing definition of this transport equality.
  Neither `lean/Sheaf` nor the upstream name index supplied another exact
  declaration under the item's id or the existing declaration name.

Repairs and delivery verdict: no mathematical mismatch found in the existing
attachment, so I did not restate the theorem, alter its signature, change
node hypotheses, or add dependency modules. No new nodes or statement
correction are present. The earlier report's statement that the ambient
exchange has no record is stale: it is now recorded, and I read its landed
module above. The source docstring describes this exact theorem but does not
carry the DAG's later expanded five-step proof. Since the existing source is
read-only and the contract requires reuse, that expansion remains in the
unchanged DAG proof and the worker report: constant-ring tensor
identification; the fixed counit mate; the forced unit equation; pullback
square coherence; equality of the two transposes. No new theorem with an
incomplete proof docstring is introduced. All data definitions used here
have actual constructions; no arbitrary `Nonempty` choice is substituted
for a canonical map.

Validation: a byte-for-byte extraction of the source theorem signature,
from `theorem` to `:=`, equals the sandbox `lean.statement`. A JSON comparison
with the current base confirms that only the `lean` field differs. I reran
`scompile.py Q44 lem-weil-pbc-transport-identifies-exchange
scratchpad/ExistingCheck.lean` using the absolute sandbox path: both wrapper
checks passed without errors or warnings. Its full quantified output checks
the theorem and both endpoint comparison isomorphisms, with no unbound
variables. `#print axioms` still includes `sorryAx`; this delivery records an
existing stage-2 statement and does not certify a completed proof. No Lean
module is delivered, so there are no sibling modules to compile.

Delivery-tool failure: I ran the prescribed `deliver2.py Q44
lem-weil-pbc-transport-identifies-exchange --no-push` twice. Both attempts
failed before preflight or pushing: `deliver2.py` line 59 calls
`scompile.run_many`; its local attempt falls back to `run_server`, whose
line 40 rereads the wrapper-created probe and raises `FileNotFoundError`.
The missing files were `/tmp/nt-stage2-probes-oeq2vdrg/ExistingChecks.lean`
and `/tmp/nt-stage2-probes-_r7q_i02/ExistingChecks.lean`, respectively.
The direct `scompile.py` scratch probe had already compiled successfully.
No delivery commit was reported. I did not modify or bypass the compiler
or delivery tools; delivery is blocked by this repeated temporary-probe
failure, not by a missing mathematical interface.

## Second reading by Q44

Independent second reading, 2026-10-16, after the earlier delivery-tool failure.
I opened the sandbox node, its blueprint source, the current upstream module
from the shared clone, and the same module returned by `scompile.py --source`.
I also opened the dependency records and their declarations; the match below
is based on those constructions, not the blueprint tag alone.

Source hypotheses: Stacks `sites-modules.tex`, lemma-pullback-module (03D2)
and lemma-adjoint-push-pull-modules (03D3), assume a morphism of topoi and a
ring sheaf. The surrounding section adds no Noetherian, smoothness, properness
or characteristic hypothesis. `categories.tex`, the transformation-between-
functors-and-adjoints lemma (0B65) and compose-counits lemma (0DV0), supplies
the counit normalization and pasting formulas. The blueprint source states
conjugation of the specified exchange; the DAG expands precisely that proof.

Objects, hypotheses and conclusions, individually matched:

1. Finite discrete commutative Lambda: section `Λ : Type (u + 1)` and
   `[CommRing Λ]`. Verdict: the existing theorem specializes to every finite
   ring in the node. Fixed-ring module sheaves encode discrete coefficients;
   no topology or condensed coefficient structure is introduced. The existing
   more general theorem needs no finiteness, so no new strengthened statement
   is delivered.
2. Four schemes and oriented arrows: the explicit section variables are
   `{X' X Y' Y : Scheme.{u}}`, `g' : X' ⟶ X`, `f' : X' ⟶ Y'`,
   `f : X ⟶ Y`, `g : Y' ⟶ Y`. Verdict: exact objects and orientation.
3. Chosen cartesian square: `sq : IsPullback g' f' f g`. I read
   `ChosenCartesianSquare`, whose isomorphism and two projection equations
   give this universal property. Conversely a pullback square supplies its
   canonical isomorphism to the chosen fibre product. Only `sq.toCommSq`
   enters either exchange. Verdict: equivalent square presentation; there
   is no conclusion depending on additional choice of identification.
4. The four qcqs hypotheses: `[QuasiCompact f] [QuasiSeparated f]`
   and `[QuasiCompact f'] [QuasiSeparated f']`. Verdict: exact; neither
   horizontal arrow is required qcqs, and properness is absent.
5. Bounded below etale L: the explicit `DerivedCategory.Plus (Sheaf
   X.smallEtaleTopology (ModuleCat.{u + 1} Λ))` binder. The recorded
   `DerivedCategories` module uses this same coefficient encoding.
   Verdict: exact, with an existential cohomological lower bound.
6. The specified constant ring on every pro-etale corner: the upstream
   coefficient category is `Sheaf (Scheme.ProEt.topology T) (ModuleCat Λ)`.
   I read `ProEtaleFiniteModules`, including its continuous-function
   coefficient sheaf, constants, scalar map, module realization and exactness.
   The constants-to-functions map is locally bijective: open level sets
   trivialize each function, including the empty cover. Its associated-module
   sheafification realizes fixed-ring module sheaves as the node's modules.
   Verdict: the same constant-ring presentation, not a claim of definitional
   equality with `FiniteCoefficientModules`.
7. Canonical structure maps on all four edges: I read Q05's delivered
   `ProEtaleConstantRingMap`, including `finiteCoefficientInverseImageMap`,
   its invertibility and its constant-preserving comparison equation. Its
   direct-image map pulls functions back by the fibre-product projection.
   In the fixed-ring presentation the same constant scalar acts before and
   after restriction. Verdict: these canonical maps, with compatible square
   composites, rather than freely chosen coefficient isomorphisms.
8. A_T: `(comparisonUpperStar (ModuleCat Λ) T).mapDerivedCategory`.
   `ProEtaleSiteComparison.proEtaleSiteComparisonModules` uses exactly its
   underived adjunction, and `finiteCoefficientDerivedComparison` derives it
   followed by the canonical realization. Verdict: the specified comparison.
9. l_u,r_u,p_u,s_u: etale `upperStar.mapDerivedCategoryPlus`, etale
   `lowerStar.rightDerivedFunctorPlus`, pro-etale `upperStar.leftDerivedFunctor`
   and `lowerStar.rightDerivedFunctor`. I read `ProEtaleOperations` and
   `ProEtaleOperationsCanonicalAdjunction`, reexported by the recorded
   operations module. Tensor extension along c identifies with transported
   action by `r ⊗ m ↦ c.inv(r)m`, inverse `m ↦ 1 ⊗ m`; its normalized Hom
   equivalence is the inverse-image module adjunction. Verdict: ordinary
   uncompleted operations on all modules; no extra completeness restriction.
10. Specified a_u: `leftDerivedUpperStarComparisonIso`. Its underived factor
    is the inverse of `comparisonUpperStarCompUpperStarIso`, which conjugates
    `lowerStarCompComparisonLowerStarIso`. I opened the recorded
    `comparisonCoefficientPullbackIso`; it has that same conjugate and
    orientation. Verdict: the specified comparison, including its square
    normalization, followed by the exact/left-derived compatibility.
11. Specified b_f,b_f': `rightDerivedLowerStarComparisonIso'`. Its main factor
    is `asIso (rightDerivedFunctorPlusBaseChange
    (lowerStarComparisonUpperStarBaseChange u (ModuleCat Λ)))`.
    `LowerStar.lean` constructs the inner map as the mate of the inverse
    restriction comparison. `PlusBaseChange.lean` derives that fixed map by
    `rightDerivedDesc` and fixes it by its unit factorization. Conjugating
    the same restriction comparison along the edge adjunction instead gives
    a_u; the mate correspondence therefore gives the transpose
    `A_U(εᵉ) ∘ a_u⁻¹`. The derived adjunction comes from those same module
    adjunctions. Verdict: the specified counit mate, not just existence of
    some isomorphism. Plus/unbounded compatibility contributes only the
    displayed canonical inclusion isomorphisms.
12. S_L: expanding `baseChangeSourceComparisonIso` first applies a_g at r_f L,
    then p_g to b_f. Verdict: exactly `p_g(b_f) ∘ a_g`.
13. T_L: expanding `baseChangeTargetComparisonIso` first applies b_f' at
    l_g' L, then s_f' to a_g'. Verdict: exactly `s_f'(a_g') ∘ b_f'`.
14. E_L: `Etale.baseChange (ModuleCat Λ) sq.toCommSq` abbreviates the recorded
    `Etale.derivedBaseChangeMapPlus`. I read that definition and
    `moduleAbelianDerivedExchange_compatibility`, including its fixed source
    and target comparisons. Verdict: the specified module exchange.
15. Ambient Ex at A_X L: upstream `ProEtale.derivedBaseChangeMap` is literally
    `mateEquiv` of `leftDerivedUpperStarSquareIso`; that square is inverse
    composition, transport by commutativity, then forward composition.
    I opened the now-landed `ProEtaleAmbientRingedExchange` and its normalized
    composition comparison. Constant-ring tensor identification preserves
    this comparison (iterated tensors multiply the same scalars) and the
    tensor-unit-normalized adjunction. Verdict: precisely its constant-ring
    specialization, with source p_g s_f A_X L and target s_f' p_g' A_X L.
16. Final equation: Lean's left side is `A.map (Plus.ι.map E_L) ≫ T_L.hom`;
    the right side is `S_L.hom ≫ Ex.app (A_X L)`. Verdict: exactly
    `T_L ∘ A(E_L) = Ex ∘ S_L`, with the correct common endpoints.
17. Conjugation: both endpoint comparisons have natural-isomorphism types.
    Verdict: the equation identifies the two named exchange maps by
    conjugation; it does not assert that exchange itself is an isomorphism.

Edge cases: empty schemes, zero complexes, zero coefficient ring, identity
squares and arbitrary horizontal morphisms are all admitted. Empty covers,
not injectivity of constant sections on an empty object, justify the
coefficient identification. There is no index family or degree n to restrict;
all degrees, including zero, occur in the derived category. There is no
characteristic or invertible-integer assumption. The schemes have arbitrary
universe u, coefficients and module carriers u+1; the small pro-etale site
retains object universe u+1 and morphism universe u. Fully quantified compiler
output introduces no extra categorical, flatness or universe-equality premise.

Independent searches this round, using the prescribed `msearch.py` wrapper:
LeanFinder query `compatibility of base change mates with change of topology
and constant coefficients` returned eight algebraic tensor-base-change
candidates, none this statement. Loogle `CategoryTheory.mateEquiv_counit`
found the generic mate normalization lemma, an ingredient only. LeanSearch
`The inverse image from etale to proetale sheaves preserves the canonical base
change natural transformation` was unavailable (Internal Server Error);
I infer no negative result from it. Direct `rg` in Mathlib CategoryTheory,
upstream SixFunctors and project `lean/Sheaf` for comparison/transport with
exchange found this upstream theorem, coefficient-forgetting comparisons,
bounded/unbounded comparisons, and unrelated tensor exchanges. Only the first
is this node. Its blueprint tag and fully expanded signature agree with the
attachment. No duplicate module is needed.

Repairs: no mathematical or signature mismatch found, and no new definitions,
dependency modules or statement correction are needed for this existing
attachment. I added this current audit and verification record. The earlier
worker report's absence-of-ambient-record observation is stale: the recorded
ambient module is now landed and was read above. The canonical-mate and
constant-ring-map nodes still have no base Lean record; I read their complete
statements and Q05's delivered coefficient-map construction. They are not
extra assumptions of this existing theorem. No private replacement is
introduced. The read-only upstream docstring names this node and describes
the equation, but lacks the DAG's later five-step proof expansion. Reuse takes
precedence over restating the theorem merely to rewrite that docstring; the
unchanged DAG and this report retain the proof route: constant tensor
identification, counit normalization, forced unit face by the triangle
identity, square coherence, equality of the two adjunction transposes.
No hollow data definition or new proof was added.

Validation: source extraction from `theorem` to `:=` is byte-for-byte equal
to `lean.statement`; comparison to the current base finds only `lean` changed.
The existing scratch import/fully-quantified-check probe passed `scompile.py`
in both sandbox and library checks, with no error or warning. The existing
stage-2 theorem still uses `sorryAx`; this is not proof completion. There
are no delivered Lean modules or sibling files requiring compilation.
