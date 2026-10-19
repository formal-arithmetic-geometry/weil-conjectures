## Worker report

Item: pur9-cs-def-bc. Defines
`AlgebraicGeometry.ProEtale.standingExceptionalBaseChange` in
`Sheaf.Paper.StandingExceptionalBaseChange`. The natural-language statement is unchanged.
There are no new DAG nodes. Two existing dependency bindings are repaired below.

The definition has real data throughout. Its only inverse is the inverse of the specified
exchange, whose invertibility is supplied by the existing finite-coefficient origin theorem.
No arbitrary morphism, unrestricted pro-etale adjunction, or ambient compactification
comparison is assumed. No new theorem about the item's arrow is stated or proved.

Clause-by-clause rendering:

1. The global finite field, distinct coefficient prime, fixed coefficient closure, finite
   subextension and positive level are `P : WeilConjectures.PurityFiniteSetting`.
   `P.field` is the recorded finite-field datum; `P.coefficients` contains the prime
   and its inequality with the characteristic; `P.extension` is the finite subextension;
   `P.level_pos` is `1 ≤ P.level`. `P.Ring` is the existing quotient
   `Padic.coefficientExtensionRing`, and `P.Coefficient` is its standard `ULift` to the
   module-value universe. The local finite instances come from
   `Padic.finite_coefficientExtensionRing`; they are not hypotheses. No ramification-index
   divisibility or unramifiedness condition is imposed. The added statement dependency
   `def-pur-conventions` records use of this already-landed bundle of the same global data.
2. All four schemes have `Over (Spec (.of P.field.k))`, `LocallyOfFiniteType`, and
   `QuasiCompact` structure morphisms. All four arrows have `IsOver` instances. The
   separated finite-type assumption on f is precisely `[IsSeparated f]`,
   `[LocallyOfFiniteType f]`, `[QuasiCompact f]`. No smoothness or flatness is imposed on g.
3. `sq : ChosenCartesianSquare g' f' f g` retains the identification of X' with
   the fiber product and both projection equations. `hsq` is its `IsPullback` witness.
   `c` and `cf'` are the two fixed `Compactification` objects. The auxiliary
   compactification is exactly `c.ofIsPullback hsq`. Quasi-compactness of f' is derived
   by `MorphismProperty.of_isPullback`, not added as a premise.
4. The ordinary etale compact-support right adjoints fixed by the text are explicit
   values `R, adj` and `R', adj'`. Their adjunctions have left functors
   `Etale.rightDerivedLowerShriekOfCompactification A c` and its `cf'` counterpart.
   `H` and `H'` are the recorded `ComparisonClassAdjunction` data from
   `thm-sf-ambient-adjoint-class`, with P exactly `DerivedCategory.plusEtaleOrigin`
   and Q exactly `DerivedCategory.TStructure.t.plus`. Their `homEquiv_normalized`
   and `comparison_normalized` fields enforce the specified compact-support/site
   transport and comparisons; they are not free Hom bijections or arbitrary coherent
   isomorphisms. These parameters make the choices already fixed in the node explicit.
   Their existence is supplied by the dependency theorem (using the finite dimension
   bounds); no additional existence assumption is made, and none is chosen from a
   bare Nonempty assertion with undetermined data.
5. `K : DerivedCategoryFiniteTor A Y` is the existing upstream fixed-module
   presentation of finite-level D^b_ctf. Its predicate is bounded constructibility
   intersected with finite Tor amplitude, tested against every module sheaf.
   At these finite coefficients the constructible comparison theorem identifies
   the etale-origin presentation of bounded constructibility with intrinsic
   bounded constructibility; no narrower constructible condition is introduced.
   `M` is literally `Rnu_Y,* ⋙ R ⋙ nu_X^*` evaluated at K, the unconditional finite
   composite of the exceptional-inverse-image node, with the chosen ordinary adjoint.
6. The source's choice of G and alpha is retained as
   `G : Etale.DerivedCategoryBoundedConstructible A X` and the specified isomorphism
   `alpha : nu_X^* G.obj ≅ M`. The existing constructible-origin/preservation results
   supply such data; the definition takes the choice explicitly as the node requests.
   `W : Scheme.FixedEtaleOriginWitness ...` contains that same G and alpha, with its
   bounded-below proof `G.property.1.1`. It does not replace the witness by mere existence.
7. The pulled-back etale object is
   `G' := (Etale.upperStar A g').mapDerivedCategoryPlus.obj W.complex`.
   `alpha'` is the inverse of `sfDerivedComparisonPullbackIso` followed by exact
   pullback of `W.iso`. Thus it has precisely the source's orientation
   `nu_X'^* u_et^{-1}G ≅ Lu^* M`. `W'` retains this object and this isomorphism.
   `pulledK` uses the exact inverse-image functor on D+; its property supplies the
   lower bound for `Lv^* K` without an extra hypothesis.
8. The auxiliary exchange is the published
   `rightDerivedLowerShriekOfCompactificationBaseChangeMap`: its defining expression
   is the proper derived mate after j_!, followed by the derived canonical open
   base-change isomorphism. The upstream theorem
   `isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app`, explicitly
   tagged thm-cbc-finite-level-proetale, supplies its invertibility on `M, hM`.
   It has arbitrary base change and no constructibility restriction on its origin
   inputs. Its proper/open proof uses exactly the witness and comparison argument
   described in this item's long proper/open paragraph; no alternative trace or
   purity theorem is used to define the exchange.
9. `theta` is `(H'.comparison (c.ofIsPullback hsq) cf').app` at the pulled-back
   origin object. The normalization and cocycle fields of `H'` identify it with
   the canonical compactification comparison from the coherence dependency.
   It is defined only on the allowed class. `thetaL` conjugates it by the named
   `leftDerivedUpperStarIsoMapDerivedCategory` component so its endpoints use the
   derived pullback occurring in the upstream exchange. The definition
   `fixedCompactSupportExchangeChosenComponent` is exactly auxiliary exchange
   followed by `thetaL.hom`, the source's Ex^circ formula at M.
10. `counit := (H.homEquiv c M hM K.obj K.property.plus).symm (𝟙 M)` is exactly
    the prescribed preimage of the identity, for the compactification c actually fixed.
    The final expression first maps the canonical `D(u^{-1}) ≅ Lu^*` inverse through
    `Rf'_!`, then applies `(asIso exchange).inv`, then the canonical
    `Lv^* ≅ D(v^{-1})` component, then `sfFixedDerivedPullback ... g` of `counit`.
    This is the displayed inverse-exchange/pulled-back-counit composite, with only
    its necessary coefficient/pullback-coordinate identifications inserted.
    Applying `H'.homEquiv cf'` gives precisely
    `Lu^* (nu_X^* R Rnu_Y,* K) ⟶ nu_X'^* R' Rnu_Y',* (Lv^*K)`.
    Both transposes use the same chosen ordinary right adjoints and their normalized
    class Hom data. An unrestricted pro-etale exceptional right adjoint never appears.

Dependency declarations read and used, including supporting declarations of their notions:

- sk-def-sf-operations: the closed upstream audit identifies the ordinary etale
  operations in `WeilConjectures.SixFunctors.Etale.{UpperLowerStar.Defs,Derived.LowerShriek,
  Derived.UpperShriek,Derived.Tensor,Derived.Hom,LowerShriek.OpenImmersion.Defs}`.
  The present finite exceptional operation is its clause-(vi) comparison composite.
- def-sf-etale-origin-subcategory: `Sheaf.Paper.EtaleOriginDerivedCategory`,
  `EtaleOriginDerivedCategory` and its forgetful functors. Here no arbitrary functor
  on that category is needed; W and W' retain the existing fixed-module witness,
  and the class used by H and H' is the fully faithful forgetful image.
- def-weil-pbc-etale-origin-witness: `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`,
  `Scheme.FixedEtaleOriginWitness`, its `complex` and `iso` fields, used directly.
- pur713-def-base-changed-compactification: `WeilConjectures.Compactification.BaseChange`,
  `Compactification.ofIsPullback` and both proper/open Cartesian-square lemmas.
- def-compact-support-direct-image-detailed: `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`,
  `Scheme.sfIntrinsicCompactSupport`; its fixed-scalar presentation is the existing
  `rightDerivedLowerShriekOfCompactification`, precisely Di_! followed by Rp_*.
- def-weil-exceptional-inverse-image: `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`,
  `ConstructibleExceptionalCoefficients.System`; the finite formula is available in
  `Sheaf.AlgebraicGeometry.{FixedFiniteExceptionalAt,SfFiniteExceptionalInverseImage}`.
  The definition writes the recorded composite with the explicitly chosen R and adj;
  it does not silently replace c by a compactification chosen through an opaque
  HasCompactification instance. The ordinary adjunction characterizes this R.
- thm-sf-ambient-adjoint-class: `Sheaf.AlgebraicGeometry.EtaleOriginAdjointClass`,
  `ComparisonClassAdjunction` and `exists_comparisonClassAdjunction`;
  `homEquiv`, `comparison`, and their normalization fields are used directly.
- lem-kun-dimension-finite-type: `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `exists_topologicalKrullDim_le`; its bounds justify existence of H and H'. The definition
  neither assumes an additional dimension bound nor chooses one to construct an object.
- lem-sf-proetale-constructible-origin: `Sheaf.Paper.ProEtaleConstructibleOrigin`,
  `constructible_proEtale_origin`, especially the bounded derived equivalence. This
  supplies the retained G, alpha after constructible preservation, as in the node.
- def-weil-derived-pullback-tensor-hom: `Sheaf.Paper.DerivedPullbackTensorHom`,
  `finiteDerivedPullback`; its fixed-scalar presentation is
  `sfFixedDerivedPullback`, exact inverse image applied termwise.
- prop-weil-pbc-inverse-image-modules-exact:
  `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`,
  `etaleInverseImageModulesExact`; the corresponding exact etale `upperStar` is used on G.
- lem-weil-pbc-comparison-pullback:
  `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`,
  `supportSiteComparison_pullback_coherent`; `sfDerivedComparisonPullbackIso`
  in the exceptional dependency is the same canonical inverse-image square, obtained
  by adjunction from restriction-functor fiber-product composition, and applied termwise.
- pur713-def-shriek-exchange: repaired exact existing upstream declaration below.
- thm-cbc-finite-level-proetale: the recorded full ringed interface is
  `Sheaf.Paper.GlobalFiniteLevelCompactSupportBaseChange.globalFiniteLevelCompactSupportBaseChange`.
  Its needed component assertion is already published in
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange` as
  `isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app`; its docstring
  explicitly identifies this DAG node and the exact proper/open exchange.
  That existing assertion is used directly, without another postponed theorem.
- pur713-def-star-exchange: `Sheaf.SecSmoothPurity.FiniteCoefficientDirectImageExchange`,
  `Scheme.proEtaleFiniteCoefficientDirectImageExchange`; in fixed-scalar coordinates
  its proper-factor mate is the existing `ProEtale.derivedBaseChangeMap` used upstream.
- def-weil-pbc-ambient-ringed-exchange: `Sheaf.Paper.PbcActualRingedExchange`,
  `Scheme.pbcActualCompletedAmbientExchange` and its reexported arbitrary-ring mate.
  Its constant-ring specialization has the same unit-square-counit formula as that
  proper-factor map; no completion operation is used here.
- lem-weil-pbc-transport-identifies-exchange:
  `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`,
  `comparison_derivedBaseChangeMap`, used by the existing proper-origin theorem.
- lem-cbc-proetale-extension-zero-comparison:
  `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`,
  `openImmersionLowerShriekComparison_coherence`; its canonical comparison is the
  origin witness for j_!M in the existing compact-support theorem's proof.
- lem-cbc-proetale-extension-zero: `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`,
  `proEtale_extension_by_zero`; exactness and the open adjunction are the existing
  ingredients of termwise descent and uniqueness of the open comparison.
- prop-compactification-coherence-detailed: `Sheaf.Paper.CompactificationCoherence`,
  `compactification_coherence`; its fixed-scalar normalized realization is
  `fixedCompactSupportOriginIso` in `FiniteComparisonClassAdjunction`.
  `H'.comparison_normalized` forces theta to be this comparison on every antecedent.
- pur713-def-shriek-exchange-chosen: replacement dependency module below, specifically
  `fixedCompactSupportExchangeChosenComponent`, used directly.
- Added existing node def-pur-conventions: `Sheaf.Paper.PurityFiniteSetting`,
  `WeilConjectures.PurityFiniteSetting`, used directly for the unchanged global data.

Import scope: the file imports the defining fixed-module/class interfaces and the
current upstream compact-support exchange. Supporting interfaces above are read against
those same canonical notions; their large ringed/global presentation modules are not
redundantly imported where they pull the withdrawn legacy family alongside the current
FiniteCoefficient family. The initial combined import was checked with scompile.py and
failed with duplicate declarations, including
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification` and
`AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv`. Using the exact current upstream
module and smaller already-existing defining modules repairs those import conflicts.
No live source was edited, and no source operation was copied privately.

Edge cases checked: g=id is allowed and the chosen square retains the identity case;
X or Y' may be empty (there is no Nonempty hypothesis or density condition);
K=0 is admitted by the existing full subcategory; n=1 is admitted by level_pos;
ramified E is allowed; g may be nonsmooth and nonflat; cf' is arbitrary and need
not be the base-changed c. A nontrivial choice of alpha is retained and transported,
rather than replaced with an identity or discarded. Module values have universe u+1,
site objects u+1 and site morphisms u; no site-universe equality is imposed.

Searches (actual msearch.py results are also in the sandbox searches.jsonl):

- LeanFinder, "exceptional inverse image base change morphism transpose inverse compact
  support exchange pulled back counit": 8 results concerning categorical/sheaf pullback
  conjugation and counits, no exceptional comparison of the required scope.
- Loogle, "CategoryTheory.Adjunction.homEquiv, CategoryTheory.mateEquiv": 0 results.
- Mathlib grep, `upperShriek.*[Bb]ase|[Bb]aseChange.*[Uu]pperShriek|exceptionalBaseChange`:
  0 results.
- LeanSearch, "exceptional inverse image base change compact support counit": 8 results,
  concerning condensed counits and scalar coextension, no matching definition.
- rg of the source WeilConjectures and shared lean/Sheaf trees, for the item id and
  exceptional/base-change names: no declaration for this node; found
  `smoothExceptionalProEtaleBaseChangeMap`, which uses the base-changed target
  compactification and a different comparison-site/etale-mate presentation; it is not
  this definition with arbitrary cf' and the retained class-restricted transpose.
- Read current server source using `scompile.py --source` for the finite-coefficient
  UpperShriek and LowerShriekBaseChange modules. The latter contains the exact existing
  auxiliary exchange, now reused in the dependency repair; the former's unchosen
  compactification Hom interface cannot be substituted for the fixed-c Hom interface.

No statement correction or mathematical dispute is proposed. The main definition's
class data are explicit choices authorized by the text, with normalization retained.

Validation: the final two modules and the existing-declaration probe passed the required
deliver2.py --no-push compilation and maintainer preflight, with no errors or unexpected
warnings. The dry run printed OK; the final delivery repeats the required checks.

## Dependency modules

`pur713-def-shriek-exchange`: lean-only binding repair to the exact existing
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap`
in the current upstream finite-coefficient module. The old module imports the legacy
family and collides with the current class-adjunction framework. The reused definition
has exactly the proper-mate followed by canonical derived open-extension formula and
retains the auxiliary compactification. It makes no invertibility assertion.
No replacement module or duplicated auxiliary definition is delivered.

`pur713-def-shriek-exchange-chosen`: new module
`Sheaf.Paper.ChosenFixedCompactSupportExchange`, replacing only its Lean binding.
The original module inherits the same legacy import conflict. The finite specialization
`finiteFixedCompactSupportExchangeChosen` states the unchanged coefficient convention,
ordinary unbounded domain, supplied ambient comparison, and postcomposition formula.
`isIso_finiteFixedCompactSupportExchangeChosen_app_iff` states its last clause, with
whole proof `sorry` and the source's complete two-inverse proof in the docstring.
The generic construction and its component helper merely expose the same composition;
the latter permits this item's theta at an origin object without asserting an ambient
theta. Every declaration has this dependency's blueprint tag. No dependency statement,
proof, source, status, or other record field changes.

## Second reading by Q16

Separate local rereading of the node, dependency records and final modules: the coefficient
prime inequality and positive exponent remain in P; all schemes and arrows are over the
fixed k; f has exactly the three separated finite-type classes; g has no smoothness or
flatness class; the chosen compactifications and the pulled-back c are distinct; G and alpha
remain values; W' has the forward etale-to-pro-etale orientation; theta is evaluated on
exactly the pulled-back origin class; the counit is inverse image of id under H; and the
last operation is H' applied to inverse exchange followed by pulled-back counit.
The chosen dependency still assumes an ambient theta only when defining its ambient
transformation, and its component helper does not demand one. All new theorem proofs
are sorry, and all definitions are real constructions.

This rereading caught the opaque HasCompactification choice issue: the original draft
used an unchosen f Hom bijection alongside a fixed-c compact-support functor. It was
replaced with the recorded normalized ComparisonClassAdjunction at exactly c and cf',
retaining the source's explicitly chosen ordinary adjoints and class bijections.
It also caught the derived-pullback versus degreewise-inverse-image endpoints; the final
formula contains the canonical comparisons on both ends of the inverse exchange.
No independent subagent review is claimed: the dispatcher explicitly forbids starting
other agents, and the maintainer performs the independent review of this delivery.
