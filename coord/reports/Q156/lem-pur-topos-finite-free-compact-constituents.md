## Worker report

Q156 states `lem-pur-topos-finite-free-compact-constituents` in
`Sheaf.CategoryTheory.ToposFiniteFreeCompactConstituents`, namespace
`CategoryTheory.ToposFiniteFreeCompact`. The primary declaration is
`finiteFreeCompactConstituents`. The recorded declaration family includes the coordinate,
composition and unit clauses; the primary theorem alone is not the entire node.
All theorem proofs are `sorry`. Definitions contain actual functors, natural transformations,
adjunction mates, or explicit predicates; none chooses unspecified comparison data.

The inherited refusal concerned an already reviewed Q40 stage-1 split. I checked the live
node and queue: the assignment is stage 2 and the node had no Lean record. The explicit
stage handoff in brief-stage2 section 0 applies. This delivery preserves that split and
changes only its `lean` record. There is no released repair note, statement correction,
new DAG node or dependency-record change.

Source read: blueprint main-20261015,
`sec-smooth-purity/sk-thm-purity-transport/sk-thm-purity-transport.proof.md`, Steps 1 and 3,
and the accepted node's full ten-step proof, including its Stacks references 03DI, 03DJ,
03CZ, 07A6, 0D6D and 0D6E. The theorem is the finite-free general-topos constituent
calculation used there, rather than a scheme-only compactification assertion.

Clause-by-clause translation (names below are in the namespace above):

1. Fixed small-site presentations are `Site.C`, `Site.J`, `Site.small`. Sites have independent
   object and morphism universes `u,v`; the coefficient/sheaf universe is `r`. Sheafification
   and local-bijection instances are retained as presentation infrastructure. The three
   sheaf-composition fields have defaults `inferInstance`; caching them avoids repeatedly
   synthesizing the same standard instance. They impose no geometric condition.
   A topos is used through its fixed presented category `Sheaf T.J (Type r)`; a second
   abstract topos or scheme is not substituted for it.
2. `coefficientMap A B T` is the actual constant-sheaf image of `algebraMap A B`, where
   `A B : CommRingCat` and `[Algebra A B]` encode the unital commutative-ring map.
   `Mod T R` is the recorded `ringedSiteModules`/Mathlib `SheafOfModules` category for
   the constant ring. Every derived category is Mathlib's ordinary `DerivedCategory`,
   with a bound `HasDerivedCategory.{w}`; no bounded or completed category is used.
3. `ScalarSite.model` is exactly the recorded `DerivedChangeOfRingsCochainModel`, including
   its actual sheafified ordinary tensor object/map formulas, universal derived pair,
   and K-flat comparison. `res` is the recorded Mathlib restriction; `U` its exact
   localization. `scalar_exact` asserts exactness of ordinary extension and invertibility
   of the universal left-derived comparison on every complex. `S` uses its exact
   termwise model. Thus it is the universal derived extension under the unique
   counit-compatible identification, not another scalar functor.
4. `ScalarSite.adjFormula` is the full normalized ordinary scalar Hom formula from
   `sheafRingDerivedCoefficientAdjunction`: the adjunct sends a local section to
   the sheafification of `1 tensor x`. `scalarAdj` localizes this original adjunction.
   `ScalarSite` retains K-injective resolution and scalar restriction exactness
   infrastructure for the actual module categories, not any boundedness assumption.
5. `Geometric.inverse`, `.direct`, `.geom`, `.leftExact` are precisely the geometric
   morphism in the question. `.liftA/.liftB` use the already published
   `AlgebraicInverseImage`; its ring and module operations are fixed on all generalized
   sections. The fields `constantsA/B` retain the actual constant-section normalization.
   The two `pushUnderlying` and `hom` equations fix module direct image and its
   adjunction by the original geometric Hom bijection. `LA/LB` are exact localized
   inverse images; `RA/RB` are the actual K-injective unbounded right-derived functors;
   `adjA/adjB` use the recorded derived adjunction construction.
6. The restriction square is fixed by `Geometric.restrictionFormula` to the identity
   on underlying inverse images. `tau` localizes precisely that square.
   `tensorPullbackInv` is its inverse scalar mate; `lambda` is the inverse isomorphism.
   Scalar Hom normalization identifies this with the canonical pure-tensor pullback
   comparison: its scalar adjunct is the identity square, so an arbitrary isomorphism
   cannot be substituted. `chi` is literally `mateEquiv (adjA f) (adjB f)` applied
   to `lambda.hom`. This is the counit transpose in the node, with Lean's left-to-right
   functor-composition convention.
7. `Open` specifies an actual subterminal sheaf, a slice equivalence, and an isomorphism
   from the presented inverse image to `Over.star`. Its exact extensions and adjunctions
   include invertible original units. Extension together with this adjunction is the
   universal left-adjoint presentation of extension by zero; comparison to the recorded
   sum-presheaf extension is the unique adjunction-preserving isomorphism. This is also
   how sections and units are transported when the original site does not represent
   the subterminal object. There is no arbitrary map between extensions. `IA/IB` and
   `openAdjA/B` localize those exact ordinary functors and original adjunctions.
8. `betaInv` is the inverse open mate of `lambda.inv`; its docstring gives the
   section-presheaf balancing identification. `betaInv_isIso` states its invertibility,
   and `beta` is the resulting canonical balancing isomorphism. Its source is
   `IA j ⋙ S T`, its target `S V ⋙ IB j`, i.e. exactly `S_T I_A -> I_B S_V`.
   On different presented left adjoints the phrase “same sections” is transported
   through the unique adjunction-preserving identification just described.
9. Finite freeness is explicitly `[Module.Finite A B] [Module.Free A B]`. No properness,
   compactness, finiteness of the topoi, or scheme hypothesis occurs.
   `FA j p = IA j ⋙ RA p` and `FB j p = IB j ⋙ RB p` encode the ordered constituents.
   `compactComparison` is exactly `chi` on `IA` followed by `RB` of `beta`, with the
   displayed canonical associators. `finiteFreeCompactConstituents` gives `IsIso chi`
   and `IsIso compactComparison`; `beta` is already a natural isomorphism. These are
   transformations in the actual B-module derived categories on arbitrary objects.
10. `constantSection` uses the constant presheaf's sheafification unit;
    `tensorSection` applies module tensor sheafification, transported by the model's
    actual object equality. It does not identify all sheaf sections with tensors.
    `BasisCoordinates T b ι` fixes every inclusion on EVERY unbounded complex by
    `x -> b_a tensor x`, together with the exact localization-factorization equation.
    Naturality and the two finite-matrix identities `ι_a q_c = delta_ac` and
    `sum q_a ι_a = 1` say that these are precisely biproduct inclusions and projections.
    This states `US = finite direct sum of identity` without choosing a second
    library biproduct instance or an unconstrained coordinate isomorphism.
11. `finiteFreeCompactCoordinates` quantifies over EVERY `Module.Basis I A B` for a
    finite index `I : Type i`, with an independent index universe. It provides these
    normalized coordinates on X,T,Y. Its first column equation is
    `ιY(RA M) >> U(chi_M) >> restrictionPushforward(S M) = RA(ιT(M))`.
    Its second is `ιT(IA M) >> U(beta_M) = IA(ιX(M)) >> restrictionOpen(S M)`.
    These are exactly all columns of the two canonical finite-biproduct comparisons,
    not merely their invertibility or an existence of some isomorphism.
12. `restrictionPushforward` is the geometric mate of the identity square `tau`.
    `restrictionOpen` is the inverse open mate of `tau.inv`. Their invertibility
    statements give the derived, identity-on-sections comparisons using their original
    adjunctions. `rho` is the inverse direct-image comparison after `RA` of the
    open restriction comparison, with exactly the order specified in proof Step 6.
    The last clause of `finiteFreeCompactConstituents` is the scalar Hom transpose of
    `compactComparison.app M`, equal to `FA.map scalarAdj.unit >> rho.hom.app(S M)`.
13. `Composite` retains the inverse-image compositor on set sheaves and its two module
    lifts, with BOTH underlying-map equations. These are ordinary, section-normalized
    structural identifications, not an arbitrary equality of derived functors.
    `compLA/LB` localize those ordinary compositors. `compRA/RB` are their conjugates
    through the specified derived adjunctions, the normalization of the recorded
    derived-composition theorem. `chi_comp` writes the requested B-linear pasting
    equality with these canonical compositors inserted.
14. `compIA/IB` are the unique left-adjoint compositors conjugate to `compLA/LB`.
    `beta_comp` is precisely the second composition formula in the node. The theorem's
    proof docstring records the inverse-balancing/unit computation of proof Step 9.
15. `open_units_isIso` retains original full faithfulness after localization;
    `openUnitA/B` expose its two components. `beta_unit` is literally the final displayed
    unit-normalization identity, with Lean composition written left-to-right.
16. No comparison definition uses a basis, an injective representative, or a K-flat
    representative choice. The coordinate theorem quantifies over all bases and all
    complexes, and the universal/right-derived functors and their normalized adjunctions
    determine resolution transport. Thus the same B-linear maps and equations are
    independent of both basis and resolution; derived restriction is never asserted
    faithful on morphisms.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.Sites.GrothendieckTopos`: `CategoryTheory.IsGrothendieckTopos`;
  its presentation is instantiated directly by the site's sheaf category.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`: public
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence theorem.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`: the public
  `SheafOfModules.AlgebraicInverseImage` and canonical pure-tensor pullback interface;
  retained transitively by the ringed coefficient presentation import.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`, its inverse, and
  `conjugateIsoEquiv`; these construct all specified comparisons/compositors.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`: `SheafOfModules.restrictScalars`.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`; its full scalar Hom normalization
  is retained in `ScalarSite.adjFormula` and exact localization of that adjunction.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `Sheaf.over`, `GrothendieckTopology.over`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`:
  `localizedSystemExtension`, `localizedSystemRestriction`, `localizedSystemExact`,
  `localizedSystemAdjunction`; these give the concrete localized-site extension and
  exactness model for the open left-adjoint presentation.
- Exact localization: `Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`,
  `mapDerivedCategoryNatIso`, `mapDerivedCategoryCompIso`, and
  `Adjunction.onDerivedCategory` from the published Mathlib/upstream modules.
- Proof-only imports retain `CochainTensorUniverses`, `RingedOpenScalarAdjunction`,
  `RingedCoefficientRestrictionCounit`, `KInjectiveDerivedMapComputation`, and
  `DerivedCategory.CompositionAdjunctionNormalization`. The open scalar module landed
  during this work; its recorded comparison was read and the import added before delivery.

Edge cases checked: the empty basis gives a zero scalar functor, and the empty sum in
`BasisCoordinates` forces the relevant object to be zero; the matrix/column statements
still make sense. Neither A nor B is assumed nonzero. Identity geometric morphisms and
identity or empty opens are included. The open is a slice of a subterminal sheaf, rather
than only a represented object of the input site. Complexes are indexed by all integers,
with no boundedness, constructibility or finite-Tor hypothesis. Site object/Hom and derived
universes are not equated. The finite index universe is independent as well.

Searches (actual results are also in the launcher's `searches.jsonl`):

- LeanFinder: “Finite free extension of constant coefficient sheaves commutes with
  derived direct image and extension by zero with coherent adjunction mates”: 8 hits,
  including free/pullback and pushforward adjunction lemmas, none the full statement.
- LeanSearch: “finite free coefficient extension commutes with unbounded derived direct
  image and extension by zero”: 8 hits, free-module/pullback lemmas, no match.
- Loogle: `CategoryTheory.mateEquiv, SheafOfModules.restrictScalars, Module.Free`: 0 hits;
  repeated with `Module.Basis`: 0 hits.
- Mathlib grep through msearch: `finiteFree|finite_free|scalarComparison` in CategoryTheory:
  0 hits; `finiteFreeCompactConstituents|ToposFiniteFreeCompact`: 0 hits.
- Additional LeanFinder on small-site constant scalar/geometric presentations: 8 module
  presentation/quasicoherence hits, none the present normalized interface.
- `rg` in both live `lean/WeilConjectures` and `lean/Sheaf` for finite-free coordinates,
  scalar comparisons, compact-support constituents and the proposed declaration names:
  existing finite-free scalar coordinate and scheme-specific compact scalar/composition
  modules were read; none states all these arbitrary-topos, unbounded normalized clauses.
- Exact item-id search in `lean/WeilConjectures`: no hits.

Compilation: `scompile.py` compiled the sandbox form and final library module cleanly;
no non-sorry warning remains. The original larger elaboration exceeded 60 seconds;
profiling identified repeated standard sheaf-compose instance synthesis. Caching these
instances in the site data and using named derived functor definitions fixed that issue
without changing any mathematical assumption. The last complete compilation before
final independent-index-universe adjustment took 33.5 s and 33.4 s. Final compile and
maintainer preflight are run again by the required delivery dry run.

No statement dispute or mathematical correction was found.

## Second reading by Q156

The dispatcher explicitly forbids starting other agents; the maintainer supplies the
independent review after delivery. This section records the worker's second reading,
not a claim that a second worker reviewed it.

I reread the node and final module together. I checked both orientations of `lambda`
and `beta`, the `chi` counit-mate definition, the order `IA` then `RA`, the order of the
restriction maps in `rho`, and the domains/codomains in all three coherence equations.
I checked each coordinate on ALL complexes, rather than only K-flat/flat-term inputs:
finite-free extension is exact. The matrix identities make the empty-basis case explicit;
only column equalities would not have done so. I replaced a common index universe with
an independent finite-index universe to retain every chosen finite basis. I also checked
that the open slice is specified for arbitrary subterminal sheaves; no representability
assumption was inserted. All extension identifications preserve the original adjunctions
and hence their units; they cannot be replaced by unrelated comparison isomorphisms.
The named family in `lean.declarations` carries every clause listed above.
