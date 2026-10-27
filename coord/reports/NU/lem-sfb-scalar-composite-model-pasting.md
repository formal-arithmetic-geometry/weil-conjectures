## Worker report

The module Sheaf.SixFunctors.ScalarCompositeModelPasting states the fixed-model coefficient
pasting equation as scalarCompositeModelPasting, with one sorry and no proofs. Four helper
definitions name the functor Rp_* j_!, its specified coefficient map, exact open composition,
and the model compositor. All have explicit bodies using existing functors and adjunctions.
No new notion or dependency module is needed. The node's statement and dependency lists are
unchanged.

Clause-by-clause correspondence:

- The prime ell is `(ell : ℕ) [Fact ell.Prime]`. The field is `(k : Type u) [Field k]`;
  `[Fact (ringChar k).Prime]` says its characteristic is positive prime, and
  `[Fact (ringChar k ≠ ell)]` excludes ell.
- Λ and Λ' are `ScalarSixRing.{u}`, bundled commutative condensed rings. The morphism
  `a : Λ ⟶ Λ'` has `_ha : ListedCoefficientMap ell a`. This exact inductive predicate
  from the direct-image dependency includes the finite ell-primary, integral and field
  extension, localization, algebraic closure, integral-to-finite continuous maps, and
  their finite composites. Its Qbar endpoint is the finite-subextension condensed ring.
  There is no flatness hypothesis.
- X, B, Y, C, S are objects of `Over (Spec (.of k))`, corresponding to X, Xbar, Y,
  Ybar, S. Every object has LocallyOfFiniteType, QuasiCompact, and IsSeparated on its
  structure morphism, exactly separated finite type over k.
- j, p, i, q are morphisms in this Over category, hence k-morphisms. The open immersions
  j and i have explicit quasi-compactness; p and q are proper. The maps f and g are
  their composites j ≫ p and i ≫ q. Eliminating separately named f and g loses no data:
  the given factorizations determine those morphisms.
- `c : Compactification.BoundaryCompactification (p.left ≫ i.left)` supplies the
  compactification (j',r) with commuting triangle, proper r and quasi-compact open j'.
  `[IsSchemeTheoreticallyDominant c.obj.obj.i]` is its density condition. The middle
  scheme has its own Over structure, the same separated finite-type assumptions, and
  both arrows are k-morphisms, as required by the standing scheme setting.
- `sfbScalarCompactModel Λ j p` is exactly H_f; the same definition at i,q is H_g,
  and at j ≫ j', r ≫ q is H_gf. It uses ordinary unbounded internal-module derived
  categories on the small pro-etale sites, not completed or adic categories.
- `scalarSixChange a V` is the published ordinary derived extension T_V. The map
  `sfbScalarCompactComparison` is gamma for the proper factor, followed by direct
  image of delta for the open factor. Gamma is `scalarDirectImageMate`, the canonical
  unit / inverse pullback comparison / counit mate. Delta is exactly the existing
  `derivedOpenImmersionShriekIso a.hom.hom`, with its published conjugate definition.
- The natural transformations ι and ι' are specified by `_hι` and `_hι'`, each the
  condition `compositionInterchangeIsNormalized` from the recorded interchange node.
  These are specifications of the unique canonical identity-on-Y maps, rather than
  freely chosen interchange arrows or extra geometric hypotheses. The dependency's
  existence/uniqueness clause supplies the maps; uniqueness at each object supplies
  their naturality. Thus quantification over their normalized natural presentations
  states the equation for precisely the canonical maps, independently of presentation.
  No assumption that the target equality holds is made.
- `sfbScalarModelCompositor` first applies Rq_* to ι at j_!K, then the inverse of
  `RootCoordinateFace.lowerComp` (Rr_* then Rq_* to R(qr)_*), then direct image of
  the open composition isomorphism j'_! j_! to (j'j)_!. The latter is the canonical
  left-adjoint composition isomorphism of the existing open adjunctions and canonical
  pullback composition. Thus this is exactly the specified alpha, with all model
  identifications retained.
- `K : ConstantModelConstructibleFiniteTor Λ.X X.left` is precisely K in Dctf: bounded
  constant-model constructible cohomology and finite Tor amplitude.
- The left side of the theorem is T_S(alpha_K), then C_(j'j,qr), in Lean's
  left-to-right composition order. The right side is C_g at H_fK, then H'_g(C_f),
  then alpha' at T_XK. Every functor after comparison uses Λ'. The equality is between
  ambient Λ'-linear derived morphisms, which is exactly equality in Dctf because it
  is a full subcategory. Stability and scalar preservation put the endpoints there;
  no extra endpoint assertions strengthen the node. No second model of gf occurs.

Dependencies read and used:

- def-sfb-derived-open-immersion-shriek-iso and sk-def-sfb-coefficient-change:
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients,
  derivedOpenImmersionShriekIso and coefficientMap (the latter under scalarSixChange).
- det-prop-scalar-six-direct-image: Sheaf.SixFunctors.ScalarSixDirectImage,
  scalarSixDirectImage, ScalarDirectImageMateCoherence.scalarDirectImageMate (in the
  common AlgebraicGeometry.ProEtale.CondensedRing namespace), and ListedCoefficientMap.
- det-prop-scalar-six-pullback: Sheaf.SixFunctors.ScalarSixPullback,
  scalarSixPullback; ScalarSixDefinitions.scalarSixChange and the actual normalized
  open scalar comparison above. Its coherence clauses are proof inputs.
- det-sf-comp-composition-interchange: Sheaf.Paper.ProEtaleProperOpenInterchange,
  properOpenInterchange and compositionInterchangeIsNormalized (including its defining
  open-adjunction hom-equivalence and canonical restriction comparison).
- sk-def-nagata-sketch-data: Sheaf.Compactification.BoundaryRefinement,
  Compactification.BoundaryCompactification and its quasi-compact open condition.
- sk-def-sfb-constructible: Sheaf.Paper.FiniteConstantRingedLocalModel publicly retains
  Sheaf.Paper.CondensedConstantConstructibility.ConstantModelConstructibleFiniteTor.
- sk-def-sfb-dc-setting: the explicit Over binders match the recorded standing setting
  in WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible;
  the theorem ranges over all specified models, rather than choosing compactificationOverField.
- sk-def-sfb-module-derived-pushpull: Sheaf.Paper.CondensedModuleDerivedPushpull,
  moduleObjectDerivedPushforward, used through RootCoordinateFace.lower; this is the
  full composite module pushforward's total derived functor. RootCoordinateFace.lowerComp
  is the canonical composition conjugate to exact pullback composition.
- Proof-only imports: ScalarSixPullback, ScalarSixCtf, CtfStabilityDirectImages.
  The proper/open interchange-square proof node currently has no recorded Lean module,
  so it cannot yet be imported. No declaration of that proof-only prerequisite is
  needed to type this statement; its id and full use are retained in the proof docstring.

Edge cases checked before drafting: empty schemes and zero objects are allowed; neither
nonemptiness nor density of j or i is assumed. Density is required only for the auxiliary
compactification j', as in the node. Identity geometric maps, identity opens, trivial
compactifications, identity coefficient maps, zero finite rings and nonflat finite quotient
maps are included. The empty finite scalar composite at Qbar is included by the recorded
predicate. No bounded-below replacement is used: all functors have unbounded domains, and
only K has the node's Dctf restriction. Site and coefficient universes are the published
u / u+1 convention; no equality of independent universes is imposed.

Searches for an existing statement (2026-10-24 UTC):

- msearch.py leanfinder: "Coefficient change commutes with the compositor on fixed proper
  open compactification models"; eight hits, including OnePoint.map_comp, Scheme.Hom.comp_appLE
  and PrimeSpectrum.BasicConstructibleSetData.map_comp'; no derived condensed coefficient
  pasting statement.
- msearch.py loogle: "CategoryTheory.NatTrans.naturality"; nine hits, including generic
  naturality and pullback/pushout cone isomorphisms. Generic naturality is a proof ingredient,
  not this statement.
- msearch.py grep: "lowerShriek.*[Cc]omp|coefficient.*[Pp]asting"; zero Mathlib hits.
- rg over lean/WeilConjectures: the same concept query finds only an ordinary
  lowerShriek_comp_forget; the exact node id finds nothing.
- rg over lean/Sheaf: examined the scalar composition/model hits. CompactSupportCoefficientChange
  treats finite scalar reduction and cartesian base change in fixed-ring sheaf categories;
  ScalarCompositorReplacementPasting is abstract and assumes its compositor square;
  ProperOpenInterchangeData/Coherence and UnboundedCompactSupportProperComposition use
  finite etale coefficients. None is this all-listed-condensed-coefficient fixed-model
  equation. Existing scalar and interchange definitions above are reused.
- rg over lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for all five
  chosen declaration names: zero matches, avoiding duplicate declarations.

Validation: scompile.py compiled both the sandbox probe and the actual library module
cleanly (33.8 s and 13.4 s). The first compile identified a stale server interface for
scalarSixOpenScalarIso; the final file calls its exact existing underlying published
construction derivedOpenImmersionShriekIso directly. No library file was edited.
No statement dispute or statement correction.

## Second reading by NU

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
