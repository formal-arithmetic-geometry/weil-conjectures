## Worker report

The module `Sheaf.Paper.DerivedOpenSquareRestriction` states
`AlgebraicGeometry.ProEtale.CondensedRing.derived_open_square_restriction`, with
one `sorry`, and four helpers containing actual constructions or a fully expanded
proposition. The node is unchanged except for `lean`. No new nodes, dependency
modules, statement correction or disputed statement are needed.

Hypothesis and clause correspondence:

- Prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`. Positive field characteristic distinct
  from ell: `{k : Type u} [Field k] [Fact (ringChar k).Prime]` and
  `[Fact (ringChar k ≠ ℓ)]`.
- The schemes W, Y and Ybar are `Over (Spec (.of k))`; each structure morphism
  has `LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated`. Thus each is
  separated finite type over k. The arrows `r` and `i` are morphisms in Over,
  hence are k-morphisms. The fibre product inherits this setting.
- Lambda is a condensed abelian sheaf with `MonObj` and `IsCommMonObj`.
  `_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ` uses the recorded admissibility
  predicate, including its finite-subextension-valued `padicAlgClRingObj` case.
  This imported predicate also retains the earlier continuous algebraic-closure
  coefficient as a separate compatibility case; the module never identifies it
  with the finite-subextension ring. The conclusion is valid for both.
- The open immersion and its quasi-compactness are `[IsOpenImmersion i.left]`
  and `[QuasiCompact i.left]`.
- U is exactly `pullback r.left i.left`; j is `pullback.fst r.left i.left`
  and p is `pullback.snd r.left i.left`. All occurrences use this same chosen
  fibre product. Its first projection is an open immersion by the library's
  base-change instance. No independent square or extra cartesian hypothesis
  is supplied.
- Ordinary unbounded module-object derived categories are
  `DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X))`. There is no derived-completeness, boundedness or
  constructibility predicate. Pullback and open extension are `mapDerivedCategory`
  of the existing exact functors. Pushforward is exactly
  `(lowerStar Λ f).rightDerivedFunctor`, the canonical total derived functor
  underlying the recorded `moduleObjectDerivedPushforward` definition. The
  expanded spelling exposes its existing canonical shift instance to elaboration.
- The two derived open adjunctions are the existing
  `derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i.left` and the same
  declaration for j. The first two conjuncts assert `IsIso` of their actual
  units. `moduleOpenUnitIsTermwise` for each open writes the unit on `Q K`,
  followed by the two exact-functor factorization comparisons, equal to `Q`
  applied to the unit of `adj.mapHomologicalComplex (.up ℤ)`. This last unit
  is degreewise the underived sheaf-of-internal-modules unit. Thus these are
  the actual adjunctions and units, with the requested termwise normalization.
- The underived natural isomorphism e is precisely `i_! ⋙ r^* ≅ p^* ⋙ j_!`
  in Lean's left-to-right functor composition. Its inverse is required equal
  to `Adjunction.exchangeLeft` of the two recorded open adjunctions and
  `moduleOpenSquarePullbackComparison`. That helper is the inverse of the
  i,p composition comparison, followed by transport through the pullback
  equation, followed by the r,j comparison. This fixes the canonical open
  base-change isomorphism; it is not an arbitrary isomorphism hypothesis.
- `moduleOpenSquareDerivedExtensionIso` derives e termwise by the actual
  `Functor.mapDerivedCategoryNatIso` and the two canonical exact-composition
  comparisons. No data are chosen from a mere existence theorem.
- The isomorphism rho is between `Rr_* ⋙ D(i^*)` and `D(j^*) ⋙ Rp_*`.
  It is a natural isomorphism of functors on the entire unbounded category
  for W. For arbitrary T, B and arrow a, the equation
  `a ≫ ρ.hom.app B = moduleOpenSquareHomEquiv ... T B a` is the exact
  requested characterization. It determines rho uniquely by taking a to be
  the identity with T equal to its source, without an extra uniqueness axiom.
- `moduleOpenSquareHomEquiv` composes, in order: the inverse Hom bijection
  for i, the inverse canonical D(r*)/Rr_* Hom bijection, `Iso.homCongr` of
  the derived open comparison and `Iso.refl B`, the Hom bijection for j,
  and the canonical D(p*)/Rp_* Hom bijection. `Iso.homCongr e (Iso.refl B)`
  is precomposition with e.inv. These are all five bijections in the node.
- The four `Adjunction.CommShift ℤ` conjuncts cover the two open
  adjunctions and the exact-pullback/canonical-right-derived adjunctions for
  r and p, using the canonical shift structures already on the functors.
  This states compatibility of their units, counits and hence Hom bijections.
  The derived e.hom has `NatTrans.CommShift`, so the middle Hom bijection
  also commutes with simultaneous shift. `NatTrans.CommShift ρ.hom ℤ`
  is the requested canonical composite shift square for rho. Integer shifts,
  including negative shifts, are all covered.
- There is no `IsProper r.left`, no bound on B or T, and no constructibility
  hypothesis. The admissibility premise is kept even though this open
  restriction fact holds for general commutative condensed rings.

Dependency declarations read and used:

- `sk-def-sfb-dc-setting`: the recorded
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `compactificationOverField` and its surrounding setting document the Over
  binders. No compactification is needed in this open-restriction theorem.
- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingAdmissibleCoefficients`,
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`.
- `sk-def-sfb-qlbar-condensed`: the imported
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`,
  `Profinite.padicAlgClCondensedRing` and `Profinite.padicAlgClRingObj`;
  their docstrings distinguish finite-subextension-valued functions.
- `sk-def-sfb-module-derived-pushpull`:
  `Sheaf.Paper.CondensedModuleDerivedPushpull.moduleObjectDerivedPushforward`
  (declaration namespace `AlgebraicGeometry.ProEtale.CondensedRing`), whose
  body is exactly `Functor.rightDerivedFunctor (lowerStar Λ f)`.
  The canonical exact-left/right-derived adjunction used in the node's proof
  is `CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction`
  from `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`.
- `sk-def-sfb-module-derived-lower-shriek`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek`,
  `rightDerivedLowerShriekOfCompactification`; the relevant exact open
  factor is the imported `openImmersionLowerShriek` from `.LowerShriek.Defs`.
  The open derived adjunction is from `.Derived.OpenImmersionLowerShriek`.
- `def-pc-fibre-product`: Mathlib's `CategoryTheory.Limits.pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.condition`.
- `def-weil-open-immersion`: Mathlib's `AlgebraicGeometry.IsOpenImmersion`
  from `Mathlib.AlgebraicGeometry.OpenImmersion`.

Every recorded proof-dependency module is imported, publicly where used in
signatures and otherwise by ordinary import. In particular the proof can use
`ringSheaf_baseChange_mates`, the recorded coefficient/eta composition interfaces,
`existsUnique_mapDerivedCategoryCompIso`, and
`canonicalRightDerivedAdjunctionShift`. Mathlib-only exact factorization,
localization of adjunctions and localization of natural isomorphisms are
available through those imports. No existing dependency is replaced.

Searches (2026-10-21):

- msearch.py leanfinder: "On unbounded derived categories of internal modules
  on the pro-etale site, open restriction commutes with total derived direct
  image in a cartesian square with canonical Hom adjunction chain and shift
  compatibility". Eight hits, all underived scheme-module restriction
  comparisons/adjunctions or a sheaf-module pullback calculation, no match.
- msearch.py loogle: `CategoryTheory.Adjunction,
  CategoryTheory.Functor.mapDerivedCategory`. Zero hits.
- msearch.py grep: `open.*[Bb]ase[Cc]hange|mapDerivedCategoryAdjunction`
  in CategoryTheory. Zero hits.
- rg in `lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject`,
  `lean/Sheaf/Paper` and `lean/Sheaf/CategoryTheory` for open/base-change,
  open-square, restriction/derived patterns located the existing exact open
  adjunction and bounded-constructible open lower-shriek base change.
  The latter is restricted to bounded constructible objects and finiteness
  coefficients, and does not state this theorem or its Hom normalization.
  rg for the item id in `lean/WeilConjectures` returned no matches.
- rg for `openSquare|derivedOpenSquare|DerivedOpenSquare` in `lean/Sheaf`
  and `dag/lean_names_upstream.json` found constant finite-ring sheaf-of-modules
  and strict-tower comparisons, not this internal-condensed-module theorem.
- Read the current source Proof (2) of det-sf-comp-composition-interchange,
  all seven statement dependency node records, the complete eight-step item
  proof, and the source interfaces above. The node itself notes that the
  older direct-image-open-coherence lemma only has an unnormalized
  E/Qbar comparison and does not subsume this result.

Edge cases checked before drafting: i = identity (ordinary canonical comparison),
Y empty (both restricted sides zero), W empty, zero B or T, arbitrary unbounded
complexes, finite torsion coefficients, integral coefficients, the precise
finite-subextension Qbar coefficient, and zero/positive/negative shifts.
The square uses the actual scheme pullback and no properness inference.
The site retains object universe u+1, morphism universe u, Ab universe u+1,
and the existing internal-module derived category universe; no size equality
or auxiliary derived category is imposed.

Validation: scompile.py compiled the sandbox module and actual library-path
module cleanly (6.1 s and 6.6 s), with no warnings other than the permitted
postponed-proof warning (suppressed by project settings). All variables and
universes are explicitly bound. The sole postponed theorem has the source
and complete eight-step natural-language proof in its docstring.

## Second reading by NP

Author's second reading, not an independent reviewer: I reopened the node and
compiling module and checked every premise and clause against the correspondence
above. The maintainer performs the independent delivery review. The first draft
used the recorded named derived pushforward inside the shift proposition; its
non-reducible definition hid the canonical CommShift instance from synthesis.
I changed only the spelling to its exact body `(lowerStar Λ f).rightDerivedFunctor`.
I also repaired field-notation line breaks and a long line. No mathematical
hypothesis or clause changed. The Hom-chain direction was checked explicitly:
its first two adjunction bijections are inverses, its middle operation uses the
inverse derived open isomorphism, and the final two bijections are forwards.
The termwise unit equalities use the actual derived open units, and the shift
claims use the same canonical right-derived adjunctions as the Hom chain.
The e.inv mate equality prevents a freely chosen base-change comparison.
All four helper declarations belong to this node's normalization/construction;
none introduces an independent notion or hides postponed proof data.
