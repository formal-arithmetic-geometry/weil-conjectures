## Worker report

The module `Sheaf.Algebra.Homology.ExternalEvaluationTwoShiftSquares` states
`CategoryTheory.ExternalEvaluation.external_evaluation_two_shift_squares`, with one
`sorry`. Its helper definitions contain actual data or propositions; no theorem is proved.
The statement and proof text of the DAG node are unchanged. The only extra statement
 dependency is the already landed `def-sfb-site-derived-constant-module-functor`, whose
commutative constant-ring presentation is needed for the tensor interface.

Sources read: `literature/stacks-project/sites-cohomology.tex`, section-hom-complexes
(lines 8570–8612), lemma-compose (8616–8635), and lemma-RHom-triangulated
(8948–8966). The node itself supplies the explicit seven-step two-variable calculation;
Stacks supplies the Hom differential, tensor-Hom composition and triangulated context.
The full seven-step argument is in the theorem docstring. The original example module
`lean/Sheaf/CategoryTheory/CompactObject.lean` is now withdrawn and empty; its recorded
upstream module `WeilConjectures.CategoryTheory.CompactObject` was also read for the
actual header, source and declaration conventions.

Hypotheses and clauses, matched with the Lean:

- A commutative ring: `A : Type (max u v)` and `[CommRing A]`. The site is
  `C : Type u`, `[Category.{v} C]`, `S : GrothendieckTopology C`; object and morphism
  universes remain independent. Modules and coefficients live in `max u v`, so the
  site is small in the module universe. This covers arbitrary relative sizes by
  choosing the ambient levels, with no equality imposed on the site universes.
- Modules over the constant ring sheaf: `Modules S A := realizationModules S A`.
  This is the actual `SheafOfModules` category, over the forgotten constant
  commutative ring sheaf. `realizationRingIso` canonically identifies this with
  the recorded constant RingCat sheaf; no new module category is constructed.
- U,V and E,H,N,M,J: `U V : Coeff A`, `E H N M J : Complex S A`. All complexes
  are indexed by all integers. `constantComplex` is termwise application of
  `commutativeSiteConstantModuleFunctor`, the existing sheafification construction
  canonically transported from `siteConstantModuleFunctorGeneral`.
- Tensor and its differential: `tensorComplex` transparently abbreviates the
  dependency's `CochainComplex.mapBifunctor` applied to `curriedTensor`. Coefficient
  tensor is Mathlib's `U ⊗ V`, the same direct-sum total construction.
- Global Hom and differential: `CochainComplex.HomComplex B J` has terms the
  product of actual module-sheaf morphisms `HomComplex.Cochain B J n`, with
  differential `δ`, namely `d_J f - (-1)^n f d_B`. This is global Hom, whereas
  `CategoryTheory.homComplex` from the dependency is internal sheaf Hom; the
  latter is imported, not copied or mistaken for global Hom. Its global cochains
  are the same ordinary cochains, as the existing
  `CategoryTheory.homComplex_global_cochains` interface states.
- A-linearity is retained: the Hom complex is displayed in `AddCommGrpCat`,
  and `IsLinearHomMap` explicitly requires `p(a*x)(y) = const(a) * p(x)(y)`
  in every component over every site object, using `realizationRingUnit`.
  Thus this presentation does not discard the A-linear chain-pairing requirement.
- Arbitrary u,v,i: the three theorem binders have exactly the stated chain-map
  domains and codomains; there is no additional property imposed on them.
- p: existential `p` with `IsExternalPairing`, whose second conjunct spells out
  the `(-1)^(s*q)` formula for every r,s,q,t, site object, coefficient and local
  section. `constantSection`, `tensorSection`, `tensorComplexSection` and
  `coefficientTensor` are the actual sheafification unit and summand inclusions.
  `unsignedEvaluation` applies u,v,i, with equality transports only for total degrees.
  Giving the chain maps and their defining equations existentially states existence
  of these uniquely characterized constructions, rather than selecting arbitrary
  data through a postponed existence theorem.
- Shifts: Mathlib's `⟦1⟧` and `⟦-1⟧` have the source's reindexing and negated
  differentials. `θ B` is an isomorphism and `IsHomShift` gives exactly
  `(θ f)^j = (-1)^n f^(j-1)`, including the required index transport.
- The shifted evaluations: `ηU`, `ηV` are isomorphisms satisfying
  `IsBalancingShift`, exactly multiplication by `(-1)^r` in the shifted coefficient
  degree. `pE`, `pH` satisfy `IsExternalPairing` with `ηU.hom ≫ u` and `ηV.hom ≫ v`
  and the correct shifted coefficient/complex. These comparisons are conclusions,
  not extra hypotheses.
- τ1,τ2,κE,κH: `coefficientShift₁/₂ A U V (-1)` and
  `tensorShift₁/₂ S A E H 1` transparently use the existing
  `mapBifunctorShift₁Iso` (unsigned) and `mapBifunctorShift₂Iso`
  (`(-1)^(a*r)` in first degree). Their types are chain isomorphisms.
- ρE,ρH: the two component equations following the pairing predicates require
  exactly `θ_G` after `precomposeCochain κ.inv`; this fixes the entire chain map.
  `G` is written explicitly as `tensorComplex S A E H`, without a hidden let.
- Both squares: the two equalities `pE ≫ ρE.hom = ...` and `pH ≫ ρH.hom = ...`
  are equalities of chain maps. The right sides are respectively τ1 and τ2,
  followed by the canonical identity-on-components commutation of forgetting
  scalars with shift, and `p⟦-1⟧'`.
- Both sign assertions: the last two universal conjuncts evaluate those composites
  on an unsigned reindexed tensor and assert signs `(s*q+s).negOnePow` and
  `(s*q+q+r).negOnePow`, respectively, with the original u,v,i unsigned evaluation.
  Equality of chain maps supplies the same formulas for the other side of each square.
- No boundedness, flatness or injectivity: there are no such binders or predicates.

Dependency declarations used and read:

- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`, chain-map category.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently `SheafOfModules`; `Modules` uses the identical Mathlib category.
- `Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral`:
  `siteConstantModulePresheafGeneral`, `siteConstantModuleFunctorGeneral`.
- `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`:
  `realizationRing`, `realizationModules`, `realizationRingUnit`,
  `commutativeSiteConstantModuleFunctor`, its additive instance and the
  `realizationRingIso` / `commutativeSiteConstantModuleFunctor_transport` comparison.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `toSheafify`, sheafification unit;
  `PresheafOfModules.sheafificationAdjunction` supplies the module tensor unit.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, additivity and colimit instances;
  `SheafOfModules.tensorObjIsoSheafification` from its upstream import fixes local tensors.
- `Mathlib.Algebra.Homology.BifunctorShift`: `mapBifunctor`, `ιMapBifunctor`,
  `mapBifunctorShift₁Iso`, `mapBifunctorShift₂Iso`, with their documented sign conventions.
- `WeilConjectures.Algebra.Homology.HomComplex`: `CategoryTheory.homComplex`,
  `homComplexFunctor`, the dependency's internal Hom construction, read in full.
  `Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift` supplies global
  `Cochain`, `HomComplex`, and the shift infrastructure.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: imported for the stated
  shift/derived-category dependency and proof plan; no derived hypothesis is added.
- `def-weil-size-convention` is explicitly a metatheoretic convention, rendered by
  the universe binders rather than an artificial object.

Edge checks: zero ring (all module values trivial), characteristic two (all signs
become one), zero complexes and maps, empty site, empty tensor summands, unbounded
complexes and negative integer degrees. No nonempty hypothesis is used. For r,s,q
in {-2,-1,0,1,2}, the E sign `s*q+r+r+s` agrees modulo two with `s*(q+1)`, and
H sign `s*q+s+q+r+s` agrees with `r+(s-1)*q`; these identities also hold for every
integer by cancellation of even terms. The output degree in the E case is
`(r-1)+(q+1)+s+t`, and in the H case `r+q+(s-1)+(t+1)`, both r+s+q+t.

Searches actually run using msearch.py under Q108 and this item:

- leansearch: `Global Hom complex tensor pairing compatibility with coefficient
  shifts and Koszul signs`. Eight results including
  `CochainComplex.HomComplex.Cochain.leftUnshift_v`, `leftUnshift`, `leftShift`,
  `rightShift` and cocycle analogues. These are component shifts, not both external squares.
- leanfinder: `The external tensor product pairing of global Hom complexes commutes
  with contravariant shifts in both coefficients with Koszul signs`. Eight results,
  including `HomologicalComplex.tensorHom`, `HomologicalComplex₂.totalShift₁Iso_hom_totalShift₂Iso_hom`,
  `ι_totalShift₂Iso_hom_f` and `CochainComplex.mapBifunctorHomologicalComplexShift₁Iso`.
  Reused the existing shift comparisons; no exact external-pairing theorem found.
- loogle: `CochainComplex, HomComplex.Cochain, CochainComplex.mapBifunctorShift₁Iso`.
  Zero hits with an unknown-identifier diagnostic for `HomComplex.Cochain`.
  This diagnostic was not interpreted as evidence of absence of ordinary cochains.
- grep wrapper: `external.*[Pp]air|[Hh]om.*[Ss]hift` in `Algebra/Homology`.
  Twenty-five hits, chiefly HomComplexShift and homotopy/shift infrastructure.
- Direct rg searches in both `lean/WeilConjectures` and `lean/Sheaf` for external
  evaluations/pairings, Hom-shift interfaces and the item id. The exact id has no
  upstream occurrence; `Sheaf.Paper.ExternalRHomConePairing` has generic evaluations
  and a derived theorem for scheme etale sites, not this arbitrary-site chain statement.
  Its global cochain normalization and sign prose were read as consumers/context;
  the large downstream module is not imported. Other searches found the already
  existing internal Hom, global cochains and generalized constant constructions used here.
  `dag/lean_names_upstream.json` has no binding for the item.

No statement correction or disputed assertion. No new DAG node or dependency repair.
Helpers only spell out this node's own evaluation and comparison formulas, and every
helper is included in `lean.declarations` with its source/blueprint docstring.

## Second reading by Q108

This is the author's separate clause-by-clause rereading; the dispatch explicitly forbids
starting another agent, so no independent worker review is claimed. Maintainer review
remains independent. With the node and final module open, checked all seven complexes,
all three arbitrary maps, the original pairing, θ, ηU/ηV, both shifted pairings,
the four tensor shifts, both ρ definitions, both chain-map equalities and both signs.
Two mismatches found and repaired before delivery: an early sign-expression helper
was evaluated on κH's signed tensor, which would insert its q sign twice; the final
formula instead uses the unsigned reindexed local tensor. The additive global Hom
presentation initially left A-linearity implicit; `IsLinearHomMap` now explicitly
records it on every local component. Both shifted pairing predicates include it too.
The final degree transports are equalities of integer totals, not arbitrary maps.
All helper definitions are real constructions or propositions, and the sole theorem
has exactly `sorry` as proof. No auto-implicit variables, local notation or private
definitions, and no line exceeds 100 columns.
