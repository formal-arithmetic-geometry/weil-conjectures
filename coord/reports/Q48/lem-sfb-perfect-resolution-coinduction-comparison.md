## Worker report

The module `Sheaf.Algebra.Homology.PerfectResolutionCoinductionComparison` states
`ModuleCat.PerfectResolutionCoinduction.perfect_resolution_coinduction_comparison`
and three complementary statements for chain naturality, top-row naturality, and
canonical K-injective replacement independence. All four proofs are `sorry`.
Every helper has real data: abbreviations use the recorded constructions, the
normalization predicates are explicit formulas, `Square` is the data and laws of
the displayed diagram, and `restrictionComp` uses the canonical exact-functor
composition isomorphism. No helper selects maps from an existence theorem.

Read the complete item and its eleven proof steps, its five statement dependencies,
and the recorded source declarations. Source places checked: dualizing.tex,
lemma-right-adjoint, lemma-composition-right-adjoints, and lemma-RHom-ext (0A70,
0C0F, 0A71); more-algebra.tex, lemma-hom-K-injective (0917) and lemma-compose (0A5Y).
The node's additional explicit square is retained, rather than replaced by the
shorter abstract Stacks composition lemma. No statement correction is needed.

Hypothesis and clause correspondence:

- Commutative rings and both homomorphisms are `[CommRing S]`, `[CommRing B]`,
  `[CommRing D]`, `f : S →+* B`, and `g : B →+* D`.
- Ordinary unbounded module derived categories are `DerivedCategory (ModuleCat S)`
  and its B and D analogues. Their `HasDerivedCategory` universes `wS`, `wB`, `wD`
  are independent. The common ambient module universe `u` does not restrict the
  mathematical rings: any three sizes admit a common larger universe.
- P and Q are `Complex S`; each has existential lower and upper strict bounds.
  Each term satisfies `Module.Finite S` and `Module.Projective S`. Over a ring,
  finite projectivity is equivalent to being a retract of a finite free module:
  split a finite-generator free surjection by projectivity; conversely a finite
  free retract is finite and projective. No freeness assumption is added.
- The actual augmentation `a` targets `single ((restrictScalars f).obj (of B B))`;
  `b` is a B-linear chain map from `(extension f).obj Q` to D in degree zero,
  restricted to B. The two `QuasiIso` hypotheses are exactly those in the node.
- `tensor P Q` is the recorded signed direct-sum `mapBifunctor` with `curriedTensor`.
  `inclusion` is Mathlib's total summand inclusion, not a replacement totalization.
- The existential `w` has target the S-restriction of D[0]. `AugmentationFormula`
  gives w(p tensor q)=b(a(p) tensor q) on the i=0 summands and zero on i≠0
  summands. These summands generate W in every degree, so this is precisely
  b(a tensor 1) and uniquely determines the map. `QuasiIso w` is asserted.
- I ranges over all S-complexes with `[I.IsKInjective]`. The theorem separately
  quantifies every `N`, every `j : N ⟶ I`, and `[QuasiIso j]`, so no coefficient
  bound or chosen replacement is added as a restriction on the original N.
- J is the existing `(coinductionComplexFunctor f).obj I`: degree n is
  Hom_S(B,I^n), with the specified B-action. `DerivedFormula` asserts J is
  K-injective over B; it never assumes its S-restriction is K-injective.
- `Square.e` has exactly the displayed top source and target product Hom
  complexes (the target uses the S-restriction of the B-presentation of D[0]).
  `Square.evaluation` specifies e(h)(d)=h(d)(1_B) on every homogeneous cochain.
  It is a chain isomorphism, hence in particular a quasi-isomorphism.
- The two vertical arrows are the existing `moduleHomPrecomp` applied to b and w,
  with restriction on the left. `left_quasiIso` and `right_quasiIso` assert the
  required quasi-isomorphisms. `commutes` is strict equality of the two chain maps.
- `Square.κ`, `formula`, and `bottom_quasiIso` give the bottom map, its exact
  normalization, and its quasi-isomorphism. The normalization evaluates extension
  adjunction at 1 tensor q, precomposes with a, curries without a sign, and then
  applies the Koszul flip. In degree i of P the resulting formula is
  (-1)^(ij) F(1 tensor q)(a(p)). When i≠0 the augmentation a(p) is zero in B[0],
  so both sides vanish; `KappaFormula` explicitly states this for every i≠0,
  every q-degree, and every cochain degree. When i=0 the sign is 1 and its first
  conjunct states the remaining formula exactly. This is a characterization of
  the specified composite, not a choice of a quasi-isomorphism or an arbitrary map.
- `Square.topD` is an isomorphism of D-complexes between actual iterated and direct
  coinduction, with the complete nested evaluation formula `topD_formula`.
  `modelLeft` and `modelRight` are chain isomorphisms from their S-restrictions to
  the top product Hom models. Their degree-zero formulas determine all components
  since D[0] has no other source degrees. `model_commutes` identifies e with the
  S-restriction of this actual D-linear lift.
- The natural isomorphism η is between the *recorded functors*
  `derivedCoinduction f ⋙ derivedCoinduction g` and `derivedCoinduction (g.comp f)`.
  `CounitFormula` says its counit is the composite of the two fixed derived
  evaluation counits, using canonical scalar restriction associativity. Uniqueness
  of right adjoints therefore fixes the actual composition comparison.
- `DerivedFormula` identifies η on every K-injective with the localization of
  `Square.topD`, using the two recorded `derivedCoinductionModel` comparisons.
  Together with `model_commutes`, `commutes`, and the vertical quasi-isomorphisms,
  this is exactly the bottom model interpretation: inverting the localized
  vertical maps identifies κ with e. The two top objects are actual D-objects,
  and their identifications fix the transported derived D-actions on the bottom
  models; no strict D-action on P, Q, or W is asserted or assumed.
- The final conjunct constructs `jW`, specifies *all* its cochain coordinates as
  postcomposition with j, and asserts `QuasiIso jW`, for arbitrary unbounded N.
- `perfect_resolution_coinduction_naturality` quantifies augmentation-preserving
  `u : P' ⟶ P` and `v : Q' ⟶ Q`, a coefficient map `t : I ⟶ I'`, and two
  normalized squares. It states compatibility of w and gives the full induced
  cochain maps F and R, with `F ≫ s'.κ = s.κ ≫ R`.
- `perfect_resolution_coinduction_top_naturality` states the corresponding e-square
  with both induced cochain maps specified, and the naturality square for topD in
  the category of D-complexes. The top row has no P/Q dependence.
- `perfect_resolution_coinduction_resolution_independence` gives the unique
  homotopy class t between any two replacements, its quasi-isomorphism, the
  homotopy j t ≃ j', and compatibility with η. The preceding chain naturality and
  the K-injective localization bijection extend these identities to every derived
  coefficient morphism, not only chain quasi-isomorphisms or a selected lift.
- There are no flatness, Noetherianity, or coefficient-boundedness hypotheses.

Recorded dependency declarations used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.DerivedCoinductionAdjunction`:
  `ModuleCat.derivedCoinduction`, `coinductionComplexFunctor`,
  `derivedCoinductionModel`, `derivedCoinductionAdjunction`.
- `WeilConjectures.Algebra.Homology.ModuleHomComplex`:
  `CochainComplex.moduleHomComplex` and its recorded homogeneous cochains.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`,
  `ιMapBifunctor`; ordinary module tensor is `MonoidalCategory.curriedTensor`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective` (the node has a mathlib_match, not a Lean record).
- Added the already-landed statement dependency
  `def-trf-module-hom-precomposition`, the definition node owning the canonical
  `CochainComplex.moduleHomPrecomp` from
  `Sheaf.Algebra.Homology.ModuleHomPrecompHomotopy`; it is not redefined.

Proof-only imports cover all proof dependencies with recorded usable modules:
projective-flatness, bounded-flat K-flatness, generic K-flatness, Hom quotient and
cocycle formulas, K-injective and K-projective localization bijections, coinduction
Hom model and adjunction, and right-adjoint uniqueness. The proof dependency
`lem-trf-bimodule-chain-currying-descent` has neither a module nor a Mathlib match
in the read clone, so its import is omitted. It is not required to type this
statement: the canonical composite is fully characterized by its generator
formula. It remains a proof dependency for stage 3, not a missing statement notion.

Edge cases checked before writing and again against the final signatures:
identity ring maps and degree-zero free resolutions give ordinary evaluation and
currying; zero rings and zero modules are permitted; characteristic two changes
no formula; terms in negative and positive degrees are both allowed and the
nonzero-degree-P clause explicitly covers both; arbitrary unbounded N is allowed;
B/S and D/B may be nonflat. Finite projective resolutions restrict only the data
P,Q as in the source, not either ring map by an additional class assumption.

Searches actually run:

- `msearch.py ... leanfinder "Coinduction transitivity computed on two finite
  projective resolutions by currying and signed tensor symmetry"`: eight Tor
  and projective-resolution hits; none is this normalized coinduction square.
- `msearch.py ... loogle '"coextendScalars"'`: twelve hits including
  `ModuleCat.coextendScalars`, `restrictCoextendScalarsAdj`, and
  `CoextendScalars.equiv`. Reused the recorded derived construction built from
  these; ordinary coextension alone does not state this theorem.
- `msearch.py ... grep 'coinduct|coextendScalars|moduleHomComplex' Algebra/Homology`:
  five unrelated homotopy coinductive-construction hits; no comparison theorem.
- `msearch.py ... leansearch "Derived coinduction comparison computed on bounded
  projective double resolutions with evaluation at one"`: eight ordinary
  projective-resolution and representation-theoretic hits; no exact match.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for coinduction names, Hom-map
  APIs, `PerfectResolutionCoinduction|perfect_resolution_coinduction|double.*
  (projective|resolution)`, and the item id: existing coinduction/Hom/precomposition
  APIs, but no statement of this square. The item-id grep of WeilConjectures
  returned no hit. The full source and docstrings of the reused APIs were read.

No new DAG nodes or dependency repairs. The helper declarations are the canonical
maps and their normalization laws belonging to this single comparison, as allowed
by the missing-helper rule. No STATEMENT-DISPUTED flag or other node fault.

## Second reading by Q48

This is a second pass by the same worker; the dispatcher explicitly prohibits
starting other agents, and the maintainer supplies the independent delivery review.
Reopened the node's full statement and proof and the final module. Rechecked every
ring and resolution binder, both quasi-isomorphism hypotheses, both bounds,
finite projectivity, unbounded coefficients, and the target of every arrow of the
square. In particular, the first map is extension adjunction, not a claim that
restriction preserves K-injectives. Checked the direction of the counit equation:
direct scalar restriction first identifies with successive restriction, then the
B/D counit and S/B counit are applied. Checked the model comparison equation in
D(D), not merely cohomology over S. Recomputed the pure tensor formula: i≠0 kills
a(p); i=0 makes (-1)^(ij)=1, so the two-part KappaFormula retains the signed flip
exactly. Checked that coefficient naturality is on actual D-complexes at the top,
and that the replacement theorem quantifies two arbitrary replacements with the
same N and gives uniqueness up to homotopy. During this pass added explicit top-row
chain naturality, alongside the bottom naturality and canonical replacement
comparison, to leave none of the final naturality clause implicit. No node text
was changed. All helper declarations are public, documented, and included in the
node's declarations list; no data is sorry and all four theorem proofs are sorry.

## Repair of returned head 08e6dfdfbe2c

H2: replaced the added theorem dependency
`lem-trf-hom-dual-preserves-homotopies` with the existing definition node
`def-trf-module-hom-precomposition`. Read its current live record and the full
`moduleHomPrecomp` construction in ModuleHomPrecompHomotopy. The definition node
owns precisely the unchanged canonical precomposition map used by both vertical
arrows; no homotopy-preservation theorem is needed to state them. Updated the
dependency paragraph above. The Lean module is byte-identical to the returned
delivery. Compared the retained node with current main before this repair: only
the delivery's lean attachment and stmt_deps differ; the accepted statement and
proof remain unchanged. Compilation and delivery checks are rerun for this repair.

Second reading of this repair: the five original statement dependencies remain,
and the additional dependency now names the already-landed definition owner,
whose existing:true record is CochainComplex.moduleHomPrecomp in the same public
import. This addresses the complete return; no other mathematical or Lean change
was requested.
