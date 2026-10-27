## Worker report

Delivered module: `Sheaf.Paper.InternalScalarMateTransitivity`. The primary theorem is
`AlgebraicGeometry.ProEtale.QuotientChange.internal_scalar_mate_transitivity`.
`internal_scalar_identity_normalization` states the identity-coefficient clauses of the
same node. Both proofs are `sorry`; all three auxiliary definitions have real data.
The node's statement, proof, dependencies and other fields are unchanged.

Source read: blueprint main-20261015, integral proper-base-change proof (3), specifically
"the reduction of each canonical map is the corresponding canonical map for the torsion
reductions"; also the item's seven explicit proof steps, and the normalization and
successive-scalar interfaces they cite. This item supplies canonical-map compatibility,
without asserting the direct-image mates are invertible.

Hypotheses and objects:

- Commutative condensed rings Lambda_0, Lambda_1, Lambda_2 are the explicit
  `Λ₀ Λ₁ Λ₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}` with
  `MonObj` and `IsCommMonObj` instances. This is the unbundled presentation of the
  recorded `Profinite.CondensedRing = Mon (...)`, not a new notion.
- The coefficient maps are `(a : Λ₀ ⟶ Λ₁) [IsMonHom a]` and
  `(b : Λ₁ ⟶ Λ₂) [IsMonHom b]`. Their composite is exactly `a ≫ b`.
- The arbitrary scheme morphism is `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
  `Modules Λ T` uses the recorded `condensedRingObj Λ T = p_T^* Λ` over
  `Scheme.ProEt.topology T`. No geometric assumption is imposed on f.
- `D`, `L`, `F`, `scalarAdj` and `rho` are the recorded internal, ordinary unbounded
  functors and actual adjunctions. No completed, solid or bounded category is substituted.
- The three specified normalized balancing isomorphisms are `l01`, `l12`, `l02`, with
  `h01 : PullNormalized a f l01`, `h12 : PullNormalized b f l12` and
  `h02 : PullNormalized (a ≫ b) f l02`. Their existence is the recorded
  `internal_scalar_pullback_normalization`; quantifying over normalized choices renders
  the node's "with normalized pullback balancing". It adds no flatness hypothesis.

Conclusion clauses, in order:

1. The existential `betaX : D a X ⋙ D b X ≅ D (a ≫ b) X` and `betaY` give precisely
   the two natural scalar-composition isomorphisms. The first two conjuncts are
   `SuccessiveNormalized a b (a ≫ b) rfl X betaX` and the analogous Y equation.
   This is the dependency's exact successive universal computation-counit predicate;
   it uses the fixed `ordinaryComp`. That ordinary comparison is built from
   `Mod.extendScalarsComp`, coefficient-map composition and uniqueness of left adjoints.
   Its generator is `(x tensor s) tensor t -> x tensor b(s)t`, with inverse
   `x tensor t -> (x tensor 1) tensor t`. Thus the representative formulas are rendered
   through the node's existing normalization predicate, rather than an arbitrary isomorphism.
2. The next two conjuncts, for all K at X and at Y, compare the two specified scalar
   units. They first apply `(scalarAdj a T).unit`, then restriction of
   `(scalarAdj b T).unit`, then restriction of beta. `scalarRestrictionComp` identifies
   the two exact restrictions with restriction along `a ≫ b`. The result is exactly
   `(scalarAdj (a ≫ b) T).unit.app K`.
3. The next two conjuncts give compatibility of the actual adjunction Hom bijections,
   for every derived input K, target H and map `g : K ⟶ (V (a ≫ b) T).obj H`.
   Transposing after beta under the successive scalar adjunction equals g followed
   by the inverse restriction comparison. This explicitly fixes the reduction-unit
   transposes. The representative scalar units and transposes are those of `scalarAdj`,
   not newly chosen adjunctions: x maps to x tensor 1 and the adjunct is scalar multiplication.
4. For all K on Y, the penultimate conjunct is the displayed pullback identity.
   Lean writes compositions in order of application: `l12`, then `D b X` applied
   to `l01`, then `betaX`, equals `L Λ₂ f` applied to `betaY`, then `l02`.
   Source and target are exactly the stated threefold composites.
5. For all K on X, the last conjunct is the displayed direct-image identity:
   `betaY` at `F Λ₀ f K` followed by `rho (a ≫ b)` equals `D b Y` applied to
   `rho a`, then `rho b` at `D a X K`, then `F Λ₂ f` applied to `betaX`.
   The `rho` definition uses `mateEquiv (adj Λ₀ f) (adj Λ₂ f)`.
6. `internal_scalar_identity_normalization` covers both possible identity positions.
   Its `betaLeft` and `betaRight` satisfy `SuccessiveNormalized` with the actual
   identity-composition equalities. Their components equal the image of the source
   scalar unitor and the target scalar unitor respectively. Hence these are the
   canonical identity comparisons; their inverses are fixed too.
7. That theorem also states the normalized identity scalar unit becomes `𝟙 K` under
   `scalarExtensionId` and `scalarRestrictionId`. Its final two conjuncts identify
   identity-coefficient balancing with `L(uY)` followed by `uX.inv`, and its mate
   with `uY` followed by `F(uX.inv)`. These say exactly that balancing and its
   direct-image mate become identities under the same canonical unitors. Applying
   the theorem to an identity a covers the tower with both arrows identities.
8. Neither theorem assumes flat coefficient maps, bounded complexes, nor invertible
   direct-image mates. No such property appears among the conclusions.

Dependency declarations used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` (the same
  underlying abelian-sheaf monoid presentation, retained by import).
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`,
  `Scheme.ProEt.topology` (objects and morphisms retain the framework's distinct sizes).
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPullback`, `moduleObjectDerivedPushforward`,
  `derivedUpperStarLowerStarAdjunction`, used through L, F and adj.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` retains the recorded generic
  `SheafOfModules.DerivedChangeOfRingsCochainModel` by public import. The internal
  specialization is the recorded D, not the ModuleCat specialization of that module.
- `Sheaf.Paper.InternalDerivedScalarComparisons`: `Modules`, `D`, `L`, `F`, `V₀`, `V`,
  `scalarAdj`, `PullNormalized`, `rho`, `ordinaryComp`, `SuccessiveNormalized`.
- `Sheaf.Paper.InternalScalarPullbackNormalization`:
  `internal_scalar_pullback_normalization` supplies normalized balancing.
- Auxiliary definitions reuse `Mod.comapComp`, `Mod.comapCongr`, `Mod.comapId`,
  `Functor.mapDerivedCategoryCompIso`, `Functor.mapDerivedCategoryNatIso`,
  `Functor.mapDerivedCategoryIdIso`, `Adjunction.leftAdjointUniq`, and
  `coefficientMap_comp` / `coefficientMap_id`.
- The proof-only imports follow the node: successive quotient normalization, ringed
  K-flat word comparison descent, sheaf-ring coefficient adjunction, cochain tensor
  universes, and Mathlib `mateEquiv`, `mateEquiv_vcomp` and identity mate formulas.

The three helpers merely name canonical composites needed to type the unit and identity
clauses of this node. `scalarRestrictionComp` and `scalarRestrictionId` lift the ordinary
identity-on-underlying-module comparisons; `scalarExtensionId` uses the specified
`scalarAdj` and uniqueness against the identity adjunction. No arbitrary map, choice,
private replacement, helper theorem or independent mathematical notion is introduced.

Edge cases checked before stating: either coefficient arrow is identity; both are
identities; zero rings; K = 0; f is identity; empty X or Y when a morphism exists; the
non-flat tower Z -> Z/4 -> Z/2. All categories and equations still type, and the ordinary
formulas agree. The proof uses no division, Tor-vanishing, properness or cohomological
boundedness. The relative site sizes remain those of the existing pro-etale framework;
no equality of site-object and site-morphism universes is imposed.

Searches performed (the msearch results are logged by the prescribed search tool):

- LeanFinder: "Successive internal derived scalar extension normalized associativity
  units pullback balancing and direct image adjunction mates" returned 8 hits,
  including sheaf/presheaf pullback comparisons and ordinary adjunction identities;
  no exact internal unbounded normalized scalar-tower theorem.
- Loogle: "CategoryTheory.mateEquiv, CategoryTheory.Mod.extendScalarsComp" returned
  0 hits with unknown identifier for the project-specific second name; this was a
  name lookup failure, not evidence the latter notion is absent.
- Loogle: "CategoryTheory.mateEquiv" returned 12 hits, including mateEquiv,
  mateEquiv_vcomp, mateEquiv_hcomp and component formulas. These provide the formal
  mate-pasting proof ingredients, but not the normalized scalar and unit theorem.
- Mathlib grep: "comapComp|extendScalarsId|comapId|mapDerivedCategoryCompIso" returned
  12 hits (ordinary ModuleCat scalar identity and Pi comap comparisons). Project
  source searches located the actual Mod and exact-derived localization interfaces.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf` and the upstream name index for
  `SuccessiveNormalized`, the new full declaration names, and scalar restriction/identity
  names found the owning comparison interface and unrelated section-module interfaces.
  No existing declaration states all clauses of this node.
- `grep -rn` for the item id in `lean/WeilConjectures` found no declaration.

No new nodes, dependency repairs, statement corrections or disputed statements.
Validation: scompile.py compiles the module in module mode against the published live
library; only the two requested theorem proofs are postponed. The required delivery dry
run and final push are performed using deliver2.py.

## Second reading by Q127

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
