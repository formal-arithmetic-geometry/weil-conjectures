## Worker report

The module `Sheaf.Paper.FormalClosedSupportDerived` states
`AlgebraicGeometry.ProEtale.CondensedRing.formal_closed_support_derived`.
Its only proof is `sorry`. No definition, new node, dependency repair, or statement
correction is introduced. The statement and all other original node fields are unchanged.

Hypotheses, read against the sheaf-support situation:

- `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}`, `[MonObj Λ]`, and
  `[IsCommMonObj Λ]` are the condensed commutative coefficient ring. The prime `ℓ`
  and `hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ` impose precisely admissibility.
- `k : Type u`, `[Field k]`, `[Fact (ringChar k).Prime]`, and
  `[Fact (ringChar k ≠ ℓ)]` give the standing field and its characteristic conditions,
  exactly as in `formal_closed_support_sheaves`.
- `X Z V : Scheme.{u}` with their `Over (Spec (.of k))` structures and
  `[LocallyOfFiniteType (X ↘ Spec (.of k))]`, `[QuasiCompact ...]`,
  `[IsSeparated ...]` give the inherited standing scheme. No finite-type hypotheses
  on Z or V are added: immersion into X supplies the setting as in the dependency.
- `i : Z ⟶ X`, `[IsClosedImmersion i]`, and `[i.IsOver ...]` give the closed immersion.
  `j : V ⟶ X`, `[IsOpenImmersion j]`, and `[j.IsOver ...]` give the open immersion.
  `hij : Set.range j = (Set.range i)ᶜ` says it is exactly the open complement.
  Quasi-compactness of j is a consequence of finite type over k, not an extra binder.
- The coefficient categories are the dependency's `pulledBackModuleObjects Λ X/Z/V`;
  the functors are the dependency's actual `upperStar`, `lowerStar`, and
  `closedModuleSectionsWithSupport Λ i j`. In particular the support functor is
  literally `moduleSectionsWithSupport Λ j ⋙ upperStar Λ i`, using the kernel of
  the actual `upperStarLowerStarAdjunction Λ j` unit in the functor category.

Clauses:

1. The existential additive instance and ordinary `adj : lowerStar Λ i ⊣
   closedModuleSectionsWithSupport Λ i j` expose structures supplied by the sheaf
   dependency, without assuming them. The term
   `adj.mapDerivedCategoryRightDerivedAdjunction` has exactly type
   `(lowerStar Λ i).mapDerivedCategory ⊣
   (closedModuleSectionsWithSupport Λ i j).rightDerivedFunctor`.
   Thus the derived adjunction is supplied as actual data, not merely a Hom cardinality
   statement. The total right derived functor is the existing Grothendieck/K-injective
   construction; `rightDerivedFunctorObjQIso` computes it on every K-injective complex.
   The recorded arbitrary-quasi-isomorphism universal pair agrees with it by
   `rightDerivedFunctorOfQuasiIsoResolutions_unique` (the same comparison used by
   `closedSupport_recordedDerived` in the broader proof dependency).
   The first conjunct gives an isomorphism of the two global Hom complexes for all
   complexes A and all K-injective representatives I of K. Both target complexes are
   K-injective by the sheaf dependency. The equation in each degree n and component
   `(p,q,hpq)` specifies the isomorphism by `adj.homEquiv`, including its naturality in
   both arguments and compatibility with their differentials. Consequently it is the
   claimed global RHom comparison, rather than just its degree-zero shadow.
2. The second conjunct quantifies over every injective module I and asserts
   `Epi ((upperStarLowerStarAdjunction Λ j).unit.app I)`: precisely sheaf-surjectivity
   of the specified unit, not surjectivity on every presheaf of sections.
3. `δ` is a natural transformation from `j^* ⋙ Rj_*` to `(RH ⋙ i_*) ⋙ [1]`.
   For every K the triangle is asserted distinguished. Its first arrow is the counit
   of the derived support adjunction; its second arrow is explicitly
   `(upperStarLowerStarAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction.unit.app K`.
   Naturality of both adjunction transformations and δ makes this a natural triangle.
   The last conjunct quantifies over every K, K-injective I and isomorphism
   `K ≅ DerivedCategory.Q.obj I`. It identifies RH(K) with exact i^* applied to Q of
   the mapping cone of the degreewise actual sheaf unit on I, shifted by -1.
   This is the fibre of the displayed derived unit. Every K has such a representative
   by `DerivedCategory.exists_iso_Q_obj_of_isKInjective`, so this does not restrict K.

Dependency declarations used/read:

- `Sheaf.Paper.FormalClosedSupportSheaves`:
  `moduleSectionsWithSupport`, `closedModuleSectionsWithSupport`, and
  `formal_closed_support_sheaves` (all in `AlgebraicGeometry.ProEtale.CondensedRing`).
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`, its universal
  unit, uniqueness and computation isomorphism. This is the recorded interface for
  both `sk-def-sfb-derived-categories` and `def-sfb-right-derived-functor`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`:
  `CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`:
  `CategoryTheory.Functor.rightDerivedFunctorObjQIso` and
  `DerivedCategory.exists_iso_Q_obj_of_isKInjective`.
- `Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction`:
  `closedSupport_lowerStarExact` supplies the exact closed direct image instance
  needed to type the public derived functor; hence this import is public.
  The broader `closedSupportDerivedAdjunction`, `closedSupport_globalRHom`,
  `closedSupport_injective_unit_epi`, `closedSupport_triangle`, and
  `closedSupport_fiber` are proof tools. They use an equivalent but non-definitionally
  identical inverse-scalar-transport presentation; they are not substituted for the
  recorded support functor here.
- Remaining proof imports are the stated proof dependencies: ring-sheaf Grothendieck
  structure and open-closed sequence, degreewise injective K-injective existence,
  right-adjoint K-injectivity, short-exact-sequence triangle, exact derived functors,
  termwise homotopy adjunction, K-injective Hom bijection, closed inverse-image
  limits, triangulated axioms/two-isomorphisms lemma, finite-type Noetherian charts,
  and quasi-separatedness. Their theorem signatures and relevant docstrings were read.

Edge cases checked: V empty (full support), Z empty (zero support), X empty,
zero complexes/modules, arbitrary unbounded complexes and arbitrary integer shifts.
There is no boundedness, constructibility, discrete-coefficient, nonempty-scheme,
extra quasi-compact-complement or extra universe-equality hypothesis. The site has
object universe u+1 and hom universe u; abelian coefficients and modules have the
published u+1 size. The shift is explicitly -1 for the fibre, and +1 in the triangle.
No statement fault or STATEMENT-DISPUTED remains.

Searches (all through the prescribed wrapper where applicable):

- LeanFinder: `Derived closed support functor right adjoint closed immersion
  localization triangle fiber open restriction`: 8 hits, chiefly ordinary Zariski
  module restriction adjunctions and scheme kernel adjunction; no exact match.
- Loogle: `CategoryTheory.Adjunction.derivedAdjunction,
  DerivedCategory.triangleOfSES`: 0 hits (first identifier unknown to the service).
- LeanSearch: `closed support derived adjunction localization triangle proetale
  condensed modules`: 8 hits, general derived adjunctions and unrelated condensed
  discrete-characterization results; no exact match.
- Mathlib grep via msearch: `closedSupport|SectionsWithSupport|localCohomology`
  in `Algebra/Homology`: 5 hits, ordinary ring/module local cohomology, no match.
- `rg` over upstream WeilConjectures for
  `formal_closed_support|closedSupport|SectionsWithSupport`: no hits; the literal
  node-id grep likewise has no hit. Upstream framework declarations were read in
  the exact side checkout and through `scompile.py --source`.
- `rg` over side `lean/Sheaf`: found FormalClosedSupportSheaves, the broader
  CondensedClosedSupportAdjunction, and the unit-level FormalClosedSupport.
  None states these exact hypotheses and clauses for the recorded sheaf support
  functor. The unit theorem additionally includes a stratum formula and uses its
  own existing formal-support presentation; it is not this item's statement.
- Full proposed declaration name searched in Mathlib, upstream, side Lean and
  `dag/lean_names_upstream.json`: no collision.

## Second reading by NY

Performed a separate pass with the node, blueprint source, dependency source and final
module open. No additional agent was started, as the dispatcher brief forbids it;
the maintainer's independent delivery review remains independent of this self-check.

The inherited admissibility, characteristic, field, finite-type/separated scheme,
closed immersion, open immersion and exact-complement hypotheses each have the
binders listed above. In particular no `[QuasiCompact j]` has been smuggled in.
The source support functor is exactly `closedModuleSectionsWithSupport`, not the
broader module's `closedSupport`. The adjunction is explicitly available from the
ordinary adjunction through the existing exact-left-adjoint construction. The RHom
claim is on whole Hom complexes, with the adjunction's formula on every component.
The injective-unit assertion uses the same upstream unit as the kernel definition.
The connecting arrow is a natural transformation and its second triangle arrow is
the derived unit. The final formula uses the mapping cone of that same actual unit,
shifted by -1 before exact closed restriction, and ranges over all K-injective
representatives of every derived K. No clause or edge case was dropped.

This pass fixed the explicit shift spelling to avoid an imported notation conflict,
and made the exact-closed-direct-image dependency import public because its instance
occurs in the theorem's public type. These are elaboration/interface fixes, with no
change to the mathematical statement. The final delivered signature is copied
verbatim into `lean.statement`. The module has one theorem, with proof `sorry`.
