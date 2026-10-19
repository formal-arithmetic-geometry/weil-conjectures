## Worker report

The module `Sheaf.AlgebraicGeometry.OpenImmersionRestriction` states
`AlgebraicGeometry.Etale.openImmersion_restriction_leray`. Its only proof is `sorry`.
No definition, auxiliary theorem, new node, dependency repair, or statement correction is
needed. Only the item's `lean` field is changed.

The source blueprint file was read on the project server at
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-open-immersion-restriction.md`.
It asserts restriction/direct-image cancellation and the Leray map for all unbounded F.
The reviewed DAG expands this with its K-injective construction and explicitly requires
compatibility with the inverse of the bounded-below comparison. This delivery retains
that quantifier and all those clauses.

Hypotheses and clauses, in order:

- Schemes U and X and their morphism j are `{U X : Scheme.{u}} (j : U ⟶ X)`.
  `[IsOpenImmersion j]` is the sole geometric hypothesis, using the recorded Mathlib
  definition; there are no quasi-compactness, finiteness, or boundedness assumptions.
- The counit `j⁻¹ j_* → id` on abelian sheaves is precisely
  `(upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).counit`.
  `IsIso` is imposed on the natural transformation itself, so the conclusion is a
  natural isomorphism, rather than unrelated isomorphisms at each sheaf.
- Every F in D(U_et) is the unrestricted quantifier
  `∀ F : DerivedCategory (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})`.
  The coefficient category is abelian groups, with the project's u+1 size convention.
- The canonical map from RΓ(X,Rj_*F) to RΓ(U,F) is
  `(rightDerivedLowerStarCompRightDerivedGlobalSectionsIso AddCommGrpCat.{u + 1} j).hom.app F`.
  Its source is the composite `(lowerStar ... j).rightDerivedFunctor` followed by
  `rightDerivedGlobalSections ... X`; its target is `rightDerivedGlobalSections ... U`.
  The second conjunct is `IsIso` of this actual canonical morphism. No arbitrary map or
  arbitrary choice of an objectwise isomorphism is substituted. Naturality is part of
  the existing natural isomorphism's type.
- Rj_* is the existing total right derived functor of the recorded `lowerStar`, and RΓ
  is the recorded `rightDerivedGlobalSections`. Both are the unbounded K-injective
  constructions; their existing computation API is
  `Functor.rightDerivedFunctorObjQIso`, and the source's composition isomorphism uses
  `Etale.preservesKInjectiveComplexes_lowerStar`. The modules for the recorded existence
  and generic total-derived nodes are imported for the proof plan, not replaced.
- The last conjunct quantifies over every
  `E : DerivedCategory.Plus (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})`.
  It equates the two paths from the inclusion of R⁺Γ_X(R⁺j_*E) to RΓ_U(ι E).
  The left path is `DerivedCategory.Plus.ι.map (rightDerivedGlobalSectionsLerayPlus j E).inv`
  followed by the Γ_U bounded/unbounded comparison. The right path is the Γ_X comparison,
  Γ_X applied to the j_* comparison, then the unbounded Leray hom at `ι E`.
  Every comparison is the canonical `rightDerivedFunctorPlusCompatibility.hom`.
  Thus the square states exactly that the unbounded Leray morphism is the inverse of
  `lem-kun-leray-bdd` under the standard identifications, including all bounded-below E.

Statement dependency declarations read and used:

- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-pbc-inverse-image` and `def-weil-pbc-direct-image`:
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.upperStar`, `.lowerStar`, `.upperStarLowerStarAdjunction`.
  The existing unbounded right-derived functor of that same lowerStar supplies Rj_*;
  the recorded bounded-below functor supplies R⁺j_* in the final square.
- `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories`, using
  its documented abelian-sheaf encoding `DerivedCategory (Sheaf ... AddCommGrpCat)`
  and Mathlib `DerivedCategory.Plus`, with its inclusion `DerivedCategory.Plus.ι`.
- `prop-weil-pbc-kinjective-resolutions-exist`:
  `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`,
  `CochainComplex.etale_kinjective_resolutions_exist` (proof-plan import).
- `lem-weil-pbc-kinjective-total-derived`: `Sheaf.CategoryTheory.KInjectiveTotalDerived`,
  `CategoryTheory.exists_rightDerived_of_enough_isKInjective` (proof-plan import).
- `def-kun-rgamma-unbounded`:
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `AlgebraicGeometry.Etale.rightDerivedGlobalSections`; reached publicly through
  `WeilConjectures.SixFunctors.Etale.Derived.GlobalSections`. The latter module defines
  the precise natural Leray isomorphism used here by deriving
  `lowerStarCompGlobalSectionsIso` with `Functor.rightDerivedFunctorCompIso'`.
- `lem-kun-leray-bdd`: `Sheaf.AlgebraicGeometry.LerayBounded`,
  `AlgebraicGeometry.Etale.rightDerivedGlobalSectionsLerayPlus`.
- The bounded/unbounded identification is the existing
  `CategoryTheory.Functor.rightDerivedFunctorPlusCompatibility` from
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`.

All recorded proof-dependency modules are also imported (ordinary imports for proof-only
uses). Besides those already listed: `RGammaUnboundedBounded.rGamma_unbounded_bounded`
(in namespace `AlgebraicGeometry.Etale`); the upstream open-immersion fully-faithful module;
Mathlib's `DerivedCategory.Plus.exists_injective_nonempty_iso` and
`CochainComplex.IsKInjective.Qh_map_bijective`; upstream
`CategoryTheory.Adjunction.preservesKInjectiveComplexes`; the recorded
`AlgebraicGeometry.Etale.upperStar_abelian_exact`; `CategoryTheory.Sheaf.Γ`; and
`CategoryTheory.Limits.pullback` with its projections and universal property.
The docstring reproduces the node's four-step proof, including naturality,
resolution independence and bounded-below inverse compatibility.

Edge cases checked mathematically before writing: the empty open subscheme has the zero
abelian-sheaf category, so both assertions still hold; the identity open immersion gives
the usual counit and Leray identifications; F=0 is included; arbitrarily unbounded F and
non-quasi-compact open immersions are included. The final square includes every lower
bound, including negatively shifted complexes. No coefficient characteristic restriction
or extra universe equality is imposed. Universes and all variables are explicitly bound.

Searches (msearch.py, Q19 / lem-kun-open-immersion-restriction):

- LeanSearch: `The counit of inverse image and direct image along an open immersion is an
  isomorphism and derived global sections of direct image satisfy Leray` returned service
  unavailable (`Internal Server Error`), recorded in sandbox `searches.jsonl`.
- LeanFinder: `Inverse image along an open immersion is a left inverse of direct image
  and derived global sections of derived direct image satisfy Leray` returned eight
  hits, about sheafed-space inverse maps and `Scheme.Modules.restrictFunctorComp`;
  none states this abelian-etale/unbounded/bounded-compatibility conjunction.
- Loogle: `CategoryTheory.Adjunction.counit, CategoryTheory.IsIso` returned twelve hits,
  including `Adjunction.counit_isIso_of_R_fully_faithful`; this supplies only the generic
  counit clause, not this node's full statement. An earlier broad Loogle query using
  `Functor.rightDerivedFunctor` found no match because that name is upstream, not Mathlib.
- Mathlib grep: `rightDerived.*[Ll]eray|IsOpenImmersion.*counit|openImmersion_restriction_leray`
  returned no hits. Upstream rg for `fullyFaithfulLowerStarOfIsOpenImmersion`,
  `lowerStarCompGlobalSectionsIso`, `rightDerivedLowerStarCompRightDerivedGlobalSectionsIso`,
  and `rightDerivedFunctorPlusCompatibility` found the existing interfaces used here.
  Project rg for the same notions found `LerayBounded` and `EtaleKInjectiveUnitLeray`.
  The former gives only the bounded comparison and the latter a different unit computation.
- Exact-name/id rg in upstream `WeilConjectures`, side `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no existing `openImmersion_restriction_leray` or
  complete declaration tagged `lem-kun-open-immersion-restriction`. Thus the full node
  requires a module, while its canonical constructions are all reused.

Validation: `scompile.py Q19 lem-kun-open-immersion-restriction` compiled the module in
both the wrapper's sandbox pass and its library pass, with no errors or warnings.
An initial field-notation line-break syntax error was repaired before this clean run.
The only postponed proof is the named theorem above, belonging to this DAG node.
No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by Q19

I read the item node, the source blueprint place (order 1699), the source proof context,
and the declarations recorded by every statement dependency. The node's objects and
clauses match the Lean theorem item by item:

- The object is a pair of schemes `{U X : Scheme.{u}}` and a morphism `j : U ⟶ X`;
  Lean binds exactly these, with `[IsOpenImmersion j]` and no additional geometric,
  Noetherian, finiteness, boundedness, characteristic, or universe-equality hypothesis.
  `IsOpenImmersion` is the recorded Mathlib scheme morphism property.
- The first conclusion clause is the counit
  `(upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).counit` and Lean states
  `IsIso` of that natural transformation. This is the node's natural isomorphism
  `j⁻¹j_* ≅ id`, using the recorded inverse/direct-image adjunction.
- The second clause quantifies over every unbounded
  `F : DerivedCategory (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})`.
  Lean states `IsIso` for the actual canonical morphism
  `(rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
  AddCommGrpCat.{u + 1} j).hom.app F`, whose source is `Rj_*` followed by `RΓ_X`
  and whose target is `RΓ_U`. Thus it is the node's canonical unbounded Leray map,
  with no replacement by an arbitrary objectwise isomorphism.
- The final clause quantifies over every
  `E : DerivedCategory.Plus (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})`.
  The displayed equality compares the inverse of the bounded-below Leray map,
  transported by `DerivedCategory.Plus.ι`, with the unbounded Leray hom after the
  canonical bounded/unbounded compatibility maps for `Γ_U`, `Γ_X`, and `j_*`.
  This is exactly the node's assertion that the unbounded map restricts to the inverse
  of `lem-kun-leray-bdd`; the composition order and all quantifiers agree.

The dependency interfaces were checked directly. `AlgebraicGeometry.IsOpenImmersion`
is the Mathlib open-immersion property. `upperStar`, `lowerStar`, and
`upperStarLowerStarAdjunction` are the recorded étale inverse/direct-image notions.
`DerivedCategory` and `DerivedCategory.Plus` use the project's abelian étale-sheaf
encoding. The K-injective existence and total right-derived declarations supply the
unbounded construction, while `rightDerivedGlobalSections` and
`rightDerivedLowerStarCompRightDerivedGlobalSectionsIso` supply the canonical Leray
map. `rightDerivedGlobalSectionsLerayPlus` and
`Functor.rightDerivedFunctorPlusCompatibility` supply the bounded-below comparison.
No private duplicate notion or dependency repair was needed.

I checked the edge cases: the identity immersion gives identity counit and Leray maps;
the empty open (including an empty ambient scheme) is covered by the same adjunction
and zero sheaf category; `F = 0` is included; complexes unbounded in either direction
are allowed by the unbounded quantifier; and there is no integer parameter or
characteristic restriction. The explicit universe `Scheme.{u}` and coefficient
`AddCommGrpCat.{u + 1}` matches the site/coefficient convention and does not exclude
these cases.

Searches were repeated in the source and project trees. The LeanSearch query for the
combined counit/Leray statement was unavailable (service error); LeanFinder returned
only generic open-immersion sheaf identities and `Scheme.Modules.restrictFunctorComp`;
Loogle returned only generic adjunction/`IsIso` results. Grep over Mathlib, upstream
`WeilConjectures`, and project `lean/Sheaf` found no declaration of this complete
statement; upstream grep did find the canonical Leray and bounded-compatibility
interfaces used by the module. Therefore the module is a genuinely new statement.

No mismatch was found and no source, node statement, dependency, or Lean declaration
was changed. The module compiled cleanly with the required `scompile.py` wrapper;
there is only the node theorem's postponed `sorry` proof.

Independent second-reader query details: LeanFinder query "The canonical comparison
between unbounded derived sections of direct image and source sections agrees with
bounded below derived sections" returned generic `mapDerivedCategoryFactors` and
sheaf-restriction results, with no exact match. Loogle query
`CategoryTheory.Functor.rightDerivedFunctorPlus, CategoryTheory.Iso` returned zero hits.
LeanSearch query "Derived global sections after pushforward along an open inclusion and
compatibility of bounded below and unbounded derived functors" was unavailable
(`Internal Server Error`); no absence verdict is inferred from that service failure.
I also read Stacks `derived.tex` at `lemma-adjoint-preserve-K-injectives`,
`lemma-K-injective`, `lemma-K-injective-defined`, and
`lemma-enough-K-injectives-implies`: their hypotheses are only the abelian/exact-adjoint
and K-injective assumptions stated in the proof plan, with no bound or compactness
condition. The blueprint's finite-type/base-field hypotheses belong to its main Kunneth
proposition; this independently stated lemma and its Stacks ingredients require none.
