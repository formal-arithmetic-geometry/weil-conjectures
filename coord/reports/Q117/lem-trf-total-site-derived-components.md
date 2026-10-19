## Worker report

The module `Sheaf.TraceFormula.TotalSiteDerivedComponents` states
`CategoryTheory.totalSiteDerivedComponents`, with one postponed theorem and one
fully specified input-data structure `CategoryTheory.TotalSiteMorphismData`.
The node's statement and dependency lists are unchanged. There are no new DAG
nodes, dependency repairs, or statement corrections.

Source read: `literature/stacks-project/spaces-simplicial.tex`, the full
compatible-family description and component restriction (09WF, 09WG), and the
construction and derived computation in 0D96 and 0D97. The already reviewed
component-restriction module also supplies 09WH. The theorem docstring carries
all five proof steps from the DAG, including the representative of the derived
unit after resolving the inverse image.

Clause-by-clause rendering:

- Small sites and size convention: `C D : SimplexCategoryᵒᵖ → Type u` with
  `SmallCategory` at every degree and topologies `J`, `K`; the total sites
  `CT`, `DT`, `JT`, `KT` are likewise small. All coefficients are actual
  `AddCommGrpCat.{u}` sheaves. This is the common small skeleton bound of
  `def-weil-size-convention`, not a restriction on the universes of the original
  presentations. Different original bounds can be placed in the common bound.
- Simplicial objects and structure maps: `p`, `q` are the structural inverse
  images for every arrow in `SimplexCategoryᵒᵖ`. For `f : j ⟶ i`, its unop is
  `[i] → [j]`, and `p f` goes from sheaves in degree `i` to degree `j`.
  `pId`, `qId`, `pComp`, `qComp` give the specified isomorphisms. The full two
  unit laws and cocycle identities are fields of the dependency's `S` and `T`.
  `pSite`, `qSite` retain the site origin: a continuous site functor, a left
  exact inverse image on sets, and the displayed identification of the abelian
  inverse image with its sheaf pullback. Preservation of colimits on sets
  follows because the pullback is a left adjoint.
- Component morphisms `h_n`: `M.component i : GeometricMorphism ... ...`
  contains the inverse and direct images, their adjunction, and left exactness.
  `hSite` identifies its direct image with precomposition for a continuous site
  functor whose inverse image on sets is left exact. Its inverse is thereby
  identified, including the adjunction, by uniqueness of left adjoints.
  `inverse_additive`, `direct_additive`, and `inverse_colimits` merely expose
  the additive and finite-colimit structures of these induced abelian functors;
  these are intrinsic properties of abelian inverse/direct images, not an
  additional geometric restriction. Inverse left-exactness is inherited from
  the geometric-morphism datum.
- Commutation with structure maps: `M.commute f` has precisely the type
  `h_i.inverse ⋙ p f ≅ q f ⋙ h_j.inverse`. `commute_id` and `commute_comp`
  give its identity and composition coherence, with both paths written out at
  each object. No strictification is imposed.
- Total sheaves as compatible families: `S` and `T` are the recorded
  `TotalSiteSystemData`, not a new family definition. Their `map_bijective`
  and `essentially_surjective` fields require ALL compatible families and ALL
  compatible morphisms, not a selected subcategory. Their component categories
  and total categories here are actual abelian sheaf categories. This records
  the abelian part of the node's total-topos family description, which is the
  part on which its restriction and derived conclusions are stated.
- The induced total morphism: the existential `H` is a geometric-morphism datum
  between the total abelian sheaf categories. The family `a` identifies its
  inverse image componentwise, and the first conjunct intertwines transitions
  using exactly `M.commute`. The family `b` identifies its direct image
  componentwise. The second conjunct says that the ordinary unit becomes the
  component unit under `a` and `b`; this is the mate normalization of `b`.
  Thus this is the induced adjunction determined by the compatible-family
  construction, up to its canonical presentation isomorphisms. The theorem
  does not choose data from its existential using a definition.
- Exactness and conservativity: both leading conjuncts assert joint
  conservativity of the respective restriction families. The existential
  `PreservesFiniteLimits`/`PreservesFiniteColimits` witnesses assert exactness
  of every `S.component i` and `T.component i`. They are conclusions, not
  extra exactness assumptions. The analogous witnesses on `H.inverse`
  assert exactness of the total inverse image.
- `r_n Rh_* ≅ Rh_{n,*} r_n`: for every `i`,
  `IsIso (Functor.rightDerivedFunctorPlusBaseChange (b i).hom)` states that
  the existing canonical natural transformation
  `H.direct.rightDerivedFunctorPlus ⋙ (T.component i).mapDerivedCategoryPlus ⟶
  (S.component i).mapDerivedCategoryPlus ⋙
  (M.component i).direct.rightDerivedFunctorPlus` is invertible. This is a
  natural comparison on `DerivedCategory.Plus`, not objectwise choices.
  Its inverse can be obtained with `asIso`; the actual comparison is fixed by
  its right-derived universal-property normalization.
- `r_n h⁻¹ ≅ h_n⁻¹ r_n`: the natural isomorphism is the explicit composite
  `(mapDerivedCategoryPlusCompIso H.inverse (S.component i)).symm ≪≫
  mapDerivedCategoryPlusNatIso (a i) ≪≫
  mapDerivedCategoryPlusCompIso (T.component i) (M.component i).inverse`.
  All three are existing canonical isomorphisms. This term appears directly in
  the final conclusion, so no arbitrary replacement comparison is quantified.
  It is already an isomorphism by its type; no additional existence assertion
  is needed to make it available to a consumer.
- Units: the last conjunct, for every component and every bounded-below complex
  `X`, maps `H.adj.derivedPlus.unit.app X` by restriction, then composes with
  the canonical direct comparison at `H.inverse X`, followed by `Rh_i` of the
  explicit inverse comparison. The result equals
  `(M.component i).adj.derivedPlus.unit.app (r_i X)`. Both units are the actual
  existing bounded-below derived-adjunction units.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings` was read. As in the published
  total-system interface, sheaves use the associated Mathlib Grothendieck
  topology; no new covering/site or sheaf definition is introduced. This
  dependency's module is publicly imported through the restriction module.
- `Sheaf.TraceFormula.TotalSiteComponentRestriction`:
  `TotalSiteCompatibleSystem`, `TotalSiteCompatibleMorphism`,
  `TotalSiteSystemData`, `totalSiteComponentRestriction`. The entire file,
  signatures, coherence and fully faithful/essential-surjectivity fields were
  read. The theorem's proof plan uses its exactness and injective preservation.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`:
  `CategoryTheory.GeometricMorphism` and its `inverse`, `direct`, `adj`,
  `leftExact` fields, from the recorded dependency.
- `Mathlib.AlgebraicTopology.SimplicialObject.Basic`:
  `CategoryTheory.SimplicialObject = SimplexCategoryᵒᵖ ⥤ C`, with its face and
  degeneracy signatures read. The coherent extension uses its same index
  category and includes every simplicial operator.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `HasDerivedCategory`, `DerivedCategory`, `DerivedCategory.Q` were read.
  `DerivedCategory.Plus`, `Functor.mapDerivedCategoryPlus`,
  `Functor.rightDerivedFunctorPlus` are the bounded-below interfaces.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange`:
  `Functor.rightDerivedFunctorPlusBaseChange`, its defining factorization,
  and the invertibility criterion on injective-acyclic representatives.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`:
  `Adjunction.derivedPlus` and its unit factorization.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `mapDerivedCategoryPlusNatIso`, `mapDerivedCategoryPlusCompIso`, with their
  localization-factorization characterizations. These are reexported by the
  public imports above.
- `Mathlib.CategoryTheory.Sites.Pullback`: `Functor.sheafPullback` and
  `Functor.sheafPushforwardContinuous` give the existing site-induced functors.
- Proof imports include `Sheaf.CategoryTheory.KInjectiveComputes`,
  `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`, and the
  Mathlib modules containing the injective-representative theorem and enough
  injectives. `HasDerivedCategory.ofIsGrothendieckAbelian` supplies the
  localization models. No site, coefficient, or derived category is redefined.

Edge checks: degree zero is included; identity and composite simplicial
operators have explicit coherence equations. With constant sites and identity
morphisms, compatible families are the ordinary covariant simplex diagrams
and all comparisons reduce to their canonical presentation identifications.
The zero sheaf and zero complex are allowed; no nonzero or nonempty sheaf
hypothesis is present. Empty sites are allowed. All `i`, including the object
`op (SimplexCategory.mk 0)`, occur in the final natural comparison and unit
formula. Only bounded-below derived categories occur, and no uniform lower
bound, boundedness above, or assumption that a complex is a pullback is added.
The direct comparison's source and target have been checked in the compiler;
its direction agrees with the component-to-total base-change formula.

Searches for existing statements and constructions:

- `msearch.py leanfinder`, query "Derived pushforward on total simplicial sites
  commutes with component restriction and adjunction units": eight hits on
  continuous/cocontinuous sheaf pushforward compatibility and module
  adjunction-unit formulas; no total-site derived-component theorem.
- `msearch.py loogle`, query `"rightDerived", "NatIso"`: three hits on
  `Functor.rightDerivedNatIso` and its projections. This is the generic derived
  comparison API, not the simplicial-site result.
- `msearch.py grep`, query `totalSite|TotalSite|simplicial.*[Dd]erived`: zero
  Mathlib hits.
- `msearch.py leansearch`, query "component restriction derived pushforward
  total simplicial site": eight hits on ordinary sheaf pushforward,
  `Sieve.pushforward`, and presheaf-module pushforward; no matching theorem.
- Direct `rg` in `WeilConjectures` and `lean/Sheaf` for
  `TotalSite|totalSite|lem-trf-total-site-derived-components`: only the already
  recorded component-restriction module and the downstream hypercover proof
  plan. No duplicate theorem exists. The names `TotalSiteMorphismData` and
  `totalSiteDerivedComponents` also have no hit in either source library or
  `dag/lean_names_upstream.json`.
- Read the upstream `PlusBaseChange`, `PlusAdjunction`, and `ExactFunctor`
  implementations; these supply the canonical comparisons reused here.

Validation: all compilation uses `scompile.py`, file by file. The first check
identified an instance hidden behind a proof-only import of the enough-
injectives module; making that import public repaired the public signature.
The final module is checked again after the site-origin binders and then by
`deliver2.py --no-push`. No statement is disputed.

## Second reading by Q117

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
