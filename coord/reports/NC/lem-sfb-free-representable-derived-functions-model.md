## Worker report

The module `Sheaf.CategoryTheory.FreeRepresentableDerivedFunctions` states
`CategoryTheory.FreeRepresentableDerivedFunctions.free_representable_derived_functions_model`.
It constructs the free representable module, its generator, the existing internal-Hom
functor, product precomposition, the two specified nonnegative resolution models,
and their canonical comparison map. The one theorem has proof `sorry`; all
construction data come from existing functors, adjunctions, and complex maps.

The prior worker's stale-assignment concern was checked against the live node.
NU's recorded delivery split and reviewed the DAG node at stage 1; it did not
supply a stage-2 Lean record or module. This delivery supplies that missing record.
No node statement, dependency list, proof, or proof dependency has been changed.

### Hypotheses and each clause

* A site small in the sheaf universe is `{C : Type u} [SmallCategory C]`
  with `(J : GrothendieckTopology C)`. The node's proof explicitly uses a common
  sheaf universe: site objects and morphisms, coefficient rings, and module
  elements all lie in `u`. This is universe polymorphic, not a fixed universe-zero
  assertion. `wA` independently specifies the chosen derived localization size;
  `[HasDerivedCategory.{wA} (Sheaf J AddCommGrpCat.{u})]` is the recorded size
  convention for that localization, not an extra geometric hypothesis.
* Finite products are `[HasFiniteProducts C]`; subcanonicity is `[J.Subcanonical]`.
  There is no finite-cover, projectivity, constant-ring, or discreteness assumption.
* The coefficient sheaf is `(R : Sheaf J CommRingCat.{u})`; `ring J R` applies
  `sheafCompose` with `forget₂ CommRingCat RingCat`. `modules J R` is precisely
  the recorded `ringedSiteModules.{u}`, hence ordinary `SheafOfModules`, not a
  topological, solid, or condensed substitute.
* The forgetful functor U is `SheafOfModules.toSheaf (ring J R)`. Inclusion ι
  is `sheafToPresheaf J AddCommGrpCat.{u}`, and a is `presheafToSheaf J
  AddCommGrpCat.{u}` with the actual `sheafificationAdjunction` counit.
* `free J R` is `yoneda ⋙ PresheafOfModules.free (ring J R).obj ⋙
  PresheafOfModules.sheafification (𝟙 (ring J R).obj)`. Its value at P is
  the sheafification of the presheaf direct sum indexed by Hom(-,P).
  `generator` sends `ModuleCat.freeMk b` through the actual adjunction unit.
  No free object is chosen from a mere existence assertion.
* `hom J R P` is exactly `(SheafOfModules.homFunctor R).obj
  (op ((free J R).obj P))`. Thus its values are the dependency's slice internal
  sheaf Hom. Additivity is inherited from the existing tensor-Hom adjunction;
  the instance introduces no new postponed theorem.
* `precomp P` is whiskering by `(prod.functor.flip.obj P).op`; its value on V
  is V × P (the flip fixes the second factor). Its additivity and finite limit
  and colimit preservation instances are the existing whiskering instances.
* Cochains use `.up ℤ`. An `InjectiveResolution M` is nonnegative, and
  `I.cochainComplex` is its canonical extension from ℕ to ℤ. The `Plus`
  membership uses the actual degree-zero lower bound, not a hypothesis
  asserting that an otherwise unrestricted complex is bounded below.
* `leftComplex J R P I` applies H_P and then U termwise to the module
  injective resolution I. It is the model of `D(U) RH_P(M[0])` explicitly
  prescribed by the node. `rightComplex J P T` applies `ι ⋙ t_P ⋙ a`
  termwise to an abelian injective resolution T of UM; this is the prescribed
  model of `D(a) D(t_P) Rι(UM[0])`. The latter resolves in **abelian sheaves**;
  it does not incorrectly assume that U preserves module injectives.
* The theorem's E is an isomorphism between these objects after the canonical
  localization `DerivedCategory.Plus.Q`. It is an isomorphism in D+, not
  merely a family of isomorphisms on cohomology groups. Quantification is over
  every I and T, so it does not impose extra chosen resolutions on the result.
  This representative formulation uses the node's own definition of the two
  derived objects, rather than defining a competing right-derived functor.
* The family θ is a natural isomorphism of functors in M from `ι U H_P`
  to `t_P ι U`. Its first conjunct gives the exact sectionwise normalization:
  `((θ P).hom.app M).app (op V) φ` equals φ evaluated over
  `Over.mk (prod.fst : V × P ⟶ V)` on `generator ... prod.snd`.
  This is precisely restriction to the slice followed by evaluation on the
  universal generator. The formula fixes θ, including its orientation.
* `Compatible I T c` is the augmentation square for a chain map
  `c : U(I.cochainComplex) ⟶ T.cochainComplex`, using the canonical
  `HomologicalComplex.singleMapHomologicalComplex` isomorphism. The theorem
  asserts existence of such c and fixes E for **every** compatible c.
  Thus normalization is neither vacuous nor an arbitrary unconstrained map.
  `sheafEvaluationIso` sheafifies θ with the actual counit; `comparisonMap`
  applies that map termwise and then applies `a t_P ι` to c. The equation
  `(E ...).hom = DerivedCategory.Plus.Q.map (comparisonMap ... c)` specifies
  the canonical derived comparison. On the degree-zero kernels, the
  augmentation square makes it the preceding generator-evaluation formula.
* Covariant naturality in a module map f is the fourth conjunct, using every
  `s : I.Hom I' f` and `t : T.Hom T' (U.map f)`. `leftMap` applies U H_P
  to `s.hom'`; `rightMap` applies `a t_P ι` to `t.hom'`. The equality of
  localized composites states exactly that the induced H_P map corresponds
  to `D(a) D(t_P) Rι(Uf)`. Taking f to be an identity also compares all
  resolution choices, and quantifying over all lifts removes lifting choices.
* Contravariant naturality in `f : P' ⟶ P` is the last conjunct.
  `leftParameterMap` is the internal-Hom precomposition by `free.map f`;
  `rightParameterMap` is restriction along `1 × f`, obtained from
  `NatTrans.op (prod.functor.flip.map f)` and then sheafified.
* `unboundedComparison` is the real construction
  `DerivedCategory.Plus.ι.mapIso E`. Its source and target are the canonical
  images of the same D+ objects in D. All commuting squares also remain
  commuting squares after this functor. No extra existence or arbitrary
  isomorphism is used for the final unbounded clause.

### Dependency declarations and sources read

* `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; the Grothendieck topology
  and sheaf portions use the Mathlib declarations recorded by the same node.
* `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, transparently `SheafOfModules`.
* `Mathlib.CategoryTheory.Sites.Sheafification`:
  `presheafToSheaf`, `toSheafify`, `sheafificationAdjunction`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic` and `.Plus`:
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Plus.Q` and `.ι`.
* `Mathlib.CategoryTheory.Preadditive.Injective.Basic`, `.Resolution`, and
  `Mathlib.CategoryTheory.Abelian.Injective.Extend`:
  `Injective`, `InjectiveResolution`, its `cochainComplex`, `ι'`, `Hom`, `hom'`.
* `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`, `homFunctor`, `homObjMap`; their full slice-Hom
  signatures and docstrings were read. `.MonoidalClosed` supplies the existing
  `tensorHomAdjunction` for the additivity instance.
* `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification` and `.sheafificationAdjunction`.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `over`, `Hom.over`, `overMap`;
  `CategoryTheory.GrothendieckTopology.over` and `Sheaf.over`.
* The size-convention dependency has no Lean module: it is a convention,
  realized by the explicit common universe and independent localization size.

Recorded proof modules are imported as plain imports: the general-universe
Grothendieck theorem `SheafOfModules.isGrothendieckAbelianOfUniverses`,
`CochainComplex.exists_mono_quasiIso_injective_boundedBelow`,
`PresheafOfModules.exists_moduleSheafificationRestrictionIso`,
`CategoryTheory.moduleSheaves_colimits_forgetful`,
`CategoryTheory.injective_module_abelian_acyclic`,
`CochainComplex.homotopy_of_comp_quasiIso_of_injective`, and
`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic`.
The Mathlib proof dependencies are the recorded enough-injectives theorem,
freeYonedaEquiv, exact sheafification, exact evaluation, mapDerivedCategoryFactors,
rightDerivedFunctorPlus, and the injective model-category lifting property.
The theorem docstring spells out all nine proof steps, including why U(I) is
ι-acyclic without being assumed injective, and how comparison and normalization
follow from the augmentation and homotopy uniqueness.

Read the source passages in `literature/stacks-project/sites-cohomology.tex`,
section-internal-hom (08J7), lemma-cohomology-modules-abelian-agree (03FD), and
`sites-modules.tex`, lemma-internal-hom (03EM). These identify the specified
injective model and the generator-evaluation formula. The derived comparison
uses derived.tex 015E, with lifting and homotopy uniqueness as in 013P and 013S.

### Edge cases

The zero ring and zero module are allowed; free module, generator and comparison
remain defined (all resulting maps are the unique zero maps in the zero-ring
case). No nontriviality, flatness, characteristic, finiteness, or discrete topology
of a coefficient ring is imposed. A terminal P specializes product restriction
to the unit parameter, and every parameter morphism, including identities, is
covered. An initial P, when present, is allowed without assuming that products
with it are initial. A finite-products category is nonempty by its terminal
object; the empty category is therefore not an omitted case. Negative complex
degrees are the canonical zeros, including the boundary differential to degree
zero. The theorem applies to all subcanonical topologies, including ones without
finite covering families; exact precomposition is evaluated at V × P and does
not appeal to any covering finiteness. Comparison existence and all identity
coefficient lifts prevent vacuous canonicity or choice independence claims.

### Searches actually performed

* `msearch.py ... leanfinder "Derived internal Hom of a free representable module
  sheaf is sheafification of derived sections on products"`: eight results,
  including freeHomEquiv and sheafificationHomEquiv; no derived comparison.
* `msearch.py ... loogle "SheafOfModules.homObj, PresheafOfModules.freeYoneda"`:
  zero results; Loogle did not know the upstream-only homObj name.
* `msearch.py ... grep "rightDerivedFunctorPlus|freeYoneda|homFunctor"
  Algebra/Category/ModuleCat`: ten hits for the free Yoneda and related
  constructions; none states this derived comparison.
* `msearch.py ... leansearch "Derived internal Hom from the free module sheaf on
  a representable equals sheafified derived sections on products"`: eight
  underived hits, including Sheaf.freeYonedaHomEquiv, SheafOfModules.free,
  PresheafOfModules.freeObj and LightCondensed.ihomPoints; no exact theorem.
* Local rg in both `lean/WeilConjectures` and `lean/Sheaf` for free-representable,
  derived, Hom and product-precomposition names; item-id grep in the upstream
  source; and `dag/lean_names_upstream.json`: no existing exact statement.
  Existing internal Hom, free modules, tensor-Hom adjunction, and resolution
  constructions were read and reused, not duplicated.
* Local DAG search for free representables and
  `tools/blueprint_refs.py search 'free representable'`: zero blueprint-node
  hits; other DAG hits concern specialized condensed constructions, not this
  arbitrary ringed-site derived comparison.

No new DAG notions or dependency replacements were needed. The helper definitions
are the canonical constructions already introduced by this item's own statement.
No mathematical statement dispute or statement correction is asserted.

### Validation

All compilation uses the prescribed `scompile.py` wrapper, against the published
live library. Initial elaboration errors were repaired using the actual natural
transformation and whiskering signatures. Scratch probes were removed from the
delivery. The complete module compiled cleanly with `scompile.py` (sandbox 35.7 s;
library module 27.8 s). `deliver2.py NC
lem-sfb-free-representable-derived-functions-model --no-push` then returned
`OK (dry run): commit 181aa72620c passes the preflight and compiles; nothing pushed`.
The final delivery invocation repeats the server checks and compiles before pushing.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
