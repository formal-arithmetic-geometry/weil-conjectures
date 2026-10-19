## Worker report

The module `Sheaf.CategoryTheory.RingedSliceExtensionTensor` states
`SheafOfModules.ringedSlice_extension_tensor`, with `sorry` as its entire proof.
Source read: `literature/stacks-project/sites-modules.tex`, Tag 0E8I,
`lemma-j-shriek-and-tensor`, including its five Hom identifications; the DAG expands
these into internal-Hom restriction, the two adjunctions, inverse maps and naturality.
All five steps are retained in the theorem docstring. Nothing is proved or defined anew.

Hypotheses and clauses, in the order of the node:

- A ringed site is `{C : Type uC} [Category.{u} C] (J : GrothendieckTopology C)`
  with `R : Sheaf J CommRingCat.{u}`. The ring is commutative, as required.
  The object universe `uC` is independent of the common bound `u` used for the
  morphism sets, rings, and section modules. In particular, a site with objects
  in `Type (u+1)` and morphisms in `Type u` is permitted; no small-category
  hypothesis, pullbacks, basis precoverage or enough-points hypothesis is imposed.
- The sheaf-compose, weak sheafification and locally bijective-equivalence instances
  on `J` and `J.over U` provide the existing module sheafification constructions.
  They are the categorical size/sheafification infrastructure, not flatness,
  finiteness, exactness or geometric assumptions on modules. The sheaf tensors
  are written directly as sheafified presheaf tensors, so the upstream proof of
  monoidality (which specializes the object universe) is not an additional hypothesis.
- `U : C`, the ring sheaf `((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U`,
  and `overFunctor` are exactly the localized site, its ring sheaf and restriction.
- Both functors have domain the product of the entire slice module category with
  the entire original module category. Thus every G and every F occur, including zero.
- The first product functor forgets G to its module presheaf and restricts F using
  `overFunctor` before forgetting. `MonoidalCategory.tensor` takes the sectionwise
  presheaf tensor; slice module sheafification gives G tensor F|U.
  `extensionByZeroPresheaf ⋙ PresheafOfModules.sheafification (𝟙 _)` then gives
  precisely j_!(G tensor F|U).
- The second functor first extends G by that same direct-sum/sheafification composite,
  forgets both it and F to presheaves, tensors them and sheafifies. This is exactly
  (j_!G) tensor F over the original ring sheaf.
- `Nonempty (leftFunctor ≅ rightFunctor)` asserts an isomorphism of those functors.
  Its components are isomorphisms of module sheaves, not just of sets or abelian
  sheaves. Naturality for every morphism of the product category includes simultaneous
  maps G -> G' and F -> F', and hence naturality in each variable as well.

Dependency interfaces read and used:

- `def-pur-localized-ringed-site`: Mathlib module
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`, declarations
  `SheafOfModules.over`, `overFunctor`, `Hom.over`, `overMap`, `overFunctorMap`;
  `Mathlib.CategoryTheory.Sites.Over`, `GrothendieckTopology.over`, `Sheaf.over`.
- `def-weil-sheaf-of-modules-category`: imported
  `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`,
  a transparent abbreviation for the same Mathlib `SheafOfModules` appearing as
  the domains of `forget` and `overFunctor`. No replacement category is introduced.
- `def-weil-extension-by-zero-presheaf`: imported
  `Sheaf.CategoryTheory.ExtensionByZeroPresheaf`, `SheafOfModules.extensionByZeroPresheaf`;
  its direct sum runs over all arrows V -> U, and its action on morphisms is retained.
- `def-weil-presheaf-modules-sheafification`: Mathlib module
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`,
  `PresheafOfModules.sheafification` specialized to the identity ring map, on each site.
- `def-pur-sheaf-tensor-product`: imported
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct` and its public upstream module
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`; inspected
  `SheafOfModules.monoidalCategory` and `tensorObjIsoSheafification` in full.
  The displayed tensor uses exactly the latter's sheafified presheaf tensor,
  `PresheafOfModules.Monoidal.tensorObj`/`tensorHom` through the presheaf tensor functor.
  It introduces no second tensor construction or monoidal structure.
- Proof imports: `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`,
  `SheafOfModules.localizedModule_adjunction_exact`;
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`, `SheafOfModules.tensorClosed`;
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`, `SheafOfModules.homObj`.
  These are proof-plan imports; their specialized interfaces do not restrict this signature.

Edge cases: empty category (the statement has an explicit U, so no false existence assertion),
zero ring, zero G, zero F, and objects V with no arrow to U are allowed. In the last
case extension starts with the empty direct sum; sheafification is still applied, as
required on an arbitrary site. No assertion of sectionwise vanishing after sheafification
is inserted. Multiple arrows V -> U are retained, not replaced by an open immersion.
Identity and zero morphisms in either parameter are included in functor naturality.
The site object and morphism universes need not coincide.

Searches performed for this item using `msearch.py NK <item>`:

- `leanfinder`: "Projection formula for extension by zero of module sheaves on an
  arbitrary slice ringed site" returned eight hits: ModuleCat.Tilde.res_apply,
  res_const, toOpen, toOpen_res, openToLocalization, SheafOfModules.Presentation.map_π_eq,
  and TopCat.Sheaf.objSupIsoProdEqLocus inverse projections. Their signatures do
  not state the projection formula for arbitrary ringed-site slices.
- `loogle`: `SheafOfModules, "tensor"` returned zero hits.
- `grep`: `projectionFormula|projection_formula|shriek.*tensor|tensor.*shriek`
  returned zero hits.
- `leansearch`: "Extension by zero tensor projection formula on a ringed site"
  was UNAVAILABLE, Internal Server Error; no no-match claim is made for this service.
- Direct `rg` of upstream `WeilConjectures` for extension/tensor/projection terms,
  of the local `lean/Sheaf` tree, and of `dag/lean_names_upstream.json` found
  special open-immersion projection formulas and fixed-coefficient Weil-sheaf
  formulas, but no assertion for arbitrary ringed sites. The item id grep in
  upstream found nothing. The new declaration name was also absent.

Server validation: `scompile.py` compiled the delivered module cleanly, with
nice 19, two threads and a 60-second per-file limit (1.5 seconds for the item).
No node correction, new node, dependency module or disputed mathematical statement.
The independent second reading and delivery are left to the designated second reader.

## Second reading by NK

Independent second reader: read the node and the delivered module side by side,
Stacks `sites-modules.tex`, `definition-ringed-site`, `lemma-j-shriek-and-tensor`
(Tag 0E8I), and the definitions and signatures of the dependencies listed below.
Verdict: the Lean states exactly the node's natural tensor projection isomorphism.
No mismatch requiring a Lean or node change was found; both are retained verbatim.

Object/hypothesis/conclusion checklist, reconstructed from the node before comparison:

1. An arbitrary site and a commutative structure sheaf: `{C : Type uC}`,
   `[Category.{u} C]`, `(J : GrothendieckTopology C)`, and
   `(R : Sheaf J CommRingCat.{u})`. Correct: no scheme, field, finiteness,
   flatness, points, pullbacks, or precoverage is assumed. The source's ringed-site
   definition adds no such assumption.
2. An object U and its localized ringed site: `(U : C)`, `J.over U`, and
   `((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U`.
   Correct. Read Mathlib `Sites/Over.lean` and
   `ModuleCat/Sheaf/PushforwardContinuous.lean`: `overFunctor` keeps section
   modules and scalar restriction maps, including their action on morphisms.
3. The category of module sheaves over each of these rings: the sources of
   `forget` and `overFunctor` are precisely `SheafOfModules` over those rings.
   Correct. Read `RingedSiteModules.lean`: `ringedSiteModules` is a transparent
   abbreviation for this category, with no additional structure or special case.
4. Every slice module G and base module F, in that order: `Functor.prod`
   has domain the product of the entire slice module category and the entire
   base module category. Correct. Neither variable is fixed, restricted to flat
   modules, or replaced by an arbitrary presheaf.
5. Extension is the specified direct-sum presheaf followed by sheafification:
   each occurrence is `extensionByZeroPresheaf Rring U` followed by
   `PresheafOfModules.sheafification (𝟙 Rring.obj)`.
   Correct. Read `ExtensionByZeroPresheaf.lean`, in particular its section,
   restriction, induced morphism and functor definitions. The index is all
   arrows V -> U; scalar multiplication and restrictions are the node's ones.
   Read Mathlib `Presheaf/Sheafification.lean`: the identity ring map gives
   the associated module sheaf, and its adjunction is to `SheafOfModules.forget`.
6. Left side j_!(G tensor F|U): the first `prod` forgets G and restricts F by
   `overFunctor` before forgetting it; the slice `MonoidalCategory.tensor`
   forms the presheaf tensor; slice sheafification precedes extension and base
   sheafification. Correct, including the order of all three sheafifications.
7. Right side (j_!G) tensor F: the second `prod` extends and sheafifies G first,
   then forgets that module and F; base presheaf tensor and base sheafification
   follow. Correct. Read Mathlib `Presheaf/Monoidal.lean`, `tensorObj`,
   `tensorObjMap`, `tensorHom`, and its monoidal instance: these are precisely
   sectionwise tensors with the required restriction and parameter maps.
8. Both tensors are the dependency's sheaf tensors: read `TensorProduct.lean`
   and upstream `Sheaf/Monoidal.lean`, especially `tensorObjIsoSheafification`.
   Correct. The displayed composites use the actual associated-presheaf-tensor
   construction from that interface, with no copied definition or assumed
   sheaf monoidal instance. This also avoids importing the specialized size
   assumption of the upstream monoidality proof into the statement.
9. An isomorphism of O-modules, natural in both variables:
   `Nonempty (leftFunctor ≅ rightFunctor)` is a natural isomorphism in the
   category of module sheaves. Correct. Its components are linear isomorphisms;
   naturality for a product-category arrow covers simultaneous G and F maps.
   The existential quantifier is outside the whole family, so it does not
   merely assert unrelated componentwise isomorphisms.
10. Sheafification infrastructure: `HasSheafCompose`, `WEqualsLocallyBijective`
    and `HasWeakSheafify` on the base and the indicated slice are exactly the
    infrastructure used by these recorded constructions, with coefficients
    `AddCommGrpCat.{u}`. Correct: no geometric or module property is encoded
    in these binders. They expose existence of the associated-sheaf operations
    used in the node at the chosen size.

Edge cases: an empty C supplies no U and hence produces no false assertion of
existence; a category with U and an empty Hom(V,U) yields the empty direct sum
in the presheaf extension. Multiple arrows are all retained. Zero G, zero F,
zero coefficient rings, all characteristics, and identity/zero parameter maps
are admitted. No positive integer, nonempty indexing type or nonzero ring is
assumed. Empty schemes are covered whenever represented as such sites.
`uC` is explicitly bound and independent of `u`; in particular objects in
Type (u+1) with morphisms in Type u are permitted. A common size bound for
rings, modules and arrow sets does not force the object universe equal to it.
No implicit free variable or universe is left in the signature.

Independent H4 searches, using different wording from the worker:

- `msearch.py ... leanfinder "Tensor product commutes with sheafified direct sum
  extension along localization of a site"`: eight results, including
  `PresheafOfModules.sheafifyHomEquiv'`, sheafification naturality lemmas,
  `SheafOfModules.mapFree`, and a condensed free-module monoidality instance.
  Their returned signatures do not assert the formula on arbitrary slice
  ringed sites.
- `msearch.py ... loogle 'SheafOfModules, "extension"'`: zero results.
- `msearch.py ... grep 'jShriek|extensionTensor|extension_tensor|shriek.*tensor'`:
  zero results. Direct independent `rg` in Mathlib's ModuleCat tree, upstream
  WeilConjectures and project lean/Sheaf for shriek/tensor, extensionByZero/tensor,
  and projection-formula terms found specialized scheme/pro-etale and
  fixed-coefficient interfaces. Opened upstream
  `SixFunctors/ProEtale/LowerShriek/OpenImmersion/Projection.lean`, especially
  `openImmersionLowerShriekTensorIso`: it concerns an open immersion of schemes
  and fixed coefficient sheaves, not an arbitrary varying ring sheaf on a site.
  It is not an exact existing declaration for this node. The new full name and
  module name are absent from upstream and the project's library-name index.

H8/proof-plan review: the docstring contains the internal-Hom restriction
identification, both adjunctions and their inverses, the explicit Yoneda inverse
maps, and parameter naturality, in the five steps of the DAG. Read the actual
`LocalizedModuleAdjunctionExact`, `TensorClosed`, and upstream `InternalHom`
interfaces, rather than identifying them from their names. Their recorded
proof interfaces specialize sizes (and the exactness theorem uses a precoverage);
these restrictions are not smuggled into this statement. A future proof at the
full displayed universes must use/generalize the relevant adjunction interface
or the direct sectionwise tensor calculation; the existing large-universe
internal Hom also enlarges the module universe. This is a proof implementation
issue, not a change to the node's underived tensor construction or a missing
object in this statement.

No new definition nodes, dependency deliveries, or statement corrections occur.
There is no data-valued sorry, local notation, local instance, private copy,
extra theorem, tautological conclusion, or proof beyond the theorem's whole
`sorry`. Source and blueprint docstrings, imports and line widths are correct.
The node's `lean.statement` is verbatim the delivered signature.

Validation repeated by this reader: `scompile.py NK
lem-weil-pbc-ringed-slice-extension-tensor
lean/Sheaf/CategoryTheory/RingedSliceExtensionTensor.lean` succeeded on the
server, nice 19, two threads, limit 60 seconds per file. It compiled the required
RingedSiteModules overlay (1.0 s) and the delivered module (1.5 s), with no errors
or warnings. Changes by the second reading: appended this independent audit only.
