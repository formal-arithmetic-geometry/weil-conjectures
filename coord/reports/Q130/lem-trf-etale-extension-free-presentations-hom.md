## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleExtensionFreePresentationsHom` states
`AlgebraicGeometry.Scheme.Modules.etaleExtension_free_presentations_hom`, with one
`sorry` proof. Its only additional declaration is the actual canonical étale-arrow
reassociation isomorphism `etaleExtensionAssociator`, with identity underlying scheme
map. No definition has postponed data. No node statement or dependency was changed.

The source was read in `literature/stacks-project/descent.tex`: the complete remark
`remark-change-topologies-ringed-sites` (03FH), lemma
`lemma-quasi-coherent-gives-quasi-coherent` (03DV), and lemma
`lemma-fully-faithful-associated` (0GN7), including their proofs. In particular, the
free presentations have arbitrary index sets, and full faithfulness follows from
the unit, without any assertion that the counit is invertible on all modules.

Hypothesis and clause correspondence:

- Every scheme is `T : Scheme.{u}`. No nonemptiness, separation, finiteness,
  Noetherian or characteristic assumption is added. Modules are exactly `T.Modules`
  and `SmallEtaleModules T`, the existing `SheafOfModules` categories over their
  existing ring sheaves. Zariski and small étale topologies are the existing
  `Opens.grothendieckTopology T` and `T.smallEtaleTopology`.
- The existential family `c : ∀ T, ZariskiEtaleModuleContext T` supplies only proofs
  of continuity and existence of the right adjoint. It contains no freely chosen
  ring, functor, map or adjunction: `c.extension`, `c.restriction`, and `c.adjunction`
  are the existing canonical tensor extension, restriction and their adjunction.
  Thus the clause `L_T ⊣ R_T` is supplied by the actual term `(c T).adjunction`.
- Preservation of every small colimit is
  `PreservesColimitsOfSize.{v, w} (c T).extension`, with both diagram universes
  explicitly arbitrary; it applies to all modules, before quasi-coherence binders.
- The second conjunct identifies extension of `SheafOfModules.unit T.ringCatSheaf`
  with `SheafOfModules.unit (smallEtaleModuleRing T)`. The latter ring has actual
  regular-function sections, not constant coefficients or a universe lift.
- For each `[F.IsQuasicoherent]`, `e T F` is an isomorphism of additive sheaves
  from the extension to the dependency's `etaleTensorSectionsSheaf F`. Its
  underlying presheaf is literally `V ↦ Γ((tensorPullback V.hom).obj F, ⊤)`,
  with `etaleTensorSectionsRestriction` on arrows, not a sheafified replacement.
- The first conjunct after `e` explicitly preserves multiplication by every
  `r : Γ(V.left, ⊤)`. Thus this additive sheaf isomorphism is a module
  identification. The next conjunct gives naturality in every module map `h`,
  with target map exactly `((tensorPullback V.hom).map h).app ⊤`. The sheaf
  isomorphism type already includes naturality for every étale site arrow.
- The affine cover is `ι : Type u`, `W : ι → T.Opens`, with pointwise union
  condition `∀ x, ∃ i, x ∈ W i` and `∀ i, IsAffineOpen (W i)`.
  On each open, `I J : Type u` and the arrows `f`, `g` give its free presentation.
  The target is the existing `(tensorPullback (W i).ι).obj F`, canonically
  isomorphic to `F|W` by the recorded unit-compatible open-restriction comparison.
  The conjunction `z : f ≫ g = 0` and `IsColimit (CokernelCofork.ofπ g z)`
  says exactly that the target is the cokernel, hence that the presentation is exact
  and ends in zero. This does not require sectionwise surjectivity on all opens.
- For both free terms, the next two isomorphisms identify their extension with
  `SheafOfModules.free` on the same index types over the actual étale ring.
  The final `z'` and cokernel cofork assert that the images of these very arrows,
  not some replacement arrows, are again a presentation. The localization `k`
  for `U = Scheme.Etale.mk (W i).ι` identifies its target with the restriction
  of the original extension. Thus this clause describes the requested images.
- The separate conjunct `((c T).extension.obj F).IsQuasicoherent` uses precisely
  Mathlib's general-site predicate, which requires presentations locally on every
  slice. It is not replaced by existence of a presentation near the final object.
- For every `U : T.Etale`, `k T F U` identifies restriction along
  `Scheme.Etale.etaleToOver U ⋙ Over.forget U` with extension on `U.left` of
  `(tensorPullback U.hom).obj F`. This is the existing slice-site equivalence,
  with the rings literally the same functions on each underlying scheme.
  It is written as an isomorphism of additive presheaves, with its module meaning
  fixed by the next equation: compose with `e` and the actual module-pullback
  composition map `tensorSectionsComp A.hom U.hom` to obtain `e T F` at the
  composite. Because `e` is linear and tensor composition is a module isomorphism,
  this forces the comparison to be linear; its inverse is linear too.
- The next equation gives naturality of `k` in `F ⟶ H`. The three-arrow equation
  says the iterated localization, followed by extension of `tensorSectionsComp`,
  equals direct localization for `A.hom ≫ U.hom`; its left source is transported
  by `etaleExtensionAssociator`, with the correct contravariant direction `.inv.op`.
  Thus compatibility with composition is explicit, not merely mentioned in prose.
- For every open `W`, the unit followed by `e` and `tensorOpenSectionIso` is
  `𝟙 _`. This is exactly the stated identity on `F(W)`, including the canonical
  identification of functions/sections on an open subscheme.
- For `[F.IsQuasicoherent] [H.IsQuasicoherent]`,
  `Function.Bijective (fun h : F ⟶ H ↦ (c T).extension.map h)` is exactly the
  induced Hom comparison. There is no arbitrary Hom equivalence in its place.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`; and
  `Mathlib.CategoryTheory.Sites.Spaces`: `Opens.grothendieckTopology`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` and
  `Scheme.Etale` (objects and morphisms have the node's meanings).
- `Sheaf.AlgebraicGeometry.ZariskiEtaleTensorSections`:
  `Scheme.Modules.zariskiEtale_tensorSections`, the existing context, ring,
  extension, restriction and adjunction (defined in its public dependency
  `Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently the original Mathlib `SheafOfModules` category.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: the dependency's public
  `SheafOfModules.IsQuasicoherent`; its finite-type conjunction is not assumed
  here. The node's quasi-coherence clause is the existing site-local predicate,
  which agrees with affine-local tilde quasi-coherence for schemes.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule` retains the general
  Mathlib `SheafOfModules.IsQuasicoherent` of the dependency; no private predicate
  or algebraic-space specialization is introduced in this statement.
- `WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf`:
  `etaleTensorSectionsSheaf`; `WeilConjectures.AlgebraicGeometry.EtaleTensorSections`:
  `etaleTensorSectionsPresheaf`, `tensorSectionsComp`, and its restrictions.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` and its upstream
  `WeilConjectures.AlgebraicGeometry.TensorPullback`: the actual `tensorPullback`;
  its normalized adjunction has not been replaced by Mathlib's abstract pullback.
- `Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent`:
  `isQuasicoherent_tensorPullback`, only to make quasi-coherence of pulled-back
  modules available to the localized section-identification term. It transports
  the recorded ordinary-pullback theorem across the canonical adjunction comparison.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`:
  `Etale.etaleToOver`, `Etale.overEquiv`, identifying the slice restriction used.
- All already stated proof dependency modules are imported, including
  `ModulePullbackPushforwardAdjunction`, `Adjunction.Limits`, étale descent,
  module sheafification, tensor-section functoriality/map naturality, affine
  tilde adjunction/free comparisons, open-restriction comparison, and the two
  tensor-section adjunction extension/open determination modules. Their signatures
  and docstrings were read. Only proof uses have non-public imports.

Edge cases checked: empty scheme, empty open, zero module, empty sets of generators
or relations, infinite small generator/relation sets, identity étale morphisms,
repeated objects/arrows in the cocycle, and arbitrary characteristic. The cover
allows empty index type on the empty scheme. No finite generation is asserted.
The site object universe remains `u+1`, its arrows and section modules retain `u`;
no equality of object and arrow universes is imposed. Arbitrary diagram universes
`v,w` are independent, explicitly bound. No `let`, hidden `show`, local notation,
file-local instance or automatically bound implicit occurs in the signature.

Searches made using the prescribed wrapper and direct source searches:

- LeanFinder: “Tensor extension from Zariski modules to small etale modules
  preserves colimits and local free presentations and is fully faithful on quasi
  coherent modules”. Eight results: scheme-module forgetful full faithfulness,
  étale-object forgetful full faithfulness, and `SheafOfModules.mapFree` /
  `SheafOfModules.Presentation.map`. None states this node.
- Loogle: `SheafOfModules.QuasicoherentData, SheafOfModules.free,
  Functor.FullyFaithful`. Zero results; the last name was not accepted as an
  identifier. The relevant actual declarations were inspected directly afterward.
- LeanSearch: “Quasicoherent modules extend from the Zariski site to the small
  etale site with free presentations and bijective Hom comparison”. Eight results,
  all general quasi-coherence predicates/data, not the topology-change theorem.
- Wrapper grep: `QuasicoherentData|def free|def IsQuasicoherent` in
  `Algebra/Category/ModuleCat/Sheaf`: 16 results, including existing free modules,
  local presentation data and presentation transport. These definitions are reused.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  tensor-extension/Hom/free names: no exact existing statement. The already landed
  scheme Zariski/étale equivalence has some consequences of this item, but lacks
  the explicit affine presentation/image and localized cocycle clauses, so is
  not an exact existing match. Searches for both new declaration names and the
  item id, including `dag/lean_names_upstream.json`, found no name collisions.

Validation: the first server compile diagnosed only an associator elaboration issue
and invalid attempts to project a presheaf morphism; these were repaired by explicit
categorical equality and the actual `SheafOfModules.toSheaf` map. The next prescribed
`scompile.py` run compiled both sandbox and final module cleanly (26.4 s and 21.9 s).
All theorem proof content is `sorry`; the associator is real isomorphism data.
No statement correction, dependency replacement or new node is required.

## Second reading by Q130

I reread the node, the completed signature, its dependent interfaces and the Stacks
source after the clean compile. This is a separate self-check, not a claim that a
second agent reviewed it: the dispatcher explicitly prohibits starting other agents,
and the maintainer performs the independent review. The clause mapping above records
that check. In particular I checked the unit equation uses the canonical open-section
comparison, the Hom function is the actual extension map, the presentation arrows
are preserved rather than reselected, and the cocycle includes reassociation of
étale arrows. No mathematical mismatch was found. The only corrections before this
reading were the two elaboration issues noted above; no informal statement changed.
