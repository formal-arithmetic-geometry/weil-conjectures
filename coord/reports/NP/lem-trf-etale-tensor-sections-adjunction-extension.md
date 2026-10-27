## Worker report

Delivered the statement of `lem-trf-etale-tensor-sections-adjunction-extension` in
`Sheaf.AlgebraicGeometry.EtaleTensorSectionsAdjunctionExtension`, together with the
section 1(B) tensor-pullback interface repair described below. The item's accepted
statement and five-step proof are unchanged. All new theorem proofs are `sorry`;
all helper definitions contain actual constructions. No new DAG nodes.

Hypotheses and clauses, matched individually:

- Scheme T: `(T : Scheme.{u})`. Its small site is `T.Etale`, with the recorded
  `T.smallEtaleTopology`; its Zariski site is `Opens.grothendieckTopology T`.
- Structure rings O_et(u) = Gamma(V,O_V): the existing
  `T.etaleStructurePresheaf` followed by `forget₂ CommRingCat.{u} RingCat.{u}`.
  This is the actual regular-function presheaf, with actual pullback ring maps.
- Arbitrary Zariski module M: `M : T.Modules`, with no quasi-coherence binder.
- Arbitrary O_et-module sheaf G: `G : PresheafOfModules.{u} (...)` together with
  `hG : Presheaf.IsSheaf T.smallEtaleTopology G.presheaf`. These are exactly the
  two fields of Mathlib `SheafOfModules`, unbundled to avoid constructing a
  second bundled structure-ring sheaf. Maps `k : G ⟶ G'` are precisely the
  componentwise linear natural maps; sheaf conditions impose no additional map data.
- P_M(u) = Gamma(V,u^*M), with normalized restrictions:
  `etaleTensorSectionsPresheaf M`, using the existing tensor-pullback presheaf.
- G_u(A) = G(A -> V -> T): `tensorExtensionOpenFunctor U.hom` composes the
  recorded `gabberOpenEtale` with `MorphismProperty.Over.map`. The actual
  `PresheafOfModules.pushforward` along this functor and the open-section ring
  identification is `tensorExtensionZariskiPresheaf`; its sheaf realization is
  `tensorExtensionZariskiRestriction U.hom G hG`. Continuity proves the sheaf
  condition by Mathlib's `op_comp_isSheaf_of_isSheaf`, without a postponed proof.
- G_T is `tensorExtensionZariskiRestriction (𝟙 T) G hG`. Its open objects have
  structural map W.ι followed by identity; `tensorExtensionBaseOpenIso` records
  the canonical identification with the ordinary open object W.ι.
- beta is a Zariski module map: the binder
  `β : M ⟶ tensorExtensionZariskiRestriction (𝟙 T) G hG`.
- The prescribed b_u is a module map: the first conjunct provides
  `b : M ⟶ (pushforward U.hom).obj (...)`, and its equation holds for every
  `W : T.Opens` and `m : Γ(M,W)`. `tensorExtensionBaseChangeArrow U.hom W`
  has underlying scheme arrow `U.hom ∣_ W`, from the inverse-image open to W.
  Thus the formula is exactly G(V_W -> W)(beta_W(m)), including scalars.
- a_u is this b_u's adjoint, not an arbitrary map: the next equation evaluates
  `((Classical.choose (exists_tensorPullbackAdjunction U.hom)).homEquiv M _).symm b`
  on global sections. `tensorExtensionTopIso` transports G_u(top) to G(U) through
  the actual scheme isomorphism from the top open to V.
- Theta is a presheaf morphism: its value has type
  `etaleTensorSectionsPresheaf M ⟶ G.presheaf`. Every naturality square is
  included in this natural-transformation type. The separate scalar equation,
  for every U, r and s, says its additive components are O_et(U)-linear.
  The explicit `SMul.smul` fixes the G.obj module structure without instance ambiguity.
  Together these data are exactly a morphism of module presheaves.
- The open equation holds for every W and m. `(tensorOpenSectionIso T M W).inv`
  is Gamma(kappa_W) with the canonical identification of restriction sections
  with M(W). It is defined using the same `exists_tensorPullbackAdjunction`
  and `restrictAdjunction`; its direction is restriction to tensor pullback.
  The G-side open isomorphism only removes the trailing identity structural map.
- Both-variable naturality: the last conjunct quantifies M', M, G, G', hG, hG',
  beta, h, k, U and s. Its left side is Theta of
  `h ≫ β ≫ tensorExtensionZariskiMap (𝟙 T) hG hG' k`; its right side first
  applies `((tensorPullback U.hom).map h).app ⊤`, then Theta, then `k.app (op U)`.
  This is exactly k composed with Theta composed with P_h, componentwise.
- There is no quasi-coherence, nonemptiness, separation or finiteness hypothesis.
  The existential Theta is fixed by the explicit sectionwise b formula and
  the adjunction Hom equivalence. It introduces no arbitrary canonical map.

The main theorem docstring carries all five DAG proof steps, including the
composition-unit calculation and both inverse-open and naturality calculations.
The helper definitions belong to the very construction introduced by this node;
none is an independent replacement of a recorded notion.

Dependency declarations used (source signatures and docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`, `smallEtaleTopology`.
- `Sheaf.CategoryTheory.RingedSiteModules`: the transparent `ringedSiteModules`
  interface, whose underlying Mathlib data are `SheafOfModules` and
  `PresheafOfModules`; these exact Mathlib types are used here.
- `WeilConjectures.AlgebraicGeometry.EtaleTensorSections`:
  `etaleTensorSectionsPresheaf`, `tensorSectionsComp`, and the normalized restrictions.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the upstream
  `tensorPullback` functor retained by the dependency's section-normalized interface.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`:
  `exists_tensorPullbackAdjunction`, including its unit-on-sections normalization.
- `WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsMapNaturality`:
  `etaleTensorSectionsMap_naturality`, supplying naturality of P_h in the proof plan.
- `Mathlib.CategoryTheory.Sites.Spaces`: `Opens.grothendieckTopology`.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  the module-presheaf category and `sheafification` interface required by the dependency.
- `WeilConjectures.AlgebraicGeometry.GabberH0ZariskiConstructions`:
  `gabberOpenEtale`, `gabberOpenEtale_continuous`, `gabberTopEtaleIso`.
- `WeilConjectures.AlgebraicGeometry.EtaleTensorOpenSectionsNaturality`:
  `tensorOpenSectionIso`. The owning node and the Gabber construction node are
  added to stmt_deps as already-landed dependencies; no accepted dependency is removed.
- `WeilConjectures.AlgebraicGeometry.Sites.Gm`: `etaleStructurePresheaf`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` and its
  presheaf counterpart: canonical restriction and scalar transport.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small`:
  `Scheme.isContinuous_overMap` proves continuity of etale localization.

Edge cases checked against the types and the source calculation: empty T; empty
V; W empty or top; identity etale arrows; M=0; G=0; arbitrary non-quasi-coherent
M. Every open and every etale object is quantified, and no Nonempty binder or
choice of cover excludes any case. Object universe u+1 and morphism universe u
of the small site are preserved; sections remain in the existing scheme-module
universe u. There is no universe equality imposed on the site.

Searches (2026-10-23):

- msearch.py leanfinder: "A map from a Zariski module to an etale module sheaf
  extends naturally to the presheaf of pullback sections by scheme module adjunction".
  Eight hits, including Scheme.Modules.Hom.app, Hom.mapPresheaf, toPresheaf_map,
  mapPresheaf_app and Tilde maps; none gives the sitewise adjunction extension.
- msearch.py loogle: `"Scheme.Modules", "Adjunction"`. Five hits:
  pullbackPushforwardAdjunction, restrictAdjunction, its counit instance and its
  sectionwise unit/counit equations. These supply adjunctions, not the item.
- msearch.py grep: `etaleTensorSections|etale.*[Aa]djunction`, AlgebraicGeometry:
  zero Mathlib hits.
- Direct rg on Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json:
  no existing main declaration or new helper name. Searching the item ID in
  WeilConjectures and Sheaf gave no existing statement.
- Concept rg found the parent ZariskiEtaleTensorSections and downstream
  SchemeZariskiEtaleQuasiCoherentEquivalence modules. Their bundled context
  and structure-ring helpers lie downstream in the DAG; neither theorem states
  this specified adjunction construction. The delivery imports neither module.
- The three requested search kinds and the upstream/project searches were also
  checked for the open comparison. Mathlib restrictFunctorIsoPullback uses the
  generic pullback and is therefore the unusable recorded interface repaired below.

Source checked: literature/stacks-project/descent.tex, lemma-compare-sites,
Tag 070S, including its explicit omission of proof (2), and the project's latest
blueprint unit sk-i-curve-zero. This is the existing auxiliary node's historical
ancestry, not the unit's own statement. The five-step proof remains agent-supplied
exactly as the accepted node records. No statement fault or STATEMENT-DISPUTED flag.

Validation: both delivered files compile separately via scompile.py, in dependency
order, without warnings or errors. The main file takes about four seconds and the
dependency file about two seconds, within the unchanged 60-second limit.

## Dependency modules

`lem-weil-pbc-open-immersion-module-pullback-restriction` receives
`Sheaf.AlgebraicGeometry.TensorPullbackOpenRestriction`. Its previous
mathlib_match's `restrictFunctorIsoPullback` uses Mathlib's generic module pullback,
whereas this project's recorded pullback is `tensorPullback`. The module defines
`restrictFunctorIsoTensorPullback` by left-adjoint uniqueness using the recorded
normalized tensor adjunction and the actual restriction adjunction. It states
`restrictFunctorIsoTensorPullback_unit`, the exact unit compatibility, with sorry.
Naturalness is built into its natural-isomorphism type; the section equation follows
by evaluation and the existing `restrictAdjunction_unit_app_app`. All schemes and
all open immersions are covered. The dependency node changes only in lean, with
an explanatory lean.note; its statement and mathlib_match are retained verbatim.
The theorem's docstring gives the full proof and source. Its owning DAG node is
this dependency, so the additional postponed proof is tracked.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
