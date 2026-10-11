## Worker report

Module `Sheaf.Topology.Sheaves.LerayAcyclicComparison` states
`TopCat.Sheaf.exists_lerayEdge_isIso_of_acyclic`, with its proof `sorry`.
No definition, new node, dependency replacement, or statement correction is needed.

Hypothesis and clause correspondence:

- Topological spaces Z and X: `{Z X : TopCat.{u}}`. An arbitrary continuous map
  f:Z→X: `(f : Z ⟶ X)`. There is no closed-immersion assumption despite the item id.
- Abelian sheaf F: `F : CategoryTheory.Sheaf (Opens.grothendieckTopology Z)
  AddCommGrpCat.{u}`; F is quantified in the comparison characterization and vanishing clause.
- Direct image with `(f_*F)(U)=F(f⁻¹U)`: the existing `TopCat.Sheaf.pushforwardAb f`.
  Its definition is `(Opens.map f).sheafPushforwardContinuous AddCommGrpCat _ _`.
  `Opens.map f` sends U to f⁻¹U; its sheaf pushforward precomposes with that functor.
- Higher direct images: `Functor.rightDerived (pushforwardAb f) q`, with its existing
  additivity supplied explicitly by `Functor.additive_of_comp_faithful` after identifying
  the underlying-presheaf composite with restriction by `(Opens.map f).op` using `Iso.refl`.
  This is a proof term of a Mathlib theorem, not a new hypothesis or new derived-functor notion.
- Vanishing for every q>0: `∀ q : ℕ, 0 < q → IsZero (... .obj F)`.
- Every p≥0: `∀ p : ℕ`.
- H^p(X,f_*F) and H^p(Z,F): the values of `Sheaf.cohomologyPresheafFunctor` evaluated
  at `op ⊤`, definitionally exactly the recorded `Sheaf.H' ... p ⊤` of the dependency.
  No alternative cohomology theory is defined.
- Natural map: `ε p` is a natural transformation between these functors on all sheaves F,
  so it commutes with every morphism of coefficient sheaves, including between acyclic ones.
- This is the Leray edge, not an arbitrary natural map: the first existential `a` names
  the canonical free-abelian-representable map. Its equation specifies the value on every
  generator, after sheafification, on each open U: the generator g becomes the generator
  `(Opens.map f).map g ≫ eqToHom (Opens.map_top f)` on f⁻¹U. The second equation specifies
  ε on every cocycle in every injective resolution J of f_*F and I of F, using every
  augmentation-compatible comparison `φ : J → f_*I`. The equation `_hst` says s and t
  represent the same global cocycle under φ and the canonical a. `InjectiveResolution.extMk`
  assigns these cocycles their Ext classes, and the equality requires the edge to send
  the class of s to the class of t. Free representables at ⊤ represent global sections;
  such t exists uniquely, φ exists because f_* preserves injectives, and extMk is surjective.
  Thus this clause determines the canonical edge and is independent of any choices.
  The auxiliary resolution/cocycle variables are universally quantified inside its
  characterization, not additional hypotheses on F or f.
- Isomorphism: `IsIso ((ε p).app F)` under exactly the stated vanishing. The edge goes
  H^p(X,f_*F)→H^p(Z,F), as in the node's proof. Its inverse gives the displayed comparison
  H^p(Z,F)≅H^p(X,f_*F) in the node statement.

Dependencies read and used:

- `def-sc-topological-abelian-cohomology`: `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`,
  `CategoryTheory.Sheaf.H'`; read the full definition, its `cohomologyPresheafFunctor` and
  Ext/free-abelian-representable encoding. The latter is used directly at ⊤.
- `def-sp-left-exact-additive` (Mathlib leaf):
  `Mathlib.CategoryTheory.Abelian.RightDerived`, `CategoryTheory.Functor.rightDerived`;
  read its signature and the injective-resolution computation `isoRightDerivedObj`.
  The explicit additivity witness uses `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`,
  `Functor.additive_of_comp_faithful` and `Functor.additive_of_iso`.
- `def-sp-injective-resolutions` (Mathlib leaf):
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`, `CategoryTheory.Injective`, and
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`, `CategoryTheory.InjectiveResolution`;
  read their full signatures and docstrings. Resolution and augmentation fields are used.
- Existing direct image: `WeilConjectures.Topology.Sheaves.PushforwardCohomology`,
  `TopCat.Sheaf.pushforwardAb`. Read this module in full, including
  `injective_pushforwardAb_obj` and `nonempty_functorH_iso_pushforwardAb`.
- Existing cocycle constructor: `Mathlib.CategoryTheory.Abelian.Injective.Ext`,
  `CategoryTheory.InjectiveResolution.extMk`, whose complete signature, definition and
  surrounding `extMk_surjective` and naturality lemmas were read. This computes the same
  Ext used by H', with no new notion.

Sources: opened Stacks Tag 01F4 at https://stacks.math.columbia.edu/tag/01F4;
part (1) is precisely the vanishing comparison. The ringed-space statement specializes
via the constant integer sheaf to arbitrary abelian sheaves. The node's two proof steps
are included in the declaration docstring, together with the resolution description of
its canonical edge. The local literature/stacks-project/cohomology.tex file is absent.

Edge cases checked mathematically before writing: p=0 gives the identity of global
sections F(Z)=f_*F(X); q=0 is correctly excluded from the vanishing assumption; the zero
sheaf has zero cohomology in every degree; the empty source has the zero abelian-sheaf
category and zero cohomology, so is included; the identity map has vanishing positive
right derived functors and the canonical identity edge. No nonemptiness, separation,
Noetherianity, quasi-coherence or finite-dimensionality is assumed. Universe u is explicit
and arbitrary; spaces and coefficient groups can be placed together in any common universe.

Searches for an existing statement (all on 2026-10-11 UTC):

- msearch.py leanfinder, query "Leray edge map isomorphism for abelian sheaf cohomology
  when higher direct images vanish": eight hits, chiefly group cohomology and
  `InjectiveResolution.isoRightDerivedObj`; none states this theorem.
- msearch.py loogle, query "Sheaf.H, Functor.rightDerived": zero hits, unknown identifier
  Sheaf.H (recorded as returned).
- msearch.py leansearch, query "Leray cohomology comparison higher direct image vanishing":
  service unavailable (Internal Server Error), not a negative mathematical result.
- msearch.py grep, query "Leray|leray|pushforward.*cohomology", Mathlib Topology/Sheaves:
  zero hits.
- rg in WeilConjectures and lean/Sheaf for
  `Leray|leray|pushforward.*[Cc]ohom|cohom.*[Pp]ushforward`: found the source
  PushforwardCohomology comparison on a dimension-shifting-stable class with pushforward
  exact on its short exact sequences, and scheme/module/étale comparisons. None has the
  present arbitrary-continuous-map and objectwise-derived-vanishing hypothesis.
- rg for the item id in WeilConjectures: no hits. rg for the new full declaration name
  in Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: no collision.
- Further Mathlib/project searches for canonical cohomology maps and free representables
  found `Adjunction.mapExtCounit`, `Sheaf.H.mapFunctor`, the existing H' primitives and
  `InjectiveResolution.extMk`. The cocycle characterization uses the last directly,
  avoiding a duplicate definition or an unnormalized arbitrary comparison isomorphism.

Validation: lcompile.py compiles the statement in 4.6 seconds with no errors or warnings.

## Second reading by U1

I reread the node statement, its Stacks source (01F4, part (1), together with 01F2),
the dependency records, and the complete Lean declaration.

- Objects: `Z X : TopCat.{u}` and `f : Z ⟶ X` render the continuous map of spaces.
- Coefficients: `F : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}`
  is universally quantified in the edge characterization and vanishing clause.
- Direct image: `pushforwardAb f` is the existing sheaf direct image, whose sections
  are by inverse image opens; no extra closedness, separation, or finiteness hypothesis
  is introduced.
- Higher direct images: the displayed `Functor.rightDerived (pushforwardAb f) q`
  uses the explicit existing additive witness and is the recorded derived-functor notion.
- Vanishing: `∀ q : ℕ, 0 < q → IsZero (...)` is exactly positive-degree vanishing.
- Cohomology: evaluation at `op ⊤` of `Sheaf.cohomologyPresheafFunctor` gives the
  recorded `H^p` objects on `Z` and `X`.
- Canonical edge: the existential `a` has the free-generator inverse-image formula;
  the second conjunct existentially supplies `ε`, with the augmentation-compatible
  resolution comparison and cocycle/ext-class equation making it the Leray edge.
- Conclusion: under the displayed vanishing, `∀ p, IsIso ((ε p).app F)` gives the
  natural edge isomorphism `H^p(X,f_*F) ≅ H^p(Z,F)`; its inverse is the node's
  displayed direction `H^p(Z,F) ≅ H^p(X,f_*F)`. Quantifier order agrees.

The source is phrased for ringed spaces and modules; the node's abelian-sheaf statement
is its standard specialization using the constant integer sheaf, and is valid for every
continuous map. The Lean statement correctly makes that specialization explicit.
No mismatch was found, so no statement or dependency record was changed.

Edge cases checked: `p = 0` is the global-sections edge; `q = 0` is excluded from
vanishing; the zero sheaf and empty source are included; the identity map has the
identity edge; arbitrary universe `u` is retained. No characteristic or Noetherian,
proper, separated, or nonemptiness assumption is added.

Searches were repeated with `msearch.py` LeanFinder/Loogle/LeanSearch queries for Leray
and higher-direct-image comparison, `rg` in Mathlib, `WeilConjectures`, and `lean/Sheaf`,
and collision searches for the declaration name. No existing declaration states this
result. The module compiles cleanly with `lcompile.py`.
