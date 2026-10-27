## Worker report

Item: `lem-trf-derived-strict-open-colimit`, Q42, stage 2, 2026-10-24.
Module: `Sheaf.AlgebraicGeometry.DerivedStrictOpenColimit`.
Main declaration: `AlgebraicGeometry.StrictOpenColimit.derived_strict_open_colimit`.
The theorem has one `sorry`. The two supporting declarations only apply the existing
normalized extension functor and its specified adjunction to complexes; their data is
fully written. No new mathematical notion, dependency repair, or statement correction.

Source read: `literature/stacks-project/cohomology.tex`, lines 11343–11438,
Tag 0D6B, `lemma-glueing-increasing-union`: the intermediate termwise colimit, its stalk
display, and the final colimit on X. The whole lemma assumes continuity and negative Ext
vanishing to construct the strict system; this node already takes that strict system
as input and isolates the colimit argument. Those extra assumptions are not introduced.
The current blueprint is `literature/blueprint/latest/` (main-20261024); the ancestor's
contracting-correspondence argument in `lem-trf-local-term-locality.proof.md` is unchanged.

Hypotheses, individually:

- Scheme X: `X : Scheme.{u}`.
- Set-sized ordinal and its indices: `E : Type u`, `[LinearOrder E]`,
  `[WellFoundedLT E]`. A well-ordered type represents the elements below an ordinal.
  The index and module universes agree with the project's small-colimit convention;
  the ambient universe u can be chosen to contain both the scheme and the index set.
  There is no `Nonempty E` assumption.
- Increasing open cover: `U : E → X.Opens`, `hU : Monotone U`,
  `_hcover : iSup U = ⊤`. This is a cover of X, without continuity at limit indices.
- Each unbounded local complex: `I a : CochainComplex
  (SheafOfModules.{u} (X.ringCatSheaf.over (U a))) ℤ`.
  This is the localized opens-site presentation of O_(U a)-modules; the recorded
  `Scheme.Modules.overEquiv (U a)` identifies it with the actual open subscheme's
  module category. There is no boundedness or injectivity assumption.
- The chain maps f: the binder `f b a h` has source `I b` and target obtained by
  termwise `SheafOfModules.overMap` along `homOfLE (hU h.le)` applied to `I a`.
- Quasi-isomorphisms: `_hf : ∀ b a h, QuasiIso (f b a h)` uses Mathlib's existing
  cohomology-isomorphism predicate, with no degree restriction.
- Strict chain-map composition: `_hcomp` is equality of the component module maps
  on every open `V ≤ U c` in every `n : ℤ`. The right side is the component of
  `f c b` followed by the component of `f b a` at the same V, regarded as an open
  below U b. Module-sheaf and chain-map extensionality make this exactly the node's
  strict equality; it is not homotopy or derived equality. Writing it sectionwise
  avoids expensive implicit comparisons of iterated restrictions.
- The `HasDerivedCategory.{w}` instances for the global and local module categories
  choose their localizations at the common morphism universe w. These are the usual
  shared size binders, not mathematical restrictions on the complexes or the scheme.
  No new Abelian or derived-category structure is chosen.

Conclusions, individually:

- `extension X (U a)` applies exactly the dependency's
  `extensionByZeroPresheaf ⋙ PresheafOfModules.sheafification` termwise. Its additivity
  instance is the first assertion of `module_extensionByZero_adjunction`.
- `unit X (U a) (I a)` is the termwise unit of the adjunction selected together with
  the dependency's section formula, which fixes the normalization. This choice is
  of an adjunction determined by that formula, not a free comparison. The first
  conclusion explicitly asserts that every such unit is an isomorphism.
- The existential functor D presents the transition chain maps. The isomorphism
  `e a : D.obj a ≅ extension(I a)` is just presentation data for those fixed
  objects. Define T_ba to be `(e b).inv ≫ D.map (homOfLE h.le) ≫ (e a).hom`.
  The next conjunct fixes its degree-n component by the normalized adjunction
  equation: its adjunct equals `f_ba`, followed by restriction of eta_a, followed
  by Mathlib's canonical `overFunctorMap` identification. Thus the arrows are
  uniquely the node's degreewise adjoints, rather than arbitrary maps satisfying
  only a quasi-isomorphism property. They are chain maps by their type. `D.map_comp`
  and cancellation of e with its inverse give exactly `T_ca = T_cb ≫ T_ba`;
  identities are built into D. No composition hypothesis on T is assumed.
- `c : Cocone D` and `Nonempty (IsColimit c)` provide L = c.pt and its chain-map
  coprojections, expressed on the actual extensions as `(e a).inv ≫ c.ι.app a`.
  For every n the additional `IsColimit` after `HomologicalComplex.eval` explicitly
  states the termwise universal property. This also asserts existence, without a
  `HasColimit D` premise. Any other termwise colimit is canonically isomorphic
  compatibly with the legs, so this existential presentation has exactly the
  usual chosen-colimit meaning of the node.
- The family s has type `I a ⟶ L|_(U a)`. Its first equation fixes it as eta_a
  followed by the restriction of the displayed coprojection. It is not a free
  family of quasi-isomorphisms.
- `∀ a, QuasiIso (s a)` is the local quasi-isomorphism assertion.
- The next conjunct is strict chain-map equality `s b = f b a h ≫ (s a)|_(U b)`,
  with the canonical `overFunctorMap` isomorphism written explicitly to identify
  the iterated restriction with restriction from X.
- The last conjunct applies the actual `overEquiv` functor termwise to s, then Q,
  and composes with `schemeOpenRestriction.mapDerivedCategoryFactors.inv`.
  Its target is precisely `(schemeOpenRestriction X (U a)).mapDerivedCategory.obj
  (DerivedCategory.Q.obj c.pt)` in `schemeDerivedCategory (U a).toScheme`.
  `IsIso` asserts invertibility of this canonical localized coprojection, not
  merely the existence of some isomorphism between its endpoints.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`, its chain-map
  category and evaluation; `Mathlib.Algebra.Homology.QuasiIso`: `QuasiIso`.
- `WeilConjectures.AlgebraicGeometry.Modules.ExtensionByZeroAdjunction`:
  `Scheme.Modules.module_extensionByZero_adjunction`, including its full section
  normalization and stalk clauses; its underlying functor is reused literally.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone`, `IsColimit`, colimit legs
  and the colimit universal property.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and Q.
- `WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps`:
  `schemeOpenRestriction` and its existing additivity/exactness instances. The
  landed node `def-pc-derived-open-restriction-maps` is added to stmt_deps for this
  shared interface; no node file or declaration of that dependency is changed.
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`: `Scheme.Modules.overEquiv`;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`: `overMap`,
  `overFunctor`, `overFunctorMap`.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`:
  `Adjunction.mapHomologicalComplex`, applying the already normalized adjunction.
- The stated proof dependencies are imported by their recorded modules:
  `CategoryTheory.moduleSheaves_colimits_forgetful`,
  `SheafOfModules.filteredColimitsTensorComplex`,
  the homology-colimit preservation instances in
  `WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits`,
  `Scheme.Modules.module_stalk_filtered_colimit`,
  `RingedSpace.module_stalk_exact`, and `open_restriction_adjunction_exact`.
  The Mathlib stalk criterion is `TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso`
  in `Mathlib.Topology.Sheaves.Stalks`. Their full signatures and source docstrings
  were read. These are proof imports, not extra mathematical assumptions.

Edge cases checked before stating the theorem: E empty (the cover forces X empty;
D is empty and its termwise colimit is zero, with all indexed assertions vacuous);
one index (the sole coprojection is an isomorphism); successor and limit ordinals;
discontinuous covers; repeated or empty opens; zero complexes; arbitrary positive
and negative cochain degrees; quasi-isomorphisms f that are not componentwise
injective. None is excluded. No continuity, K-injectivity, negative-Hom vanishing,
separatedness, quasi-compactness, or Noetherianity was added.

Searches actually run:

- msearch.py leanfinder: `Strictly compatible quasi-isomorphisms of complexes on
  nested opens give a locally quasi-isomorphic colimit of extensions by zero`:
  8 hits (shape-extension quasi-isomorphism lemmas and derived fraction lemmas),
  none concerning extensions by zero on opens.
- msearch.py loogle: `"SheafOfModules", "colimit"`: 12 hits for presheaf colimits,
  evaluation and forgetful functors; none states the local strict-colimit theorem.
- msearch.py grep, `Algebra/Homology`:
  `(colimit|directLimit).*(quasiIso|quasi_iso)|extension[Bb]y[Zz]ero`: 0 hits.
- rg on `lean/WeilConjectures` and `lean/Sheaf`, by the item id and the patterns
  `strict.*[Cc]olimit`, `[Cc]olimit.*[Ss]trict`, `extensionByZero` and
  `strictOpenColimit`: no exact theorem. Existing RHom strict-colimit machinery
  concerns coefficient/localization diagrams; the extension-by-zero stalk and
  adjunction modules supply the ingredients, not this assertion.
- Read the exact `overFunctor`, `overMap`, `overFunctorMap`, and termwise-adjunction
  declarations; found the already recorded `schemeOpenRestriction` interface by
  rg and read its owning node and module. No duplicate definition node was created.

No STATEMENT-DISPUTED flag or mathematical node fault was found. The theorem's
seven-step docstring retains the complete accepted natural-language argument.
An initial compile diagnosed a missing additivity instance for the inline composite;
using the already published `schemeOpenRestriction` interface resolves it without
adding assumptions or changing universes. All compilation uses scompile.py.

## Second reading by Q42

I reread the copied DAG node and the complete module signature after the successful
server compile. The scheme, ordinal/index, monotone increasing cover, cover equation,
unbounded complexes, strict chain-map family, quasi-isomorphism premise, strict
composition equation, common derived-category instances, and every existential and
universal conclusion are all present. In particular, the empty-index case is not
excluded, the transition formula uses the existing normalized adjunction unit, the
colimit is stated both as a complex cocone and degreewise, the strict s-compatibility
includes the canonical overFunctorMap isomorphism, and the final clause is an `IsIso`
in the local derived category. I found no mismatch and made no changes in this reading.
