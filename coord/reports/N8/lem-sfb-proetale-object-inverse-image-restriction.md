## Worker report

Stage 2, N8, 2026-10-17. The module
`Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction` states the complete
three-clause node as `AlgebraicGeometry.Scheme.proEtaleObjectInverseImageRestriction`.
Its only theorem has proof `by sorry`. The three supporting declarations have real
data: the distinguished structured arrow is the existing composition/base-change
adjunction unit; the comparison structure packages exactly the specified comparison
assertions; module restriction specializes Mathlib's existing sectionwise pushforward.
These are helpers of this node, recorded in `lean.declarations`, not independent notions.
There are no new nodes, dependency repairs, statement corrections or disputed statements.
The preserved sandbox initially contained only search bookkeeping. Q154's accepted
stage-1 review is preserved verbatim; this delivery does not resplit or revise it.

Hypotheses and setup, clause by clause:

- `X : Scheme.{u}` supplies the scheme; `W : X.ProEt` supplies the morphism
  `r = W.hom`, its domain `W.left`, and the required weakly-etale property `W.prop`.
  No open-immersion, monomorphism, quasi-compactness or finite-coefficient assumption
  is introduced. `A : Type u` and `[CommRing A]` supply the commutative ring.
  This follows the published size convention of the statement dependency: schemes
  and coefficients are taken in a common universe, coefficient values use `ULift A`
  in `u+1`, and the original site retains objects in `u+1` and morphisms in `u`.
- Composition is exactly `MorphismProperty.Over.map (f := W.hom) ⊤ W.prop`.
  The existing `ProEtale.localizationRestriction D W.hom W.prop` is its continuous
  sheaf pushforward, hence on objects, restriction maps and morphisms it is precisely
  `G(U → W → X)`. The localization dependency identifies this concrete composition
  with the stated slice restriction; no replacement site or chosen comparison is used.
- All occurrences of inverse image use `proEtaleSheafInverseImage`, its actual Kan
  extension `(proEtaleBaseChange W.hom).op.lan`, and Mathlib's `toSheafify`. The
  structure map is the recorded `proEtaleCoefficientInverseImageMap`, not a fresh map.
  Module pullback and its maps are `proEtaleConstantModulePullback` and
  `proEtaleConstantModulePullbackMap`, the actual inverse-image-and-tensor constructions.

Clause (1):

- `proEtaleObjectInverseImageIndexPoint W U` has type
  `proEtaleInverseImageIndex W.hom U`. It is `StructuredArrow.mk` of the unit of
  `MorphismProperty.Over.mapPullbackAdj`. I read its implementation in Mathlib
  `CategoryTheory/MorphismProperty/OverAdjunction.lean:195–203`: the unit's underlying
  arrow is `pullback.lift (𝟙 _) U.hom`, so it is exactly the specified pair. The
  existing choice orders the fibre-product factors as `U ×_X W`, and thus writes
  `(id,str)` for the node's `(str,id)` in `W ×_X U`.
- `∀ U, Nonempty (IsInitial (...))` asserts initiality of this particular pair,
  not merely existence of some initial object. `IsInitial` is data in Lean, which
  explains the logically equivalent `Nonempty` wrapper.
- `ProEtaleObjectRestrictionComparison` packages the rest of this clause. Its
  `presheafIso` is a natural isomorphism from restriction's underlying presheaf
  functor to the actual Kan inverse-image functor. `coprojection` identifies every
  component with the distinguished coprojection. The expression is the Kan unit
  at the composite object followed by the Kan extension's map on the distinguished
  arrow. Mathlib's `Functor.ι_leftKanExtensionObjIsoColimit_inv` identifies exactly
  this expression with `colimit.ι` followed by the canonical colimit comparison;
  hence no arbitrary natural isomorphism is substituted for the required one.
- `sheafification_isIso` asserts that the actual `toSheafify` for every input sheaf
  is an isomorphism. `sheafIso` is the natural sheaf comparison `r⁻¹ ≅ restriction`;
  `sheafIso_inv` fixes its inverse as the canonical coprojection comparison followed
  by that actual sheafification unit. Presheaf/sheaf morphisms encode naturality
  in U, and the natural isomorphisms encode naturality in G.
- The theorem includes these assertions for `Type (u+1)`, `AddCommGrpCat.{u+1}`,
  and `RingCat.{u+1}`. Thus sets, abelian groups, and arbitrary ring sheaves are all
  covered. The commutative-ring instance retains the same ring comparison with
  commutativity for use by the coefficient and module clauses.

Clause (2):

- The existential `e : proEtaleConstantRing W.left A ≅ restriction(A_X)` is the
  localization comparison `A_W ≅ A_X|_W`. Its first conjunct is the equality of
  its composites with the actual constant-presheaf sheafification units at every U.
  This is the same constant-section normalization as clause (2) of
  `ProEt.weaklyEtale_localization`. The constant-sheaf universal property makes it
  unique, so it identifies that particular comparison, not an arbitrary ring iso.
- `proEtaleCoefficientInverseImageMap W.hom A ≫ e.hom =
  comparison.sheafIso.hom.app (proEtaleConstantRing X A)` identifies the specified
  structure map under the specified inverse-image/restriction comparison with
  `e.inv`. Since both e and the comparison are isomorphisms, the structure map is
  itself an isomorphism, precisely as required.

Clause (3):

- `proEtaleObjectModuleRestriction W A e` is `SheafOfModules.pushforward` along
  the composition functor with coefficient map obtained by forgetting commutativity
  from `e.hom`. It has exactly the restricted groups, restriction maps and module
  morphisms, and the A_W-action is through `e : A_W ≅ A_X|_W`, as required.
  The continuity instance is the existing named `ProEt.isContinuous_overMap`.
- `rho : ∀ M, proEtaleConstantModulePullback W.hom A M ≅ ...obj M` is an isomorphism
  in the category of A_W-module sheaves, so includes linearity and compatibility
  with restrictions. Its final equality for every `a : M ⟶ N` is naturality in M
  using the actual published map on tensor pullbacks. No pullback functor laws or
  arbitrary-coefficient adjunction are assumed.
- Applying the forgetful functor to rho supplies the asserted isomorphism of
  underlying abelian sheaves; there is no additional condition on M.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`, whose full definition exposes
  the ordinary small site, constant commutative ring sheaf, and intrinsic module
  category. The module is publicly imported through the recorded dependencies.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`:
  `AlgebraicGeometry.Scheme.ProEt.weaklyEtale_localization`; read the complete
  signature and docstring, also using `scompile.py --source` to check current source.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`: the currently recorded
  inverse-image dependency module; read its declarations and its reexported
  `ProEtaleInverseImage` module in full. The finite-only helper named as the record's
  primary declaration is not used for arbitrary A: the record explicitly retains
  the original arbitrary-ring inverse-image constructions, which this module uses.
  These are `proEtaleBaseChange`, `proEtaleInverseImageIndex`,
  `proEtaleSheafInverseImage`, `proEtaleConstantRing`,
  `proEtaleCoefficientInverseImageMap`, `proEtaleConstantModulePullback` and its map.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`;
  `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction`; read full signatures and docstrings.
- The proof-dependency imports include the recorded tensor module
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`, module
  sheafification, fibre products and the continuous functor/sheaf pullback
  adjunction. Mathlib's existing `SheafOfModules.pushforward` and the reexported
  `AlgebraicGeometry.ProEtale.localizationRestriction` give the restriction formulas.

Edge cases checked mathematically before writing: identity W = X; empty W or U;
non-monomorphic W = X ⊔ X over X; zero coefficient ring and zero module; infinite
commutative coefficients; and noncommutative ring-valued sheaves in clause (1).
The projected indexing arrow is unique in all cases even though W → X need not
be mono. Tensor collapse uses only the coefficient ring iso, not finiteness or
nonzero coefficients. The empty-site assertions remain valid with terminal values.
No excluded finite or open-only case was added.

Searches (all run for this item with msearch.py, plus direct source searches):

- LeanFinder: "Inverse image of pro-etale sheaves along a site object is restriction
  to the localized site, with the constant ring structure map and module pullback".
  Eight hits, including `Scheme.Modules.restrictFunctor` and ringed-space restriction;
  none states the three clauses for pro-etale site objects.
- Loogle: `"overPullback"`. Twelve hits including
  `GrothendieckTopology.overPullback`, `Sheaf.toPushforwardOverPullback`, and
  `SheafOfModules.overPullback`. These are generic slice operations, not the whole
  specified inverse-image comparison.
- LeanSearch: "Inverse image of a sheaf along a site object is restriction to its
  slice; the canonical sheafification unit and constant coefficient structure map
  are isomorphisms". Eight hits on `sheafificationIso`, `isoSheafify`, `toSheafify`,
  and related units. These are used generic constructions, not a match for this node.
- Mathlib grep via msearch: `overPullback|sheafPullbackConstruction`, under
  `CategoryTheory/Sites`. Twelve hits in Over.lean, Pullback.lean, etc.; signatures
  and pertinent docstrings were opened. No whole-node match.
- Direct rg of upstream `WeilConjectures` and side `lean/Sheaf`: the item id,
  `inverse.*[Rr]estrict|[Rr]estrict.*[Ii]nverse|object.*[Ii]nverse`, the proposed names,
  and `upperStarIsoLocalizationRestriction`. The upstream localization comparison
  covers the ordinary sheaf isomorphism only; the open-unit module additionally
  assumes an open immersion and finite coefficients. Neither covers the full node.
  Existing localization restriction is reused. Searches for pro-etale restriction
  and index helper definitions found no exact specialized helper already present.

Validation: the required scompile.py wrapper successfully compiled both sandbox and
library-name forms of the only delivered file (8.3 and 7.3 seconds); no errors or
warnings. Initial failures were repaired by binding the source scheme explicitly
and supplying the existing continuity instance inside the restriction abbreviation;
no mathematical hypothesis was changed. No global build, live-source edit, direct
Git command, or unapproved compilation was run.

## Second reading by N8

This is the author's second pass; independent review is left to the maintainer as
specified by the dispatcher brief. I reopened the full node, the delivered module,
and the source formulas. The initial object uses the adjunction unit, which the
Mathlib implementation constructs by `(id,str)` in the chosen factor order. The
coprojection field fixes the presheaf isomorphism, and `sheafIso_inv` fixes the
sheaf isomorphism rather than silently choosing a different comparison. The
coefficient equation has the correct orientation: c followed by e is the comparison
from inverse image to restriction, so under that comparison c equals e inverse.
Module restriction uses e itself as the scalar map A_W → A_X|_W; the final equality
is naturality in the correct direction. The full module-sheaf iso implies the
underlying-abelian-sheaf clause. No nonemptiness, finiteness, mono, open, boundedness
or additional universe equality is imposed. All three original clauses are covered.
No mathematical mismatch or statement fault was found, and no node field other
than `lean` was changed. The only fixes during this pass concern elaboration, as
recorded above; the main theorem remains the sole sorry.
