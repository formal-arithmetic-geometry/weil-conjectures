## Worker report

Attached the exact existing definition
`AlgebraicGeometry.ProEtale.CondensedRing.derivedLowerShriekHom` in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`
(lines 306–326, declaration lines 316–326). No module, definition, theorem or proof
is added. Only the item's `lean` field changes. The source read is the full blueprint
`main-20261015/blueprint/sec-six-functors-basics/sk-def-sfb-coefficient-comparisons/def-sfb-derived-lower-shriek-hom.md`.
No repair note exists for this item.

Hypotheses and clauses, checked against the upstream declaration including the
section binders:

- Commutative condensed rings Λ and Λ′ are
  `{Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}`, with
  `[MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']`.
- The ring morphism is `(a : Λ ⟶ Λ') [IsMonHom a]`. Its pullback to a scheme is
  `AlgebraicGeometry.ProEtale.coefficientMap a X`, defined as
  `(upperStarFromPoint X).map a` (lines 85–97). The derived scalar extension T^X
  is `L(Mod.extendScalars (coefficientMap a X))`, not an arbitrary functor.
- The finite-limit assumption for every scheme is exactly
  `[∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]`
  in the LowerShriek section. There is no flatness or invertibility assumption
  beyond the finite-limit condition stated in the node.
- Schemes and morphism are `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
  `[HasCompactification f]` supplies the chosen
  `HasCompactification.compactification f`; `Compactification` has fields `Z`,
  `i`, `g`, `comm : f = i ≫ g`, `isOpenImmersion` and `isProper`.
  The choice is precisely the one used by the recorded lower-shriek dependency.
- `R(f)_!⟦Λ⟧` unfolds to `D((c.i)_!open⟦Λ⟧) ⋙ R((c.g)_*⟦Λ⟧)` for that same
  chosen c, by `rightDerivedLowerShriek` and
  `rightDerivedLowerShriekOfCompactification`. The primed side uses the same c.
- The source of the natural transformation is
  `R(f)_!⟦Λ⟧ ⋙ L(Mod.extendScalars (coefficientMap a Y))`; its target is
  `L(Mod.extendScalars (coefficientMap a X)) ⋙ R(f)_!⟦Λ'⟧`.
  Lean's `⋙` writes functors in application order, so these are exactly
  T^Y ∘ Rf_! and Rf_! ∘ T^X, from the unbounded derived category of Λ_X-module
  objects to that of Λ′_Y-module objects.
- The definition's first associator exposes the proper pushforward factor;
  `Functor.whiskerLeft D((c.i)_!open⟦Λ⟧) (derivedPushHom a c.g)` applies (Push)_g.
  The inverse associator exposes the open factor, then
  `Functor.whiskerRight (derivedOpenImmersionShriekIso a c.i).hom
  R((c.g)_*⟦Λ'⟧)` applies the specified extension-by-zero isomorphism.
  The final associator restores the target parenthesization. These are exactly
  the two arrows of the displayed composite; no isomorphism of (Push) is assumed.

Dependency declarations read and used:

- `sk-def-sfb-coefficient-change`: `AlgebraicGeometry.ProEtale.coefficientMap`,
  `coefficientMap_id`, `coefficientMap_comp`,
  `map_coefficientMap_comp_condensedPullbackHom`, and
  `condensedPushforwardHom_comp_map_coefficientMap` in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`.
  The associated `L(Mod.extendScalars ...)` construction and
  `CategoryTheory.Mod.derivedExtendMapDerivedCategoryAdjunction` were read in
  `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`.
- `sk-def-sfb-module-derived-lower-shriek`:
  `AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification`,
  its `Plus` and `PlusCompatibility` variants, `rightDerivedLowerShriek`,
  `rightDerivedLowerShriekPlus`, and `rightDerivedLowerShriekPlusCompatibility` in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek`.
  The present item uses the unbounded chosen version. Full signatures and
  docstrings of the six recorded declarations were read.
- `def-sfb-derived-push-hom`:
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedPushHom`, same
  `ChangeOfCoefficients` module, lines 245–254. Its mate construction is exactly
  the recorded dependency's construction.
- `def-sfb-derived-open-immersion-shriek-iso`:
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedOpenImmersionShriekIso`, same
  module, lines 291–302. It is the conjugate along the stated derived adjunctions,
  with no finite-limit hypothesis in its OpenImmersion section.

Edge cases checked by reading the definition and its binders: the identity
coefficient change is admitted; zero coefficient rings and zero derived objects
are not excluded; empty schemes are not excluded; no boundedness is imposed;
no assumption that (Push) is invertible is made. The universe u is unrestricted,
and coefficient sheaves use Ab.{u+1} on the actual pro-etale site. Arbitrary
compactifiable f is allowed, with properness required only of c.g and openness
only of c.i. No extra quasi-compactness, Noetherian or separatedness binder is
introduced. The construction makes no independence-of-compactification claim.

Searches actually run through msearch.py (Q132, this item):

- LeanFinder: "Derived scalar extension comparison with pushforward with proper
  support via compactification and extension by zero". Eight hits, including
  `SheafOfModules.pushforwardPushforwardAdj`, ordinary module pushforwards and
  `Scheme.Modules.pushforwardComp`; none is this derived compactification map.
- Loogle: `"derivedLowerShriekHom"`. Zero hits in Mathlib.
- Mathlib grep: `derivedLowerShriek|lowerShriek|exceptionalPushforward`. Zero hits.
- LeanSearch: "Derived change of coefficients comparison with exceptional direct
  image using a compactification". Eight hits on cotangent/Kaehler base change
  and unrelated constructions; no exact match.
- `rg -n 'derivedLowerShriekHom|def-sfb-derived-lower-shriek-hom'` in
  `dag/lean_names_upstream.json`, `lean/WeilConjectures` and `lean/Sheaf` found the
  exact live upstream definition at ChangeOfCoefficients.lean:316 and its
  downstream isomorphism/colimit uses. Sheaf's archived UpstreamExtra file has
  only documentation mentioning the name, not a second declaration. The
  compact-support projection module mentions it as a source, not a definition.
- `grep -rn 'def-sfb-derived-lower-shriek-hom' lean/WeilConjectures` returned no
  node-tag occurrence. The existing match was found by declaration-name search
  and checked against the complete source, not inferred from the node tag.

No new nodes, dependency repairs, statement correction or disputed statement.
The definition has a real composite body; its inherited proof obligations remain
open in the DAG. An existing attachment adds no Lean file, so there is no new
file to compile (brief-stage2 §1 and §6).

## Second reading by Q132

Reopened the item, the four dependency statements, and the exact upstream
LowerShriek section after drafting this report. Matched both commutative
coefficient rings, IsMonHom, the scheme-wide finite-limit assumption, f and its
chosen compactification, both unbounded derived endpoints, and the Push/open
pasting term separately. The direction agrees after reversing the printed
mathematical composition order into Lean's `⋙`; the open isomorphism uses `.hom`
in the required direction. The proper factor and open factor are taken from
exactly the compactification used by both lower-shriek functors. No mismatch
or correction was found. This is the dispatch worker's second reading; the
maintainer performs the independent review as specified in the brief.
