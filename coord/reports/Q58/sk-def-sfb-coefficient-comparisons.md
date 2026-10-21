## Worker report

Existing aggregate match; no Lean module is added. The primary declaration is
`AlgebraicGeometry.ProEtale.CondensedRing.derivedPullIso` in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`.
The record's fifteen declarations, all in that module, cover the entire unit.
The primary signature is copied verbatim from the keyword through the type,
excluding `:=`. Only the item's `lean` field changes.

I read the node, all six statement-dependency statements and their Lean records,
the current main-20261015 blueprint unit and proof, the recorded dependency
interfaces and docstrings, and the full comparison module. The live module was
also read using `scompile.py --source
WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`; its
comparison signatures and bodies agree with the local source.
There is no repair note for this item.

The following correspondence uses names in
`AlgebraicGeometry.ProEtale.CondensedRing` unless a full namespace is given.
Functor composition `F ⋙ G` means mathematical composition `G ∘ F`.

| Hypothesis or clause in the node | Exact existing Lean rendering |
| --- | --- |
| Arbitrary commutative condensed rings Λ, Λ' | `{Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}`, with `[MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']`. The universe `u` is arbitrary. |
| A ring morphism a | `(a : Λ ⟶ Λ') [IsMonHom a]`; no invertibility or flatness is assumed globally. |
| Its changes a_X and total derived extension T^X | `AlgebraicGeometry.ProEtale.coefficientMap a X` is `(upperStarFromPoint X).map a`; `L(Mod.extendScalars (coefficientMap a X))` is exactly T^X. |
| A morphism f : X → Y of schemes | `{X Y : Scheme.{u}} (f : X ⟶ Y)`; no properness, separatedness or quasi-compactness condition enters (Pull)/(Push). |
| Underived module pullback and pushforward | `(f)^*⟦Λ⟧ = upperStar Λ f` and `(f)_*⟦Λ⟧ = lowerStar Λ f`, the dependency's existing scalar-extension / scalar-restriction composites. |
| Total derived module functors | `L((f)^*⟦Λ⟧)` and `R((f)_*⟦Λ⟧)`; these are the generic total derived functors of the full composites, on `DerivedCategory`, not only the bounded-below category. |
| Restriction commutes with pushforward | `comapLowerStarIso a f : (f)_*⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a Y) ≅ Mod.comap (coefficientMap a X) ⋙ (f)_*⟦Λ⟧`. Its body is `Mod.comapMapModComapIso` applied to the coefficient pushforward square. |
| Restriction commutes with pullback | `comapUpperStarIso a f : (f)^*⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a X) ≅ Mod.comap (coefficientMap a Y) ⋙ (f)^*⟦Λ⟧`; its body uses the invertible vertical coefficient morphisms. `derivedComapUpperStarIso` is its levelwise derived comparison. |
| Underived extension-by-zero isomorphism for every open j : U → X | With `{U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]`, `openImmersionShriekIso a j : (j)_!open⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a X) ≅ Mod.extendScalars (coefficientMap a U) ⋙ (j)_!open⟦Λ'⟧`. No flatness binder is in this section. |
| Unbounded derived extension-by-zero isomorphism without flatness | `derivedOpenImmersionShriekIso a j : D((j)_!open⟦Λ⟧) ⋙ L(Mod.extendScalars (coefficientMap a X)) ≅ L(Mod.extendScalars (coefficientMap a U)) ⋙ D((j)_!open⟦Λ'⟧)`. Its body conjugates `derivedComapUpperStarIso a j` through the open and coefficient derived adjunctions. |
| Flatness at every scheme | Only the Derived and LowerShriek sections introduce `[∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]`. Extension already preserves finite colimits as a left adjoint, so this is precisely exactness. `preservesHomology_extendScalars_coefficientMap` names the resulting homology preservation; `preservesKInjectiveComplexes_comap_coefficientMap` supplies K-injective preservation. |
| (Pull) under flatness | `derivedPullIso a f : L((f)^*⟦Λ⟧) ⋙ L(Mod.extendScalars (coefficientMap a X)) ≅ L(Mod.extendScalars (coefficientMap a Y)) ⋙ L((f)^*⟦Λ'⟧)`. This is `Adjunction.pullIsoOfComapIso` on `derivedComapLowerStarIso a f` and the four specified derived adjunctions. |
| (Push) under flatness, a transformation | `derivedPushHom a f : R((f)_*⟦Λ⟧) ⋙ L(Mod.extendScalars (coefficientMap a Y)) ⟶ L(Mod.extendScalars (coefficientMap a X)) ⋙ R((f)_*⟦Λ'⟧)`. Its body is `Adjunction.pushHomOfComapIso` applied to the same right-adjoint square; it asserts no `IsIso`. |
| (Shriek) for a chosen compactification f = g ∘ i | `[HasCompactification f]` and `HasCompactification.compactification f`, shared for both rings. `derivedLowerShriekHom a f : R(f)_!⟦Λ⟧ ⋙ L(Mod.extendScalars (coefficientMap a Y)) ⟶ L(Mod.extendScalars (coefficientMap a X)) ⋙ R(f)_!⟦Λ'⟧`. Its body first whiskers `derivedPushHom a c.g` by `D((c.i)_!open⟦Λ⟧)`, then whiskers `(derivedOpenImmersionShriekIso a c.i).hom` by `R((c.g)_*⟦Λ'⟧)`, inserting associators. |
| Shriek invertible when Push for g is | `isIso_derivedLowerShriekHom a f` requires exactly `[IsIso (derivedPushHom a (HasCompactification.compactification f).g)]` and concludes `IsIso (derivedLowerShriekHom a f)`. It does not require invertibility for every morphism. |
| Underived Pull and Push without flatness | `pullIso a f` and `pushHom a f` have the analogous types with `Mod.extendScalars` and underived `upperStar`/`lowerStar`. Both lie before the flatness section. The former is the adjunction conjugate, the latter the prescribed mate of `comapLowerStarIso a f`. |

The recorded restriction/open-extension comparison
`comapOpenImmersionLowerShriekIso` is the linear projection-formula comparison
and the coefficient square pasted with associators. The generic mate body was
read in `CategoryTheory.ModuleObjects.ChangeOfScalarsSquare`: it uses
`(mateEquiv adj₁ adj₂).symm` on the inverse restriction square. Thus these are
the prescribed canonical transformations, with the unit/square/counit direction
of the node's proof, rather than arbitrary maps of the same types.

Dependency declarations used, with modules:

- `sk-def-sfb-coefficient-change`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`,
  `AlgebraicGeometry.ProEtale.coefficientMap`, its identity/composition laws and
  `map_coefficientMap_comp_condensedPullbackHom`,
  `condensedPushforwardHom_comp_map_coefficientMap`.
- `sk-def-sfb-module-pushforward-pullback`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`,
  `lowerStar`, `upperStar`, `upperStarLowerStarAdjunction`.
- `sk-def-sfb-module-derived-pushpull`:
  `Sheaf.Paper.CondensedModuleDerivedPushpull`,
  `moduleObjectDerivedPushforward`, `moduleObjectDerivedPullback`; their bodies
  are exactly `(lowerStar Λ f).rightDerivedFunctor` and
  `(upperStar Λ f).leftDerivedFunctor`, so the comparison module's `R` and `L`
  notation uses the very same objects. The public upstream
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`
  provides `derivedUpperStarLowerStarAdjunction`.
- `sk-def-sfb-module-lower-shriek`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`,
  `openImmersionLowerShriek`, its exactness and
  `openImmersionLowerShriekUpperStarAdjunction`, `lowerShriek`.
- `sk-def-sfb-module-derived-lower-shriek`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek`,
  `rightDerivedLowerShriekOfCompactification` and `rightDerivedLowerShriek`.
  The former is literally `D((c.i)_!open⟦Λ⟧) ⋙ R((c.g)_*⟦Λ⟧)`; the latter
  substitutes the chosen compactification.
- `sk-def-sfb-change-of-scalars`:
  `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`,
  `CategoryTheory.Mod.extendScalars` and `extendRestrictAdjunction`;
  `CategoryTheory.Mod.comap` is Mathlib's module-object restriction in
  `Mathlib.CategoryTheory.Monoidal.Mod`. The derived coefficient adjunction is
  `CategoryTheory.Mod.derivedExtendMapDerivedCategoryAdjunction` in
  `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`.

Edge cases checked by reading all section binders and construction bodies:
identity coefficient morphisms and identity scheme maps are included; zero
objects and the empty scheme are not excluded; the empty open immersion and
non-quasi-compact open immersions are included; no flatness is used for either
open-immersion comparison or underived Pull/Push; unbounded objects are allowed
throughout the derived comparisons; general Push has no invertibility
assertion. A compactification hypothesis occurs only for Shriek and the same
choice is used for both rings. There is no extra properness hypothesis on f.

Searches made:

- `msearch.py ... leanfinder` with query "Change of condensed coefficient rings
  commutes with pullback and open extension by zero, and has comparison
  transformations for derived pushforward and lower shriek": eight results,
  led by `CondensedMod.hom_naturality_apply` and
  `SheafOfModules.pushforwardCongr`; these are not the aggregate statement.
- `msearch.py ... loogle "CategoryTheory.conjugateIsoEquiv"`: five hits in
  `Mathlib.CategoryTheory.Adjunction.Mates`; this gives the general conjugate
  formalism, not the condensed comparison package.
- `msearch.py ... grep
  "comapLowerStarIso|derivedPullIso|derivedPushHom|derivedOpenImmersionShriekIso|derivedLowerShriekHom"`:
  zero Mathlib hits.
- `rg -n` for that same expression in both `lean/WeilConjectures` and
  `lean/Sheaf`: the upstream `ChangeOfCoefficients.lean` has all the exact
  definitions, while Sheaf consumers already use them. The retired overlay
  copy is not a second interface to import.
- `rg -n "sk-def-sfb-coefficient-comparisons" lean/WeilConjectures`: no hits;
  the match is by the declaration signatures and bodies, not an id annotation.
- `scompile.py --source` confirms the live upstream file and its signatures.

No statement correction, new node, dependency repair, new proof, or new `sorry`
is needed. Existing upstream open proof dependencies remain open; this record
asserts a construction/statement match and does not assert proof closure.

## Second reading by Q58

Final worker self-check, not an independent second-agent review: reread the
node's Extension by zero, Pull, Push, Shriek and final underived clauses against
the source signatures and section binders. The two easy-to-miss conditions are
preserved: derived open extension by zero has no flatness binder, and Shriek's
invertibility uses only Push at the chosen proper part. The comparison directions
agree after translating `⋙` to ordinary composition. No mismatches or source
statement faults were found. The dispatcher's brief reserves the independent
review for the maintainer and forbids starting another agent.
