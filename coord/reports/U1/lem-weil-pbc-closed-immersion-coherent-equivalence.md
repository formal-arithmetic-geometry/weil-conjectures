## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ClosedImmersionCoherentEquivalence.lean`
states the three clauses of the node in three theorems, with one auxiliary theorem
for the Noetherian structure on the source of the closed immersion. All four proofs
are `sorry`; no new definition or private copy of a dependency was introduced.
The node changes only in `lean`.

Hypothesis and clause correspondence:

- The schemes are `{Z X : Scheme.{u}}`, with explicit universe `u`, and the closed
  immersion is `(i : Z ⟶ X) [IsClosedImmersion i]` in all declarations.
- Part (1)'s locally Noetherian hypotheses are `[IsLocallyNoetherian X]` and
  `[IsLocallyNoetherian Z]`. Its defining quasi-coherent ideal J is exactly `i.ker`,
  built into the existing predicate `CoherentModuleSupportedOn F i`; there is no
  independent ideal requiring an identification hypothesis.
- The coherent module category on Z is `CoherentModules Z`. The target is the full
  subcategory of `CoherentModules X` specified by `CoherentModuleSupportedOn F i`,
  which unfolds to `IsZero (Scheme.idealModuleProduct i.ker.toModulesι F.obj)`.
  Thus it is precisely J F = 0, not a condition merely on topological support.
- `closedImmersion_coherent_equivalence` existentially gives an equivalence `E`
  between these categories. Its natural isomorphism identifies `E.functor`, after
  the two full-subcategory inclusions, with the coherent inclusion followed by
  `Scheme.Modules.pushforward i`. This states that pushforward induces the
  equivalence, not merely that some equivalence between the categories exists;
  the natural comparison identifies the functor on morphisms as well as objects.
- `closedImmersion_coherent_support` states the other clause of (1): the
  nonzero-stalk locus of `(Scheme.Modules.pushforward i).obj G.obj` equals
  `i '' {z : Z | ¬ Subsingleton (G.obj.presheaf.stalk z)}` for every coherent G.
  This is the existing project's inline support convention.
- In part (2), `[IsNoetherian X]` is exactly locally Noetherian plus quasi-compact,
  and `(I : X.IdealSheafData)` supplies any quasi-coherent sheaf of ideals.
  The extended ideal I O_Z is the existing `I.comap i`. No assumption on I, its
  radical, or the characteristic is added.
- To type the source formal category without adding `[IsNoetherian Z]` as an
  assumption, `closedImmersion_source_isNoetherian i` states precisely node proof
  step 1. This named `sorry` theorem is supplied as the explicit proof argument
  of `@CoherentFormalModule Z (closedImmersion_source_isNoetherian i) (I.comap i)`.
- The first conjunct of `closedImmersion_coherentFormal_equivalence` gives an
  equivalence from that category to the full subcategory of
  `CoherentFormalModule X I` cut out by `SupportedOn I M i`. That predicate is the
  existing scheme-theoretic condition `AnnihilatedBy I i.ker M`, term by term.
- The accompanying natural isomorphism, after forgetting both full subcategories,
  identifies the equivalence functor with
  `ObjectProperty.ι (IsCoherentFormalModule (I.comap i)) ⋙
  (Functor.whiskeringRight ℕᵒᵖ Z.Modules X.Modules).obj (Scheme.Modules.pushforward i)`.
  This is exactly `(G_n) ↦ (i_* G_n)`, with transitions and morphisms pushed forward.
- The second conjunct gives a natural isomorphism θ between completion after
  pushforward and pushforward after completion, as functors from coherent
  Z-modules to inverse systems of X-modules. `formalCompletionFunctor` is the
  existing underlying-system functor of `completion`, so these are the actual
  completion systems. The formal equivalence's comparison identifies its image
  with these underlying systems; full subcategory inclusions are fully faithful,
  so this is equally a natural isomorphism in Coh(X,I).
- For every coherent G and every n, the additional equation states that the
  quotient projection on i_*G followed by θ at level `op n` equals pushforward of
  the quotient projection on G. Since `op n` is level n+1, all positive powers are
  included. This makes θ the canonical quotient comparison
  `(i_*G)/I^(n+1)(i_*G) ≅ i_*(G/(I O_Z)^(n+1)G)`, rather than an arbitrary
  isomorphism of objects. θ's natural-transformation type supplies compatibility
  with every transition map and naturality in coherent G. Its inverse is the
  direction `i_*(G^∧) ≅ (i_*G)^∧` written in the node.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, the closed embedding with surjective
  structure-sheaf stalk maps.
- `Mathlib.AlgebraicGeometry.Noetherian`:
  `AlgebraicGeometry.IsLocallyNoetherian` and `AlgebraicGeometry.IsNoetherian`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`:
  `AlgebraicGeometry.Scheme.Hom.ker`, used through the existing support predicates.
- `Sheaf.AlgebraicGeometry.Coherent`:
  `AlgebraicGeometry.RingedSpace.IsCoherent`, used in `CoherentModules` and inclusions.
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`:
  read the support docstring of `Scheme.Modules.HasSupportProperOver`; used the
  specified inline nonzero-stalk support, rather than importing unrelated properness.
- `Sheaf.AlgebraicGeometry.CoherentFormalModule`:
  `CoherentModules`, `CoherentModuleSupportedOn`, `CoherentFormalModule`,
  `IsCoherentFormalModule`, `SupportedOn`, `AnnihilatedBy`,
  `formalCompletionFunctor`, `formalModuleQuotientπ`, and the description of
  `completion`. All underlying definitions are reused.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`:
  `AlgebraicGeometry.Scheme.IdealSheafData.comap`, precisely the extended ideal.
- `Sheaf.AlgebraicGeometry.TensorPullback`: read `Scheme.Modules.tensorPullback`
  and its adjunction docstring. The item states pushforward, not pullback; its
  actual pushforward is the existing `Scheme.Modules.pushforward` in
  `Mathlib.AlgebraicGeometry.Modules.Sheaf`, also read in full. No duplicate
  pullback or pushforward was introduced and no unused pullback import is added.
- `Mathlib.CategoryTheory.Whiskering`: `Functor.whiskeringRight`, the standard
  postcomposition functor, expresses termwise pushforward of systems and maps.

Edge cases checked before writing: the empty scheme and the empty closed subscheme
are allowed; coherent zero modules and zero formal systems are allowed. For an
identity closed immersion, J=0 and the supported subcategories are the entire
categories. For I=0 the systems are constant up to their transition isomorphisms,
and completion gives constant systems. For I=O_X the formal categories consist of
zero systems and all completion quotients are zero. Nilpotent structure on Z is
retained by J-annihilation; topological support alone would be insufficient.
Formal levels are exactly all positive integers: `op 0` is level 1, and no extra
level-0 condition is imposed. Universe `u` matches the project's module categories
on `Scheme.{u}`; the fixed natural-number index introduces no arbitrary-universe
quantification or vacuous test objects.

Searches made for the item's exact statement (msearch.py, group U1, this item):

- LeanSearch: `Coherent modules on a closed subscheme equivalent to coherent modules
  annihilated by its ideal via pushforward`. The service returned UNAVAILABLE,
  Internal Server Error; no verdict is claimed for this service.
- LeanFinder: `Pushforward along a closed immersion gives an equivalence on coherent
  modules annihilated by the defining ideal and on coherent adic systems`.
  Eight results, including `IsClosedImmersion.overEquivIdealSheafData`, equivalences
  for open-immersion restriction/pushforward, and module local cohomology; none is
  this coherent-module or coherent-formal-module equivalence.
- Loogle: `AlgebraicGeometry.Scheme.Modules.pushforward, CategoryTheory.Equivalence`.
  Zero results.
- msearch grep: `coherent|annihilat|equivalence` in `AlgebraicGeometry/Modules`.
  Ten hits on quasi-coherent tilde and open restriction; no exact equivalence.
- Local `rg -n` of `closed.*[Ee]quiv|[Ee]quiv.*closed|coherent.*[Ee]quiv|CoherentFormal|closedImmersion`
  in both `lean/Sheaf/AlgebraicGeometry` and the read-only source's
  `WeilConjectures`: found the formal definitions and adjacent closed-immersion
  statements, but no theorem stating this node. The source's same-name blueprint
  grep for `lem-weil-pbc-closed-immersion-coherent-equivalence` found no declaration.
- Fresh-name search for all three main declaration names in Mathlib,
  `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision.

Source check: the local `literature/stacks-project/coherent.tex` is absent on this
machine, so the authoritative pages were opened directly:
[087T](https://stacks.math.columbia.edu/tag/087T),
[088A](https://stacks.math.columbia.edu/tag/088A),
[088C](https://stacks.math.columbia.edu/tag/088C), and
[088E](https://stacks.math.columbia.edu/tag/088E).
They confirm the equivalence, its use on systems, and the scheme-theoretic meaning
of “supported on Z.” No statement correction or disputed statement is needed.

Server validation: `scompile.py U1 lem-weil-pbc-closed-immersion-coherent-equivalence`
compiled the final module cleanly in 3.1 seconds, exit code 0. Initial elaboration
errors (missing source-Noetherian proof and the namespace of `whiskeringRight`)
were repaired. No warnings remain. All variables and the universe are explicit.
The second reading is intentionally left to the independent second worker.

## Second reading by U1

I reread the node statement, its Stacks source, all recorded statement dependencies, and the
Lean module declaration-by-declaration.

- Objects and hypotheses: the Lean introduces schemes `Z X : Scheme.{u}`, a morphism
  `i : Z ⟶ X`, and `[IsClosedImmersion i]`. Part (1) has exactly
  `[IsLocallyNoetherian X] [IsLocallyNoetherian Z]`; its coherent source category is
  `CoherentModules Z`, and its target is the full subcategory of `CoherentModules X`
  satisfying `CoherentModuleSupportedOn F i`, namely the scheme-theoretic equation
  `IsZero (Scheme.idealModuleProduct i.ker.toModulesι F.obj)`. The defining ideal is
  therefore exactly `i.ker`, as required by the node.
- Part (1) clause 1 is the existential equivalence `E`; the following `Nonempty` natural
  isomorphism compares its underlying functor with
  `Scheme.Modules.pushforward i`, through the two coherence/full-subcategory inclusions.
  This records that the equivalence is induced by pushforward, including maps.
- Part (1) clause 2 is `closedImmersion_coherent_support`: for every coherent `G`, the
  non-subsingleton stalk locus of `(Scheme.Modules.pushforward i).obj G.obj` equals
  `i '' {z | ¬ Subsingleton (G.obj.presheaf.stalk z)}`. This is the project's support
  convention and is the node's `Supp(i_*G)=i(Supp G)`.
- Part (2) has exactly `[IsNoetherian X]` and an arbitrary `I : X.IdealSheafData`, with
  extended ideal `I.comap i`; no radical, characteristic, finiteness, or separatedness
  assumption was added. The source formal category is typed using the existing theorem
  `isNoetherian_of_locallyOfFiniteType i` as the explicit `IsNoetherian Z` proof, so this
  does not add `[IsNoetherian Z]` as a hypothesis. The first conjunct is an equivalence
  from `CoherentFormalModule Z (I.comap i)` to the full subcategory of
  `CoherentFormalModule X I` satisfying `SupportedOn I M i` (which is `AnnihilatedBy I
  i.ker M`, termwise). Its comparison is with termwise pushforward via
  `Functor.whiskeringRight ℕᵒᵖ Z.Modules X.Modules`.
- The second conjunct is the natural isomorphism between completion after pushforward and
  pushforward after completion, with `formalCompletionFunctor` on both sides. For every
  coherent `G` and `n : ℕ`, the equation at `op n` compares the quotient projections at
  level `n+1`; hence all positive levels in the node are represented, and the equation
  specifies the canonical quotient comparison rather than an arbitrary isomorphism.
  Quantifier order and directions match the node.

Edge cases checked: empty schemes and empty closed subschemes, zero coherent modules and
zero systems, identity immersions (`i.ker = 0`), zero and unit ideals, nilpotent structure
(on which scheme-theoretic annihilation is stricter than set-theoretic support), arbitrary
universe `u`, and `op 0` as the positive first level. No index universe or characteristic
restriction is introduced.

Searches were repeated with `rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf`, plus
LeanFinder and Loogle via `msearch.py` for closed-immersion coherent equivalences and
pushforward/full-subcategory equivalences. LeanSearch was unavailable (recorded as such).
No existing declaration states this theorem. The source pages 087T, 088A, 088C, and 088E
were checked directly; they use the same annihilator interpretation of “supported on Z”.

One mismatch was found and repaired: the worker had introduced a duplicate auxiliary
`sorry` theorem `closedImmersion_source_isNoetherian`. This notion already exists as
`WeilConjectures.AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType`; I imported that
existing declaration, used it explicitly in the formal equivalence, removed the duplicate
from the module and declaration list, and updated the node note. No hypothesis or
conclusion of the item's statement was changed.
