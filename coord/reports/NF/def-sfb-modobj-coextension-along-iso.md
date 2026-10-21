## Worker report

Recorded the existing definition `CategoryTheory.Mod.coextendScalarsIsoComapInv` in
`WeilConjectures.CategoryTheory.ModuleObjects.MapMod`, lines 178–181. No Lean module is
submitted and only the item's `lean` field changes. Its signature is copied verbatim:

```lean
noncomputable def coextendScalarsIsoComapInv : coextendScalars φ ≅ comap (asIso φ).inv
```

The declaration's docstring says coextension along an isomorphism is restriction along
its inverse, by uniqueness of right adjoints. The source is the current blueprint
`sec-proetale-coefficients/sk-def-sfb-change-of-scalars/def-sfb-modobj-coextension-along-iso.md`
and clause 5 of that unit's `_section.md`; both were opened and checked.

Clause-by-clause and hypothesis-by-hypothesis reading:

- The category is arbitrary `C : Type u₁` with `[Category.{v₁} C]`, with independent
  object and morphism universes. `[MonoidalCategory C]` gives its tensor structure.
- The inherited closedness and equalizer assumptions are `[MonoidalClosed C]` and
  `[HasEqualizers C]`. The inherited braiding, coequalizers, preservation of colimits
  by tensoring on either side, and commutativity of R are present in the source's
  section variables but unused in this construction. Lean omits them from the
  elaborated declaration, as it does for the recorded restriction equivalence.
  Applying this already-existing construction in the node's full situation gives
  exactly the required object; no new or stronger hypotheses are imposed.
- The two monoid objects are `{R S : C} [MonObj R] [MonObj S]`.
- Their isomorphism is `(φ : R ⟶ S) [IsMonHom φ] [IsIso φ]`; `asIso φ` packages
  that same arrow as an isomorphism, and `(asIso φ).inv` is its inverse.
- The left-hand functor is the dependency's exact `Mod.coextendScalars φ`, not a
  different coextension: `Mod C R ⥤ Mod C S`.
- The right-hand functor `Mod.comap (asIso φ).inv` is restriction along the inverse,
  also `Mod C R ⥤ Mod C S`.
- `≅` is an isomorphism in this functor category, hence precisely a natural
  isomorphism, with both componentwise inverse identities and naturality.

Dependency declarations read and used:

- `def-sfb-modobj-restriction-equivalence` records
  `CategoryTheory.Mod.comapEquivalenceOfIsIso` in
  `WeilConjectures.CategoryTheory.ModuleObjects.MapMod`. Its forward functor is
  `comap φ` and its inverse is definitionally `comap (asIso φ).inv`.
- `def-sfb-modobj-coextension` records `CategoryTheory.Mod.coextendScalars` in
  `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`. Read its full
  context, functor definition, equalizer maps, and the adjunction section.
  The internal Hom equalizer and right-multiplication action are the node's
  specified construction, with postcomposition on morphisms.
- The construction also uses `Mod.restrictCoextendAdjunction` in `ExtendScalars`,
  whose natural Hom equivalence evaluates at the unit, and
  `Equivalence.toAdjunction` in `Mathlib.CategoryTheory.Adjunction.Basic`.
  The latter supplies the quasi-inverse adjunction after `Equivalence.mk` has
  adjusted the unit to satisfy the triangle identities.
- `Adjunction.rightAdjointUniq` in `Mathlib.CategoryTheory.Adjunction.Unique`
  gives the natural isomorphism in the required orientation. Its
  `rightAdjointUniq_hom_app_counit` gives exactly the proof's counit equation.
  These are the Mathlib matches of `lem-weil-pbc-quasi-inverse-adjoint` and
  `det-sp-unique-right-adjoint`. No missing proof-dependency node is restated.

Edge cases checked: the identity isomorphism has inverse the identity and both
functors have the required domain and codomain; the terminal monoidal category
has the same construction; no nontriviality or nonempty index hypothesis is
needed. The argument needs no elementwise interpretation of C and works without
additivity or an abelian structure. Arbitrary independent universes are retained.
The counit-compatible direction is Coext to inverse restriction, not its reversal.
No disputed statement or node correction was needed.

Searches (all 2026-10-21):

- `msearch.py ... leanfinder "Coextension of scalars along an isomorphism of monoid
  objects is naturally isomorphic to restriction along its inverse"`: eight
  hits, including `Rep.coindFunctorIso`, `Rep.coindIso`, and ordinary ModuleCat
  Hom-equivalence lemmas; no exact Mathlib module-object comparison.
- `msearch.py ... loogle "CategoryTheory.Mod.coextendScalarsIsoComapInv,
  CategoryTheory.Adjunction.rightAdjointUniq"`: no hits; Loogle does not know
  the upstream project declaration.
- `msearch.py ... leansearch "Coextension of scalars along an isomorphism is
  restriction of scalars along its inverse"`: eight hits, including
  `ModuleCat.coextendScalars` and restriction pseudofunctors, not this generality.
- `msearch.py ... grep "coextendScalarsIsoComapInv|rightAdjointUniq" CategoryTheory`:
  19 Mathlib hits, including the generic uniqueness construction and its formulas.
- `rg` for `coextendScalarsIsoComapInv|coextension.*isomorphism` in both project
  roots finds the exact definition at `WeilConjectures/.../MapMod.lean:180` and
  its consumer at line 186. No duplicate in `Sheaf`.
- `grep -rn "def-sfb-modobj-coextension-along-iso"` in `lean/WeilConjectures`
  gives no blueprint-id annotation, but the exact named definition above exists.
- The same name was searched in `dag/lean_names_upstream.json`; no index hit.

Server verification: `scompile.py NF def-sfb-modobj-coextension-along-iso` on the
sandbox scratch probe imported MapMod and printed the full existing declaration
and checked both dependency declarations and the adjunction. It confirmed the
above universes and retained hypotheses. The exploratory `pp.universes` option
produced a development-only linter warning and was removed from the scratch file;
no scratch file or new declaration is submitted. The delivery wrapper's clean
existing-declaration probe and server preflight provide final validation.

## Second reading by NF

This is a self-check, not a claim of an independent reviewer: the dispatch brief
forbids starting agents and assigns the independent reading to the maintainer.
Reopened the node statement, its two dependency bindings, and MapMod's actual
source. Both sides of the displayed comparison use the recorded definitions;
the inverse arrow is exactly `asIso φ |>.inv`; the source and target are exactly
R-modules and S-modules. The body is the prescribed right-adjoint uniqueness
construction with the specified inverse equivalence. The server's elaborated
signature confirms the source file's unused section assumptions are omitted,
without narrowing the categories or universes. No mismatch or amendment found.
