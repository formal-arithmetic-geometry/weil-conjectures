## Worker report

The module defines `SheafOfModules.extensionByZeroPresheaf`, a functor from sheaves of
modules on the localized ringed site at `U` to presheaves of modules on the original site.
Its object data are the direct sum indexed by all maps `V ⟶ U`; its morphism data act
componentwise. The functor and semilinearity laws are named theorem statements with
`sorry` proofs. Source: Stacks Project, Modules on Sites, Lemma 03DI, especially the first
paragraph of its proof; special case in Lemma 0F6Z.

Clause-by-clause correspondence:

- The site `C` and its topology are `{C : Type u₁} [Category.{v₁} C]` and
  `{J : GrothendieckTopology C}`. The ring sheaf is `R : Sheaf J RingCat.{u}` and
  the chosen object is `U : C`. There is no smallness, nonemptiness, or
  subsingleton hypothesis on `C` or its hom types.
- The localized site is Mathlib's `J.over U`, and its ring sheaf is `R.over U`.
  The input `G : SheafOfModules.{v} (R.over U)` uses the existing sheaf-of-modules
  category. The module universe `v` is independent of the ring universe `u`.
- `extensionByZeroPresheafSection R U G V` is
  `ModuleCat.of _ (DirectSum (V.unop ⟶ U) (fun φ => G.val.obj (op (Over.mk φ))))`.
  Thus each map `φ` has exactly one summand of sections of `G` at `(V, φ)`.
- The `R.obj.obj V` module structure on that `DirectSum` acts componentwise;
  Mathlib identifies `(R.over U).obj.obj (op (Over.mk φ))` definitionally with
  `R.obj.obj V`. The theorem `extensionByZeroPresheafRestrict_smul` states
  semilinearity against `R.obj.map a`.
- `extensionByZeroPresheafRestrictAdd` is `DirectSum.toAddMonoid` of the map
  `G.val.map (op (Over.homMk a.unop))` followed by `DirectSum.of` at
  `a.unop ≫ φ`. This is exactly restriction of a section in the `φ` summand
  along `a : V' ⟶ V`, placed in the `φa` summand. `extensionByZeroPresheafMap`
  packages it as a module morphism; the named `_id` and `_comp` theorems are
  the presheaf laws.
- `extensionByZeroPresheafHomApp` applies `α.val.app (op (Over.mk φ))` on every
  summand using `DirectSum.lmap`. `extensionByZeroPresheafHom` packages this as
  a presheaf morphism using the named `_naturality` theorem, and
  `extensionByZeroPresheaf` uses the named `_id` and `_comp` theorems to form
  the claimed functor.
- When `V ⟶ U` is empty, `extensionByZeroPresheafSection_isEmpty` states that
  the section module is subsingleton, hence zero. When it has a unique map,
  `extensionByZeroPresheafSection_unique` states the canonical isomorphism to
  the corresponding section of `G`, lifted to the direct sum's universe.
  The same restriction formula handles both cases: an arrow into a `V` with
  no map to `U` has zero domain, and an arrow into a `V` with a map to `U`
  lands in the unique summand when maps are subsingleton.

Dependencies read and used:

- `def-pur-localized-ringed-site`: Mathlib `GrothendieckTopology.over`,
  `Sheaf.over` (`Mathlib.CategoryTheory.Sites.Over`), and
  `SheafOfModules.over` (`Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`).
  The recorded `SheafOfModules.over` signature gives the restriction of an
  existing sheaf; the present module uses the same localized ring sheaf `R.over U`.
- `def-weil-sheaf-of-modules-category`: Mathlib `SheafOfModules` and its
  underlying `PresheafOfModules` (`Mathlib.Algebra.Category.ModuleCat.Sheaf`
  and `Mathlib.Algebra.Category.ModuleCat.Presheaf`).

Edge cases checked: no maps `V ⟶ U` gives the empty direct sum; a unique map
gives the single summand; multiple maps remain distinct summands; a map from
`V'` to a `V` with no map to `U` has the zero restriction map from zero;
the zero module remains a zero direct sum. The output module universe is
`max v v₁` because direct sums over the hom type can raise the universe.
No characteristic or commutativity hypothesis was introduced.

Searches for an existing declaration:

- `msearch.py leanfinder "extension by zero presheaf of modules on localized
  ringed site direct sum over maps to U"`: eight unrelated or broader hits;
  no direct-sum extension-by-zero presheaf.
- `msearch.py loogle "PresheafOfModules.pullback,
  PresheafOfModules.pushforward, SheafOfModules.over"`: zero hits for the
  combined query. The individual pullback/pushforward and `over` constructions
  do not have this direct-sum formula.
- `msearch.py grep "extensionByZero|extension.?by.?zero|lowerShriek"
  Algebra/Category/ModuleCat`: zero hits.
- `rg "extension.?by.?zero|extensionByZero|ExtensionByZero|lowerShriek"`
  in the source repository: hits concern geometric or derived extensions by
  zero, not this generic site presheaf. Exact-name search for
  `extensionByZeroPresheaf` found no match.
- `grep -rn "def-weil-extension-by-zero-presheaf"` in the source repository:
  no match. `rg "extension.?by.?zero|extensionByZero|ExtensionByZero|lowerShriek"`
  under the project `lean/Sheaf`: no match.
- The existing stage-1 Mathlib searches in the node find no exact declaration;
  the present search confirms that result.

The server single-file compile passed without errors or warnings.

## Second reading by E1

Independent comparison with the node statement and Stacks Project, Modules on
Sites, Lemma 03DI (especially its proof's first paragraph) and Lemma 0F6Z:

- Site and object: `{C : Type u₁} [Category.{v₁} C]` and `U : C` give the
  arbitrary category/site object; `{J : GrothendieckTopology C}` gives its
  topology. Verdict: exact; there is no extra size, nonempty, or separation
  hypothesis. In Stacks 03DI the standing hypothesis is only a ringed site.
- Ring sheaf and localization: `R : Sheaf J RingCat.{u}`, `R.over U`, and
  `G : SheafOfModules.{v} (R.over U)` give `O`, `O_U`, and its module sheaf.
  The dependency `def-pur-localized-ringed-site` records Mathlib's
  `GrothendieckTopology.over`, `Sheaf.over`, and `SheafOfModules.over`;
  `def-weil-sheaf-of-modules-category` records `SheafOfModules`. Their
  signatures were read in Mathlib. Verdict: exact; no abelian or sheafify
  instance is needed merely to form this functor.
- Section formula: `extensionByZeroPresheafSection` is `ModuleCat.of _
  (DirectSum (V.unop ⟶ U) (fun φ => G.val.obj (op (Over.mk φ))))`.
  Verdict: one summand per arrow, including parallel arrows; its scalar
  action is the direct sum's componentwise action over `R.obj.obj V`, which
  is the ring of `(R.over U)` at each `Over.mk φ`.
- Restriction: `extensionByZeroPresheafRestrictAdd` maps the `φ` injection
  by `G.val.map (op (Over.homMk a.unop))` into the `a.unop ≫ φ` injection.
  `extensionByZeroPresheafRestrict_smul` supplies semilinearity over
  `R.obj.map a`; `extensionByZeroPresheafMap`, `_id`, and `_comp` package
  the presheaf laws. Verdict: exact, including direction of `a : V' ⟶ V`.
- Morphisms and functor: `extensionByZeroPresheafHomApp` uses `DirectSum.lmap`
  of `α.val.app` at each `Over.mk φ`; `_naturality`, `_id`, and `_comp`
  package this into `extensionByZeroPresheaf`. Verdict: exact.
- At most one arrow: `_isEmpty` gives the zero module when there is no
  arrow. When there is one, `_unique` gives the isomorphism to the lifted
  section of `G` and now specifies its action on the unique summand's
  injection. The restriction formula above gives the stated restriction
  in both cases. Verdict: exact after the repair below. Stacks 0F6Z uses
  the global at-most-one-arrow hypothesis for its related abelian-sheaf
  result; this construction works for every site, hence also that case.

Edge cases: an empty hom type produces the zero direct sum; a singleton
hom type gives the canonical one-summand identification; distinct arrows
stay distinct summands. An empty category has no `U`, so the quantified
construction has no instance; an empty scheme's site is otherwise covered.
The zero sheaf gives the zero direct sum. No natural number, characteristic,
field, finiteness, or Noetherian assumption occurs. The independent module
universe `v` and hom universe `v₁` are both covered by output `max v v₁`.

Searches made independently: `msearch.py leanfinder "presheaf of modules
induced from sheaf on over category by summing sections over arrows to U"`
returned only generic presheaf-of-modules constructions; `msearch.py loogle
"DirectSum, PresheafOfModules"` returned zero hits; `msearch.py grep
"leftKanExtension|lan|sumOver|sigma.*[Oo]ver"` returned unrelated hits.
An exact-name `rg extensionByZeroPresheaf` over Mathlib, `WeilConjectures`,
and project `lean/Sheaf` returned no match; broader searches there found
geometric or derived extensions by zero, not this direct-sum presheaf.

Mismatch and repair: `_unique` originally stated only `Nonempty` of an
isomorphism, without saying that it is the canonical single-summand map.
Its conclusion now characterizes the isomorphism on every injected section.
No change was needed to the main definition or its node record. Single-file
compile completed with no errors or warnings.
