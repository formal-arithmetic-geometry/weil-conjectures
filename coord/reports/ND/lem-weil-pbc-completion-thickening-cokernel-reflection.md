## Worker report

This delivery attaches the exact existing upstream theorem
`AlgebraicGeometry.completion_thickening_cokernel_reflection` in
`WeilConjectures.AlgebraicGeometry.CompletionThickeningCokernelReflection`
(source `lean/WeilConjectures/AlgebraicGeometry/CompletionThickeningCokernelReflection.lean`,
line 124). No new Lean module, definition, theorem, or sorry is introduced. Only the item's
`lean` field changes. The signature is extracted verbatim from the existing theorem.

Source checked: `literature/stacks-project/coherent.tex`,
`lemma-existence-tricky` (Tag 088A), especially its second appeal to
`remark-inverse-systems-kernel-cokernel-annihilated-by` (Tag 0888), and
`lemma-i-star-equivalence` (Tag 087T). These are the source places named by the node.
The existing theorem's source/proof docstring explicitly identifies this node and explains
reflection through faithful completion on the fixed closed thickening.

Hypothesis-by-hypothesis and clause-by-clause matching:

- A Noetherian scheme is `{X : Scheme.{u}} [IsNoetherian X]`. Mathlib's class extends
  `IsLocallyNoetherian X` and `CompactSpace X`, so this retains quasi-compactness rather
  than merely assuming local Noetherianness. The universe `u` is explicitly declared.
- The two quasi-coherent ideals are `(I K : X.IdealSheafData)`. This is the project's
  recorded ideal-sheaf convention, not arbitrary module subobjects.
- The positive thickening exponent is `(q : ℕ) (hq : 1 ≤ q)`.
- The closed thickening `Z = V(K^q)` is `(K ^ q).subscheme`, with closed inclusion
  `(K ^ q).subschemeι`.
- The extended ideal `I O_Z` is `I.comap (K ^ q).subschemeι`.
- Completion being an equivalence for every Noetherian instance is exactly
  `hcomplete : ∀ hZ : IsNoetherian (K ^ q).subscheme,
  Functor.IsEquivalence
  (@completion ((K ^ q).subscheme) hZ (I.comap (K ^ q).subschemeι))`.
  The Noetherian structure is quantified, not assumed as an extra independent hypothesis.
  It exists because a closed subscheme of a Noetherian scheme is Noetherian.
- The coherent modules and their morphism are `(F G : CoherentModules X) (a : F ⟶ G)`.
  This full subcategory uses `RingedSpace.IsCoherent X.toRingedSpace`, whose actual current
  definition is finite type with finite-type kernels of all local maps from finite free
  modules, exactly the coherent clause of `pqf-def-coherent`.
- The conditions `K^q F = 0` and `K^q G = 0` are respectively `hF` and `hG`, using
  `IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι q).2 F.obj)`
  and the identical expression with `G.obj`. Both are retained, even though the proof
  docstring notes that `hF` is unnecessary to its stronger intermediate conclusion.
- The positive torsion exponent is `(s : ℕ) (hs : 1 ≤ s)`.
- Every `n ≥ 0` is covered by `hred : ∀ n : ℕ, ...`.
- The reduction `F/I^(n+1)F → G/I^(n+1)G` is the canonical
  `formalModuleQuotientMap I a.hom (Nat.le_refl (n + 1))`. The source and target reduction
  powers coincide; these are cokernels of the actual multiplication-image inclusions.
- The reduced ordinary cokernel is `cokernel (formalModuleQuotientMap ...)`, and its
  annihilation by `K^s` is `IsZero (Scheme.idealModuleProduct
  (Scheme.idealSheafPower K.toModulesι s).2 (cokernel ...))`.
- The conclusion is exactly `IsZero (Scheme.idealModuleProduct
  (Scheme.idealSheafPower K.toModulesι (2 * s)).2 (cokernel a.hom))`.
  In particular the exponent remains `2 * s`, not `s` or `4 * s`.
- All these cokernels and ideal products live in the ambient `X.Modules`. `a.hom`
  forgets the full coherent subcategory; no cokernel in the adic-system category is used.

Dependency declarations read (full signatures, definitions, and docstrings):

- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`; also its `IsNoetherian` class for the item's
  explicitly stronger Noetherian hypothesis.
- `def-weil-pbc-coherent-formal-module`:
  `WeilConjectures.AlgebraicGeometry.CoherentFormalModule`,
  `AlgebraicGeometry.CoherentModules`, `formalModuleQuotient`, `formalModuleQuotientπ`,
  `formalModuleQuotientMap`, `IsCoherentFormalModule`, `CoherentFormalModule`, and
  `completion`. Inverse-system index `op n` represents level `n + 1`.
- `pqf-def-coherent`: the recorded
  `Sheaf.AlgebraicGeometry.CoherentFiniteType` /
  `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType` was read. It only supplies
  the quasi-coherent finite-type conjunction. For the coherent clause the node's closed
  upstream audit identifies `WeilConjectures.AlgebraicGeometry.Coherent` /
  `AlgebraicGeometry.RingedSpace.IsCoherent`; its current definition was read and is
  exactly what `CoherentModules` uses. Thus the existing theorem uses the actual coherent
  notion, without a replacement or repair module.
- `lem-weil-pbc-quasi-coherent-ideal-closed-subscheme`: its Mathlib match was read in
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`, namely
  `AlgebraicGeometry.Scheme.IdealSheafData.subscheme`, `subschemeι`, `ker_subschemeι`,
  `subschemeCover`, `opensRange_subschemeCover_map`, `subschemeCover_map_subschemeι`;
  the closed-immersion instance was read in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `def-nagata-extended-ideal`:
  `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`,
  `AlgebraicGeometry.Scheme.IdealSheafData.comap`. Its definition is precisely the kernel
  ideal of the first projection from the base change of the closed subscheme.
- Product/power data used by the recorded completion interface were read in
  `WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk`:
  `Scheme.idealModuleProduct`, `idealModuleProductι`, `idealSheafPower`.
  The ideal module and inclusion `IdealSheafData.toModules`, `toModulesι` were read in
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`.

Searches made on 2026-10-23:

- `msearch.py ... leanfinder "Completion equivalence reflects ideal annihilation of
  cokernels on a fixed closed thickening"`: eight adic-completion hits (including
  `IsAdicComplete` and `AdicCompletion`); no exact Mathlib result.
- `msearch.py ... leansearch "Completion equivalence reflects annihilation of cokernels
  of coherent sheaf morphisms"`: eight categorical-cokernel hits; no exact Mathlib result.
- `msearch.py ... loogle "CategoryTheory.Limits.cokernel.mapIso"`: three hits, the generic
  cokernel isomorphism and its hom/inv formulas; none is the reflection theorem.
- `msearch.py ... grep "completion.*annihilat|annihilat.*completion"`: zero Mathlib hits.
- `rg -n 'completion_thickening_cokernel_reflection|completion.*cokernel|
  CompletionThickening' lean/WeilConjectures lean/Sheaf`: the exact theorem is present
  in both trees; the upstream module is preferred. Its source was read in full.
- `grep -rn 'lem-weil-pbc-completion-thickening-cokernel-reflection'
  lean/WeilConjectures`: the upstream theorem's blueprint docstring is the exact node.
- `rg -n 'completion_thickening_cokernel_reflection' dag/lean_names_upstream.json`:
  no match in that older index; actual current source and the live server probe supersede it.

Edge cases checked by reading the definitions and signature:

- `q = 1`, `s = 1` are included; zero exponents are excluded exactly as the node requires.
- `n = 0` gives quotient by `I^1`, so there is no missing first level or level-zero term.
- Zero modules, zero morphisms, and the empty scheme remain allowed.
- `K = 0` and `K = O_X` are not excluded. In the latter case the support assumptions
  force both modules to be zero; completion on the empty thickening is meaningful.
- `I = 0` and `I = O_X` are not excluded. The equivalence hypothesis retains its full
  force in these cases; it has not been replaced by a vacuous arbitrary map assumption.
- No separatedness, properness, affine hypothesis, characteristic condition, kernel torsion
  assumption, or equality of independent universes has been introduced.

Validation: a scratch module-mode probe publicly imports the upstream theorem's module,
checks the declaration, and prints its axioms. Prescribed `scompile.py` succeeded in both
sandbox and library checks (1.3 seconds each), without warnings or errors. The axioms are
exactly `[propext, Classical.choice, Quot.sound]`. This directly resolves the node's stale
lead note about the withdrawn interface: the currently published upstream theorem works.
The probe is not part of the delivery, and no module is delivered for an existing match.

There is no statement correction, new node, or dependency module. No statement dispute
was found.

## Second reading by ND

A separate second pass in this worker reopened the node, the upstream theorem signature,
and the definitions of coherent modules, completion, quotient maps, ideal products, and
extended ideals. No other agent was started, as the dispatcher explicitly forbids it;
this is a self-review, with the maintainer's independent review still to follow.

The pass checked every binder against the mapping above: Noetherian X, both ideals,
positive q and s, equivalence on the fixed thickening for every Noetherian structure,
coherent F and G, a, both support bounds, and every positive reduction. It checked the
ambient cokernel and precisely the doubled exponent in the conclusion. All agree.
In particular it did not drop hF because the existing proof can do without it, and did
not replace the conclusion by its stronger intermediate K^s estimate. The only metadata
change is the exact existing upstream binding; no mathematical text changed. The stale
coherent finite-type dependency record was not mistaken for the definition of coherence:
the audited current `RingedSpace.IsCoherent` definition was opened and checked directly.
