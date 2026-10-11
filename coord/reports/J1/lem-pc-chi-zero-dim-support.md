## Worker report

The module `Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport` states
`AlgebraicGeometry.Scheme.Modules.eulerChar_zero_dim_support`, with one `sorry` and no
new definitions. The node statement is unchanged. Its additional statement dependency
`def-sc-ringed-space-module-cohomology` is already landed and supplies the standard
cohomology of O_X-modules required by the standing stage-2 brief. Support is rendered by
the set comprehension already specified in the item's own statement, using existing stalks;
there is no additional support definition.

Hypotheses and clauses, individually:

- The field k is `(k : Type u) [Field k]`.
- The scheme X over k is `(X : Scheme.{u}) [X.Over (Spec (.of k))]`.
- Properness over k is `[IsProper (X ↘ Spec (.of k))]`, the recorded properness notion.
- F is an O_X-module via `(F : X.Modules)`; coherence is
  `hF : RingedSpace.IsCoherent X.toRingedSpace F`.
- The support is `{x : X | ¬ Subsingleton (F.presheaf.stalk x)}`. An abelian stalk is
  zero exactly when its underlying type is subsingleton. Its dimension at most zero is
  `hdim : topologicalKrullDim {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ≤ 0`.
- Clause 1 is `∀ i : ℕ, 0 < i → IsZero
  ((RingedSpace.moduleCohomology X.toRingedSpace i).obj F)`.
- For clause 2, `H0` denotes degree-zero module cohomology. Its k-action and that on
  `Γ(F, ⊤)` are restriction of scalars along `globalSectionsRingHom k`. The two equalities
  are `F.eulerChar k = (Module.finrank k H0 : ℤ)` and
  `Module.finrank k H0 = Module.finrank k Γ(F, ⊤)`. The natural-number dimension is
  cast to integers only where compared with the integer Euler characteristic.
- Clause 3 quantifies over every `(N : X.Modules) [N.IsInvertible]`. Its `T` is exactly
  `F ⊗ N`, typed as X.Modules to select the established module tensor product.
  `RingedSpace.IsCoherent X.toRingedSpace T` asserts tensor coherence; the equality
  of the two nonzero-stalk sets asserts exactly equal support; and
  `T.eulerChar k = F.eulerChar k` asserts tensor invariance.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Sheaf.AlgebraicGeometry.Coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim` (including the subspace topology).
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`:
  `AlgebraicGeometry.Scheme.Modules.eulerChar`, `Scheme.globalSectionsRingHom`.
  Euler characteristic uses the upstream abelian-sheaf H model; its comparison with
  module cohomology is a stage-3 injective-module acyclicity bridge, not a replacement
  definition or an additional hypothesis. This comparison is mentioned in the proof docstring.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` and its imported monoidal structure.
- `Sheaf.Topology.RingedSpaceModuleCohomology`:
  `AlgebraicGeometry.RingedSpace.moduleCohomology`, the right derived functor of
  module global sections into modules over global functions.
- Existing Mathlib module presheaves, stalks and sections are used directly.

Source checked: https://stacks.math.columbia.edu/tag/0AYT, Lemma 33.33.3, parts (3)--(5),
including its proof. The local literature/stacks-project/varieties.tex is absent on this
machine, so the source was read online. Its locally free rank n tensor statement specializes
here to invertible modules, n=1, as specified by the node. The proof docstring follows all
four DAG proof steps, including finite support, finite closed subscheme reduction, affine
cohomology and tensor dimension calculation, and the Euler characteristic calculation.

Edge cases checked mathematically: F=0 gives empty support and dimension -∞, satisfying
≤0, and all conclusions give zero. Empty X is allowed (no Nonempty hypothesis). For
X=Spec k and F a finite-dimensional vector space, positive cohomology is zero and both
dimensions equal its ordinary dimension. For a closed point with residue extension l/k,
the dimension is measured over k, giving [l:k], not the dimension over l. Twisting by
an invertible module preserves every stalk's vanishing. No restriction on characteristic
or reducedness is imposed; finite nonreduced support is covered. Field, scheme and
module universes follow the recorded upstream API, with u explicitly declared; all
binders are explicit and there are no auto-bound implicits.

Searches made (actual msearch entries are in searches.jsonl):

- LeanFinder: `coherent sheaf zero dimensional support higher cohomology vanishes Euler
  characteristic tensor invertible`: eight hits on abstract derived-category and complex
  vanishing, no match for this geometric statement.
- Loogle: `topologicalKrullDim, Subsingleton`: zero hits.
- LeanSearch: `coherent sheaf finite support Euler characteristic`: unavailable, Internal
  Server Error; no mathematical verdict inferred from the failed service.
- Mathlib grep via msearch: `support|eulerChar` in AlgebraicGeometry/Modules: zero hits.
- rg of WeilConjectures cohomology and module files for `support|eulerChar`: EulerChar.lean
  has Grothendieck vanishing by dimension of the whole scheme, base change, and disjoint-open
  formulas; none states vanishing by support dimension together with tensor invariance.
- rg for `lem-pc-chi-zero-dim-support` in WeilConjectures: no hits.
- rg for `support|moduleCohomology|eulerChar` and support definitions in lean/Sheaf:
  module cohomology is already recorded; etale supports are different notions. No exact
  statement found. The new full declaration name was searched in Mathlib/source/project
  and dag/lean_names_upstream.json, with no collision.

No statement correction, unusable dependency, new definition node, or disputed statement
was found. Server compilation is used exclusively; nothing was compiled locally.

## Second reading by J1

I reread the node statement, its dependency records, the source declaration of
`def-pc-euler-characteristic`, and the module signature clause by clause.

- The field and scheme are rendered by `(k : Type u) [Field k]`,
  `(X : Scheme.{u}) [X.Over (Spec (.of k))]`; properness is
  `[IsProper (X ↘ Spec (.of k))]`. These match the node and the recorded
  `def-weil-proper-morphism` notion, with no extra finiteness or characteristic
  hypothesis.
- Coherence is `hF : RingedSpace.IsCoherent X.toRingedSpace F`, using the
  recorded `pqf-def-coherent` declaration. The support is the set
  `{x : X | ¬ Subsingleton (F.presheaf.stalk x)}`, which is the zero/nonzero
  stalk formulation of the node. The dimension hypothesis is exactly
  `topologicalKrullDim ... ≤ 0`.
- The positive-degree clause is now `∀ i : ℕ, 0 < i → IsZero (F.H i)`, and
  the degree-zero object is `H0 := F.H 0`. This is the `Scheme.Modules.H`
  used by `def-pc-euler-characteristic`; the field actions are explicitly
  restricted along `globalSectionsRingHom` for both `H0` and `Γ(F, ⊤)`.
- The Euler characteristic clause is
  `F.eulerChar k = (Module.finrank k H0 : ℤ)` and the dimension clause is
  `Module.finrank k H0 = Module.finrank k Γ(F, ⊤)`, matching the two equalities
  in the node. The final quantifier is every `(N : X.Modules) [N.IsInvertible]`,
  with `T := F ⊗ N`, tensor coherence, equality of the two nonzero-stalk sets,
  and `T.eulerChar k = F.eulerChar k` in the same order.

The first reading found one mismatch: the worker used the separately defined
`RingedSpace.moduleCohomology` in the vanishing and dimension clauses. The
Euler-characteristic dependency defines `H` as `Scheme.Modules.H`, so those
clauses did not express the node's cohomology. I replaced `moduleCohomology` by
`F.H`, removed the forced unused `def-sc-ringed-space-module-cohomology`
dependency, and removed the now-inapplicable comparison sentence in the proof
docstring. The node statement itself remains unchanged; all eight citers still hold because
their use is precisely the zero-dimensional-support vanishing/tensor conclusion.

Edge cases checked: `F = 0` has empty support and all cohomology and Euler
characteristic terms zero; empty `X` is allowed; `X = Spec k` gives the usual
finite-dimensional vector-space result; a closed point with residue extension
measures dimension over `k`; tensoring by an invertible module preserves stalk
vanishing. No characteristic, reducedness, nonempty, or universe case was
silently excluded, and all variables are explicit.

Searches were independently checked with LeanFinder/Loogle/LeanSearch and
`rg` in Mathlib, `WeilConjectures`, and `lean/Sheaf`; no exact existing
statement or declaration was found. The source Tag 0AYT was reread directly,
including parts (3)--(5) and its proof. The corrected file compiles cleanly
with `scompile.py`, with only the permitted `sorry` declaration warning.
