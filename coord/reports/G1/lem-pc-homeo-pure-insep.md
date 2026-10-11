## Worker report

The module `Sheaf.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange` states
`AlgebraicGeometry.isHomeomorph_baseChange_of_isPurelyInseparable` with a `sorry`
proof. No definitions or additional nodes are needed, and the node is unchanged
except for `lean`.

Hypothesis and conclusion correspondence:

- “k ⊂ k' a field extension”: `(k K : Type u) [Field k] [Field K] [Algebra k K]`.
  A field algebra map is injective, so this represents the inclusion without
  requiring the fields to be literally subsets of one type.
- “purely inseparable”: `[IsPurelyInseparable k K]`. Mathlib's
  `isPurelyInseparable_iff_pow_mem` identifies this with the power-in-the-base-field
  definition in `def-pc-field-tower`; exponential characteristic is 1 in
  characteristic zero, so this also gives the surjective-map clause there.
- “X a scheme”: `(X : Scheme.{u})`.
- “over k”: `[X.Over (Spec (CommRingCat.of k))]`; the structure morphism is
  `X ↘ Spec (CommRingCat.of k)`.
- “X_{k'}”: the domain of `pullback.fst` is the scheme pullback of that structure
  morphism along `Spec.map (CommRingCat.ofHom (algebraMap k K))`.
- “canonical morphism X_{k'} → X”: precisely that `pullback.fst`.
- “homeomorphism of underlying topological spaces”: `IsHomeomorph (...).base`.
  `Scheme.Hom.base` is the underlying continuous map. `IsHomeomorph` requires
  continuity, openness and bijectivity, and supplies a continuous inverse.

Dependencies read and used:

- `def-pc-base-change`: `Sheaf.AlgebraicGeometry.BaseChangeConventions`, read in full
  and imported. Its explicit convention is `Limits.pullback f T.hom` for X_T,
  `pullback.snd` for pr_T and `pullback.fst` for f_T. Its primary recorded
  `AlgebraicGeometry.Scheme.Modules.moduleBaseChange` concerns module base change;
  that clause is not used here. The recorded scheme convention is usable as is.
- `def-pc-field-tower`: read `Sheaf.FieldTheory.FieldTower` and its recorded
  `FieldExtension.degree` signature and docstring. Degree is not used here. Its
  module docstring explicitly delegates the purely inseparable clause to Mathlib's
  `IsPurelyInseparable`, which is reused from
  `Mathlib.FieldTheory.PurelyInseparable.Basic`. No private field-tower definition
  is introduced and the unused degree module is not imported.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`. Their full
  signatures and docstrings identify a locally affine locally ringed space and
  morphisms of the underlying locally ringed spaces.
- `def-weil-scheme-over-base`: `Mathlib.AlgebraicGeometry.Over`, declaration
  `AlgebraicGeometry.Scheme.Over` (the OverClass abbreviation) and its structure
  morphism notation. Its signature and docstring were read and its module imported.

Edge cases checked before writing:

- X empty: no nonemptiness assumption; its pullback is empty, and the map on empty
  spaces is a homeomorphism.
- K = k: the projection is an isomorphism, hence a homeomorphism.
- Characteristic zero: purely inseparable field extensions are trivial as field
  extensions; the binder does not exclude this case or assume positive characteristic.
- Infinite purely inseparable extensions: no finite degree or finite type binder.
- Nonreduced, nonaffine, nonseparated schemes: none of these restrictions are imposed.
- No Noetherian or proper hypothesis. Universe `u` is explicitly bound and arbitrary;
  the fields and schemes lie in the common universe required for the category of
  schemes and its pullback. Any given collection fits a common universe; this
  imposes no mathematical size or finiteness restriction.

Searches on 2026-10-11:

- `msearch.py ... leanfinder "base change of an arbitrary scheme along a purely
  inseparable field extension is a homeomorphism"`: eight hits; the two relevant
  hits were `PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable` and its
  tensor-product-map version. Both are affine cases, not the arbitrary-scheme
  statement. Other hits concern residue fields, unramified morphisms or field maps.
- `msearch.py ... loogle "IsPurelyInseparable, IsHomeomorph"`: two hits, exactly
  those affine prime-spectrum results.
- `msearch.py ... leansearch "purely inseparable field extension scheme base change
  homeomorphism"`: unavailable (Internal Server Error), not a negative search result.
- `msearch.py ... grep "IsPurelyInseparable|isHomeomorph" AlgebraicGeometry`: ten
  hits, involving unrelated morphisms or the residue-field characterization of
  universally injective morphisms, no arbitrary-scheme base-change theorem.
- `rg -n 'IsPurelyInseparable|isHomeomorph|baseChange'` in the source's universal
  homeomorphism modules, and `rg -n 'homeo-pure|PurelyInseparable|purely inseparable'`
  in its AlgebraicGeometry tree: found the general universal homeomorphism results,
  `Algebra.IsUniversalHomeomorphism.of_isPurelyInseparable`, and curve-specific
  applications; no declaration stating this node's specialization.
- `rg -n 'lem-pc-homeo-pure-insep'` in source WeilConjectures: no matches.
- `rg -n 'purely|IsPurelyInseparable|isHomeomorph'` in `lean/Sheaf/AlgebraicGeometry`:
  only unrelated closed-point field declarations.
- `rg -n 'isHomeomorph.*isPurelyInseparable|baseChange_isHomeomorph_of_isPurelyInseparable'`
  in `dag/lean_names_upstream.json`, `lean/Sheaf`, and source WeilConjectures:
  no matching declaration. The chosen declaration name was also checked against
  the source and Mathlib results; the preflight checks name uniqueness.

Source check: the local blueprint text path named by the node is not materialized
on this machine. Read the node's complete source and proof records and the original
Stacks sources at https://stacks.math.columbia.edu/tag/0BR5 (opening paragraph,
asserting the affine base-change result for any algebra) and
https://stacks.math.columbia.edu/tag/04DF (integral, universally injective,
surjective iff universal homeomorphism). These support the recorded three-step
proof, which is reproduced in the theorem docstring with each dependency named.
No statement dispute or correction.

Validation: server single-file compilation and `deliver2.py --no-push` are run
before returning READY. The second reader will add the independent reading;
no second-reading section has been written by this worker.

## Second reading by G1

I read the node `lem-pc-homeo-pure-insep` and the module
`Sheaf/AlgebraicGeometry/HomeomorphPurelyInseparableBaseChange.lean` independently.
The node introduces a field extension `k ⊂ k'` that is purely inseparable and a
scheme `X` over `k`; its conclusion has one clause: the canonical map from the
base change `X_{k'}` to `X` is a homeomorphism on underlying spaces.

The Lean renders the field extension as `(k K : Type u)` with `[Field k]`,
`[Field K]`, `[Algebra k K]`, and `[IsPurelyInseparable k K]`. This is the
Mathlib field-extension formulation; fields make the algebra map injective, and
`IsPurelyInseparable` includes the algebraicity/power condition (including the
trivial characteristic-zero case). It does not add finiteness, positivity of
the characteristic, or a degree assumption. `X : Scheme.{u}` renders the
scheme, and `[X.Over (Spec (CommRingCat.of k))]` supplies exactly its structure
morphism over `Spec k`. The displayed expression is
`pullback.fst (X ↘ Spec (CommRingCat.of k))`
`(Spec.map (CommRingCat.ofHom (algebraMap k K)))`, whose `.base` is the
canonical projection from the pullback/base change to `X`; `IsHomeomorph` is
the homeomorphism clause on underlying topological spaces. Quantifier order
and all hypotheses agree with the node.

The source check used the node's Stacks references: Tag 0BR5 gives the
purely-inseparable spectrum homeomorphism (and its opening paragraph assumes
an algebraic purely inseparable extension), while Tags 0BR9/0BRA supply the
power criterion and universal-homeomorphism argument; the scheme-level
conclusion is the base-change instance described by Tag 04DF. The Lean
docstring records the three proof steps and names the corresponding dependency
nodes. No statement mismatch was found and no change was needed.

Edge cases checked: `K = k` gives the identity projection; in characteristic
zero the purely inseparable extension is trivial; empty schemes give the empty
homeomorphism; nonreduced, nonaffine, nonseparated, infinite, and arbitrary
universe-compatible schemes are all admitted; no Noetherian, proper, finite,
or nonempty assumptions are present.

Searches were repeated with `msearch.py` (LeanFinder, Loogle, and grep) for
purely-inseparable scheme base change/homeomorphisms, and with `rg` over the
source `WeilConjectures`, Mathlib algebraic-geometry files, and `lean/Sheaf`.
Only the affine `PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable`
results were found; no declaration states this arbitrary-scheme theorem.
The dependency declarations and base-change convention module were opened;
`def-pc-base-change`, `def-pc-field-tower`, `def-pc-scheme`, and
`def-weil-scheme-over-base` match the objects used here. The module compiled
cleanly with `scompile.py`; its only proof is the required `sorry`.
