## Worker report

The module `Sheaf.AlgebraicGeometry.UniversalThickeningFlatBaseChange` states
`AlgebraicGeometry.universalFirstOrderThickening_flat_base_change`, with proof `sorry`.
No definitions, dependency repairs, new nodes, or statement corrections are needed.

Hypothesis and clause correspondence:

- Schemes W, W', X, Y are `{W W' X Y : Scheme.{u}}`, with u explicitly declared.
- h':W→Y is `hW : W ⟶ Y`, and formal unramifiedness is `[FormallyUnramified hW]`.
- g:X→Y is `g : X ⟶ Y`, and flatness is `[Flat g]`.
- Z=X×_Y W and Z'=X×_Y W' are the chosen `pullback g hW` and `pullback g s`.
  h and f are respectively `pullback.fst g hW` and `pullback.snd g hW`.
- W⊂W' and its structure morphism are `iW : W ⟶ W'` and `s : W' ⟶ Y`.
  `HW : IsUniversalFirstOrderThickening hW iW s` includes closed immersion,
  square-zero ideal, compatibility `iW ≫ s = hW`, and the full unique lifting property.
- The induced map id_X×iW is named `iZ`. Its two defining projection equations
  are `_hfst` and `hsnd`. These are specifications of the map already named in
  the node, not additional geometric restrictions: the fibre product universal
  property supplies exactly one such map. In particular `hsnd` is the node's
  equation f'∘iZ=iW∘f. No cartesian-square hypothesis is added.
- Clause (1) is `∃ hu : FormallyUnramified (pullback.fst g hW), ...`.
  This is a proof witness, permitting dependent use in the conormal definition;
  it introduces no extra choice of scheme or module.
- Clause (2) is `∃ HZ : IsUniversalFirstOrderThickening
  (pullback.fst g hW) iZ (pullback.fst g s), ...`.
- Clause (3), flatness of f', is `Flat (pullback.snd g s)`.
- Clause (3), the conormal isomorphism, is `IsIso c` for the map `c` equal to
  `Classical.choose ((Classical.choose_spec (...closedImmersion_conormal_functorial...).2).2)`.
  The ambient map is `pullback.snd g s`, the restricted map is `pullback.snd g hW`,
  and the square equation is `hsnd`. The two closed-immersion instances are
  supplied explicitly by `HZ.1.1` and `HW.1.1`, rather than assumed.
  The domain is tensor pullback of `formallyUnramifiedConormal hW iW s HW`;
  the codomain is `formallyUnramifiedConormal` for h, hu, iZ, and HZ.
  Unfolding the recorded definition gives exactly the types of the canonical
  map in the functoriality dependency. The universal quantification over `c`
  followed by equality to the chosen canonical map is equivalent to asserting
  that this map is an isomorphism; it does not assert an arbitrary isomorphism.
  The chosen `γ` of that dependency is its ideal map induced by f'^sharp.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified`:
  `AlgebraicGeometry.FormallyUnramified`; read the full class and its agreement
  lemmas `FormallyUnramified.hom_ext` and `FormallyUnramified.of_hom_ext`.
  This dependency is a Mathlib leaf and needs no new lean record.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`;
  read `Flat.iff_flat_stalkMap`, identifying it with the node's stalkwise condition.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, and their
  universal property. Scheme pullbacks are provided by Mathlib's scheme instance.
- `Sheaf.AlgebraicGeometry.UniversalFirstOrderThickening`:
  `AlgebraicGeometry.IsUniversalFirstOrderThickening` (imported transitively).
- `Sheaf.AlgebraicGeometry.FormallyUnramifiedConormal`:
  `AlgebraicGeometry.formallyUnramifiedConormal`.
- `Sheaf.AlgebraicGeometry.TensorPullback`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullback` (imported transitively).
- `Sheaf.AlgebraicGeometry.ClosedImmersionConormalFunctorial`:
  `AlgebraicGeometry.Scheme.Modules.closedImmersion_conormal_functorial`.
  Read its entire signature and docstring, including the sectionwise ideal map,
  unique conormal map, and affine characterization.

Source checking: the local Stacks TeX file is absent on this machine, so read
https://stacks.math.columbia.edu/tag/04F8 and https://stacks.math.columbia.edu/tag/04F9,
and the map/isomorphism sources https://stacks.math.columbia.edu/tag/01R4 and
https://stacks.math.columbia.edu/tag/0473. Their statements and proofs agree with
this node. The module docstring reproduces the node's five-step proof and its
named proof dependencies.

Edge cases checked before writing: empty W or X are allowed, no nonempty or
point hypothesis is imposed; identity g and identity thickenings are allowed;
zero conormal modules are allowed and their canonical identity is an isomorphism.
No Noetherian, finite-type, separatedness, or characteristic restriction is present.
The same explicit arbitrary universe u is used throughout, including the existing
universal-thickening predicate's test schemes. Neither test scheme is restricted
to affine schemes. No independent smaller universe makes a lifting hypothesis vacuous.

Searches made (2026-10-11):

- `msearch.py ... leanfinder`, query: "Universal first order thickenings and their
  conormal sheaves commute with flat base change of schemes". Eight results:
  `AlgebraicGeometry.Flat`, its fst/snd and base-change instances,
  `FormallyUnramified.instIsStableUnderBaseChangeScheme`, and flat affine-section
  lemmas. No universal-thickening or conormal statement.
- `msearch.py ... loogle`, query: `"conormal"`. Zero hits.
- `msearch.py ... grep`, query: `universal.*[Tt]hickening|conormal`, subdirectory
  `AlgebraicGeometry`. Zero hits in Mathlib.
- `rg -n -i 'universal.*thickening|conormal'` in source `WeilConjectures`:
  only the DeformationToNormalCone docstring mentions conormal as follow-up work;
  no matching declaration. Search for this exact blueprint node ID: no hits.
- `rg` in project `lean/Sheaf/AlgebraicGeometry`: the existing conormal-functoriality,
  closed-immersion flat-base-change, first-order thickening base-change and universal
  thickening modules exist; none states the present three-clause result. Read the
  closed-immersion flat-base-change sibling to check how it refers to the same
  canonical map, and the FormallyUnramifiedConormal module in full.

Server compilation: `scompile.py K1 lem-weil-pbc-universal-thickening-flat-base-change
<module>` returned exit 0, compiled in 2.6 seconds, no warnings.

## Second reading by K1

I reread the node statement, its Stacks source (04F8 and 04F9, with the
conormal map from 01R4 and its flatness result 0473), and the complete Lean
module. The correspondence is as follows.

- The schemes `W W' X Y : Scheme.{u}` are the four schemes in the node; all
  share one universe, so no case is excluded by a universe restriction.
- `hW : W ⟶ Y` with `[FormallyUnramified hW]` is the node's formally
  unramified `h'`; `g : X ⟶ Y` with `[Flat g]` is its flat morphism.
- `pullback g hW` and `pullback g s` are respectively `Z = X ×_Y W` and
  `Z' = X ×_Y W'`. Their `fst` and `snd` projections render the node's `h`,
  `f`, the projection `Z' ⟶ X`, and `f' : Z' ⟶ W'`.
- `iW`, `s`, and `HW : IsUniversalFirstOrderThickening hW iW s` render the
  closed immersion, structure map, and universal first order thickening of
  `W` over `Y`.
- `iZ` is accompanied by `_hfst : iZ ≫ fst = fst` and
  `hsnd : iZ ≫ snd = snd ≫ iW`. By the pullback universal property these are
  exactly the two projection equations for `id_X × iW`; they add no
  geometric hypothesis and exclude no induced map.
- The first conclusion is the witness
  `∃ hu : FormallyUnramified (pullback.fst g hW)`, exactly clause (1).
  The second is
  `∃ HZ : IsUniversalFirstOrderThickening ...`, exactly clause (2), including
  the first order and universal lifting conditions in the recorded predicate.
- The conjunction's `Flat (pullback.snd g s)` is clause (3)'s flatness of
  `f'`. Its final universal implication identifies every `c` with the unique
  canonical map selected by `closedImmersion_conormal_functorial` and asserts
  `IsIso c`; hence it states that the canonical map from the pulled-back
  conormal of `W/Y` to that of `Z/X` is an isomorphism. The source and node's
  `tensorPullback`, conormal, square equation, and closed-immersion instances
  are all present explicitly.

Edge cases checked: empty schemes and zero conormal modules are permitted;
identity maps and identity thickenings are permitted; no nonemptiness,
Noetherian, finite type, separatedness, characteristic, or affine restriction
is introduced. The single universe `u` is used throughout, including the
universal-thickening predicate's test schemes.

I searched Mathlib and the project/source with LeanFinder, Loogle, grep, and
`rg` for universal first order thickenings, conormal sheaves, and the exact
blueprint name. Only the existing project declarations for the component
notions and functorial map were found; no existing theorem states this result.
The local Stacks TeX copy is absent, so the tagged online source pages listed
in the worker report were checked.

No mismatch was found and no file or node statement was changed. The module
contains only the requested theorem with a `sorry` proof and its docstring
records the source and proof steps.
