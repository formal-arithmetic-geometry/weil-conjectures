## Worker report

The module `Sheaf.AlgebraicGeometry.FlatPullbackIdealPow` states
`AlgebraicGeometry.image_tensorPullback_ideal_pow`, with proof `sorry`. It introduces
no definitions or auxiliary theorems. The node changes only in `lean`.

I read the current node, its six statement dependencies, the recorded interfaces,
the proof dependencies, and the main-20261015 blueprint statement at
`literature/blueprint/main-20261015/blueprint/sec-nagata-compactification/sk-lem-nagata-sketch-blowups/lemma-nagata-flat-pullback-ideal-pow.md`.
There is no repair note for this item. The old CompactObject example is now a withdrawn
module; the module-mode header and public-section conventions of the standing brief
are followed.

Hypotheses and clauses, matched individually:

- The schemes are `{X Y : Scheme.{u}}`, with the universe `u` explicitly declared.
  They have no finiteness, separation, nonemptiness, or characteristic restrictions.
- The quasi-coherent ideal subsheaf of O_X is `(I : X.IdealSheafData)`. This is the
  project's standard encoding of quasi-coherent ideal sheaves, including arbitrary
  ideals, rather than just coherent or finitely generated ones. `I.toModules` is
  its actual module sheaf, and `I.toModulesι` its monomorphism into O_X.
- The morphism is `(g : Y ⟶ X)` and its flatness is exactly `[Flat g]`.
- Every natural power is covered by `(n : ℕ)`. The expression `(I ^ n).toModulesι`
  is the inclusion of the actual nth ideal-sheaf power, including n = 0.
- The pullback of this inclusion is
  `(Scheme.Modules.tensorPullback g).map (I ^ n).toModulesι`, using the tensor
  pullback of the recorded dependency, rather than Mathlib's differently encoded
  `Modules.pullback`.
- Its map to O_Y is the composite with the inverse Hom equivalence of
  `Scheme.Modules.tensorPullbackSectionAdjunction g`, applied to
  `SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom`. This is exactly
  the adjoint of g-sharp under the section-normalized tensor adjunction. It fixes
  the canonical scalar map and does not posit an arbitrary map or adjunction.
- The left side is `imageSubobject` of that composite in the category Y.Modules.
  This is the sheaf image, with no assumption that sections commute with images.
- The right side is `Subobject.mk ((I.comap g) ^ n).toModulesι`. Here `I.comap g`
  is precisely the extended ideal from def-nagata-extended-ideal: the kernel ideal
  of the first projection of `Y ×_X V(I)`. Its power is the recorded ideal-sheaf
  power, and `Subobject.mk` records its inclusion into the same structure sheaf.
  Thus equality is equality inside O_Y, rather than just an abstract isomorphism.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`; its
  `iff_flat_stalkMap` identifies the affine and stalkwise definitions.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `Scheme.IdealSheafData`, its
  multiplication and natural-power instances, and `ideal_pow`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`:
  `Scheme.IdealSheafData.comap`, defined as `(pullback.fst g I.subschemeι).ker`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`:
  `Scheme.IdealSheafData.toModules` and `toModulesι`; the affine-range formula
  identifies this module inclusion with the affine ideals in IdealSheafData.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullbackSectionAdjunction` and its publicly imported
  `Scheme.Modules.tensorPullback`. I read both the tensor construction and the
  normalized unit characterization in `existsUnique_tensorPullbackSectionAdjunction`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` is imported as the recorded
  pqf-def-coherent module. Its extra finite-type predicate is not imposed here:
  quasi-coherence of the ideal is already built into IdealSheafData.

The proof-dependency imports are included as plain imports: Subscheme for the
canonical closed subscheme, AffineScheme for the affine-open basis, Ideal.Maps
for `Ideal.map_pow`, the recorded
`WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage` for
`closedSubscheme_baseChange_ideal_image`, and the recorded
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine` for
`Scheme.IdealSheafData.ideal_comap_appLE`. The remaining proof dependencies share
Basic or Functorial, already imported publicly. The theorem docstring gives all
five steps of the node's proof and names their dependencies.

Edge cases were checked mathematically before writing: for n = 0 the map is
pullback of the unit ideal and its image is all O_Y, as is the zeroth power on the
right. For I = 0 and n > 0 both sides are zero; for I = O_X both are O_Y. Empty
schemes and zero affine rings are allowed and give the same formulas. Identity
morphisms recover the same power inclusion. Flatness is retained, although an
image equality does not need it; injectivity of the pulled-back inclusion is not
asserted as an extra conclusion. No statement correction or disputed assertion.

Searches actually run (2026-10-22):

- msearch.py leanfinder: "The image of the pullback of a power of a quasi-coherent
  ideal sheaf along a flat morphism equals the power of the extended ideal sheaf".
  Eight hits: idealPowersDiagram, IdealSheafData.comap, le_map_comap, Ideal.le_comap_pow,
  IdealSheafData.map, comap_map_le, ideal_map, Ideal.map_pow. No direct image statement.
- msearch.py loogle: `Ideal.map_pow`. One exact ring-level hit, not a sheaf-image
  assertion.
- msearch.py grep: `comap.*pow|pow.*comap|pullback.*[Pp]ow|[Pp]ow.*pullback`
  in Mathlib/AlgebraicGeometry. Eight unrelated spectrum, localization and tensor
  tilde hits; no direct image statement.
- rg with the same pattern in `lean/WeilConjectures` and `lean/Sheaf`, and grep
  for this item's id in `lean/WeilConjectures`. I opened the relevant matches:
  `WeilConjectures/Blowup/FlatBaseChange.lean` supplies
  `Ideal.range_powLiftBaseChange` and `Ideal.injective_powLiftBaseChange_of_flat`
  only for rings, not module sheaves on an arbitrary scheme.
  `WeilConjectures/Mathlib/AlgebraicGeometry/IdealSheaf/Functorial.lean` supplies
  `Scheme.IdealSheafData.comap_pow`, an equality of extended ideal data that still
  needs the module-image comparison to state this node's explicit image equality.
  `modulePullbackIdealPowerProductImage` is about product images in f*G, with
  recursively defined module-subobject powers; it is not the present inclusion
  into O_Y. None is used as an exact existing match.
- rg in `dag/lean_names_upstream.json` located the two affine ring results above;
  the proposed full declaration name was searched in Mathlib, WeilConjectures,
  and Sheaf and is unused.

Validation: scompile.py compiled the module in both sandbox and library mode
without errors or warnings (1.7 and 1.9 seconds). All variables and universes
are explicitly bound, and every theorem proof in this delivery is `sorry`.

The dispatcher brief assigns independent review to the maintainer; this report
is the author's reading and does not claim an independent second reading.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
