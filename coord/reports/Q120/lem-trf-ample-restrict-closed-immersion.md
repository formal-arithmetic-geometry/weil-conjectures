## Worker report

The module states restriction of an ample invertible module to an arbitrary closed
subscheme, exactly as Stacks Properties Tag 01PU, lemma-ample-on-closed. The source
and Definition 01PS were read in properties.tex. Only the theorem proof is postponed
with `sorry`; there are no new definitions, dependency repairs, or statement changes.

Hypotheses and conclusion, clause by clause:

- Any scheme Y: `{Y : Scheme.{u}}`, with the explicitly declared universe `u`.
- An O_Y-module M: `(M : Y.Modules)`.
- M invertible: `[M.IsInvertible]`, the recorded scheme-module class.
- M ample: `(hM : IsAmple Y M)`, the absolute notion including quasi-compactness
  and an affine nonvanishing locus from a positive tensor power at every point.
- Every closed immersion: `{X : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]`.
- Its pullback is ample on X: `@IsAmple X ((tensorPullback i).obj M)
  ((invertible_pullback_tensor i).1 M).2`. The last argument supplies the established
  proof that the tensor pullback is invertible, rather than requiring an extra
  assumption. It is a Prop proof argument and does not change ampleness.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible:
  `Scheme.Modules.IsInvertible` and `IsInvertible.pullback`.
- WeilConjectures.AlgebraicGeometry.Ample: `Scheme.Modules.IsAmple` and
  `Scheme.Modules.nonvanishingLocus`, the absolute Stacks 01PS definitions.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion:
  `IsClosedImmersion`, its `IsAffineHom` instance, and `Scheme.Hom.app_surjective`.
- Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction: the recorded module for
  def-pc-module-pullback, publicly importing the original
  WeilConjectures.AlgebraicGeometry.TensorPullback `Scheme.Modules.tensorPullback`.
  The section-normalized adjunction is not needed to express the conclusion.
- WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor:
  `Scheme.Modules.invertible_pullback_tensor`, its existing invertibility transport
  for the explicit tensor pullback. No second invertibility or pullback is defined.
- WeilConjectures.AlgebraicGeometry.Modules.TensorPowerSectionNonvanishingPullback:
  `Scheme.Modules.exists_tensorPow_section_nonvanishing_pullback`, imported for the
  recorded proof plan.
- Mathlib.Topology.Compactness.Compact: `IsClosed.isCompact`; and
  Mathlib.AlgebraicGeometry.Morphisms.Affine: `IsAffineOpen.preimage`.
  These proof-plan dependencies are available transitively from the imports.
  The converse affine-cover criterion uses `HasAffineProperty.iff_of_iSup_eq_top`
  and `IsClosedImmersion.hasAffineProperty` in the recorded Mathlib match.

The older local checkout lacks several published upstream modules. Their full
current declarations were read with `scompile.py --source`, including Ample,
TensorPullback, InvertiblePullbackTensor and TensorPowerSectionNonvanishingPullback.

Edge cases checked: X empty is permitted, with no point needing an affine witness;
the identity immersion recovers the same ample module; Spec(R/I) inside Spec(R)
permits arbitrary ideals, including nilpotent ideals and ideals not finitely
generated. Neither scheme is assumed reduced, Noetherian, projective, nonempty,
or over a field. Quasi-compactness is a consequence of ampleness, not an extra
hypothesis. A single arbitrary universe follows the recorded Scheme/pullback API.

Searches made:

- msearch.py leanfinder, “Pullback of an ample invertible module along a closed
  immersion of schemes is ample”: eight hits for closed immersions and base change;
  no ampleness theorem.
- msearch.py loogle, `IsAmple, IsClosedImmersion`: unknown identifier IsAmple,
  zero hits.
- msearch.py grep in AlgebraicGeometry,
  `IsAmple|ample.*closed|closed.*ample`: zero Mathlib hits.
- rg in WeilConjectures and lean/Sheaf for IsAmple and closed-immersion ampleness:
  upstream `AlgebraicGeometry.IsAmple.pullback` concerns the different, projective
  over a field notion, so is not a match. `isAmple_tensorPullback_of_isAffineHom`
  concerns arbitrary affine morphisms, so supplies a more general tool but does
  not have this node's hypothesis. Its live source was read with scompile --source.
  No exact closed-immersion specialization was found.
- grep for the item's id in the source WeilConjectures tree: no hits. Search in
  dag/lean_names_upstream.json found no exact declaration name for this item.

The declaration docstring follows the node's three proof steps, retaining all the
named dependencies. No disputed statement or node fault was found.

## Second reading by Q120

No second reading by a worker: the dispatched brief requires direct delivery and
forbids starting other agents. The maintainer supplies the independent review.
