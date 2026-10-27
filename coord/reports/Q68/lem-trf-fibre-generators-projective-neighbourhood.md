## Worker report

The module `Sheaf.AlgebraicGeometry.FibreGeneratorsProjectiveNeighbourhood` states
`AlgebraicGeometry.Scheme.Modules.fibre_generators_projective_neighbourhood`, with its
only proof `sorry`. No definition, dependency repair, or statement correction is needed.
The node is unchanged except for `lean`.

Source read: Stacks `coherent.tex`, Tag 0D2N, `lemma-ample-in-neighbourhood`, first proof
paragraph, especially the union of nonvanishing opens, shrinking by closedness, the
construction of phi, its twist, and identification of its fibre. The extracted claim does
not need the surrounding Noetherianity or ampleness hypotheses: those were used to obtain
the supplied global sections, whereas this node assumes those sections already exist.
The node's five proof steps, including chart/twist and properness details from 01NE, 01NG,
01W4 and 01W6, are reproduced in the theorem docstring.

Hypothesis and conclusion correspondence:

- Schemes Z and S, morphism f, properness, and s in S are `{Z S : Scheme.{u}}`,
  `(f : Z ⟶ S)`, `[IsProper f]`, and `(s : S)`.
- The scheme-theoretic fibre is `f.fiber s`; its two specified projections are
  `f.fiberι s` and `f.fiberToSpecResidueField s`. The residue field is `S.residueField s`.
- The invertible module is `(M : Z.Modules) [M.IsInvertible]`, using the recorded scheme
  module predicate. All module pullbacks use `tensorPullback`.
- The integer r >= 0 is `(r : ℕ)`; the r+1 sections are
  `a : ULift.{u} (Fin (r + 1)) → M.sections`. ULift preserves exactly this coordinate set
  while meeting the existing free-sheaf and projective-space universe conventions.
  A compatible family of sections is equivalent to its value at the top open.
- `us` names the pulled-back tuple on the fibre. `hus` fixes its top components to the
  images of the original sections under `tensorPullbackSectionAdjunction`'s unit.
  This is the recorded, normalized pullback, not an arbitrary map or an additional
  generation assumption. Compatible families are uniquely determined by these top
  values and always exist by restriction of a top section. `hgen` is exactly the
  epimorphism of the free sheaf for this tuple, as in the generating-sections node.
- The neighbourhood is `∃ U : S.Opens, s ∈ U ∧ IsAffineOpen U`. Its inverse image is
  `(f ⁻¹ᵁ U).toScheme`, structural morphism `f ∣_ U`, and inclusion `(f ⁻¹ᵁ U).ι`.
  The restricted module is `(tensorPullback (f ⁻¹ᵁ U).ι).obj M`.
- The existential invertibility witness `hMU` is an output for the restricted module,
  not a new assumption. The tuple `v` is fixed to the restrictions of `a` by the same
  normalized-unit formula. `hv` expresses exactly its generation.
- `φ` is equated to the recorded `ProjectiveSpace.homOfGeneratingSections` with the
  specified structural map, module, invertibility witness, tuple and epimorphism.
  Thus it is the associated U-morphism, not an arbitrary proper map. `IsProper φ`
  states its properness.
- `e` is an isomorphism from the tensor pullback of `ProjectiveSpace.twist ... 1` to
  the restricted M. For each coordinate, `e.hom.app ⊤` sends the normalized pullback
  of `ProjectiveSpace.twistOneSection` to `(v j).val (op ⊤)`. These equations are
  quotient compatibility.
- `b` is the residue-field map into U, fixed by `b ≫ U.ι = S.fromSpecResidueField s`.
  `i` is the fibre inclusion into the inverse image of U, fixed by `hi`; the included
  `IsPullback` identifies this square with the original scheme-theoretic fibre.
- `φs` is equated to the associated morphism of M_s and the original pulled-back
  tuple `us`. The equation `hc : φs ≫ ProjectiveSpace.map ... b = i ≫ φ` says it is
  the base change of φ under the canonical projective-space comparison. Indeed
  `ProjectiveSpace.isPullback_map` gives that comparison square, and the defining
  projection identity of `homOfGeneratingSections` gives its other projection.
- `β` identifies the pullback of O(1) under `ProjectiveSpace.map ... b` with O(1) over
  the residue field. Its coordinate equations fix the quotient-compatible comparison.
  The standard sections generate, so these equations uniquely fix the isomorphism.
- `es` is the fibre twist isomorphism and carries each coordinate to `us`. The final
  isomorphism equality states that `es` agrees with pullback of `e`, using `β`, the
  normalized comparisons `tensorPullbackSectionComp`, and the equality transports
  supplied by `hc` and `hi`. This includes the same-isomorphism clause, not merely
  existence of two unrelated isomorphisms.

Recorded statement dependencies used (module; declarations):

- `Mathlib.AlgebraicGeometry.Scheme`; `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`; `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Fiber`; `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`; `Scheme.fromSpecResidueField` from its residue-field import.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`; `Scheme.Modules.IsInvertible`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`;
  `Scheme.Modules.tensorPullback`, `tensorPullbackSectionAdjunction`,
  `tensorPullbackSectionComp`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`;
  `SheafOfModules.GeneratingSections`'s `Epi (M.freeHomEquiv.symm tuple)` interface.
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections`;
  `ProjectiveSpace.homOfGeneratingSections` (the signature and full construction read).
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`;
  `AlgebraicGeometry.ProjectiveSpace`, `ProjectiveSpace.map`, `isPullback_map`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`;
  `ProjectiveSpace.twist`, `twistOneSection`. These are the prescribed twists and coordinates,
  including the affine-base model of def-pc-projective-space-twist.

The recorded proof modules are imported: NonvanishingSectionTrivializes,
NonvanishingTensorPullback, InvertibleGeneratingSectionsFibre, InvertiblePullbackTensor,
ProjectiveSpaceFunctorOfPoints, ProjectiveSpaceStandardCharts, ProjPolynomialTwistChart;
the other proof dependencies are supplied by AffineScheme, Proper, Fiber, ProjectiveSpace,
Twist and the statement imports. `invertible_pullback_tensor` also supplies the explicit
fibre invertibility proof passed to the existing associated-morphism construction.

Edge cases checked: r=0 gives one coordinate and P^0. An empty fibre satisfies generation
vacuously and properness permits choosing a neighbourhood with empty inverse image if all
sections vanish there; the empty scheme and its unique sheaf isomorphisms are retained.
There is no nonemptiness, Noetherian, reducedness, separated-base, field-characteristic,
or nonzero-section assumption. An empty base cannot supply the point s, exactly as in the
node. Nonreduced schemes are permitted. The scheme universe u is arbitrary and no equality
of independent site or coefficient universes was imposed.

Searches actually run through msearch.py for this item:

- leanfinder: "Sections of an invertible module generating on a fibre of a proper scheme
  generate on an affine neighbourhood and define a proper projective space morphism".
  Eight hits, chiefly `Proj.fromOfGlobalSections` and projective-spectrum properness;
  no match for shrinking plus quotient-compatible fibre comparison.
- leansearch: "Sections generating an invertible sheaf on one fibre of a proper scheme
  define a projective morphism near the fibre". Eight hits, including GeneratingSections.mk,
  Proj.fromOfGlobalSections and IsProper.instMorphismRestrict, none the complete statement.
- loogle: `"IsProper", "GeneratingSections"`: zero hits.
- grep: `generat.*(fiber|fibre)|(fiber|fibre).*generat`, Mathlib AlgebraicGeometry:
  zero hits.
- rg of the same pattern in the project WeilConjectures and Sheaf sources found related
  generating and shrinking lemmas, including ProperFibreGeneratorPullbackLocus and
  NoetherianFibreAmpleNeighbourhood; neither states the tuple/projective-space/fibre
  comparison here. The latter assumes fibre ampleness and concludes ampleness.
- rg for the exact item id in WeilConjectures and Sheaf: no declaration match.

Validation: scompile.py's server confirmation compiled the module cleanly in 5.7 seconds
before the final explicit import cleanup. Its local attempt reports ENOSPC and the wrapper
successfully falls back to the server. The initial deterministic elaboration timeout was
removed by fully specifying coordinate types and using the existing modules' transparency
settings; the 60-second limit was not changed. Final compile and dry-run results follow
from the delivery wrapper.

No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by Q68

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
