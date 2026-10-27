# Q32: relative ampleness and absolute pullback twists

## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeAmpleAbsoluteTwist` states
`AlgebraicGeometry.Scheme.Modules.isAmple_tensorPullback_tensorPow_of_relative`.
It introduces no definitions and postpones exactly this theorem with `sorry`.
Its docstring contains all eight steps of the node's proof, with their cited nodes.
The source was read in `literature/stacks-project/morphisms.tex`,
`lemma-pullback-ample-tensor-relatively-ample` (Tag 0892), assertion (1).
The node is unchanged except for its `lean` field. No correction, new node,
or dependency replacement is necessary.

### Hypotheses and conclusion, clause by clause

- Schemes Z and T: `{Z T : Scheme.{u}}`, for arbitrary explicitly bound `u`.
- The morphism f: `(f : Z ⟶ T)`, using `Scheme.Hom`.
- Quasi-compactness of f: `[QuasiCompact f]`. Mathlib's compact-open
  inverse-image condition is equivalent to the affine-open condition in the node.
  No properness, finite type, or separatedness assumption is added.
- N and M are modules on the stated schemes: `(N : Z.Modules) (M : T.Modules)`.
- Both are invertible: `[N.IsInvertible] [M.IsInvertible]`, the recorded scheme
  module notion (locally free of rank one), not a second definition.
- Every affine open V of T is quantified in `hN : ∀ V : T.Opens,
  IsAffineOpen V → ...`. The open inverse image is `f ⁻¹ᵁ V`.
- Restricting N to this open subscheme uses the recorded tensor pullback:
  `((tensorPullback (f ⁻¹ᵁ V).ι).obj N)`.
- Ampleness on every such restriction is
  `∃ h : ... .IsInvertible, @IsAmple (f ⁻¹ᵁ V).toScheme ... h`.
  The existential provides the proof argument required by `IsAmple`;
  it does not choose another module or add a substantive condition.
  Invertibility of this actual pullback already follows from invertibility of N
  by the existing invertible-pullback theorem.
- Ampleness of M is `(hM : IsAmple T M)`. This definition already includes
  quasi-compactness of T and the positive-power affine nonvanishing cover.
- The integer threshold is `∃ a₀ : ℤ, 0 ≤ a₀ ∧ ...`.
- Every integer at or beyond the threshold is included by
  `∀ a : ℤ, a₀ ≤ a → ...`; this is the full tail, not a single suitable power
  or only a sufficiently divisible subsequence.
- The twisting power is `M.tensorPow a.toNat`. The preceding inequalities imply
  `0 ≤ a`, so `Int.toNat` is the exact conversion of a nonnegative integer to
  the exponent type of the existing `tensorPow`; no negative power is asserted.
- The pullback is `(tensorPullback f).obj (M.tensorPow a.toNat)`.
- Tensoring with N is `tensorObj N (...)`, the existing sheaf tensor on Z.
- The conclusion is `∃ h : (tensorObj N ...).IsInvertible,
  @IsAmple Z (tensorObj N ...) h`. This states ampleness of the specified
  invertible module. Its invertibility witness is a proposition about that
  exact construction, not a replacement object. It follows independently from
  tensor-power, pullback and tensor preservation of invertibility.

### Dependency declarations read and used

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (def-pc-scheme).
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `tensorObj`, `tensorPow`.
  `tensorObj` is the monoidal tensor on scheme modules; `tensorPow 0` is the
  structure module and the successor is the actual iterated tensor.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (def-weil-pbc-quasi-compact-scheme),
  used inside the recorded `IsAmple`. Quasi-compactness of the morphism uses
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
  `AlgebraicGeometry.QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple`
  (def-weil-pbc-ample-invertible-module).
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: public interface to
  `AlgebraicGeometry.Scheme.Modules.tensorPullback` from
  `WeilConjectures.AlgebraicGeometry.TensorPullback`
  (def-pc-module-pullback). The signature and explicit inverse-image/change-of-rings
  construction were read, as was the recorded normalized adjunction interface.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, the recorded tensor dependency interface
  (def-pur-sheaf-tensor-product). The scheme tensor itself is the existing
  `Scheme.Modules.tensorObj`; no second sheaf tensor is defined here.

All recorded proof-dependency modules are imported privately when their declarations
are stated. The Mathlib permanence, separatedness, affine-intersection and affine-cover
facts are available through these imports. Their use, including the empty-scheme case,
is explained in the eight-step theorem docstring. Public imports expose statement
notions; proof imports remain ordinary imports.

### Edge cases checked before writing

The empty Z is allowed: ampleness has a vacuous pointwise clause and compactness,
and the proof explicitly takes threshold zero. If T is empty, the morphism forces
Z to be empty as well. An empty affine open is not excluded by `hN`.
Exponent zero means the structure module, as the existing `tensorPow` definition
requires; the theorem does not require the chosen threshold to be zero.
The final quantifier covers every integer beyond the bound, including the bound.
There is no negative-exponent case under a nonnegative threshold. There is no
field, characteristic, nonemptiness, Noetherian or finiteness restriction.
The schemes use the same arbitrary universe required by their morphism category.
Existential witnesses of invertibility are proof-irrelevant and impose no choice
of tensor product, pullback, or restriction.

### Searches for existing declarations

All searches used the prescribed `msearch.py Q32
lem-sfb-relative-ample-absolute-twist` service on 2026-10-22.

- LeanFinder: `A relatively ample invertible sheaf tensored with the pullback of
  all sufficiently large powers of an ample invertible sheaf is ample`.
  Eight hits: pullback tensor carriers, section-clearing powers, Proj.pow_apply,
  and base-change permanence; none states ampleness of the twisted invertible module.
- Loogle: `"IsAmple"`. Zero hits.
- Mathlib grep: `relatively.?ample|ample.*tensor.*pullback|pullback.*ample.*tensor`,
  subdirectory `AlgebraicGeometry`. Zero hits.
- LeanSearch: `Relative ampleness and ampleness on the base imply absolute
  ampleness after twisting by all sufficiently large pullback powers`.
  Eight hits: additive pullback, smooth relative dimension, affine target
  morphism properties, and base-change permanence. No match.
- Project and upstream rg: `relative.*ample.*twist|ample.*relative.*twist|
  ample.*absolute.*twist|lem-sfb-relative-ample-absolute-twist|
  lem-per-relative-ample-absolute-twist` in `lean/WeilConjectures` and `lean/Sheaf`.
  The assigned node is cited by QuasiprojectiveQCComposition; the other hits are
  Chow modification twists, which concern a different statement.
- Name search for `isAmple_tensorPullback_tensorPow_of_relative` and
  `RelativeAmpleAbsoluteTwist` in Mathlib, both source roots and
  `dag/lean_names_upstream.json`: no existing declaration or module.

### Previous attempt and validation

The previous attempt reported the stage-1 reviewed split as blocking stage 2.
The current node still has no Lean record. This delivery only adds its stage-2
statement, preserving Q60's reviewed split and all of its proof steps.
Validation uses only `scompile.py` and `deliver2.py`; the shared clone is read-only.

## Second reading by Q32

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
