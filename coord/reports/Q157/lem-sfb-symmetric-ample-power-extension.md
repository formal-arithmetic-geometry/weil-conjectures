## Worker report

The module `Sheaf.AlgebraicGeometry.SymmetricAmplePowerExtension` states
`AlgebraicGeometry.symmetricAmplePowerExtension`, with its entire proof `sorry`.
The node's mathematical statement and proof plan are unchanged. Its `stmt_deps`
gains the already landed `def-sfb-semiabelian-geometric-fibres`, as authorized by
brief-stage2 §5 for an existing node with a Lean record. No new node is needed.

The three auxiliary definitions are actual constructions belonging to this theorem:
`amplePowerRigidification` recursively tensors the specified rigidification and uses
unit multiplication; `amplePowerOpenMap` is the existing `baseChangeMap` along an
inclusion of base opens; `amplePowerOpenRigidification` composes the existing
normalized tensor-pullback composition comparisons, the equality of base-changed
sections, pullback of the rigidification, and the existing unit comparison. None
selects an unspecified map, extension, or isomorphism. There is no proof postponed
inside a definition.

Each hypothesis and conclusion is rendered as follows:

| Node clause | Lean rendering |
| --- | --- |
| T is a scheme | `T : Scheme.{u}` |
| T is affine | `[IsAffine T]` |
| T is integral | `[IsIntegral T]`, including nonemptiness |
| T is Noetherian | `[IsLocallyNoetherian T]` together with affineness, which gives quasi-compactness |
| Every local ring is an integrally closed domain | `hT : ∀ t : T, IsDomain (T.presheaf.stalk t) ∧ IsIntegrallyClosed (T.presheaf.stalk t)` |
| q:H → T is a commutative group scheme with identity | `H : Grp (Over T)` and `[IsCommMonObj H.X]`; q is `H.X.hom`, e is `η[H.X].left` |
| q is smooth | `[Smooth H.X.hom]` |
| q is separated, meaning a closed diagonal | `[IsSeparated H.X.hom]`, whose defining field is `isClosedImmersion_diagonal` |
| q is of finite presentation | `[LocallyOfFinitePresentation H.X.hom]` and `[QuasiCompact H.X.hom]`, with quasi-separatedness already implied by separatedness |
| Every geometric fibre is semiabelian, including rank zero | `hH : HasSemiabelianGeometricFibres H` from the existing node; its definition quantifies over algebraically closed fields and maps to T, with a split torus, an abelian variety, a kernel pullback square and fppf locally surjective quotient |
| V is a dense open of T | `V : T.Opens` and `hV : Dense (V : Set T)`; the open immersion is `V.ι` |
| H_V → V is proper | `[IsProper (pullback.snd H.X.hom V.ι)]` |
| M is invertible on H_V | `M : (pullback H.X.hom V.ι).Modules` and `[M.IsInvertible]` |
| The given rigidification e_V-star M ≅ O_V | `r`, using the actual `sectionBaseChange` of the identity and the monoidal unit `𝟙_ V.toScheme.Modules` |
| M is symmetric | `symmetry`, an isomorphism from tensor pullback under the inverse of the base-changed group to M |
| M is ample over every affine open of V | `hM`, quantifying over `A : V.toScheme.Opens` with `IsAffineOpen A` and applying `Scheme.Modules.IsAmple` to the tensor restriction over its inverse image |
| There exists an affine open covering of T | `∃ (I : Type u) (W : I → T.Opens), (⨆ i, W i) = ⊤ ∧ (∀ i, IsAffineOpen (W i)) ∧ ...` |
| On each nonempty covering member | `∀ i, Nonempty (W i) → ...` |
| There is an integer n_i ≥ 1 | `∃ n : ℕ, 1 ≤ n ∧ ...`; positive integers and positive naturals describe the same allowed exponents |
| There is an invertible B_i on H_(T_i) | `∃ (B : (pullback H.X.hom (W i).ι).Modules) (hB : B.IsInvertible), ...` |
| B_i is relatively ample over T_i | The first conjunct quantifies over every affine `A : (W i).toScheme.Opens` and asserts absolute ampleness of its inverse-image restriction |
| In particular B_i is ample on H_(T_i) | The separate conjunct `@Scheme.Modules.IsAmple _ B hB` |
| B_i is rigidified | `∃ rB : e_(W i)-star B ≅ 𝟙_ (W i).toScheme.Modules, ...`, with the identity section written as `sectionBaseChange` |
| B_i restricts to M to the n_i-th power on H_(V ∩ T_i) | `∃ α`, from tensor pullback of B along `amplePowerOpenMap ... inf_le_right` to tensor pullback of `M.tensorPow n` along `amplePowerOpenMap ... inf_le_left`, both over `V ⊓ W i` |
| That isomorphism preserves rigidifications | The final equality: pullback of `α.hom` along the identity over `V ⊓ W i`, composed with the restriction of the n-th tensor-power rigidification of r, equals the restriction of rB |
| This is an existence result, with no extension as input | B, hB, rB and α all occur under existential quantifiers after the conclusion colon |
| All module pullbacks are tensor inverse images | Every module pullback is `Scheme.Modules.tensorPullback`; Mathlib's distinct `Scheme.Modules.pullback` is never substituted in the statement |

Existential invertibility witnesses inside relative ampleness only furnish the proof
argument required by `IsAmple`; they add no hypothesis. The overlap is the actual
base-changed scheme over `V ⊓ W i`, rather than independently chosen schemes or maps.
The section equation `Over.w η[H.X]` supplies the group identity's existing structure
law without an additional assumption.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom` and `Scheme.Opens` (exposed through the public imports).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, with `IsDomain` on each stalk, as the normal-ring node prescribes.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: open subschemes and their `U.ι` (available through the public imports); no private open-immersion predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`, `IsSeparated`; the base-change instance is also the recorded match of `lem-weil-pbc-proper-base-change`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `tensorPow` and the sheaf monoidal structure, publicly imported by `Ample` and the tensor comparison module.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: `AlgebraicGeometry.Scheme.Modules.tensorPullback` and `tensorPullbackSectionComp`.
- `WeilConjectures.AlgebraicGeometry.Ample`: `AlgebraicGeometry.Scheme.Modules.IsAmple`.
- `Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres`: `AlgebraicGeometry.HasSemiabelianGeometricFibres`; also read its split torus and `IsAbelianVariety` definitions.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` and its public `Picard.Defs` import: `sectionBaseChange`, `baseChangeMap`, `sectionBaseChange_comp_baseChangeMap`.
- `WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons`: `boundaryPullbackTensorIso` and `boundaryPullbackPowIso`, used for the existing tensor and unit comparisons.
- Plain proof import `Sheaf.AlgebraicGeometry.SchemeRelativeAmpleBaseChange`: `AlgebraicGeometry.Scheme.Modules.isAmple_on_affineOpens_tensorPullback_baseChange`.

All statement dependencies' node statements and recorded declarations were read.
The three cubical theorem proof dependencies currently have no usable Lean record in
the read clone, so they supply the docstring's proof plan but cannot yet be imported.
No downstream prerequisite was used to define the canonical maps in this delivery.
The other two proof dependencies are available and imported. The CompactObject
example requested by the brief is now a withdrawn module; its node points to the
identical upstream `WeilConjectures.CategoryTheory.CompactObject` definition.

Edge cases checked before and after drafting:

- The empty base is excluded by integrality in the node and Lean alike. Consequently
  a dense V is nonempty; no extra nonempty hypothesis is added.
- Empty covering members are allowed and require no B. An empty index set cannot
  cover integral T; the displayed cover equation enforces this.
- V = T is allowed. The result permits exponent 1, and no properness of all of H is
  assumed when V is smaller.
- Rank-zero torus (the abelian case), positive toric rank and the zero-dimensional
  trivial group are all covered by the existing semiabelian predicate.
- n = 0 is excluded from the result by `1 ≤ n`. The helper's degree-zero case is
  nevertheless the actual pullback-unit isomorphism, so its recursive definition is total.
- No characteristic, dimension, regularity or DVR hypothesis is added. A normal
  singular affine integral Noetherian base remains in scope.
- Symmetry is an isomorphism of underlying invertible modules, exactly as stated;
  no symmetric linearization, cubical input, or rigidification-compatibility condition
  on the symmetry itself is imposed.
- The overlap equation preserves the specified input r, not merely some trivialization.
  Its target is the same unit module on `(V ⊓ W i).toScheme` on both sides.
- Scheme, coefficient-stalk and geometric-field universes are the existing common u;
  the affine-cover index is `Type u`, with no independent smaller test-field universe.

Searches (2026-10-24):

- `msearch.py ... leanfinder "A positive tensor power of a symmetric rigidified relatively ample line bundle on the abelian dense open of a semiabelian scheme extends locally to an ample line bundle"`: 8 hits, concerning affine localization, quasi-separated schemes, affine limits and affine space. None states this theorem.
- `msearch.py ... leansearch "symmetric relatively ample line bundle extension on a semiabelian scheme"`: 8 hits, on symmetric algebras, linear maps, scalar extension and additive group extensions. None is a line-bundle extension theorem.
- `msearch.py ... loogle '"IsAmple", "IsInvertible"'`: 0 hits.
- `msearch.py ... grep 'Semiabelian|semiabelian|rigidified|symmetric.*ample' AlgebraicGeometry`: 0 Mathlib hits.
- `rg` in `lean/WeilConjectures/AlgebraicGeometry` and `lean/Sheaf/AlgebraicGeometry` for symmetric/ample/extension combinations: the upstream abelian-variety projectivity and isogeny lemmas construct symmetric ample modules on an abelian variety, not the extension in this item. `SymmetricLinePowerProlongation` only extends an unrigidified line without ampleness; `RigidifiedLineBigOpenExtension` only extends to a big open. Neither is an exact match.
- `rg`/the prescribed item-id grep in `lean/WeilConjectures` and `rg` in `lean/Sheaf`: no declaration already carries this item's statement or identifier. The semiabelian-fibre search found the existing definition used here.
- `rg` for all four proposed declaration names in Mathlib, `lean/WeilConjectures` and `lean/Sheaf`: no collision.
- Read `dag/lean_names_upstream.json`; no semiabelian/cubical/rigidified match supplies this theorem.
- Read the current blueprint unit `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and searched that blueprint for semiabelian/cubical/symmetric ample extension. This supporting theorem is not itself the unit's statement. The node's source transparently marks the Raynaud/Moret-Bailly originals as WANTED and its normal formulation as agent responsibility; this delivery does not claim to have read missing originals or silently replace that formulation.

No statement correction, mathematical dispute, new node or dependency repair is made.

## Second reading by Q157

Author's explicit rereading, not an independent review (the dispatch brief assigns
independent review to the maintainer). I reread the node and the entire final module.
The table above matches every assumption, the affine cover, the nonempty-member
qualification, the positive exponent, invertibility, both ampleness clauses and the
rigidified overlap isomorphism. The extension is wholly existential. In particular,
merely asserting a line isomorphism would have lost the rigidification condition;
the final equality is present and uses the induced power and restriction maps.
Finite presentation is expressed by local finite presentation plus quasi-compactness
and the given separatedness, without a stronger properness assumption on H. The
initial elaboration attempt used repeated `simp` calls for the identity section law;
these were replaced by the exact existing `Over.w` law and the usual transparency
options, avoiding the heartbeat failure. One line-length warning was repaired.
The final theorem and three helpers have no automatic implicit variables or `let`
binders in their signatures, and every definition has real data.

## Validation

The final module is compiled only through the prescribed `scompile.py` wrapper.
The local compile overlay once reported ENOSPC; the wrapper automatically confirmed
the statement against the current server sources, where it compiled in 2.8 seconds
with only the subsequently repaired line-length warning. The final clean server compile completed in 3.1 seconds with no errors or warnings.
`deliver2.py Q157 lem-sfb-symmetric-ample-power-extension --no-push` then printed
`OK (dry run): commit 7c0233d7c25 passes the preflight and compiles; nothing pushed`.
The report is included in the final prescribed delivery check and push.
