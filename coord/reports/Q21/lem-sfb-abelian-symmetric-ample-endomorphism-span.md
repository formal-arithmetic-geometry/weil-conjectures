## Worker report

The module Sheaf.AlgebraicGeometry.AbelianSymmetricAmpleEndomorphismSpan states
AlgebraicGeometry.IsAbelianVariety.symmetric_ample_endomorphism_span. Its only
proof is `sorry`; it introduces no definitions or additional axioms. The accepted
stage-1 split is preserved verbatim. The stage-2 handoff paragraph of
coord/brief-stage2.md explicitly permits this statement delivery despite the
inherited previous worker's stage-1 concern.

Hypothesis and clause correspondence:

- The arbitrary field k is `{k : Type u} [Field k]`. The universe u is explicit.
- A/k is `A : Over (Spec (.of k))`, with `[GrpObj A] [IsAbelianVariety A]`.
  Thus its morphisms are over k, and properness, smoothness and connectedness
  are exactly the fields of the recorded abelian-variety class.
- L and M are actual sheaves of O_A-modules, `L M : A.left.Modules`, with
  `[L.IsInvertible] [M.IsInvertible]` for the two invertibility assumptions.
- Symmetry of each line is respectively `hLsym` and `hMsym`, namely
  `Nonempty ((Scheme.Modules.tensorPullback (ι[A]).left).obj L ≅ L)` and
  the same expression with M. Here `ι[A]` is the group inversion morphism.
  These use the tensor inverse-image functor, not the older module pullback.
- Ampleness of each line is `hLamp : Scheme.Modules.IsAmple A.left L` and
  `hMamp : Scheme.Modules.IsAmple A.left M`, the recorded absolute ampleness
  definition, including quasi-compactness and affine nonvanishing loci.
- The positive integers a and r are `∃ a : ℕ, 1 ≤ a ∧ ∃ r : ℕ, 1 ≤ r ∧ ...`.
  Naturals at least one encode exactly integers at least one, with no omitted case.
- The r endomorphisms are `b : Fin r → (A ⟶ A)` together with
  `(∀ j : Fin r, IsMonHom (b j))`. Over-morphisms enforce k-linearity of
  the scheme maps; IsMonHom enforces compatibility with the group law, so these
  are group-scheme endomorphisms, including noninvertible ones.
- The conclusion is a `Nonempty` isomorphism in `A.left.Modules`, with left side
  `M.tensorPow a`. The right side enumerates exactly the r objects
  `(Scheme.Modules.tensorPullback (b j).left).obj L` using `List.ofFn`, then
  `foldr (fun P Q ↦ P ⊗ Q) (𝟙_ A.left.Modules)`. This is the ordinary finite
  tensor product over O_A. The terminal tensor unit changes only parenthesization
  and the unitor, and adds no geometric factor or condition.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field` (def-weil-field's Mathlib match).
- WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs:
  `AlgebraicGeometry.IsAbelianVariety`.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `tensorPow`, and its
  monoidal structure. This is publicly imported by the recorded Ample module.
- Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction:
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction`, and
  its public upstream `tensorPullback` functor from
  WeilConjectures.AlgebraicGeometry.TensorPullback. The functor has explicit
  tensor-formula data; no new copy or choice is introduced here.
- WeilConjectures.AlgebraicGeometry.Ample:
  `AlgebraicGeometry.Scheme.Modules.IsAmple` (absolute ampleness).
- Mathlib.AlgebraicGeometry.Group.Abelian supplies the group-object interface,
  `GrpObj`, inversion, and `IsMonHom` used to specify the endomorphisms.

The already-stated proof dependencies are imported with ordinary, nonpublic
imports: Mathlib.LinearAlgebra.TensorProduct.Basic for the recorded TensorProduct
match and WeilConjectures.AlgebraicGeometry.ModulePullbackTensor for
`Scheme.Modules.module_pullback_tensor`. The other three proof inputs
lem-sfb-polarization-calculus-over-field,
lem-sfb-ample-polarization-positive-spectrum, and
lem-sfb-split-real-algebra-positive-squares have no Lean records or Mathlib
matches in the live DAG; they are not statement prerequisites and supply no
objects needed to type this theorem, so no imports can yet be added for them.
Their full four-step argument, including all node names, is in the docstring.

Edge cases checked before writing: the zero-dimensional abelian variety is
allowed, with trivial line modules and witnesses a = r = 1 and the identity
endomorphism. A group scheme over a field cannot be empty (its identity section
exists). The r = 0 and a = 0 cases are expressly excluded as in the node. No
algebraic closedness, perfection, characteristic-zero, positive-dimension,
isogeny, or automorphism assumption is imposed. Arbitrary characteristic,
including characteristic two, is retained: symmetry means pullback along the
actual inverse morphism. Naturals do not exclude any positive integer. The
finite fold uses the existing tensor product, exactly as the project's
InvertiblePullbackTensor module already renders finite families.

Searches actually run with msearch.py for this group and item:

- leanfinder: "For symmetric ample line bundles L M on an abelian variety a
  positive tensor power of M is a tensor product of endomorphism pullbacks of L".
  Eight hits: scheme pullback tensorCongr identities, TensorPower and tensor
  equivalence powers. None states this geometric theorem.
- leansearch: the same query. Eight tensor-power, tensor-equivalence and symmetric
  tensor algebra hits; none states the theorem.
- loogle: `"AbelianVariety", "pullback"`. Zero hits.
- grep: `symmetric.*ample|ample.*endomorphism|Rosati`, subdirectory
  AlgebraicGeometry. Zero Mathlib hits.
- rg in lean/WeilConjectures and lean/Sheaf for
  `symmetric.*ample|ample.*endomorphism|endomorphism.*span` found the upstream
  symmetric-ample existence and symmetrisation results in AbelianVariety/Projective,
  and its use in Isogeny. Reading their signatures shows that they do not assert
  generation of M by endomorphism pullbacks of a prescribed L.
- The item id search in lean/WeilConjectures had no hits. The proposed theorem
  name search in Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json
  had no hits.

Source audit: the Raynaud PDF named by the node is absent locally, as the
accepted stage-1 report and proof_origin already record. I read the available
Milne AV PDF's Rosati section and the latest blueprint's symmetric-ample context;
this statement requires no source-based correction and changes no hypothesis.
No STATEMENT-DISPUTED finding and no new nodes or dependency repairs.

## Second reading by Q21

No second reading by another worker: the dispatcher brief prohibits starting
other agents and requires direct delivery. The maintainer's independent review
is the review, as also recorded by the delivery wrapper since 2026-10-17.
