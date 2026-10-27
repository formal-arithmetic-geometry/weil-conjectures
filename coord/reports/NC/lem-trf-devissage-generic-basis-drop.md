## Worker report

Module: `Sheaf.AlgebraicGeometry.DevissageGenericBasisDrop`.
Declaration: `AlgebraicGeometry.Scheme.Modules.devissage_generic_basis_drop`.
This is a single theorem statement with a `sorry` proof. No new definition, dependency
repair, or statement correction is needed. The original node is changed only in `lean`.

Source read: `literature/stacks-project/flat.tex`, Tag 05HF,
`lemma-existence-alpha`, statement and complete proof. As the node explicitly records,
this uses that proof for any finite-type quasi-coherent module on its smooth target.
Stacks writes a positive rank in the devissage setting; this node allows zero rank
because the generic residue vector space can be zero for an arbitrary module.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Affine schemes Y and B, and their morphism | `{Y B : Scheme.{u}} [IsAffine Y] [IsAffine B] (f : Y ⟶ B)` |
| Smooth morphism | `[Smooth f]` |
| Geometrically irreducible fibres | `[GeometricallyIrreducible f]`; Mathlib `GeometricallyIrreducible.iff_geometricallyIrreducible_fiber` identifies this with geometric irreducibility of every fibre over its residue field. |
| Fixed dimension d ≥ 0 of every fibre | `(d : ℕ)` and `hdim : ∀ t : B, topologicalKrullDim (f.fiber t) = (d : WithBot ℕ∞)` |
| Point b of B | `(b : B)` |
| Arbitrary finite-type quasi-coherent module H | `(H : Y.Modules) (hH : H.IsQuasiCoherentFiniteType)`; the recorded dependency definition is exactly the conjunction of the two Mathlib predicates. |
| Generic point ξ of Y_b | `(ξ : f.fiber b) (hξ : IsGenericPoint ξ Set.univ)` |
| Rank r ≥ 0 and α : O_Y^r → H | Existential `(r : ℕ)` and `α : SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r)) ⟶ H`. Mathlib defines `free` as the coproduct of copies of the structure module. The lift only places the finite indexing type in the coefficient universe. |
| Induced residue map κ(ξ)^r → H_ξ ⊗ κ(ξ) is an isomorphism | `IsIso` of `moduleStalkFunctor.map α` extended by `ModuleCat.extendScalars` along `((f.fiberι b).stalkMap ξ ≫ (f.fiber b).residue ξ).hom`. Here H_ξ means the ambient stalk at `(f.fiberι b) ξ`. The composite is the actual local-ring homomorphism to the fibre residue field, not an arbitrary scalar map. The source is canonically κ(ξ)^r since stalks of a finite free sheaf are free; Mathlib writes scalar extension with the field on the left, canonically symmetric to the node's tensor order. No separately chosen map or isomorphism replaces the map induced by α. |
| Q = coker α, finite type and quasi-coherent | `IsQuasiCoherentFiniteType (X := Y) (cokernel α)` using the actual categorical cokernel, the quotient by the image in the abelian category of module sheaves. |
| Subscript b denotes tensor pullback to Y_b | `f.fiber b` is definitionally `pullback f (B.fromSpecResidueField b)`; pullback of Q is `(tensorPullback (f.fiberι b)).obj (cokernel α)`. |
| Support is exactly the set of nonzero stalks | `∃ Z : Set (f.fiber b), Z = {x | ¬ Subsingleton (...presheaf.stalk x)} ∧ ...`; this equality only names the actual support. A module is zero precisely when its carrier is subsingleton. |
| Proper closed subset, avoiding ξ | `IsClosed Z ∧ Z ⊂ Set.univ ∧ ξ ∉ Z` |
| If nonempty, global dimension strictly less than d | `Z.Nonempty → topologicalKrullDim Z < (d : WithBot ℕ∞) ∧ ...` |
| Dimension at every point of support strictly less than d | Under the same implication, `∀ z : Z, topologicalKrullDimAt z < (d : WithBot ℕ∞)`. Both dimensions are those of the support with its subspace topology. |
| If d = 0 the support is empty | `d = 0 → Z = ∅` |
| No flatness or finite presentation of H | Neither appears among the binders. No Noetherian hypothesis is added. |

Dependency declarations read and reused:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom`.
- `def-weil-affine-spectrum`: the same module's `Spec` and `Spec.map`; the
  fibre uses the chosen spectrum of the base point's residue field.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`. No relative-dimension replacement is assumed.
- `def-pc-geometrically-irreducible`: the recorded
  `Mathlib.AlgebraicGeometry.Geometrically.Integral` imports the exact
  `AlgebraicGeometry.GeometricallyIrreducible` class; its fibre characterization was read.
- `def-kun-dimension`: `WeilConjectures.Mathlib.Topology.KrullDimension`,
  `topologicalKrullDimAt`, and Mathlib `topologicalKrullDim`.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType`,
  `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`, with the underlying
  `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType`.
- `def-pc-module-pullback`:
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` publicly exposes
  `AlgebraicGeometry.Scheme.Modules.tensorPullback` from
  `WeilConjectures.AlgebraicGeometry.TensorPullback`. Its real inverse-image,
  change-of-rings, and sheafification construction is retained.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, and `pullback.snd`.
  `Mathlib.AlgebraicGeometry.Fiber` exposes the definitional abbreviations
  `Scheme.Hom.fiber`, `fiberι`, and `fiberToSpecResidueField` for these objects/maps.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `Scheme.residueField` and `Scheme.residue` for the actual local quotient.
- `def-weil-pbc-module-stalk`: recorded
  `WeilConjectures.Topology.PresheafModuleStalkFunctor`,
  `PresheafOfModules.moduleStalkFunctor`. Its recorded note explicitly directs
  scheme module sheaves to `RingedSpace.moduleStalkFunctor`, used here via
  `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`. Both have the original
  `TopCat.Presheaf.stalk` carrier and the natural stalk map; there is no new stalk notion.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` and the canonical map on
  tensors, supplied through `ModuleCat.extendScalars` in
  `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`. Its map sends `a ⊗ m` to
  `a ⊗ α_ξ(m)`, so it is exactly tensoring the induced stalk map.

All available recorded proof-dependency modules are imported without `public`:
`QuasicoherentFiniteTypeAffine`, `Modules.Tilde`, `Modules.QuasiCoherentCokernelImage`,
`TensorProduct.RightExactness`, `LocalRing.Module`, `LocalRing.ResidueField.Ideal`,
`Modules.TensorPullbackStalk`, `TensorPullbackTilde`, `RingTheory.Support`, and
`Topology.IrreducibleOpenComplementDimension` (full prefixes are in the module).
Other proof dependencies are already public statement dependencies or Mathlib declarations
available from these imports, including the affine-spectrum pullback formula.
The theorem docstring carries all seven proof steps and their DAG citations.

Edge cases checked before drafting and on the second pass:

- H = 0 allows r = 0 and the empty support. More generally a torsion module may
  have zero generic residue fibre, so positive rank must not be required.
- For H = O on the affine line over a field, r = 1 with α the identity works.
  For H = O ⊕ O/(x), r = 1 leaves support {0}, of dimension zero < 1.
- The empty support is permitted for any d; no global dimension inequality is
  required there beyond the node's implication. For d = 0, support is empty explicitly.
- The point b and generic point ξ exclude empty B or empty chosen fibre in exactly
  the same way as the informal statement. No additional nonemptiness binder is added.
- No flatness, coherence, finite presentation, or Noetherian assumption on H or B
  is introduced. The proof uses finite generation and local Nakayama only.
- The field is that of ξ in the fibre; the local ring acting on H is that of its
  image in Y. The displayed composite keeps these distinct.
- A single arbitrary universe u covers schemes and coefficient stalks in every
  size; `ULift.{u} (Fin r)` includes the empty index type.

Searches actually run on 2026-10-24:

1. `msearch.py ... leanfinder`: "For a finite type quasi coherent module on a smooth
   affine scheme with irreducible fibres choose sections basis at generic fibre
   point with cokernel support of smaller dimension". Eight results, including
   `SheafOfModules.IsFiniteType.exists_localGeneratorsData`,
   `localGeneratorsDataOfIsFiniteType`, `QuasicoherentData.localGeneratorsData_generators`,
   and structure-sheaf fraction formulas. None asserts this existence and dimension drop.
2. `msearch.py ... loogle`: "Module.Finite, IsGenericPoint, cokernel".
   Zero hits; diagnostic "unknown identifier 'cokernel'". This query was not
   treated as evidence of nonexistence by itself.
3. `msearch.py ... grep`: `generic.*basis|basis.*generic|cokernel.*support`.
   Zero Mathlib hits.
4. `msearch.py ... leansearch`: "Finite type quasi coherent module smooth irreducible
   fibre generic point choose basis sections cokernel support smaller dimension".
   Eight results, including `Module.supportDim_quotSMulTop_succ_eq_supportDim`,
   `SheafOfModules.generatorsOfIsCokernelFree`, and quasi-coherent finite-presentation
   declarations. None matches; the regular-element support-dimension theorem has
   different hypotheses and objects.
5. `rg -n 'generic.*basis|basis.*generic|lem-trf-devissage-generic-basis-drop'`
   on `lean/WeilConjectures` and `lean/Sheaf`, and the prescribed node-id grep on
   `lean/WeilConjectures`: no existing statement for this node. Related project
   declarations `local_generic_basis_universal_injective` and
   `generic_basis_base_open_universal_injectivity` concern a prescribed map becoming
   injective and require flatness; they do not produce this map or support drop.
   Searches for `generic.*cokernel|cokernel.*dimension|generic_free|basis_drop`
   similarly found generic-freeness and unrelated cokernel results, not this theorem.

Validation: the prescribed `scompile.py` passed both sandbox and library module modes
for the delivered file, with no errors or non-sorry warnings. The first compile
found only field-notation inference on `cokernel α`; the conclusion now uses the
explicit recorded predicate `IsQuasiCoherentFiniteType (X := Y) (cokernel α)`.
No statement dispute or node fault was found.

## Second reading by NC

The dispatcher brief assigns independent review to the maintainer and forbids starting
another agent. This section records the same worker's second pass, not an independent
review claim. With the node and final file open, I checked the correspondence table
above against each binder and each conjunct. The geometric-irreducibility hypothesis
is equivalent to the node's fibrewise hypothesis by the Mathlib fibre characterization;
the dimension hypothesis quantifies over every point, not just b. The free source
allows zero rank. The residue map uses the ambient stalk and the fibre residue field,
with the canonical scalar map, and is required to be an isomorphism. The exact cokernel
is finite type and quasi-coherent. The named set is exactly the support of its tensor
pullback, is closed and proper, avoids ξ, has both global and pointwise strict dimension
bounds when nonempty, and is empty when d = 0. There are no flatness or finite-presentation
binders. No mismatch or mathematical change was found; the sole compiler repair was
the field notation described above. Every theorem proof is still `sorry`, every variable
and universe is explicitly bound, and there are no helper definitions or extra nodes.
