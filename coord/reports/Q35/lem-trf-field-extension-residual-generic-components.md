## Worker report

The module `Sheaf.AlgebraicGeometry.FieldExtensionResidualGenericComponents` states
`AlgebraicGeometry.Scheme.Hom.field_extension_residual_generic_components`, with
one `sorry` as the whole proof. It includes every clause of the unchanged node.
Three helper definitions specialize existing tensor-product constructions to the
canonical residue-field algebra; their data are fully constructed, with no choice
from an existence assertion and no postponed definitional proof. There are no
new DAG nodes, dependency repairs, or statement corrections.

For readability in this report only, write `g = Spec.map (CommRingCat.ofHom
(algebraMap k L))`, `P = pullback (Z ↘ Spec (.of k)) g`, `p = pullback.fst
(Z ↘ Spec (.of k)) g`, and `z = p w`. These are expanded in the Lean signature;
there are no file-local notations, instances, private abbreviations, or statement
`let` binders.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A field `k`, an arbitrary field `L`, and its specified extension structure:
  `{k L : Type u} [Field k] [Field L] [Algebra k L]`. Nothing requires algebraicity,
  separability, finite dimensionality, finite type, or a specified characteristic.
- A scheme over `k`: `(Z : Scheme.{u}) [Z.Over (Spec (.of k))]`. The structure map
  is the recorded `Z ↘ Spec (.of k)`, not an arbitrary extra morphism.
- The scalar extension and projection are Mathlib's actual `pullback` and
  `pullback.fst`; the pullback's category is explicitly `Scheme.{u}`.
- Any point `w` of `Z_L` is the `w : pullback ...` binder. The expression `p w`
  directly renders the node's abbreviation `z = p(w)`, without adding a point or
  an equality hypothesis.
- `fieldExtensionResidualRing (k := k) (L := L) z` is literally
  `CommRingCat.of ((Z.residueField z) ⊗[k] L)`. Its local algebra in the DEFINITION
  BODY is `(Z ↘ Spec (.of k)).residueFieldAlgebraMap z |>.toAlgebra`. The
  `residueFieldAlgebraMap` is the existing upstream canonical embedding, not an
  extra assumed algebra structure. The left and right helpers are precisely
  `Algebra.TensorProduct.includeLeftRingHom` and `includeRight.toRingHom`, with
  `R := k`, `A := Z.residueField z`, `B := L`.
- The residual-fibre identification is the first conjunct, `∃! e : p.fiber z ≅
  Spec (fieldExtensionResidualRing ... z), ...`. Its two conditions identify
  `e.hom` followed by the spectrum of the left inclusion with
  `p.fiberToSpecResidueField z`, and `e.hom` followed by the spectrum of the
  right inclusion with `p.fiberι z ≫ pullback.snd ...`. These are exactly the
  two residual tensor projections. They characterize the canonical isomorphism
  uniquely by the fibre-product universal property; no arbitrary isomorphism is
  substituted for a canonical one. This is a conclusion, not a hypothesis.
- The equivalence is `w ∈ genericPoints P ↔ p w ∈ genericPoints Z ∧
  p.asFiber w ∈ genericPoints (p.fiber (p w))`. Mathlib defines `genericPoints X`
  as `{x | closure {x} ∈ irreducibleComponents X}`; by the recorded
  `IsGenericPoint x C := closure {x} = C`, this is precisely being generic in
  an irreducible component. `p.asFiber w` is the actual residual-fibre point,
  constructed by Mathlib's inverse fibre homeomorphism. The first conjunct
  identifies this fibre canonically with the tensor spectrum.
- “In this case” is the implication from `w ∈ genericPoints P`. Its first
  conclusion is explicitly `closure {w} ∈ irreducibleComponents P`.
- Every closed immersion and every lift are the conclusion's binders
  `∀ (T : Scheme.{u}) (j : T ⟶ P) [IsClosedImmersion j] (v : T), j v = w → ...`.
  In particular no reducedness, flatness, or finiteness is imposed on `T` or `j`.
- The final two conclusions are `j '' closure {v} = closure {w}` and
  `v ∈ genericPoints T`. The former is the set-theoretic image equality in the
  node; the latter is genericity in an irreducible component of `T`.
- `u` is declared explicitly; all scheme and field data use the common ambient
  universe required by Mathlib's scheme pullbacks. No test-object quantification
  is restricted to a smaller independent universe, and no universe equality is
  imposed between independently specified objects.

Dependency declarations read and used:

| DAG dependency | Module and declaration |
| --- | --- |
| def-weil-field | Mathlib.Algebra.Field.Defs: `Field` |
| def-pc-field-extension | Mathlib.Algebra.Algebra.Defs: `Algebra`, `algebraMap` |
| def-weil-scheme-over-base | Mathlib.AlgebraicGeometry.Over: `AlgebraicGeometry.Scheme.Over` |
| def-pc-fibre-product | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`, `pullback.fst`, `pullback.snd` |
| def-weil-irreducible-components | Mathlib.Topology.Irreducible: `irreducibleComponents` |
| def-sc-generic-point | Mathlib.Topology.Sober: `IsGenericPoint`; its `genericPoints` packages exactly the component-generic condition |
| def-pc-scheme-fibre | Mathlib.AlgebraicGeometry.Fiber: `Scheme.Hom.fiber`, `fiberι`, `fiberToSpecResidueField`, `asFiber` |
| def-weil-residue-field | Mathlib.AlgebraicGeometry.ResidueField: `Scheme.residueField`, `Scheme.Hom.residueFieldMap` |
| def-weil-pbc-module-tensor-product | Mathlib.LinearAlgebra.TensorProduct.Defs: `TensorProduct`; Mathlib.RingTheory.TensorProduct.Basic gives the existing ring structure and inclusions |
| def-weil-affine-spectrum | Mathlib.AlgebraicGeometry.Scheme: `Spec`, `Spec.map` |
| def-weil-closed-immersion | Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion` |

The additional existing canonical map is `Scheme.Hom.residueFieldAlgebraMap` in
`WeilConjectures.ZetaSeries`, read at its definition. Its geometric description is
`Scheme.Hom.specMap_residueFieldAlgebraMap` in `WeilConjectures.PointCount`, also
read: `Spec.map` of this ring homomorphism equals `Z.fromSpecResidueField z`
followed by the structure morphism. Only the defining module is needed publicly.
These helpers belong to the residual-fibre notion already in the item's statement.

Proof-only imports are `Mathlib.AlgebraicGeometry.Morphisms.Flat` (the three flatness
leaves) and `Mathlib.RingTheory.Ideal.GoingDown` (`Algebra.HasGoingDown.of_flat`).
`Fiber` publicly imports the affine pullback and carrier modules, giving
`pullbackSpecIso`, open-pullback compatibility and prime-spectrum components.
The docstring carries all six proof steps with the DAG nodes used, including
`lem-weil-pbc-spec-irreducible-components-minimal-primes`, the affine and open
fibre-product nodes, the field-extension and base-change flatness nodes, and
`lem-sc-flat-going-down`.

Sources inspected locally: `more-morphisms.tex`, lemma-associated-point-specializes
(Tag 0GSI), first two proof paragraphs; `divisors.tex`,
lemma-base-change-relative-assassin (Tag 05DC), particularly its displayed residual
fibre identification. The finite-type assumption of 05DC concerns its associated
point theorem, not the residual tensor identification. The node's proof uses flat
going-down for the more general component-generic assertion; no finite-type
hypothesis is imported from the associated-point statement.

Edge cases checked mathematically before writing:

- Empty `Z` has no `w`; the theorem makes no nonemptiness assumption or conclusion.
- `L = k` reduces to the identity base change and a one-point residual fibre.
- For `Z = Spec ℂ` over `ℝ` and `L = ℂ`, the tensor product has two components;
  neither the fibre nor the scalar extension is assumed irreducible.
- For `Z = Spec k(t)` and `L = k(u)`, the prime `(t-u)` in the tensor ring maps
  to the generic base point but is not component generic. The residual-fibre
  condition is present and prevents the false image-only criterion.
- Purely inseparable extensions can give a nonreduced tensor ring. The statement
  uses its actual spectrum and imposes no reducedness or separability.
- Infinite transcendental extensions, non-Noetherian schemes, and nonreduced closed
  immersions are all admitted. No finite-dimensional or local-finite-type API is
  used to state the result.
- For `j = 𝟙 P`, the image-of-closure assertion is the identity assertion, and the
  source genericity is exactly the assumed component genericity. For a nilpotent
  closed thickening, the same topology gives the same intended conclusion.

Searches (2026-10-24):

- `msearch.py ... leanfinder "A point of a scheme after extension of the base field
  is generic in an irreducible component if and only if its image and its point in
  the residual fibre are generic in irreducible components"`: 8 hits, including
  `genericPoint_eq_of_isOpenImmersion`, `Scheme.SpecToEquivOfField`, and residue-field
  constructions. None states this equivalence or its closed-immersion conclusion.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.Hom.fiber, irreducibleComponents"`:
  OK, zero hits.
- `msearch.py ... grep "generic.*(baseChange|fiber)|irreducibleComponents.*fiber|fiber.*[Ii]so|pullback.*[Tt]ensor" AlgebraicGeometry`:
  OK, 15 hits, including geometric irreducibility, `Spec.fiberToSpecResidueFieldIso`,
  and pullback carrier lemmas. The affine fibre isomorphism requires an affine
  source; it does not state this arbitrary-scheme result.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for generic/base-change,
  generic/fibre, residual/generic and field-extension/generic combinations found
  related generalization and fibre results, but no exact statement. In particular
  `FlatFibreGenericGeneralization` is a different specialization-lifting result.
- `grep -rn "lem-trf-field-extension-residual-generic-components"
  lean/WeilConjectures`: no hits. `rg` of all four proposed full-name suffixes in
  Mathlib/project upstream name records and the two source roots found no clash.
- Searches for the residue-field algebra found and reused the existing upstream
  `residueFieldAlgebraMap`; searches and source reads for tensor inclusions found
  and reused Mathlib's inclusions. The specialized helpers do not redefine fields,
  generic points, components, tensor products, fibres, or scheme pullbacks.

No STATEMENT-DISPUTED flag: the unchanged statement passes the cases above.
The only postponed proof is the named theorem listed above.

## Second reading by Q35

A second pass by this worker, not an independent agent: the dispatcher explicitly
prohibits starting other agents and provides independent maintainer review after
delivery. I reopened the unchanged node and the module and checked the correspondence
listed above. In particular I checked both directions of the equivalence, the
actual `asFiber` point, both projection equations specifying the canonical
identification, the unconditional placement of that identification, the conditional
component/closed-immersion clause, and universal quantification over all lifts.
The initial compile required explicit scheme-category annotations and explicit
`k`, tensor-factor arguments for the inclusion helpers; those were corrected.
The mathematical statement, its hypotheses, and all node fields other than `lean`
are unchanged. All helper bodies are genuine tensor constructions; no auxiliary
postponed theorem, private copy of a dependency, or arbitrary chosen map is used.

## Validation

All compilation and delivery checks use the prescribed `scompile.py` and
`deliver2.py` wrappers. Compilation errors during development were repaired; the
final `scompile.py` run exited 0, with no errors or warnings. The library-path
compile completed in 2.7 seconds. `deliver2.py ... --no-push` then printed
`OK (dry run): commit 873440a8f42 passes the preflight and compiles; nothing pushed`.
The node-diff check confirms that only `lean` changed; every delivered Lean line
is at most 100 characters.
