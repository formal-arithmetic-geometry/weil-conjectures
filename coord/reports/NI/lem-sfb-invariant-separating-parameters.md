## Worker report

The module `Sheaf.FieldTheory.InvariantSeparatingParameters` states
`Algebra.exists_invariant_separating_parameters`, with `sorry` as its only proof.
It introduces no definitions and changes only the item's `lean` record. The live
stage-1 split reviewed for NK is retained verbatim; that split is not a Lean
statement and does not finish stage 2. The sandbox was empty at this retry.
No repair note exists for the item.

### Exact correspondence

- Fields k and E and their specified inclusion: `(k : Type u) (E : Type v)`
  with `[Field k] [Field E] [Algebra k E]`. The inclusion is `algebraMap k E`,
  automatically injective for fields. The fields have independent universes.
- E/k finitely generated as a field extension: `hfg :
  (⊤ : IntermediateField k E).FG`. This is generation of the whole field by a
  finite set, not finite generation as a k-algebra.
- d is the transcendence degree: `(d : ℕ)` and
  `hd : Algebra.trdeg k E = (d : Cardinal)`. Finite generation makes this
  natural-number presentation equivalent to the node's d.
- For every extension field K/k the commutative tensor-product algebra is a
  domain: `hgeom : ∀ (K : Type (max u v z)) [Field K] [Algebra k K],
  IsDomain (E ⊗[k] K)`. Mathlib's `RingTheory.TensorProduct.Basic` provides
  exactly the multiplication `(a ⊗ b)(c ⊗ e) = ac ⊗ be`. The testing universe
  contains both original field universes and an arbitrary enlargement z; it is
  not an unrelated smaller universe in which no test extension need exist.
  This is the project's all-extension-fields convention: field/tensor failures
  are detected over small subextensions and persist under faithful field base
  change, so larger extension fields are not mathematically excluded.
- Finite group: `(H : Type w) [Group H] [Finite H]`, with independent universe w.
- Actions by field automorphisms: `ρk : H →* (k ≃+* k)` and
  `ρE : H →* (E ≃+* E)`. A monoid homomorphism supplies the identity and
  composition laws; a ring equivalence between fields is a field automorphism.
- Compatibility of the actions: `hcompat : ∀ (h : H) (a : k),
  ρE h (algebraMap k E a) = algebraMap k E (ρk h a)`.
  In particular, E's automorphisms are not required to fix k pointwise.
- No faithfulness: neither action homomorphism has an injectivity hypothesis.
- There are d parameters: `∃ t : Fin d → E`.
- Each parameter lies in E^H: `(∀ (h : H) (i : Fin d), ρE h (t i) = t i)`.
  This is the node's displayed membership condition directly, without creating
  another fixed-field definition or imposing a different action on the subfield.
- Algebraic independence over k: `AlgebraicIndependent k t`. This is injectivity
  of multivariable polynomial evaluation, equivalently no nonzero polynomial
  vanishes, precisely as the node explains.
- The subfield k(t₁,…,t_d): `IntermediateField.adjoin k (Set.range t)`.
  Its construction is the subfield closure of the image of k union the family,
  hence the intersection/minimal generated subfield of the dependency node.
- Finite-dimensionality of E over that exact subfield:
  `FiniteDimensional (IntermediateField.adjoin k (Set.range t)) E`.
- Separability of the extension over the same subfield:
  `Algebra.IsSeparable (IntermediateField.adjoin k (Set.range t)) E`.
  This class says every minimal polynomial is separable, and entails algebraicity.
- Empty family: there is no positivity assumption on d; `Fin 0` is empty.

### Recorded dependency declarations used

Read each dependency's full statement and its recorded Lean signature/docstring.
All five statement dependencies have usable Mathlib interfaces:

- `def-weil-field`: `Field` in `Mathlib.Algebra.Field.Defs`.
- `def-pc-field-extension`: `Algebra` in `Mathlib.Algebra.Algebra.Defs`.
- `def-kun-transcendence-degree`: `Algebra.trdeg` in
  `Mathlib.RingTheory.AlgebraicIndependent.Basic`, and `AlgebraicIndependent` in
  its public dependency `Mathlib.RingTheory.AlgebraicIndependent.Defs`.
- `def-weil-pbc-transcendence-basis`: its Mathlib match is `IsTranscendenceBasis`
  in `Mathlib.RingTheory.AlgebraicIndependent.Defs`. Here its generated-subfield
  part is used via `IntermediateField.adjoin` in
  `Mathlib.FieldTheory.IntermediateField.Adjoin.Defs`; the conclusion explicitly
  states independence and finite separability, as the item itself does, rather
  than adding a redundant transcendence-basis clause.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable` in
  `Mathlib.FieldTheory.Separable`.

The public imports expose the statement's Mathlib definitions. Plain proof
imports cover all currently stated proof dependencies: fixed-field Galois
results (`Galois.Basic`), algebraic finite generation (`IntermediateField.Adjoin.Basic`),
finite-dimensional subspaces, tower transcendence degree (`TranscendenceBasis`),
flat tensor injections (`Flat.Basic`), perfect-field separating bases
(`SeparablyGenerated`), separable towers (`SeparableDegree`), and independence
under algebraic scalar extension (`AlgebraicClosure`). The three project proof
imports are `Sheaf.RingTheory.GeometricReducednessSeparableScalarRestriction`
(`Algebra.forall_isReduced_tensorProduct_iff_of_isSeparable`),
`WeilConjectures.FieldTheory.GeometricallyReducedExtensionSeparable`
(`Algebra.isSeparableExtension_of_forall_isReduced_tensorProduct`), and
`WeilConjectures.FieldTheory.SeparableExtension`
(`Algebra.IsSeparablyGenerated`, `Algebra.IsSeparableExtension`). Their source
signatures/docstrings were read. No duplicate helper or dependency module is needed.
The theorem docstring contains every one of the nine DAG proof steps, including
the explicit orbit-coefficient field, scalar restriction, flat tensor inclusion,
and the final Bézout identity.

### Sources and edge cases

Read the publisher PDF of de Jong, *Families of curves and alterations* (1997),
Lemma 5.2, pp. 612–613:
https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf . The proof selects invariant
parameters for the pencil. The DAG explicitly records its full-basis algebraic
formulation as an agent formulation, with the nine-step proof retained unchanged.
The local Stacks and Mathlib interfaces provide its stated algebraic ingredients.
No source-based statement correction was needed.

Checked d=0: the family and invariance/independence conditions are empty, the
adjoin is k, and the assertion is finite separability; geometric integrality
actually forces such an algebraic extension to be trivial. Checked E=k with
nontrivial actions on k: the compatibility equation permits exactly those
semilinear actions and the empty family works. Checked the trivial group and
nonfaithful actions: no assumption excludes them. Checked positive-characteristic
wild translation on k(u), with u ↦ u+1: u^p-u is invariant and gives a degree-p
separable extension (derivative -1), so neither tameness nor invertibility of
|H| was silently assumed. Checked a Frobenius action on finite-field constants
in k(u), fixing u: the statement permits a nontrivial base-field action.
No perfectness, characteristic, or lower bound on d is added.

### Searches made on this retry

All remote searches used the prescribed `msearch.py NI
lem-sfb-invariant-separating-parameters` interface on 2026-10-22.

- LeanFinder query: "A finitely generated geometrically integral field extension
  with a finite semilinear group action admits invariant separating transcendence
  parameters". Eight hits included `FixedPoints.isSeparable`, fixed-field Galois
  facts and invariance integrality; none selects a separating invariant family.
- Loogle query: `IsTranscendenceBasis, fixedField`. Zero hits, with the service
  reporting unknown identifier `fixedField`; not treated as conclusive alone.
- Mathlib grep query:
  `fixedField.*(Separ|[Tt]ranscend)|([Ss]epar|[Tt]ranscend).*fixedField`,
  restricted to `FieldTheory`. One hit in `Galois/Basic.lean:423`, a separable-tower
  argument, not this statement.
- LeanSearch query: "A finite semilinear group action on a finitely generated
  geometrically integral field extension has an invariant separating transcendence
  basis". Eight hits: fixed-field Galois facts, `IsTranscendenceBasis`, ordinary
  separating-basis existence over perfect fields and related facts. No exact match.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for
  `invariant.*[Ss]eparat|[Ss]eparat.*invariant|lem-sfb-invariant-separating-parameters`:
  the equivariant curve-pencil consumer cites this node in its proof; no theorem
  states it. Other hits concerned unrelated separation/invariance.
- `rg` for the proposed full declaration name in Mathlib, both project source
  trees and `dag/lean_names_upstream.json`: no hit. The related landed module
  `SeparatingTranscendenceBasisFiniteSubextension` was read: it only descends finitely
  many coefficients of an already supplied separating basis, with no group action.

### Validation

`scompile.py NI lem-sfb-invariant-separating-parameters
lean/Sheaf/FieldTheory/InvariantSeparatingParameters.lean` passed the sandbox and
library-module compiles in module mode (3.5 s and 2.3 s respectively), with no
errors or warnings reported. Every variable and universe is explicitly bound.
No interactive/global build, live source edit, or direct Git command was used.
No disputed statement or dependency fault was found.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
