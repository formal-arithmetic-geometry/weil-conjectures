## Worker report

Restores `lean/Sheaf/RingTheory/JTwoFiniteAlgebraCriterion.lean`, stating
`isOpen_regularLocus_of_finite_algebras` with one postponed theorem proof and no
new definitions. The base node already records this declaration, but its note
says the module was deleted as dead on 2026-10-20. Current source searches confirm
that the declaration and module are absent. Only the node's `lean` field changes;
the mathematical statement, split, and dependency lists are unchanged.

I read the full node and all its statement dependencies, their Lean records and
Mathlib matches, and the corresponding declaration signatures and docstrings.
I read the local Stacks source `more-algebra.tex`, definition-J (Tag 07P7), and
lemma-J-2 (Tag 07PC): the item is exactly implication (3) to (1), with the proof
passing through (4). The theorem docstring gives all six steps of the accepted
node proof, including the explicit finite-domain model construction.

Hypothesis and conclusion correspondence:

- A commutative Noetherian ring R: `(R : Type u) [CommRing R]
  [IsNoetherianRing R]`.
- Every commutative R-algebra B: the universally quantified `(B : Type (max u v))
  [CommRing B] [Algebra R B]` inside `hfinite`. No injectivity or nonzero
  condition is imposed on the algebra map.
- B is finitely generated as an R-module: `[Module.Finite R B]`, meaning the top
  R-submodule has finite generators, rather than finiteness as a set.
- Its prime spectrum: `PrimeSpectrum B`, the Zariski topological space underlying
  the recorded `AlgebraicGeometry.Spec (CommRingCat.of B)`.
- Its local ring at q is regular local:
  `IsRegularLocalRing (Localization.AtPrime q.asIdeal)`. This is the ring clause
  of the regular-scheme dependency's Mathlib match, rather than scheme regularity
  or relative smoothness.
- That subset is open: `IsOpen {q : PrimeSpectrum B | ...}` in `hfinite`.
- Every finite type commutative R-algebra C: the arbitrary binder
  `(C : Type (max u v)) [CommRing C] [Algebra R C] [Algebra.FiniteType R C]`.
  The finite-type dependency records `RingHom.FiniteType`; its algebraMap
  specialization is exactly `Algebra.FiniteType`, by the recorded definition and
  `RingHom.finiteType_algebraMap`.
- The conclusion is precisely
  `IsOpen {q : PrimeSpectrum C | IsRegularLocalRing
    (Localization.AtPrime q.asIdeal)}`.
- The final 'equivalently J-2' sentence names this same universal conclusion; it
  does not add quasi-excellence or a G-ring hypothesis. At v = 0 it is literally
  the open-regular-locus clause of the recorded `IsQuasiExcellent` definition.
  General v allows larger algebra carriers without a universe below R.

Dependency declarations used and imported:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` (its underlying
  Zariski space is used as `PrimeSpectrum`).
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: the dependency's
  `AlgebraicGeometry.IsRegularScheme`; its ring clauses use the unchanged
  Mathlib match `IsRegularLocalRing`, imported directly from
  `Mathlib.RingTheory.RegularLocalRing.Defs`.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` and `Algebra.FiniteType`.
- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent` and `IsExcellent`; J-2 is
  their already defined universal open-regular-locus clause.
- Proof imports: `Mathlib.FieldTheory.PurelyInseparable.Basic`
  (`IsPurelyInseparable`), `Mathlib.RingTheory.Noetherian.Basic`
  (`IsNoetherianRing.of_finite`), and
  `Sheaf.RingTheory.JTwoResidueFieldCriterion`
  (`isOpen_regularLocus_of_residueField_finite_models`). No proof import cycle.

Edge cases checked before writing: R may be the zero ring, in which case every
unital R-algebra is zero and the loci are empty and open. B and C may be zero
without assuming R zero. A regular generic point is used only for the nonzero
domain models inside a field, not for arbitrary B. C = R is permitted (zero
algebra generators). No reducedness, domain, field, characteristic, or nontrivial
ring hypothesis is added. In characteristic zero the model is R/p; positive
characteristic includes exponent n = 1. The field's zero maximal ideal is
allowed an empty generating family. Both test and conclusion algebras live in
`Type (max u v)`, matching the recorded residue-field criterion and avoiding a
vacuous test universe smaller than R. All universes and variables are explicitly
bound, with `autoImplicit false`.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder "A Noetherian ring is J2 if every module finite
  algebra has open regular locus"`: eight hits, concerning Noetherianity and
  Orzech's property; no finite-algebra J-2 criterion.
- `msearch.py ... loogle "IsQuasiExcellent, IsRegularLocalRing"`: zero hits;
  `IsQuasiExcellent` is unknown to the Mathlib service.
- `msearch.py ... leansearch "Every finite algebra has open regular locus implies
  every finite type algebra has open regular locus"`: eight hits on smooth,
  etale, and unramified loci; no criterion for absolute regular loci.
- `msearch.py ... grep "JTwo|IsJTwo|J2Ring|regularLocus"`: zero Mathlib hits.
- Local `rg` of `lean/WeilConjectures` and `lean/Sheaf` for those names,
  `IsQuasiExcellent`, the theorem name, and finite-algebra/regular-locus patterns:
  found `Sheaf.RingTheory.ExcellentRing`, the residue-field criterion, and
  upstream `WeilConjectures.RingTheory.Excellent` defining `IsJ1`, `IsJ2`, and
  `PrimeSpectrum.regularLocus`, but no theorem with the assigned statement.
  The upstream excellence module also defines names already supplied by the
  recorded Sheaf dependency; it is not imported as a second copy.
- `rg` of the blueprint id in `lean/WeilConjectures` and of the declaration in
  `dag/lean_names_upstream.json`: no declaration for this item. The older node
  record is the only previous binding, explicitly marked deleted.

No statement correction, new node, unusable dependency, or disputed statement.

## Second reading by Q102

A separate pass by the same worker (the dispatcher explicitly prohibits starting
other agents) reread the node and completed module clause by clause. The
maintainer's independent review remains required; this section does not claim
an independent agent read it.

The base ring hypotheses match exactly. The finite-algebra premise uses module
finiteness and quantifies every commutative algebra, including noninjective maps
and the zero algebra. The conclusion uses algebra finite type, not module
finiteness. Both regular-locus expressions use the identical prime localization
and absolute regular-local-ring predicate. Universal quantification in C is the
J-2 reformulation, without a spurious quasi-excellence assertion. The common
`max u v` universe agrees with the available proof dependency. Imports cover all
statement and already stated proof dependencies. No extra hypothesis, missing
clause, new notion, or mathematical mismatch was found; no statement change was
needed. The file has one `sorry`, as the whole named theorem proof, and no data
construction. The recorded signature is extracted verbatim from this file.

Validation: prescribed `scompile.py Q102 lem-per-j2-finite-algebra-criterion`
compiled the delivered file in sandbox mode (8.7 s) and its proper library module
mode (5.1 s), with no errors or unexpected warnings.
