## Worker report

Item: lem-sfb-log-cotangent-characteristic-quotient, group Q35, stage 2.
Module: `Sheaf.AlgebraicGeometry.LogCotangentCharacteristicQuotientTrivialBase`.
Declaration:
`AlgebraicGeometry.EtaleLogHom.existsUnique_logCotangent_characteristicQuotient_of_trivialBase`.
The only new declaration is this theorem with proof `sorry`. No definitions or
proofs are introduced. Its docstring contains all seven steps of the DAG proof.

The preceding worker mistook a stage-1 completion for completion of this assignment.
The ledger entry at 2026-10-22 05:52 records NN's reviewed proof-plan split; the
current node has no `lean` record. This delivery leaves that reviewed proof intact
and supplies the stage-2 statement, rather than resplitting it.

Hypothesis and clause correspondence:

- The field F is `{F : Type u} [Field F]`.
- The locally Noetherian fs log scheme (X,M) is
  `(X : FineSaturatedLogScheme.{u})`. Its existing fields supply precisely the
  local Noetherianity and fine saturated charts; M is `X.logStructure`.
- The trivial log field is presented by
  `(N : EtaleLogStructure (Spec (.of F))) (hN : N.IsFineSaturated)` with
  `htriv : N.trivialityLocus = Set.univ`. The log unit axiom and vanishing of
  every characteristic stalk identify N with the sheaf of regular units. This is
  a presentation of the specified trivial log structure, not a restriction on F
  or a choice of unrelated maps. The condition is not vacuous: the standard log
  point has nontrivial characteristic and fails it. `hN` is the fs field of the
  required base object; trivial log structures have charts by the unit monoid.
  Local Noetherianity of `Spec F` is synthesized by `inferInstance`, so no
  additional Noetherian hypothesis is imposed on the field.
- The given log morphism is
  `f : EtaleLogHom X ⟨Spec (.of F), inferInstance, N, hN⟩`. It uses the
  recorded relative-test-object presentation and all its compatibility equations.
- The geometric point is `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and
  `t : Spec (.of Ω) ⟶ X.scheme`, with no identification of residue field and Ω.
- The actual geometric local ring A is `strictLocalRing X.scheme t`, the
  ring-valued pointed-etale colimit used by the differential and log-stalk APIs.
- The residue field k is the existing `logCotangentResidue t`: A modulo the
  ideal spanned by nonunits. For local A this ideal is its unique maximal ideal,
  so this is exactly A/m_A. The locality proof is part of the node's proof plan,
  not an extra local-ring hypothesis. Linear maps require only the available
  commutative-ring structure of this explicitly constructed residue quotient.
- The characteristic monoid is the dependency's `X.logStructure.characteristic t`,
  definitionally `Associates (X.logStructure.stalk t)`. It identifies precisely
  elements differing by a unit. Its group completion C is
  `Additive (Algebra.GrothendieckGroup (X.logStructure.characteristic t))`.
  `Additive` changes notation from multiplicative to additive, without changing
  the group or choosing another group completion.
- The relative differential module is `f.LogDifferential t`, the recorded actual
  quotient by additive, Leibniz, logarithmic, structural and all neighbourhood
  base relations. The source `LogCotangentTarget f t` unfolds to
  `TensorProduct A (logCotangentResidue t) (f.LogDifferential t)`, hence k tensor_A ω.
- The target is `TensorProduct ℤ (logCotangentResidue t) (Additive (...))`, hence
  k tensor_Z C, with its standard scalar action on the first factor.
- The map is explicitly quantified as a `→ₗ[logCotangentResidue t]` linear map.
  `Function.Surjective π` is the required surjectivity.
- For every `m : X.logStructure.stalk t`, the first formula sends the tensor of
  `f.logDLog t m` with 1 to the tensor of 1 with
  `Additive.ofMul (Algebra.GrothendieckGroup.of (Associates.mk m))`.
  This is exactly the canonical class [m], through the quotient by units first.
- For every `a : strictLocalRing X.scheme t`, the second formula sends the tensor
  of `f.logD t a` with 1 to zero.
- The map is defined on the actual differential quotient and its actual scalar
  extension, and the right-hand formula uses the actual characteristic quotient.
  Existence therefore asserts well-definedness for all differential and unit
  relations, not merely for chosen representatives or a free module.
- The `∃!` asserts the canonicity already in the node: the prescribed symbols
  generate, so the two formulas determine the map uniquely. Including
  surjectivity in its predicate gives the same unique map, since the prescribed
  characteristic symbols generate its target.
- No `IsLogSmooth`, regularity, perfection, chart, chosen basis, finite-type or
  freeness hypothesis is present. All universes and variables are explicit and
  `autoImplicit` is disabled.

Dependencies used (their declarations and docstrings were read):

- `Mathlib.Algebra.Field.Defs`: `Field`, the Mathlib match of def-weil-field.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`:
  `FineSaturatedLogScheme`, `EtaleLogStructure`, `EtaleLogHom`,
  `EtalePrelogStructure.stalk`, `EtaleLogStructure.characteristic`,
  `EtaleLogStructure.trivialityLocus` and their structural fields.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`: `pointedEtaleStalk`,
  `pointedEtaleStalkDiagram`, `pointedEtaleGerm`; the imported log stalk uses
  precisely this interface. The ring colimit is `strictLocalRing` from
  `Sheaf.AlgebraicGeometry.LogRegularPair` as used by these definitions.
- `Sheaf.AlgebraicGeometry.LogDifferentialStalk`:
  `EtaleLogHom.LogDifferential`, `logDifferentialRelations`, `logDLog`, `logD`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, `TensorProduct.mk`
  and pure tensors; `Basic`: `TensorProduct.lift` and `TensorProduct.ext'`;
  `Tower`: the recorded scalar-extension convention of `LinearMap.baseChange`
  and the tensor product's canonical left module structure.
- `Sheaf.AlgebraicGeometry.LogCotangentComparison`:
  `EtaleLogHom.logCotangentResidue`, `EtaleLogHom.LogCotangentTarget`.
  Its already landed owning node def-per-log-cotangent-comparison is added to
  stmt_deps, as the standing brief allows for existing landed dependencies.
  Neither this dependency node nor its module is modified or copied.
- The remaining stated proof dependencies are imported without `public`:
  `WeilConjectures.AlgebraicGeometry.StrictHenselization`,
  `Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility`,
  `WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization`, and
  `Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic`. Their intended inputs are
  `Scheme.strictHenselizationRing`, `strictHenselizationLocalStructure`,
  `Scheme.AffinePointedEtaleNeighborhood.initial_ι`, and
  `IsLocalRing.notMem_maximalIdeal`, as named in the proof plan.

Source check: read the local ILO PDF with `pdftotext -f 142 -l 143`, corresponding
exactly to printed pp.136--137. Map (1) is the residue tensor of log differentials
onto the relative characteristic group, prescribed on dlog symbols; the next
page explicitly asserts surjectivity. With trivial base, the base log image
consists of units, so its relative characteristic group is C here. The seven
relation checks in the reviewed node establish that this map does not require
log smoothness; the preparation lemma's further conclusions do require it.

Edge cases checked mathematically before writing:

- Trivial source log structure: C is zero; the zero map onto zero is surjective,
  even if the ordinary differential fibre is nonzero. No injectivity is claimed.
- Standard log point with characteristic N^r over an algebraically closed F:
  the map sends its r logarithmic basis vectors to the r characteristic basis
  vectors; r = 0 is included.
- A log coordinate which becomes a unit at t has zero characteristic class;
  its dlog is killed because it is the unit multiple of an ordinary differential.
  A nonunit coordinate has structural coefficient with zero residue.
- Arbitrary characteristic and imperfect F: no separability or perfection is
  imposed. All base-neighbourhood relations from LogDifferentialStalk remain
  present. The actual residue field need not be the chosen geometric field Ω.
- Empty X: there is no t, so the universally parameterized pointwise assertion
  adds no assertion at a nonexistent point.

Searches for an existing declaration:

- `msearch.py ... leanfinder` with query "The logarithmic differential fibre over
  a trivial log field surjects onto the residue field tensor the group completion
  of the characteristic monoid": eight hits, concerning ordinary Kaehler or
  algebra-extension cotangent modules, none for log structures.
- `msearch.py ... loogle` with query `"LogDifferential", "characteristic"`:
  zero hits.
- `msearch.py ... grep` with query
  `logDifferential|logCotangent|characteristicMonoid`: zero Mathlib hits.
- `msearch.py ... leansearch` with query "Logarithmic cotangent space maps onto
  the residue field tensor the characteristic group of a log structure": eight
  hits, all ordinary cotangent/Kaehler or scheme residue constructions, no match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `characteristic.*[Qq]uotient|[Qq]uotient.*characteristic|logCotangent.*[Ss]urject`
  and the item id found only related log constructions and the citer's proof
  docstring, no statement of this assertion without log smoothness.
- Checked the new theorem name against `dag/lean_names_upstream.json`, Mathlib,
  `lean/WeilConjectures` and `lean/Sheaf`: no collision.
- Read the related lem-per-log-cotangent-characteristic-quotient record. It
  assumes log smoothness and adds further conclusions, and its module is retired.
  It cannot supply this node's unconditional map and is not used.

No statement fault, dispute, new node or dependency repair is needed. Apart from
`lean`, the only changed item field is the addition of the already landed
residue/cotangent definition node to stmt_deps. The stage-1 proof, review, source,
statement and proof dependencies are retained verbatim.

Validation: the prescribed scompile.py compiled this file separately in sandbox
and library module contexts against the live server build, clean in 4.1 s and
4.8 s respectively. The theorem's sole postponed proof is the expected `sorry`.

## Second reading by Q35

A separate reading pass by the same worker checked the final node and final Lean
file against the clause correspondence above. No second agent was started, as
the dispatch brief prohibits it; the maintainer supplies the independent review.
The base really is Spec F with trivial log structure, the geometric residue is
A/m_A rather than Ω, the source uses the existing relative differential quotient,
and the target uses the existing characteristic quotient and its actual group
completion. Both formulas quantify over every stalk element, and surjectivity
and unique characterization are included. In particular the statement does not
inherit the discarded sibling's log-smoothness hypothesis. No mismatch or source
correction was found; no change was made in this pass.
