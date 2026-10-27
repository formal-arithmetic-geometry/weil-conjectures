## Worker report

The module `Sheaf.Paper.QcqsLisseStratifiedIntegralLattices` states
`AlgebraicGeometry.ProEtale.qcqs_lisse_stratified_integral_lattices`, with its entire
proof `sorry`. It introduces no definitions. The node is changed only in `lean` and by adding landed definition owners to `stmt_deps`.

Hypothesis and clause correspondence:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The chosen algebraic closure is the existing
  `PadicAlgCl ℓ`. `E : PadicAlgCl.FiniteIntermediateField ℓ` is precisely a finite
  intermediate extension inside that closure, with its inherited norm topology.
- The first conjunct treats `Λ = underline E`, using
  `Profinite.continuousMapRingObj E.1`. The second uses
  `Profinite.padicAlgClRingObj ℓ`, the finite-subextension-valued condensed ring,
  whose sections are not all continuous maps into the algebraic closure.
- `T : Scheme.{u}` is arbitrary; `[CompactSpace T] [QuasiSeparatedSpace T]` say qcqs.
  There is no Noetherianity, dimension, base field, characteristic or invertibility
  hypothesis. The site remains `Scheme.ProEt.topology T`, with objects in `u+1`,
  morphisms in `u`, and abelian coefficients in `u+1`. The number field coefficients
  themselves are small, as in the existing fixed algebraic-closure coefficient API;
  no relation on scheme universe `u` is imposed.
- All modules are the recorded internal `CategoryTheory.Mod` of abelian sheaves,
  over `condensedRingObj`, the actual inverse image from the condensed point.
  `IsLisseCoefficientModule Λ M` is the recorded pro-etale covering predicate:
  its coefficient-module pullback is `Mod.IsFree`, a finite biproduct of the regular module.
  It permits different finite ranks on different members of a cover.
- In the finite-field conjunct we substitute the explicitly permitted choices
  `F = E`, `L = M` from the start. The first scalar isomorphism is the canonical
  `Mod.extendScalarsId`, so no redundant existential field or arbitrary first
  comparison is introduced. This conjunct is exactly the conclusion with those
  specified choices. The requested induced Λ-scalar map is already the displayed
  `Mod.extendHom` because Λ = F.
- In the closure conjunct, `∃ F` ranges over all finite intermediate fields,
  `∃ L` gives the lisse finite-field model, and `∃ e` is the actual isomorphism
  `(Mod.extendScalars (coefficientMap ... T)).obj L ≅ M`.
- Each `S : Scheme.FiniteLocallyClosedStratification T` includes a finite `Fin S.n`
  partition, locally closed strata, pairwise disjointness, covering, schemes
  `S.domain s`, and genuine immersions `S.immersion s` with those exact images.
  The separately required `∀ s, Topology.IsConstructible (S.stratum s)` enforces
  constructibility; it is not inferred from being locally closed on a qcqs base.
- On each stratum `B` is a module over the actual pulled-back
  `Profinite.padicIntegersRingObj ℓ F.1`. This is continuous functions into the
  valuation ring with its subspace norm topology, as defined in upstream EllAdic.
  `IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ F.1) B` imposes lissity
  (with E in place of F in the first conjunct).
- `ι : B ⟶ (Mod.comap (padicIntegersToPadicSubfield ...)).obj (...)` with `Mono ι`
  is an embedded integral submodule of the restricted L, not an abstract model.
  The target `(...)` is `(CondensedRing.upperStar ... (S.immersion s)).obj L`.
- `IsIso (Mod.extendHom ... ι)` says the scalar extension of that very inclusion
  is an isomorphism. This does not replace the inclusion-induced map with an
  unspecified isomorphism.
- The last `IsIso` is imposed on the actual composite: canonical tensor
  transitivity `Mod.extendScalarsComp`, scalar extension of `Mod.extendHom ... ι`,
  the canonical inverse-image/scalar-extension comparison `CondensedRing.pullIso`,
  and pullback of `e.hom`. Its domain is Λ extended directly from A_F and its
  codomain is M restricted to the stratum. Thus the final clause is included.
- The preliminary constructibility, D_ctf, and ordinary uncompleted derived
  conventions specify the ambient setting; this heart-level theorem neither
  assumes constructibility nor asserts a derived condition. Their recorded modules
  are publicly imported unchanged.

Dependency declarations used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` publicly imports the
  recorded coefficient extension constructions, including degree, spectral
  absolute value and valuation ring. The concrete finite subfields and their
  normed integer coefficient rings use the existing upstream
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic` and
  `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization`:
  `Profinite.padicIntegersRingObj`, `padicIntegersToPadicSubfield`, and
  `padicIntegersRingObjToContinuousMapRingObj`.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing`, `Profinite.padicAlgClRingObj`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, and `upperStarFromPoint`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPushforward` and
  `CondensedRing.moduleObjectDerivedPullback` (ambient convention, not a new
  derived construction).
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `IsConstantModelConstructible`, `HasFiniteConstantLocalModel`,
  `ConstantModelConstructibleFiniteTor` (ambient convention only).
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `QuasiSeparated`, `quasiSeparated_iff_quasiSeparatedSpace`.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification`.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`:
  `AlgebraicGeometry.ProEtale.IsLisseCoefficientModule`, owned by
  `def-sfb-lisse-coefficient-module`, renders all five lisse conditions.
- `Sheaf.Paper.ContinuousLocallyFreePullback` is a plain proof-dependency import.
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`:
  `Mod.extendScalars`, `Mod.comap`, `Mod.extendHom`, `Mod.extendScalarsId`,
  `Mod.extendScalarsComp`; the morphism `extendHom` is the inverse of the
  extension/restriction adjunction's hom equivalence.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension`:
  `Profinite.padicSubfieldRingObjToPadicAlgCl`;
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`:
  `coefficientMap`, `CondensedRing.pullIso`, and `CondensedRing.upperStar`
  through its defining imports.

Every recorded proof dependency is imported as a plain import. The lisse definition
owner is publicly imported because it occurs in the statement.
`lem-sfb-embedded-lattice-coefficient-comparison` has no Lean record on the read
base, so its not-yet-stated module is not imported. It is a proof prerequisite,
not a notion required to type this statement; its source proof step is retained
in the docstring. No dependency module is needed for this delivery.

Edge cases checked before drafting: on empty T one can use the empty
stratification (the closure case can choose E and its zero model); no Nonempty
binder excludes this. Rank zero is the finite free object with zero summands,
so B = 0 and its zero-to-zero inclusion is monic and rationalizes invertibly.
No fixed rank binder excludes varying ranks. Constructibility is explicit even
on non-Noetherian qcqs T. No global lattice is asserted: the node's nodal-curve
example is therefore respected. The finite-extension case does not enlarge E.

Searches (2026-10-23):

- `msearch.py ... leanfinder`: "A lisse rational l adic module on a quasi compact
  quasi separated scheme admits integral lattices on a finite constructible
  locally closed stratification". Eight hits, concerning qcqs regular functions,
  integral schemes, finite-type module generators and locally Noetherian schemes;
  no match.
- `msearch.py ... loogle`: "Mod.extendRestrictAdjunction, LocallyFree,
  CompactSpace, QuasiSeparatedSpace". Zero hits; Mod.extendRestrictAdjunction is
  unknown to the Mathlib-only service. The actual project definition was read.
- `msearch.py ... grep`: "stratified.*lattice|lisse.*lattice|integral.*lattice".
  Five Mathlib hits concern number-field lattice bases, root systems and
  integration; none concern rational coefficient module sheaves.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` with
  `stratified.*lattice|lisse.*lattice|Stratified.*Lattice` found the narrower
  `StratifiedLattice` (standing finite-type base),
  `TopologicalStratifiedLisseLattices` (Noetherian topological space), and the
  supplied-partition refinement tree. All signatures were read; none states
  the arbitrary qcqs lattice-existence assertion. Searching the item id in
  `lean/WeilConjectures` found no match.

Sources read: the current `literature/blueprint/latest` stratified-lattice unit
statement and proof, finite-descent-lisse assertion (1), and Stacks
`etale-cohomology.tex`, lemma-etale-stratified-finite (Tag 03S0). The source's
finite-stratification/trace route supports the node's qcqs refinement. No
statement correction or STATEMENT-DISPUTED flag is needed.

Validation: scompile.py compiled the sandbox and named library module cleanly
(10.4 s and 9.8 s), with no error or non-sorry warning. During the compiler check,
the live canonical `pullIso` component required `.hom` in the displayed composite;
the direction was corrected before this successful compile. All universes and
variables are explicit; there are no local definitions, local notation,
instances or additional theorem declarations.

## Second reading by Q126

The dispatcher explicitly prohibits starting another agent, so this is a second
self-reading, not a claim of independent review; the maintainer's independent
reader remains the external review. I reopened the node and the final Lean file
and compared each clause: the only base conditions are qcqs; the two conjuncts
have exactly the two coefficient rings; the finite case keeps M over E; the
closure case chooses one F and one lisse L before choosing S; constructibility
is separate from locally closedness; each B has a genuine monic inclusion; both
rationalization and the final induced closure map are expressed as invertibility
of the actual maps. I also checked the finite and empty indexing, lack of a fixed
rank, and lack of a Noetherian or characteristic assumption. No mismatch was
found in this second reading and no mathematical statement was changed. The
canonical pullIso direction was the earlier typing repair already described.


## Repair of return H4 (head 5434b1738be2)

The initial saved-packet dry run passed at 2dc03bc782e. The saved node differs from
current main only in its Lean attachment, so no unrelated main-branch changes
needed reconciliation. This repair nevertheless addresses the independent H4
finding: all five occurrences of `CondensedRing.LocallyFree` were replaced by the
recorded `IsLisseCoefficientModule` of `def-sfb-lisse-coefficient-module`, passing
the condensed coefficient ring rather than its pullback. The five occurrences
are, in order: finite-field M, finite-field integral B, closure M, finite model L,
and closure integral B. `CoefficientHeartStratificationDefs` is a public import;
`ContinuousLocallyFreePullback` is now a plain proof import.

The advisory owners are also added to `stmt_deps`: `def-sfb-module-upper-star`
for `CondensedRing.upperStar`; `sk-def-sfb-change-of-scalars` for `extendScalars`,
`comap`, and tensor identity/transitivity; `def-sfb-modobj-extend-restrict-adjunction`
for the inclusion-induced `extendHom`; `def-sfb-integers-to-subfield` for
`padicIntegersToPadicSubfield`; `def-sfb-qlbar-subextension-to-qlbar` for
`Profinite.padicSubfieldRingObjToPadicAlgCl`; and `def-sfb-coefficient-map` for
`coefficientMap`. Their node statements, recorded Lean bindings, full signatures
and source docstrings were read. The import closure already publicly provides
these modules. No definition, theorem, dependency module, or new node was added.
The node's mathematical statement and proof remain unchanged; its Lean signature
is updated verbatim.

Repair self-reading: reopened the owning lisse definition, the node, and the
repaired theorem. Its cover is pro-etale, each pullback is finite free over the
pulled-back coefficient ring, and the ranks may vary and be zero. Thus the five
conditions express precisely the existing node's lissity for M, B, L, B. The
qcqs hypotheses, order F/L/e/S, both coefficient cases, constructible strata,
monic inclusions, and actual rationalization composites are retained. There is
still exactly one named theorem with its whole proof `sorry` and no new data.

Repair validation (2026-10-23): `scompile.py Q126
lem-sfb-qcqs-lisse-stratified-integral-lattices` compiled the repaired module in
both sandbox and library form (8.7 s and 6.6 s), with no errors or warnings.
The saved signature equals the declaration text verbatim; all five predicates
use the owned lisse notion, there is one sorry proof, and all Lean lines are at
most 100 characters. Only `lean` and additive `stmt_deps` changes occur in the
node copy, and every added definition node has a landed Lean binding.
