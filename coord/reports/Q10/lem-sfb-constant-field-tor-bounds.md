## Worker report

The module `Sheaf.AlgebraicGeometry.ConstantFieldTorBounds` states
`AlgebraicGeometry.Scheme.constant_field_tor_bounds` and
`AlgebraicGeometry.Scheme.constant_field_finite_tor_amplitude_iff`.
Both proofs are exactly `sorry`; there are no new definitions. The node statement
and dependencies are unchanged. The delivery contains only the item node and its
module; the live dependency bindings are retained without changes.

Hypotheses and clauses, with the node and source open:

- Any scheme X: `(X : Scheme.{u})`, with no geometric property instances.
- Any field κ: `(κ : Type (max v (u + 1))) [Field κ]`. There is no finiteness,
  characteristic, Noetherianity, constructibility or enough-points assumption.
- A small representative of the pro-etale site, in an enclosing universe:
  `coefficientProEtaleModelTopology.{u, v} X`. Its category is the existing
  `AsSmall.{max v (u + 1)} X.ProEt`; its topology is the original ProEt topology
  induced along `AsSmall.down`. The model does not restrict its objects or covers.
  The two universes u and v remain independent. Smaller fields may be lifted to
  this enclosing universe, as in the existing constant-coefficient conventions.
- The constant field ring sheaf is
  `ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) κ`,
  definitionally `(constantSheaf J CommRingCat).obj (CommRingCat.of κ)`.
- Module sheaves use `ConstantCompletion.Mod R`, definitionally
  `ringedSiteModules (siteModuleRings R)`, hence Mathlib's `SheafOfModules` over
  the constant sheaf with commutativity forgotten. The Abelian instance is
  Mathlib's, and all required sheafification/locally-bijective instances on this
  small site are already available; no categorical structure is chosen as a
  new hypothesis.
- Every unbounded derived object: `B : ConstantCompletion.D R`, the standard
  Mathlib localization of the category of Z-indexed cochain complexes in Mod R.
  There is no boundedness hypothesis on B.
- Every ordered integer interval: `(a b : ℤ) (hab : a ≤ b)`.
- Left condition: `∀ i : ℤ, i < a ∨ b < i → IsZero
  ((coefficientModelCohomology R i).obj B)`. This explicitly says the cohomology
  sheaf vanishes in every degree outside [a,b], retaining both endpoints.
- Right condition: `HasCoefficientProEtaleTorAmplitude X κ B a b`. Its definition
  is `a ≤ b` and, for every K-flat representative P of B and every module sheaf
  M, `IsZero` of the degree-q homology of the ordinary total tensor P tensor
  M[0], whenever `q < a ∨ b < q`. Here M[0] is exactly
  `(HomologicalComplex.single (ConstantCompletion.Mod R) (ComplexShape.up ℤ) 0).obj M`.
  Thus the right side is the node's second displayed condition, equivalently the
  cited Tor-amplitude predicate; it is not a test only on constant or finite M.
  Universal quantification over K-flat representatives is the existing predicate's
  choice-independent rendering of ordinary K-flat derived tensor, not an extra
  mathematical restriction. K-flat representatives exist by the recorded
  `exists_isKFlatResolutionIndependentCoefficients` theorem.
- The equivalence sign is `↔`, in the same direction as the first displayed
  equivalence. The right predicate's internal ordering is already supplied by hab.
- The final sentence is stated separately: `HasFiniteCoefficientProEtaleTorAmplitude
  X κ B ↔ ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, i < a ∨ b < i → IsZero (...)`.
  Both sides use one common interval, independent of the test sheaf. Bounded
  cohomology is spelled out, without a replacement bounded-derived object.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`, extending `CommRing` and `DivisionRing`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `AlgebraicGeometry.Scheme.ProEt`, `ProEt.topology`; the existing coefficient
  model is in `Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses`,
  publicly reached through the recorded Tor module.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `HasDerivedCategory.standard`, `DerivedCategory.Q`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, `homologyFunctorFactors`; the existing
  `coefficientModelCohomology` abbreviation in the Tor module applies this
  functor to `ConstantCompletion.Mod R` with its standard localization.
- `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude`:
  `HasCoefficientProEtaleTorAmplitude`, `HasFiniteCoefficientProEtaleTorAmplitude`,
  `HasCoefficientModelTorAmplitude`, `coefficientModelCohomology`. The retained
  original `HasProEtaleTorAmplitude` has the smaller A : Type t interface, so
  the recorded coefficient-sized interface is used instead.

The module also imports the stated proof dependencies: `ConstantFieldFlat`
(`SheafOfModules.isFlat_constantFieldModule`), Mathlib's derived `TStructure`
(`exists_iso_Q_obj_of_isGE_of_isLE`, the exact Mathlib match of
lem-sfb-bounded-representative), `BoundedFlatIndependentCoefficients`
(`isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite`),
`KFlatTensorPreservesQuasiIsoIndependentCoefficients`
(`kFlatTensorPreservesQuasiIsoIndependentCoefficients`), `BifunctorShift`
(`CochainComplex.mapBifunctor`), `KFlatResolutionIndependentCoefficients`
(`exists_isKFlatResolutionIndependentCoefficients`), and `CochainTensorUniverses`
(the recorded sheaf tensor monoidal interface). Their signatures and proof
interfaces were read. Proof-only imports are nonpublic.

The source blueprint paragraph explicitly says the residue ring being a field
makes every bounded complex have finite Tor dimension. The expanded node's
five-step proof is transcribed in the first theorem's docstring: flatness;
bounded representatives and degree-zero K-flatness; localization of tensor and
termwise bounds; testing with the unit; existential bounds. The second docstring
states the existential-interval deduction. The local Stacks text supplies the
flatness, K-flat and Tor definitions cited in the node.

Edge cases checked mathematically: a=b, negative endpoints, zero B, arbitrary
infinite-dimensional field-module sheaves, and the empty scheme. The zero object
satisfies both interval predicates, and the finite assertion permits [0,0].
The empty scheme still has its zero module category; no nonempty-site or points
hypothesis occurs. Fields have 0≠1, exactly as def-weil-field, but all characteristics
are allowed. The open endpoints `i<a` and `b<i` leave a and b unrestricted.
Unbounded B remains quantified: its exclusion from any particular finite interval
is a conclusion of failure of both tests, not an omitted case. All variables and
universes are explicitly bound (`set_option autoImplicit false`).

Searches for an existing statement, made through the prescribed msearch.py wrapper:

- LeanFinder: "For sheaves of modules over a constant field sheaf cohomology
  concentrated in an interval is equivalent to Tor amplitude in that interval".
  Eight results, including `DerivedCategory.isLE_iff`, `isGE_iff`, and the bounded
  representative lemmas. None states the constant-field tensor equivalence.
- Loogle: `DerivedCategory, "tensor"`: zero hits.
- Mathlib grep: `torAmplitude|tor_amplitude|constantField|constant_field` under
  CategoryTheory: zero hits.
- LeanSearch: "A derived complex of sheaves over a constant field has Tor
  amplitude in an interval exactly when its cohomology is concentrated in that
  interval". Eight results, including
  `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`; no tensor-bound equivalence.
- rg of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  Tor-amplitude, constant-field and field/Tor combinations located the existing
  Tor predicates, flat-model comparisons, and constant-field flatness; none is
  the requested theorem. `lem-sfb-constant-field-tor-bounds` has no upstream
  source hit. Exact proposed declaration names have no pre-existing hit.
- Read the nearby private `residueTensorVanishing` in
  `Sheaf.Paper.ConstructibleFlatCohomologyTorBound`: it is a private helper and
  not the interval equivalence (its public theorem has extra padic, affine,
  completeness and local-constructibility hypotheses). It is not an exact match.

No STATEMENT-DISPUTED issue, statement correction, or new notion was required.
The example CompactObject module is now withdrawn; the delivery follows the
current module/header/docstring conventions of the active dependency modules.

## Second reading by Q10

Self-check under the dispatcher's direct-delivery protocol, not an independent
review: reread the complete node, the source blueprint paragraph, the final Lean
file, and the expanded Tor predicate definition. X and κ have exactly the stated
assumptions, B is any intrinsic unbounded derived object, a and b are ordered
integers, and the left side spells out both cohomological bounds. Expanded the
right side: its test quantifies over every module sheaf, puts it in degree zero,
and computes the ordinary K-flat derived tensor. The explicit coefficient-sized
site is the existing AsSmall model, retaining independent scheme and coefficient
universes. The finite assertion existentially quantifies the same ordered
interval. No omitted constructibility, points or finiteness condition was found.
The live dependency records are retained. The item uses the existing
`coefficientModelCohomology` and Tor-amplitude predicates without copying them;
the latter computes its representative tensor using `ringedKoszulTensor`. Both
postponed theorems belong to this node and carry source/proof docstrings. The
first server compile found one overlong line; it was wrapped before the clean
compile and delivery checks. Maintainer independent review remains required.

## Returned delivery repair

Repair of independent review L at immutable head `a014f19ddb11` (H13/H4):

- F1: dropped the sandbox node file `def-weil-derived-cohomology-sheaves.json`.
  The live N5 record remains owned by `Sheaf.Paper.SfCommonStageWeilCohomology`,
  with its full declaration list and landed proofs. No cohomology node is rebound.
- F2: dropped the sandbox node file `def-weil-derived-tensor.json`. The live NE
  `existing: true` binding to `AlgebraicGeometry.ProEtale.derivedTensor` remains.
  Removed the unused `IntrinsicDerivedTensorOfUniverses` import from the item.

Both accepted theorem signatures, their proof docstrings, and the item node are
unchanged from the returned packet. The retained packet passed an initial dry
run before these repairs. The repaired packet is compiled and checked again
using the prescribed wrappers before delivery. The self-check confirms that
cohomology is `coefficientModelCohomology` and the tensor test is the existing
Tor-amplitude predicate from `CoefficientProEtaleTorAmplitude`; neither needs
a dependency record change.
