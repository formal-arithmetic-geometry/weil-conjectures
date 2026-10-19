## Worker report

The module `Sheaf.Paper.EtaleCoefficientSystemAdjoint` states this node in a main
existence theorem and its scalar, cofinal, identity and composition assertions. It
uses the recorded strict varying-ring system category, rather than a category of
unrelated level outputs. All theorem proofs are `sorry`; all definitions have real
data. The auxiliary structures and maps belong to this node's adjoint/comparison
interface, carry this node's source/blueprint docstrings, and are listed in
`lean.declarations`. Coherence propositions are grouped in named predicates, and each full package
is a subtype of its data record (or a product for the smaller packages). Stored
fields are accessible through `val`, with reducible named projections for the fields
used later in the specification. `Subtype.property` gives the coherence. The clause
names below refer to the corresponding comments in the coherence predicates. No independent notion or dependency is replaced.

Hypotheses and objects:

- `D : WeilConjectures.FiniteFieldDatum` is the global datum, including its algebraic
  closure `D.k`; `[Fact l.Prime]` and `_hl : l ≠ D.p` retain both prime conditions.
- `[Field E]`, `[Algebra (Padic l) E]` and `[FiniteDimensional (Padic l) E]` say that
  E is a finite extension of Q_l. The integer ring and uniformizer are exactly
  `Padic.coefficientExtensionIntegers l E` and
  `Padic.coefficientExtensionUniformizer l E`, the dependency's chosen objects.
- `X.Over` and `Y.Over (Spec (.of D.k))`, with `LocallyOfFiniteType` and
  `QuasiCompact` on their structure morphisms, say finite type over k.
  `f.IsOver`, `IsSeparated f`, `LocallyOfFiniteType f` and `QuasiCompact f`
  retain the hypotheses on f. No separatedness condition is imposed on Y.
- `c : Compactification f` is the recorded compactification; `c.i`, `c.g`, `c.Z`
  are its open immersion, proper map and middle scheme.
- `strictEtaleCoefficientSystem` and `strictEtaleLevel` are abbreviations of the
  recorded `CoefficientSystem` and `coefficientLevelModules`. Index n is the
  paper's positive exponent n+1. `StrictEtaleEvaluation` abbreviates the recorded
  `CoefficientEvaluationDerivedPackage` at these sites. The sites still have
  object universe u+1 and morphism universe u. Coefficients/modules have universe
  u+1. Derived categories use localization universe u+2 and the fixed standard models
  supplied by `strictEtaleSystemDerived` and `strictEtaleLevelDerived`. These select
  `HasDerivedCategory.standard` for the recorded categories, without further
  hypotheses. The global sheafification instances cache existing witnesses.
  Data records reuse the recorded structures. No theorem signature has a `let` binder.

Clause correspondence:

- `StrictEtaleCompactSupport` fixes actual ordinary geometric inverse/direct images
  using `CoefficientSystemOrdinaryImage`, and universal unbounded derived images
  using `CoefficientSystemDerivedImage`. `openExtension` is the exact left adjoint
  of the geometric open restriction, hence extension by zero. Its finite-level
  evaluations and transpose equations fix its action on transitions and morphisms.
  `openFactors`, `derivedOpenTranspose`, `levelOpenFactors` and
  `levelDerivedOpenTranspose` fix the derived descent and adjunctions on complex
  representatives. `StrictEtaleCompactSupport.functor` is literally
  `S.derivedOpen ⋙ S.properDerived.system.direct`, i.e. Rp_* j_!.
- `etaleCoefficientSystemAdjoint` asserts the existence of this package and of
  `StrictEtaleExceptionalAdjoint`. Its `right` and `adjunction` give G and F ⊣ G
  on the unbounded derived categories. `rightAdditive`, `shift` and `exact`
  express exactness. `StrictEtaleScalarAction` is normalized by actual constant
  sheafification multiplication and its localization on complexes; `linear`
  expresses O-linearity, including the action on Homs.
- `levelFunctor` is finite-level compact support in the dependency's constant-ring
  module encoding. `levelRight` and `levelAdjunction` specify its ordinary étale
  right adjoint; by uniqueness this is the ordinary finite-level f_n^times.
  `evaluation` gives e_n G ≅ G_n e_n. `coherence` fixes this comparison as the `mateEquiv` image of the evaluated
  compact-support square. This single mates equation is equivalent to the evaluated
  unit and counit equations; it specifies actual natural transformations.
- `quotientOpen`, `quotientProper`, and their mate equations fix the actual open
  and proper coefficient projection maps. `quotientProjection_def` composes them.
  `quotientMate` fixes the exceptional comparison by counit transposition.
  `transition` identifies the actual derived adjoint transition, using the
  recorded normalization predicate's tensor/restriction adjunction. Quotient
  maps may be nonflat. `quotientIdentity` and `quotientComposition` explicitly use
  the dependency's representative-normalized tensor unit and associator.
- `bound` is `∃ c_f : ℕ, ∀ a M, M.IsGE a → (right.obj M).IsGE (a-c_f)`.
  Thus c_f is nonnegative and uniform in every level and every a. `normalized`
  retains exactly the bounded-below input hypothesis and both bounded-below and
  `IsNormalizedCoefficientSystem` output conclusions.
- Functors, natural isomorphisms and adjunctions occur as actual data in the
  derived categories. The evaluation-factor, tensor-counit and representative
  equations fix their map action and independence of complex resolutions.
- `strictEtaleIntegerMap` restricts the actual field embedding i to integer rings;
  its only membership proof is the separately named theorem
  `strictEtaleIntegerMap_mem`. `strictCoefficientRingMap` is the actual quotient
  lift, with its kernel proof separately named `strictCoefficientMap_kills`.
  `strictEtaleSameIndexChange` therefore uses the image of the original uniformizer,
  rather than silently switching to the target uniformizer.
- `strictEtaleScalarLevelModule` is B_n restricted along the real A_n → B_n map.
  `strictEtaleScalarLevelModule_finiteFree` gives a finite basis of that module.
  `StrictEtaleCoefficientTransport` describes the exact levelwise tensor functor,
  with its actual tensor-unit maps, successor transitions, exact derived descent,
  and finite-level derived evaluations. `etaleCoefficientSystemAdjoint_scalar`
  supplies the O'-power-system package, its right adjoint, the three transports
  at X, Y and the compactification, and `StrictEtaleExceptionalTransport`.
- `StrictEtaleInverseTransport` fixes the geometric scalar square on tensor units
  and representatives. `StrictEtaleCompactSupportTransport` fixes its open and
  proper mates and composes them into the projection square.
  `StrictEtaleExceptionalTransport.mate` is precisely inverse projection followed
  by the extended counit, transposed under F_B ⊣ G_B. Its `right` is the asserted
  T_X G_A ≅ G_B T_Y. `projectionEvaluation`, `levelMate` and `rightEvaluation`
  relate it to the same finite-level maps.
- `StrictEtaleTransportQuotient` fixes the scalar/quotient interchange on ordinary
  tensor units and universal derived counits. The exceptional transport's
  `quotient` equation gives compatibility with quotient maps using those canonical
  associators. `StrictEtaleTransportIdentity` and `StrictEtaleTransportComposition`
  fix tensor units and associators on actual strict systems and their derived
  descents. The identity and composition theorems give equalities of actual
  exceptional comparison morphisms under these identifications, before evaluation.
- `strictEtaleRamifiedIndex e n = e*(n+1)-1` indexes the positive-exponent cofinal
  subsequence. `etaleCoefficientSystemAdjoint_cofinal` gives positive e and the
  equality of the two actual quotient ideals at every level. The ramified change
  uses `Ideal.quotEquivOfEq`, not arbitrary ring maps. Its transports and exceptional
  comparison identify the full-uniformizer construction restricted to this
  subsequence with the original-uniformizer-power construction, including maps.
  The general composition theorem includes composition of such reindexings.
- There is no inverse-limit, completed-output, constructibility or pro-étale
  exceptional-adjoint conclusion.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its imported
  `CoefficientExtension`: `Padic.finite_coefficientExtensionRing`,
  `coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionRing`, `coefficientExtensionTransition`.
- `WeilConjectures.Compactification.Refinement`:
  `AlgebraicGeometry.Compactification` and its geometric fields.
- `Sheaf.Paper.CoefficientSystemDerivedComparison`:
  `SheafOfModules.coefficientSystemDerivedComparison`,
  `CoefficientSystemOrdinaryImage`, `CoefficientDerivedImage`,
  `CoefficientSystemDerivedImage`, `IsNormalizedCoefficientSystem`.
  Its imported `CoefficientEvaluationDerivedLeftAdjoint` supplies the existing
  strict category, quotient sheaves/maps, tensor/restriction, universal derived
  scalar extension, normalized transition maps, and evaluation package.
- `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`:
  `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
  The finite-level functor above uses the equivalent constant-ring module encoding
  required by the system dependency, characterized by the geometric adjunctions.
- The morphism-properties dependency is the convention record; its Mathlib
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, and `IsOver` are used.

The published proof-dependency modules are imported without `public`; their
arguments are retained in the complete natural-language proof docstrings. The two
currently unstated non-Mathlib proof dependencies (semilinear derived sections and system
left extension) are proof inputs, not substituted definitions in this statement.

Edge cases checked: n=0 is exponent one; ramification e=1 includes the identity
subsequence and e>1 starts at exponent e; equal coefficient indices use the tensor
unit; identity and composite field extensions are included. Empty schemes, zero
objects, arbitrary unbounded complexes and nonseparated Y are allowed. Only
normalization preservation requires bounded-below input. No quotient-flatness or
faithfulness of evaluation on derived morphisms is assumed; the coherence proof
uses adjunction Hom bijections.

Searches: `searches.jsonl` retains the msearch outputs. Mathlib grep for
`CoefficientSystem|strict.*coefficient|system.*adjoint` found no matching theorem;
Loogle for `CategoryTheory.Adjunction, DerivedCategory, coefficient system` found
none. LeanFinder for a right adjoint of compact-support pushforward on strict
varying coefficient systems returned ordinary sheaf adjunctions, and LeanSearch
for a derived strict-system scalar-extension comparison returned ordinary
ModuleCat scalar adjunctions. These do not assert this node. Greps for the node id
and for `StrictEtale|strictEtale` in the upstream project and `lean/Sheaf` found no
existing declaration. The existing system and scalar notions found in the recorded
dependencies are imported and specialized, not redefined.

No statement correction or disputed statement is reported. The retained draft had
omitted the scalar and cofinal conclusions and left quotient projections arbitrary;
this packet fills those clauses and fixes the maps by their canonical mates.

The current recorded proof modules `Sheaf.Paper.EtaleDerivedScalarTensor` and
`Sheaf.AlgebraicGeometry.RingedTopoiModuleAdjunctionRepair` replace their older
recorded imports; the former publicly reexports the independent-coefficient
interface used by this statement.

## Second reading by Q124

The dispatcher prohibits additional workers; the maintainer supplies the independent
review. I reread the current node, its six statement-dependency records and sources,
and every line of the retained module. The hypothesis and clause mapping above was
checked against the actual fields. The positive-exponent convention includes the
first level; quotient mates cover nonflat maps; scalar change uses the image of the
original uniformizer; ramified restriction starts at exponent e. The identity and
composition equations are equations of actual system maps. The lower bound is
uniform, and only normalization preservation assumes a bounded-below input.

The first required dry run reported a 60-second timeout. Profiling identified
repeated generated record declarations and instance reconstruction. The final
representation separates data records from their coherence predicates and fixes the
standard localization models. It imports the dependency's full open-image comparison
package, so its already normalized tensor comparisons are reused directly. No
ordinary tensor equation is restated with a new interface. The implicit quotient
indices are retained explicitly in the convenience projection. The eight theorems
have `sorry` proofs and complete proof plans. Only `lean` changes in the node.

Final validation: `deliver2.py Q124 lem-pur-etale-coefficient-system-adjoint
--no-push` returned `OK (dry run)` for commit `772bbba2f3`. It compiled the
complete module separately in the sandbox and under its library module name,
with the 60-second limits, and passed the server preflight. The final self-check
confirmed the exact main signature, all 99 declaration records, eight postponed
theorems, the line-width limit, and that only `lean` differs in the node. The
open-image tensor-unit and representative equations are the dependency's
`tensor_unit` and `derivedTensor_rep` fields, reused through `openDerived`.
