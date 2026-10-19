## Worker report

The module `Sheaf.Paper.PbcIdempotentCompleteTriangulation` states
`AlgebraicGeometry.Scheme.pbcIdempotentCompleteTriangulation`, with its entire proof
postponed by `sorry`. It uses the actual raw finite-stage pair category and the
published scalar, shift, and distinguished-triangle structures. No definition or
dependency node is restated, and the node changes only in `lean`.

The source is the blueprint file
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/thm-weil-pbc-idempotent-complete-triangulation.md`,
order 1544. The current DAG proof corrects the source proof's final reference to
Qbar-linearity of j_E: its domain is E-linear, and the statement correctly says
E-linear. The declaration docstring follows all six steps of the current DAG proof.

Hypotheses, inherited from `def-weil-pbc-qbar-category`:

- The prime ell is `(l : ℕ) [Fact l.Prime]`; its local field is `ℚ_[l]`.
- The chosen algebraic closure is `(Qbar : Type w) [Field Qbar]
  [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar]`.
- The base is `(T : Scheme.{u}) [IsNoetherian T]`.
- Finite dimension is `[hDim : Fact (∃ n : ℕ,
  topologicalKrullDim T ≤ (n : WithBot ℕ∞))]`.
- Invertibility of ell is `[hInv : Fact (∀ t : T,
  IsUnit (l : T.presheaf.stalk t))]`.
- `w` and `u` are explicitly declared independent universes. No equality of
  coefficient and site universes is imposed; the recorded categories already
  incorporate their canonical finite-field small models.

Clauses, in the order of the declaration's conjunction:

1. Independence of the representative is `∀ α r s, Rep.Rel r s →
   Rep.Rel (qbarScalarRep ... α r) (qbarScalarRep ... α s)`. This is exactly
   compatibility of the prescribed representative operation with eventual equality.
2. Independence of the auxiliary finite overfield N is the formula for arbitrary
   `M`, `hX`, `hY`, `f`, `N`, `hMN`, and `hα`. It equates
   `α • PairCategory.mkHom M hX hY f` with the class at N of
   `(⟨α,hα⟩ : N.val) • S.tr hMN f`. The left side uses the published
   `pbcQbarLinear` instance, whose `homModule.smul` is definitionally the
   published `pbcQbarScalarAction`. Hence this is the specified operation,
   and any two allowed N give the same class.
3. `Nonempty (Linear Qbar (pbcQbarCategory l Qbar T))` states Qbar-linearity
   of the category with its fixed common-stage additive structure. The instance
   used in clause 2 is the canonical one defined in `PbcQbarCategory`, rather
   than an arbitrary scalar action.
4. `CategoryTheory.IsTriangulated (pbcQbarCategory l Qbar T)` asserts the
   octahedral axiom for the inherited pretriangulation; the latter already has
   TR1--TR3 and exactly the prescribed common-stage distinguished triangles.
5. `IsIdempotentComplete (pbcQbarCategory l Qbar T)` is idempotent completeness
   of this same category, without replacing it by its envelope.
6. `(toKaroubi ...).IsEquivalence` and `(toKaroubi ...).IsTriangulated`
   state that the canonical inclusion is an exact equivalence. The shift
   comparison and retract triangulation are the canonical published upstream
   structures, not existentially chosen ones.
7. For every `E : Padic.FiniteCoefficientFields l Qbar`, the functor is literally
   `(pbcScalarSystem ...).ι E`. Its `IsTriangulated` clause expresses exactness
   with its existing common-stage shift comparison. Its `Additive` clause and
   the equation `j_E.map (a • f) = (a : Qbar) • j_E.map f` express precisely
   E-linearity. This writes the fields of the recorded linear-functor interface
   with the actual inclusion `E.val → Qbar` explicit: the target's installed
   scalar structure is Qbar-linear, so no second category or arbitrary E-action
   is introduced. `Functor.Additive` gives the addition equation and the displayed
   scalar equation is `Functor.Linear.map_smul` after restricting scalars.

Statement dependencies read and used:

- `Sheaf.Paper.PbcQbarCategory`: `AlgebraicGeometry.Scheme.pbcQbarCategory`,
  `pbcQbarScalarAction`, `pbcQbarLinear`, `pbcQbarTriangulated`, and
  `CategoryTheory.StageSystem.qbarScalarRep`, `qbarScalarHom_mkHom`.
- `Mathlib.CategoryTheory.Idempotents.Karoubi`:
  `CategoryTheory.Idempotents.Karoubi` and `toKaroubi`.
- `Mathlib.CategoryTheory.Linear.Basic`: `CategoryTheory.Linear`.
- `Mathlib.CategoryTheory.Linear.LinearFunctor`: `CategoryTheory.Functor.Linear`
  (its scalar equation is expanded with the explicit coefficient inclusion), and
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`: `Functor.Additive`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`: `Pretriangulated`;
  `Mathlib.CategoryTheory.Triangulated.Triangulated`: `IsTriangulated`;
  `Mathlib.CategoryTheory.Triangulated.Functor`: `Functor.IsTriangulated`.

Additional existing interfaces used are `CategoryTheory.IsIdempotentComplete`
from Mathlib's idempotent-completeness interface and the canonical envelope
pretriangulation and `toKaroubi` shift comparison from
`WeilConjectures.CategoryTheory.Idempotents.Pretriangulated` and its imports.
The pair representatives, relation, transport, and stage functor are the recorded
`CategoryTheory.StageSystem` interfaces, read in the current source through
`scompile.py --source WeilConjectures.CategoryTheory.StageSystem.Basic` because
this module is absent from the older source checkout.

All currently stated proof dependencies are imported: `ScalarLocalization`,
`PbcRationalCategory`, `FiniteStagePairCategory`, `CommonStageCalculus`,
`PbcVerdierAxioms`, `DerivedChangeOfRingsIndependentCoefficients`, as well as the
statement dependencies. `prop-weil-pbc-scalar-extension` and
`thm-weil-pbc-qbar-idempotent-complete` have no usable recorded Lean module in
the current DAG and are therefore not imported as proof modules. They are
proof dependencies only, not additional hypotheses or missing statement objects.

Edge cases checked before drafting:

- `N = M` is allowed whenever the scalar already belongs to M; no strict
  overfield condition is used. This includes E-scalars in the final clause.
- Zero and unit scalars, zero arrows, zero objects, and equal source/target
  stages are included in the universal scalar and representative clauses.
- Representatives may begin at distinct stages; `Rep.Rel` retains that full
  common-stage relation rather than checking equality only at a fixed stage.
- The empty scheme is allowed: invertibility is then vacuous as in the source,
  and no nonempty base or positive dimension hypothesis is added.
- Every finite intermediate field is included, including the base field.
  The conclusion gives E-linearity of j_E, without assuming a Qbar-module
  structure on its finite-stage source.
- Exactness uses the installed common-stage and canonical retract shift
  comparisons and distinguished sets. No different pretriangulation is chosen.

Searches for an existing statement:

- `msearch.py`, LeanFinder: “The finite coefficient common-stage category of
  constructible l-adic complexes over an algebraic closure is linear triangulated
  idempotent complete and finite stage inclusions are exact linear”: eight hits,
  on homological functors and derived t-structures, none stating this theorem.
- `msearch.py`, Loogle: `CategoryTheory.Linear,
  CategoryTheory.Idempotents.toKaroubi`: zero hits.
- `msearch.py`, grep: `Karoubi|IsIdempotentComplete` in
  `CategoryTheory/Triangulated`: zero hits.
- `msearch.py`, LeanSearch: “The category of constructible l-adic complexes over
  an algebraic closure is linear triangulated and idempotent complete”: eight
  hits, on `IsIdempotentComplete`, abelian categories, complexes, and the derived
  triangulation; none concerns the specified common-stage category.
- Direct `rg` of Mathlib found the standard linear, linear-functor, idempotent,
  envelope, and triangulated interfaces, all reused. Searching for a categorical
  restriction-of-scalars linear instance found no such interface.
- Direct `rg` of `WeilConjectures` for the blueprint id, `pbcQbarCategory`,
  `pbcQbarScalarAction`, and `pbcIdempotentCompleteTriangulation` found no
  duplicate statement. Concept searches found the generic canonical Karoubi
  pretriangulation, which is reused for the exact-equivalence conclusion.
- Direct `rg` of `lean/Sheaf` for the same names found only the recorded
  `PbcQbarCategory` definitions and instances, not this full theorem.
- The upstream declaration-name index has no entry for the proposed theorem
  name or the concrete Qbar scalar/category names.

No statement correction, new node, dependency-node repair, or disputed clause.

Validation: `scompile.py Q35 thm-weil-pbc-idempotent-complete-triangulation`
compiled the delivered module cleanly, with no errors or warnings. The prescribed
`deliver2.py Q35 thm-weil-pbc-idempotent-complete-triangulation --no-push`
printed `OK (dry run)`: compilation and preflight passed except for the independent
second-reading section, which the second reader supplies. Nothing was pushed.


## Second reading by Q35

I independently read the sandbox node and Lean module, the blueprint theorem
(order 1544), the Qbar-category definition (order 1311), and the unit section.
The theorem is specific to the blueprint, not an assertion found in Stacks.
I also read `derived.tex` at the labels for Tags 0145, 014V, 05R6 and 05QW,
including the additive-category and shift conventions preceding 0145. These
supply the meanings of triangulation, exactness, localization triangulation and
Karoubianity; the countable-(co)product assumption of 05QW is a sufficient
criterion, not an additional hypothesis of this blueprint theorem.

Object and hypothesis checklist, with verdicts:

1. A prime ell: `(l : ℕ) [Fact l.Prime]`. Exact; neither ell = 0 nor ell = 1
   belongs to the source, and no other prime is excluded.
2. Its local field and chosen algebraic closure: `ℚ_[l]`, `(Qbar : Type w)`,
   `[Field Qbar] [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar]`. Exact;
   no choice of a particular algebraic closure or embedding is imposed.
3. A noetherian finite-dimensional scheme with ell invertible: `(T : Scheme.{u})`,
   `[IsNoetherian T]`, `hDim : Fact (∃ n : ℕ,
   topologicalKrullDim T ≤ (n : WithBot ℕ∞))`, and
   `hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))`. Exact;
   these are the hypotheses explicitly inherited from the current Qbar node.
   There is no separation, nonemptiness, base-field or positive-dimension assumption.
4. The category P_T = Dbc(T,Qbar): `pbcQbarCategory l Qbar T`. Exact;
   I opened `PbcQbarCategory` and `FiniteStagePairCategory`: this abbreviation
   is the actual `PbcFiniteStagePairCategory` for `pbcScalarSystem`, whose stages
   are the raw `PbcRationalCategory` at the canonical small coefficient models.
   It is not the Karoubi envelope. I read `StageSystem.Basic` using the prescribed
   `scompile.py --source` command: its objects are stage/object pairs, `Rep`
   consists of common-stage arrows, and `Rep.Rel` is eventual transported equality.
5. Scalars, representatives and finite overfields: `α : Qbar`, arbitrary
   `{X Y : pbcQbarCategory ...}`, `r s : PairCategory.Rep X Y`, and arbitrary
   `M N : Padic.FiniteCoefficientFields l Qbar` with `hX`, `hY`, `hMN`, `hα`.
   Exact. `FiniteCoefficientFields` is the subtype of intermediate fields finite
   over Q_l. `X.toStage` uses the specified coefficient extension and `S.tr`
   conjugates by its specified tensor associators; no arbitrary transport is used.
6. The finite-stage inclusion: `(pbcScalarSystem ...).ι E` from
   `pbcStageCategory ... E`. Exact; this is the recorded j_E, with its inherited
   shift comparison and its E-module Hom structure `qbarStageLinear`.

Conclusion checklist, in the conjunction's order, with verdicts:

1. Independence of representative: `Rep.Rel r s → Rep.Rel
   (qbarScalarRep ... α r) (qbarScalarRep ... α s)`. Exact. The chosen operation
   enlarges the representative stage by the compositum with Q_l(alpha), then
   multiplies the transported arrow. This is the operation of the definition.
2. Independence of auxiliary N: the universal `mkHom` equation computes `α • f`
   at every `N ≥ M` containing alpha. Exact. Thus every two allowed choices give
   the same class, for every representative. I checked the definitions
   `pbcQbarLinear → qbarPairLinear → qbarScalarHom`, so the left-hand scalar
   operation is the prescribed quotient action, not an unrelated action.
3. Qbar-linearity: `Nonempty (Linear Qbar (pbcQbarCategory ...))`. Exact in this
   context: the dependency already installs `pbcQbarLinear` with precisely that
   action and the common-stage additive groups. The preceding equation fixes the
   interpretation of the action. Mathlib `Linear` gives module Hom structures
   and both scalar-composition identities; `Preadditive` gives addition laws.
4. Ordinary triangulation for the specified shift/triangles:
   `CategoryTheory.IsTriangulated (pbcQbarCategory ...)`. Exact. I read
   `PbcCommonStageCones`, `PbcVerdierAxioms`, and `StageSystemVerdier`:
   `qbarPairPretriangulated` is chosen from the unique structure characterized
   by `CommonStageDistinguished`, and includes TR1--TR3; `IsTriangulated`
   supplies TR4. No alternative triangulation is existentially substituted.
5. Idempotent completeness of that category: `IsIdempotentComplete (...)`.
   Exact: Mathlib's class splits every idempotent, including zero and identity.
6. The canonical exact equivalence to Kar(P_T): the two clauses
   `(toKaroubi ...).IsEquivalence` and `(toKaroubi ...).IsTriangulated`.
   Exact. I opened Mathlib's `Karoubi`, `Hom` and `toKaroubi` definitions and
   upstream `Idempotents.Pretriangulated`: objects are (K,e), morphisms satisfy
   the projector relation, and the inclusion uses identity projectors.
   Its shift comparison is canonical; distinguished triangles are retracts of
   images of the original distinguished triangles. Exactness therefore refers
   to the intended envelope structure, not merely an underlying equivalence.
7. Every finite j_E is exact and E-linear: the last universal quantifier
   asserts `IsTriangulated`, `Additive`, and
   `j_E.map (a • f) = (a : Qbar) • j_E.map f`. Exact. I checked both
   `Functor.Linear.map_smul` and `Functor.Additive`: the expanded equation is
   precisely linearity after restriction along E -> Qbar, together with
   preservation of addition. It correctly does not demand Qbar-linearity from
   a source category whose Hom modules have only E-scalars.

Edge cases: M=N and E equal to the base field are included; neither inclusion
is strict. Alpha=0 and alpha=1, zero arrows, zero objects, and representatives
at different stages are covered by the universal quantifiers and full eventual
relation. The empty scheme is admitted (invertibility is vacuous there), as are
dimension-zero schemes and shifts in all integer degrees including zero. There
is no new characteristic restriction beyond ell being invertible. There is no
arbitrary external index type: the coefficient index is the actual nonempty
directed finite-field poset, whose bottom is the base field, so empty finite
diagrams are also covered. Universes `w` and `u` are independently bound; the
recorded small coefficient models and field equivalences transport scalars
without a coefficient/site universe equality. No variable is auto-implicit.

Independent searches used different wording from the first worker:

- LeanFinder via `msearch.py`: "A category assembled from finite coefficient
  fields in an algebraic closure has compatible scalar multiplication,
  triangulation, and splitting of idempotents". Eight hits, on Schur's lemma,
  finite generated algebra/module categories and matrix categories; no match.
- Loogle via `msearch.py`, `"toKaroubi"`: twelve hits. The generic
  `toKaroubi_isEquivalence` assumes idempotent completeness and only proves the
  underlying equivalence. It does not state this theorem. Its canonical
  construction is already reused here.
- Direct `rg` of Mathlib category theory, upstream `WeilConjectures`, project
  `lean/Sheaf`, and the upstream declaration-name index for
  `pbcIdempotentCompleteTriangulation`, idempotent-complete triangulation,
  Qbar/idempotent combinations and linear/colimit combinations found no
  duplicate. Other hits concern module colimits and unrelated linear orders.
- I inspected the general interfaces rather than relying on their names:
  Mathlib `Linear`, `Functor.Linear`, `IsIdempotentComplete`, `IsTriangulated`,
  and `Functor.IsTriangulated`, and the upstream canonical Karoubi triangulation.

No mismatch found. No Lean or node fields changed. No new nodes, dependency
modules or statement correction were needed. All recorded statement-dependency
interfaces are used; the E-linear-functor fields are expanded to make the
coefficient inclusion explicit. All currently recorded proof modules are
imported. The scalar-extension and Qbar-idempotent-completeness proof nodes
still have no Lean record, so there is no module to import for either.

The declaration's docstring covers all six DAG proof steps, including the
K-flat tensor scalar calculation, compositum comparison, quotient laws,
Verdier axioms, canonical Karoubi equivalence, and the E-scalar calculation.
The source proof's final additional claim of Qbar-linearity of j_E is already
corrected in the DAG proof and is not part of the source theorem statement.
The only local theorem proof remains `by sorry`; no data definitions or proofs
were added. The module has no private definitions, local notation or instances.
The node's `lean.statement` was checked byte-for-byte against the file signature;
all Lean lines have at most 92 characters.

Additional independent LeanSearch query via `msearch.py`: "A directed union of
triangulated categories over finite subfields is linear over their union and its
canonical inclusion into the idempotent completion is an exact equivalence".
Eight hits: the generic `toKaroubi_isEquivalence`/`toKaroubiEquivalence`,
triangulated equivalence constructors, Karoubi universal extension, linear
triangles, and derived-category triangulation. None gives the concrete varying
coefficient category theorem. I opened the Karoubi equivalence instance and the
triangulated-equivalence constructor; these do not justify marking this whole
node existing.

Validation: the required `scompile.py` invocation from the sandbox compiled
both its sandbox check and library module successfully (11.6 s and 20.3 s),
with no warnings or errors. The first invocation had used the read-only
repository as its working directory, so its relative sandbox file path was
absent; rerunning from the correct sandbox directory resolved that immediately.
