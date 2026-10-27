## Worker report

Existing declaration, with no new module:
`WeilConjectures.GeneralAlgebraicallyClosedCoefficients.shift_existsUnique`,
`Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`, line 534.
The signature is copied verbatim into `lean.statement`. Only the item's `lean`
field changes. The declaration already has the postponed proof required by stage 2;
this delivery neither proves it nor introduces another copy.

I read the item's complete statement, source and all five proof steps, every
statement-dependency node and its recorded Lean or Mathlib match, the existing
signature and its docstring, and the definitions used by that signature. The current
blueprint source is
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/_section.md`,
especially its finite-field Hom descent and ordinary categorical 2-colimit clauses.
The item's source additionally expressly identifies the retained literal-pair
shift construction and this existing `shift_existsUnique` signature. The current
blueprint unit concerns the later pro-etale comparison; this delivery preserves
the item and its retained intrinsic construction without changing any unit.

Clause-by-clause correspondence:

- Prime: the section parameter `l : ℕ` has `[Fact l.Prime]`.
- Algebraic closure: `Ω : Type v`, `[Field Ω]`, `[Algebra (Padic l) Ω]`,
  `[IsAlgClosure (Padic l) Ω]`. `Padic` is Mathlib's norm completion of ℚ;
  `IsAlgClosure` supplies algebraic closedness and algebraicity.
- Arbitrary scheme and independent universes: `Y : Scheme.{u}` and `Ω : Type v`
  are separate section parameters. No finite-field datum, structure map,
  noetherianity or equality of these universes occurs in the signature.
- Index fields: `Index l Ω` is the existing finite coefficient field indexing
  type, `Padic.FiniteCoefficientFields l Ω`, ordered by inclusion.
- Raw stages: `Stage l Ω Y E` uses the specified small model
  `Coefficient.{u} l Ω E` in `sfRationalConstructibleCategory`. That category
  is `ScalarLocalization` of the integral category, without Karoubi completion.
- Fixed normalized system: `Pair l Ω Y` is literally
  `(stageSystem l Ω Y).PairCategory`. `stageTransition` is that system's `T`;
  its `stageTransitionCommShift` transports the fixed integral-image-normalized
  comparison by equality of the transition functors. No replacement system,
  arbitrary functor or alternative comparison is quantified over.
- Fixed abelian-group Hom structure: `ColimitHom A B` is
  `AddCommGroup.DirectLimit (StageHom A B) (transportHom A B)`;
  `homCoordinates` is chosen from the unique representative-normalized
  equivalence. `homAddCommGroup` transfers this actual colimit structure and
  the existing `preadditive` instance uses exactly those groups.
- Existence and uniqueness of the whole coherent shift:
  `∃! s : HasShift (Pair l Ω Y) ℤ, ...`. The lambda binds `shiftInst := s`,
  so every clause refers to the quantified candidate rather than the later
  chosen global instance. Mathlib's `HasShift` stores a functor and its
  monoidal structure, including the unit and tensorator. Thus equality in
  `ExistsUnique` includes zero/add coherence data, not merely functor equality.
- Additivity of every integer shift: the first conjunct is
  `∀ n : ℤ, (shiftFunctor (Pair l Ω Y) n).Additive`.
- Literal object formula: the second conjunct equates the shifted object to
  `shiftPair n A`, defined as
  `⟨A.stage, (shiftFunctor (Stage l Ω Y A.stage) n).obj A.obj⟩`.
- All representatives: the third conjunct quantifies over `n`, `A`, `B`, `L`,
  `hA`, `hB`, and every `f : StageHom A B ⟨L, hA, hB⟩`. Its `HEq` compares
  the shifted `ofHom` with the `ofHom` of `shiftRepresentative` at that same `L`.
  This is precisely the requested interpretation after the object equalities.
- Orientation of the representative formula: `shiftRepresentative` is
  `σ_A.hom ≫ (shiftFunctor _ n).map f ≫ σ_B.inv`. Lean's `≫` is composition
  in order of application, giving the node's `σ_B⁻¹ ∘ f[n] ∘ σ_A`.
- Inclusion comparisons: the final existential supplies
  `c : ∀ E, (inclusion E).CommShift ℤ`. Its inner lambda installs exactly `c`.
  The final `HEq` requires the hom component at every integer and stage object
  to be the identity of `inclusion E` applied to the shifted object.
- Naturality, shift zero, and shift addition: `Functor.CommShift` contains the
  natural isomorphisms, `commShiftIso_zero = CommShift.isoZero`, and
  `commShiftIso_add = CommShift.isoAdd`. Those are the specified coherent
  zero/add equations. The existential witnesses cannot be arbitrary exactness
  witnesses because their components are forced to the displayed identities.

Dependency declarations read and reused by the existing construction:

- Mathlib.NumberTheory.Padics.PadicNumbers: `Padic`.
- Mathlib.FieldTheory.IsAlgClosed.Basic / AlgebraicClosure:
  `IsAlgClosure`, `IsAlgClosed`, `AlgebraicClosure`.
- Sheaf.NumberTheory.Padics.FiniteCoefficientFields:
  `Padic.FiniteCoefficientFields`, `Padic.finiteCoefficientBase`,
  `Padic.finiteCoefficientCompositum`, `Padic.finiteCoefficientFields_properties`.
- Sheaf.Paper.SfRationalizationKaroubi:
  `WeilConjectures.sfRationalConstructibleCategory`,
  `sfRationalConstructibleShift`, `sfRationalConstructibleShiftAdditive`.
- Sheaf.Paper.GeneralAlgebraicallyClosedCoefficientStages:
  `GeneralAlgebraicallyClosedCoefficients.Stage`, `stageSystem_existsUnique`,
  `stageSystem`, `stageTransition`, `stageTransitionCommShift`.
- Sheaf.CategoryTheory.ExactStagePairData:
  `CategoryTheory.StageSystem.ExactStagePairData`; its pair construction is
  the existing `StageSystem`, `StageSystem.PairCategory`, and `StageSystem.ι`
  from WeilConjectures.CategoryTheory.StageSystem.Basic. The present node
  constructs the shift, so does not assume the optional exact-stage package.
- Mathlib.Algebra.Colimit.Module: `AddCommGroup.DirectLimit` and its `of`.
- Sheaf.Paper.GeneralPairHomCoordinates:
  `GeneralAlgebraicallyClosedCoefficients.pairHomCoordinates`, which states
  the full coordinate, addition, zero, bilinearity, inclusion and representative
  interface on the same existing objects and group structures.
- Mathlib.CategoryTheory.Shift.Basic and Shift.CommShift:
  `CategoryTheory.HasShift`, `ShiftMkCore`, `hasShiftMk`, `Functor.CommShift`.
  Mathlib.CategoryTheory.Triangulated.Pretriangulated supplies the dependency's
  full pretriangulated notion; this item only asserts its coherent shift part.

The existing declaration's proof docstring describes descending shifted finite
representatives and stage zero/add comparisons, checking coherence at a common
field, and using identity inclusion comparisons on every literal pair to force
full-structure uniqueness. The newly split proof prerequisites are recorded in
this item's unchanged `proof_deps`; this existing-declaration delivery introduces
no new imports or proof changes.

Edge cases checked against the actual signature and definitions: n = 0 and
negative n are included by quantification over all ℤ; repeated coefficient fields
and arbitrary common stages are allowed because hA/hB are non-strict inequalities;
the base coefficient field exists so the index is nonempty; zero arrows and zero
objects remain subject to the same formulas and colimit group structure; the empty
scheme is allowed; the zero/add comparisons are constrained even in degree zero;
the scheme and closure universes remain independent. There is no unitor or strict
identity-transition hypothesis added to the pair construction.

Searches (2026-10-27):

- msearch.py leanfinder: "Unique coherent integer shifts on the finite coefficient
  pair category with prescribed representative maps and identity shift comparisons
  on stage inclusions". Eight generic hits, including `ShiftMkCore`, `hasShiftMk`
  and `ShiftMkCore.mk.inj`; none is the concrete normalized coefficient statement.
- msearch.py loogle: "CategoryTheory.HasShift, CategoryTheory.Functor.CommShift".
  Twelve generic shift-commutation results; no concrete coefficient-pair result.
- msearch.py grep: "StageSystem|PairCategory|shift_existsUnique". Zero Mathlib hits.
- rg on lean/WeilConjectures for `shift_existsUnique|shiftRepresentative|shiftPair`,
  and grep for the exact node id: no hits.
- rg on lean/Sheaf: exact matching `shift_existsUnique` at
  GeneralAlgebraicallyClosedCoefficients.lean:534. The similarly named theorem in
  SfAlgebraicallyClosedCoefficients requires a finite-field datum, so is not the
  datum-free statement. Existing consumers also use the selected declaration.

No statement correction, disputed statement, new node or dependency repair.
Independent maintainer review is supplied by the delivery workflow; no independent
second-reading claim is made here.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
