## Worker report

This delivery states `lem-per-adic-closed-constructible` in
`Sheaf.Paper.AdicClosedConstructible`, namespace `WeilConjectures.AdicClosed`.
The mathematical statement and proof are unchanged. The former module was removed
as dead; this delivery restores its statement using the current intrinsic interfaces.
All theorem proofs are `sorry`. All definitions contain actual data; the chosen
transpose is uniquely determined on every arrow by `transpose_existsUnique`.

Hypothesis and clause correspondence:

- `k : Type u`, `[Field k]` is any field, including characteristic zero and imperfect
  fields. There is no finite-field datum on the scheme.
- `l : ℕ`, `[Fact l.Prime]`, `hl : IsUnit (l : k)` express the prime and its
  invertibility. `residueInvertible` maps the actual unit along the structure
  morphism's `residueFieldAlgebraMap`, supplying invertibility in every residue
  field without a further assumption.
- `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`
  express the finite coefficient extension. The recorded Padic constructions supply
  its valuation ring, chosen uniformizer and finite quotients; no new versions occur.
- `W : Scheme.{u}`, `[W.Over (Spec (.of k))]`, and `LocallyOfFiniteType`,
  `QuasiCompact`, `IsSeparated` on the structure map express separated finite type.
- `sfIntegralConstructibleCategory l E W` is the existing full subcategory of
  derived modules over the completed coefficient sheaf: derived completeness,
  constructible positive reductions and one uniform finite cohomological interval.
  The site has object universe u+1 and arrow universe u; these remain distinct.
  A common ambient u for scheme and coefficient models follows the recorded API.
- `hom_constructible` says that the actual ambient `integralDerivedInternalHom`
  object of every P,Q satisfies this predicate. `hom` restricts precisely that
  bifunctor, on both objects and arrows, using this closure proof.
- `tensor` is the recorded `constructibleIntegralTensor`, the restriction of the
  strict reduction/Roos `integralCompletedTensor`.
- `transpose_existsUnique` fixes the additive Hom bijection by precomposing with
  the actual coherent reduction/limit adjunction unit, its tensor comparison and
  the inverse Roos realization, then applying the ambient ringed-site transpose.
  This is exactly the ordinary-to-completed tensor map. `transpose` selects the
  uniquely characterized equivalence. `evaluation` is its inverse at identity.
- `closed_symmetric_monoidal` gives `CoefficientClosedStructure (hom ...)`, whose
  tensor is exactly `tensor`, with `SymmetricCategory` and degree-zero completed
  coefficient unit. Every Hom equivalence equals `transpose`. Thus evaluation is
  pinned to the ambient adjunction, rather than an unrelated existential choice.
- `L` has the same finite-extension instances, and `ι : E →ₐ[ℚ_[l]] L` is the
  coefficient inclusion. A homomorphism of fields is injective. The scalar functor
  is `sfConstructibleIntegralScalarExtension` with the unused auxiliary p set to
  zero and l≠0 supplied by primality; this puts no condition on characteristic k.
- `scalarHom P Q` is defined for every constructible pair. It is the target
  transpose of inverse `integralTensorScalarComparison` followed by scalar-extended
  `evaluation`. This fixes exactly the comparison in the node.
- `scalarHom_isIso` asserts invertibility. `scalarHom_naturality` quantifies over
  arbitrary a:P'→P and b:Q→Q', including the contravariant first variable.
- `scalarHom_evaluation` is the evaluation square with the recorded tensor
  comparison. `scalarHom_transpose` states preservation of every adjunction
  bijection, for every M,P,Q and every f:M completed-tensor P→Q.
- `scalar_identity` uses `sfIntegralScalarUnit` on Hom and both inputs; the first
  input uses the inverse before taking its opposite. `scalar_tower` uses
  `sfIntegralScalarComp` in the same directions for every E→L→F. These are exactly
  identity and composition compatibility, with no unramified assumption.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` reexports the recorded
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionRing`, and provides `finite_coefficientExtensionRing`.
- `def-weil-scheme-morphism-properties` is a convention node; its constituent
  Mathlib notions are `Scheme.Over`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsSeparated`. `WeilConjectures.ZetaSeries` gives the actual residue-field map.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` reexports the completed
  sheaf, its projections and `integralConstantToCompletionOfUniverses`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory` (full defining predicate inspected).
- `Sheaf.Paper.DerivedPullbackTensorHom` reexports from
  `FiniteRationalDerivedOperations` the `constructibleIntegralTensor` and
  `integralTensorScalarComparison`; `IntegralDerivedOperations` gives the actual
  `integralCompletedTensor` and `integralDerivedInternalHom`.
- `Sheaf.Paper.IntegralScalarExtensionUniverses` reexports the strict Roos/K-flat
  scalar construction and its independent-universe interface.
- `Sheaf.Paper.IntegralOperationsScalarComparisons`: `scalarTensorCompleted`,
  `scalarHomCompleted`, `scalarHomCompleteInputs` and their representative
  normalizations. The tensor comparison used in scalarHom is their restriction.
- `Sheaf.Paper.SfScalarExtensionComposition`: `sfIntegralScalarComp` and
  `sfIntegralScalarUnit`, uniquely fixed by ordinary balanced associativity and
  multiplication after the normalized ordinary-to-completed comparisons.
- `Sheaf.Paper.CompletedPullbackTensorComparison` reexports
  `pullbackTensorCalculus`, `pullbackTensorIntegralTensorModel`: the actual
  coherent reduction/limit adjunction and strict Roos-normalized realization.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`: `CoefficientClosedStructure`,
  its tensor and transpose. The already existing owning node is added to stmt_deps.
- `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`:
  `sfConstructibleIntegralScalarExtension`. Its existing owning node is added to
  stmt_deps. No definition node or dependency module is created.
- Stated proof dependency modules are imported privately, including
  `FiniteTorInternalHomAnyField`, `IntegralHomReduction`, the completion reflector,
  stratified-perfect characterization, Serre closure, derived-origin comparison,
  finite-free comparison and ringed Hom base change. The finite-type Noetherian,
  SES triangle and homology long-exact inputs use their existing Mathlib matches.

Source reading: the local Bhatt–Scholze PDF, Definition 3.4.10, Lemma 3.4.11,
Lemmas 6.7.12–13 and their proofs. Lemma 6.7.13 assumes quasi-excellence and
ell-coprimality, not positive characteristic. The node's nine proof steps expand
unit membership, completion comparison, residue Hom finiteness, uniform-bound
induction, closed adjunction/coherence and finite-free scalar normalization.
The theorem docstrings carry those arguments with their owning node id.

Edge cases checked: empty W; Spec k; zero inputs and tensor parameter; characteristic
zero; imperfect k with l invertible; torsion integral complexes; negative shifts;
identity coefficient inclusion and towers containing identity stages; ramified
extensions with different uniformizers. No perfectness or finite-Tor assumption
has been added to integral inputs. All positive reduction exponents remain included.

Searches actually run (2026-10-28; the sandbox searches.jsonl retains service results):

- LeanFinder: “Derived internal Hom of integral constructible l adic complexes is
  constructible and completed tensor forms a closed symmetric monoidal category”:
  eight generic condensed/light condensed closed-category hits, no exact match.
- Loogle: `"MonoidalClosed", "FullSubcategory"`: zero hits.
- Mathlib grep via msearch: `constructible.*[Hh]om|[Hh]om.*constructible`,
  CategoryTheory: zero hits.
- Earlier persisted searches: LeanSearch “Constructible adic complexes closed
  symmetric monoidal derived internal Hom” gave generic internal-Hom interfaces;
  LeanFinder on finite scalar extension gave light condensed and adic-completion
  tensor maps; neither supplies this constructibility statement.
- Direct rg in WeilConjectures for the node id and `AdicClosed`: localization and
  closed-immersion names only. Direct rg in Sheaf found the recorded operations
  and `FiniteTorStability`, whose Hom result requires a finite-field datum and
  cannot state the arbitrary-field theorem. Existing generic structures are reused.

No STATEMENT-DISPUTED flag or statement correction is required.

## Second reading by NA

This is a second pass in the dispatched worker thread, not a claim of an independent
agent review; the brief prohibits starting other agents. The maintainer independently
reviews the delivered packet. I reread the node and the final declarations together.
The first draft imported `podIntegralClosed` from an automorphism result whose DAG
proof dependency chain leads back to this item. I removed that import and stated
its required completed transposition directly with the already recorded unit,
reduction tensor comparison and strict Roos realization. No downstream result is
used as a premise or selected construction.

The unit now passes `completedIntegralCoefficientSheafUnrestricted` (RingCat) to
`SheafOfModules.unit`; the earlier CommRingCat argument was ill-typed. Scalar
comparisons now take all P,Q directly and use the same full hom functor, with
separate isomorphism, naturality, evaluation and transpose assertions. Identity
and tower equations use inverse first-variable unit/associator followed by opposite,
as required by contravariance. The closed theorem fixes every transpose, so its
evaluation is the displayed ambient one. No base-field or ramification case is lost.

Validation: scompile.py compiled the final module both as sandbox and library
(9.0 s and 7.4 s respectively), with no warnings or errors. Nine named theorems
remain sorry as required for stage 2; every one has its proof plan in its docstring.
