## Worker report

Existing-declaration attachment; no new Lean module, definition, theorem, or proof is written.
The item is already stated by the following public declarations in
`Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`, namespace
`WeilConjectures.GeneralAlgebraicallyClosedCoefficients`:
`specialization_stageSystem`, `specialization`, `specialization_pairs`, and
`specialization_transport`. The component comparisons are `specialization_comparisons`
in that module and `specialization_transition` in its public import
`Sheaf.Paper.GeneralAlgebraicallyClosedCoefficientStages`. All six names are recorded.
The primary declaration is `specialization_pairs`; its signature is copied verbatim to
`lean.statement`. The current server source was read with
`scompile.py --source Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` and agrees with
the checked local source at the relevant declarations (lines 767–893).

Hypothesis and clause correspondence:

- The fixed global datum is `(D : FiniteFieldDatum.{d})`; primality and the distinct
  coefficient characteristic are `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`.
  `FiniteFieldDatum` is exactly the recorded dependency in `Sheaf.Paper.FiniteFieldFiber`.
- The closure is `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]`. These are Mathlib's actual p-adic field and algebraic
  closure predicate, not an extra closure assumption or a particular chosen model.
- The scheme is `(Y : AlgebraicGeometry.Scheme.{u})`. The independent universe variables
  `d u v` retain both the arbitrary datum and the independent scheme/coefficient universes.
  There is no structure map to `D.k`, finite type, separatedness, or characteristic
  hypothesis on `Y`.
- The directed index is `AlgebraicallyClosedCoefficients.Index l Ω`, an abbreviation for
  `Padic.FiniteCoefficientFields l Ω`. Its coefficient model is
  `AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E = Shrink.{u} E.val`.
  The existing `coefficientSmall` constructs the smallness proof by finite-dimensionality;
  no equality of the scheme and closure universes is imposed.
- The stages are `GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E`, defined as
  `sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y`. That rational category
  is the raw `ScalarLocalization` of `sfIntegralConstructibleCategory`, with no
  idempotent completion. The latter is precisely the intrinsic full subcategory:
  derived completeness, constructible positive reductions, and one uniform finite
  cohomological interval for those reductions.
- The normalized systems are `stageSystem l Ω Y` and
  `SfAlgebraicallyClosedCoefficients.stageSystem D l hl Ω Y`. Their transitions use
  `sfRationalScalarExtension` with characteristic proof parameters `0` and `D.p`.
  `specialization_transition` equates the concrete transitions for every `E ≤ L`.
  `specialization_comparisons.1` equates their specified normalized associators by `HEq`
  for every `E ≤ L ≤ M`. This is an equality of the given tensor comparisons, not
  existence of unspecified comparison isomorphisms. Its unit clause is an ancillary
  existing normalization fact; no additional clause is added to the item's statement.
- `specialization_stageSystem D l hl Ω Y` is the asserted equality `η : S = S_D` of
  complete stage systems. In particular it identifies the `T` and `assoc` fields;
  the cocycle field is a proof. This gives precisely the component statements for
  the actual chosen stage systems, as well as the concrete transition comparisons.
- `Pair l Ω Y` is `(stageSystem l Ω Y).PairCategory`, and the specialized `Pair` is
  the same upstream pair construction for the specialized system.
  `specialization D l hl Ω Y` is defined literally by
  `Pi.eqToEquivalence (fun S : StageSystem (Stage l Ω Y) ↦ S.PairCategory)
  (specialization_stageSystem D l hl Ω Y)`. It is the required equality transport.
  Proof irrelevance identifies its equality witness with any witness named `η`.
- `specialization_pairs.1` quantifies over every coefficient field `E` and every
  `K : Stage l Ω Y E`, and states
  `(specialization D l hl Ω Y).functor.obj ⟨E, K⟩ = ⟨E, K⟩`.
  Thus the object is the literal same labelled pair.
- `specialization_pairs.2` quantifies over `A B`, a field `L`, and bounds
  `hA : A.stage ≤ L`, `hB : B.stage ≤ L`. Its `f : StageHom A B ⟨L,hA,hB⟩` and
  specialized `g` have exactly the node's two finite Hom types. The hypothesis
  `HEq f g` is the stipulated agreement under equality transport. The conclusion
  is `HEq` between the functor image of `ofHom A B L hA hB f` and the specialized
  `ofHom` with the same `A.stage`, `B.stage`, and `L`. Here `ofHom` is the existing
  `StageSystem.PairCategory.mkHom`, so it is exactly `e([L,u]) = [L,u_D]`
  with its transported endpoints; no enlargement of a representative field occurs.
- `specialization_transport` quantifies over `L M : Common A B` and `h : L ≤ M`;
  the common-stage subtype stores precisely both source bounds. Any later field
  `M ≥ L` carries these bounds by transitivity, so this excludes no later stage.
  Its hypothesis is the same `HEq f g`; its conclusion is `HEq` of the two actual
  `transport` values. The displayed definitions of `transport` are
  `(S.assoc hA h).inv.app A.obj ≫ (S.T h).map f ≫ (S.assoc hB h).hom.app B.obj`,
  that is `S.tr h f`, with exactly the node's endpoints and associator conjugation.

Dependency declarations read and reused, in addition to the named scalar-stage module:
`Sheaf.Paper.FiniteFieldFiber` / `WeilConjectures.FiniteFieldDatum`;
`Mathlib.NumberTheory.Padics.PadicNumbers` / `Padic`;
`Mathlib.FieldTheory.IsAlgClosed.Basic` / `IsAlgClosure` (and the recorded concrete
`AlgebraicClosure` from `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`);
`Sheaf.NumberTheory.Padics.FiniteCoefficientFields` / `Padic.FiniteCoefficientFields`;
`Sheaf.Paper.SfIntegralConstructible` / `WeilConjectures.sfIntegralConstructible` and
`sfIntegralConstructibleCategory`;
`Sheaf.Paper.SfRationalizationKaroubi` / `WeilConjectures.sfRationalConstructibleCategory`;
`Sheaf.CategoryTheory.ExactStagePairData` / `CategoryTheory.StageSystem.ExactStagePairData`
and its reused upstream `StageSystem`, `PairCategory`, `mkHom`, and `tr` from
`WeilConjectures.CategoryTheory.StageSystem.Basic`. The proof dependency
`Sheaf.Paper.SfScalarExtensionComposition` supplies the specified `sfRationalScalarComp`
and `sfRationalScalarUnit`; the existing module already imports the scalar-stage module
and the specialized coefficient module that imports these constructions.

Edge cases checked in the signatures and definitions: all bounds use `≤`, allowing
identity inclusions, `E=L=M`, repeated source labels, and `L=M` in the transport formula.
The abstract equality-induction proofs use no strictness or distinctness of fields.
Every object and every representative is quantified, including zero objects and zero
maps. The empty scheme is allowed by the unrestricted scheme binder. The field index
is nonempty by the existing base coefficient field, not an added assumption. The
parameter-zero proof uses primality to get `l ≠ 0`, not a characteristic assumption on
`Y`. No change to the statement, dependency lists, or proof is necessary. No node fault
or disputed statement was found.

Searches performed on 2026-10-27 (the wrapper records its calls in `searches.jsonl`):

- `msearch.py ... leansearch "Equality of directed coefficient stage systems fixes pairs and
  finite representatives under the equality transport equivalence"`: eight generic direct-limit
  and inverse-system hits (including `Module.DirectLimit.congr_simp` and
  `DirectLimit.setoid`), no theorem about the specified coefficient-system normalization.
- `msearch.py ... leanfinder "Equality of normalized coefficient stage systems induces an
  equivalence fixing finite coefficient pairs and representative maps and Hom transports"`:
  eight unrelated normalization/injectivity hits, no exact Mathlib theorem.
- `msearch.py ... loogle "CategoryTheory.Pi.eqToEquivalence"`: ten hits, including the
  actual generic equality-transport equivalence. Read its definition in
  `Mathlib/CategoryTheory/Pi/Basic.lean:302`; it provides the specified transport, not
  the coefficient-system equality by itself.
- `msearch.py ... grep "stage_equality_pairs|specialization_pairs|specialization_transport"`:
  zero Mathlib hits.
- Direct `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the specialization theorem
  names: no upstream `WeilConjectures` match; exact public project matches in the two
  `GeneralAlgebraicallyClosedCoefficient*` modules. Direct search of the item id in
  `lean/WeilConjectures` (also repeated with the requested `grep -rn`) has no match.
  The exact names are also absent from `dag/lean_names_upstream.json`. The private generic helpers in the general module
  are not used as the public attachment.

Validation: the prescribed `deliver2.py --no-push` performs the server compilation of
an automatically generated module-mode `#check` probe for every recorded existing name,
followed by the maintainer's preflight. No new module requires a separate compile.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
