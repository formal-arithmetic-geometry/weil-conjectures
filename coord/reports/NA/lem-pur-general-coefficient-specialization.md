## Worker report

Existing-declaration attachment. The four public declarations in
`Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` are:

- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.specialization_commShift_existsUnique`
  (line 937): the unique identity-normalized coherent shift comparison.
- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.specialization_commShift`
  (line 948): the instance selecting this uniquely specified comparison.
- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.specialization_distinguished`
  (line 960): preservation and reflection of distinguished triangles.
- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.specialization_exact`
  (line 972): exactness for that comparison.

No Lean module is written: these are the retained statements explicitly named in the
node's source, with their full signatures and docstrings read. The first and third still
have `sorry`; this is a stage-2 attachment, not a claim of proof completion. The node's
statement, dependencies and proof plan are unchanged. The `lean.statement` is the
verbatim signature of the primary theorem, before `:= by`.

Hypotheses and clauses, individually:

1. The global finite-field datum is the section parameter `D : FiniteFieldDatum.{d}`.
   The prime is `l : ℕ` with `[Fact l.Prime]`, and the distinctness hypothesis is
   `hl : l ≠ D.p`. The datum's exponent, field cardinality and chosen closure are
   fields of the recorded structure, not extra assumptions on Y.
2. The chosen coefficient closure is `Ω : Type v` with `[Field Ω]`,
   `[Algebra (Padic l) Ω]` and `[IsAlgClosure (Padic l) Ω]`.
3. The only scheme parameter is `Y : AlgebraicGeometry.Scheme.{u}`. Universes `u`,
   `v`, and `d` are independent; no map from Y to D.k, finite-type or noetherian
   hypothesis occurs.
4. The finite coefficient index is `AlgebraicallyClosedCoefficients.Index l Ω`,
   reusing `Padic.FiniteCoefficientFields`. `Stage l Ω Y E` is precisely
   `sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y`. Its coefficient
   is the prescribed Shrink model. `SfAlgebraicallyClosedCoefficients.Stage`
   unfolds through `FiniteFieldDatum.sfRationalCategory` to the same raw category.
   The integral predicate is `sfIntegralConstructible`, and rationalization is
   `ScalarLocalization`; no Karoubi completion is used.
5. The normalized scalar systems are the two `stageSystem`s. The general transition
   has proof parameter 0, and the intrinsic finite-field transition has D.p and hl.
   `specialization_stageSystem` is their equality. The definition `specialization`
   is literally `Pi.eqToEquivalence (fun S : StageSystem (Stage l Ω Y) ↦
   S.PairCategory) (specialization_stageSystem D l hl Ω Y)`. It is the prescribed
   equality functor, with no arbitrary equivalence parameter.
6. `Pair l Ω Y` and `SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y` abbreviate
   those systems' `PairCategory`. The existing `preadditive` instances are the
   prescribed colimit Hom structures; `specialization_additive` and
   `specialization_homCoordinates` are exactly the recorded additivity dependency.
7. The general `hasShift` and `inclusionCommShift` are selected from the recorded
   `shift_existsUnique`; the finite-field versions are selected from its intrinsic
   counterpart. Their representative formulas use the fixed
   `stageTransitionCommShift`. The canonical `transIso` compatibility is the
   recorded `transitionIso_commShift`, not a replacement comparison.
8. Existence and uniqueness is `∃! c : (specialization D l hl Ω Y).functor.CommShift ℤ`.
   `CommShift` stores a natural isomorphism for every integer plus its shift-zero
   and shift-add equations. Thus uniqueness is equality of the entire coherent
   comparison. The predicate quantifies over every `n : ℤ` and `A : Pair l Ω Y`.
   Its `HEq` identifies the hom component with the identity of the displayed shifted
   target pair after the prescribed object equalities. This matches precisely the
   node's identity normalization, including the direction e(A[n]) to e(A)[n].
9. The `specialization_commShift` instance is
   `(specialization_commShift_existsUnique D l hl Ω Y).exists.choose`.
   Hence the subsequent statements use this very comparison. Both `pretriangulated`
   instances come from `StageSystem.commonStage_verdier_existsUnique` for the actual
   systems, with the distinguished sets characterized by `distinguished_iff`.
10. `specialization_distinguished (T : Triangle (Pair l Ω Y))` states exactly
    `T ∈ distTriang (Pair l Ω Y) ↔ (specialization D l hl Ω Y).functor.mapTriangle.obj T
    ∈ distTriang (SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y)`.
    This covers every triangle and both implications. `specialization_exact` is
    `.functor.IsTriangulated` with the same installed `CommShift` instance.
11. For the final literal-cone assertion, retain the supplied L,C,u,i,p and the
    actual `StageSystem.commonStageCone`; its third object is `(L,C)`, its first
    arrow is `mkHom L hA hB u`, its second is `isoToStage.hom ≫ inclusion.map i`,
    and its third is `inclusion.map p ≫ inclusion.commShiftIso.hom.app _ ≫
    shiftFunctor.map isoToStage.inv`. No fresh cone is chosen. The already recorded
    `specialization_pairs` fixes `(L,C)` and every finite representative (including
    representatives of the second and third arrows); `specialization_transport`
    fixes their associator-conjugated transitions. By the definition of Mathlib's
    `Functor.mapTriangle`, the first two image arrows are simply e.map of those
    arrows, and the third is e.map of the supplied third arrow postcomposed with
    the normalized c_1 component. That component is the identity by the primary
    theorem. Therefore the label, literal third pair and all three prescribed
    arrows are retained after the displayed equalities. This clause is the direct
    representative-level consequence of the existing dependency and normalization,
    not merely preservation of an unspecified isomorphic cone.

Dependency declarations inspected and reused:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- Mathlib `NumberTheory.Padics.PadicNumbers`: `Padic`; Mathlib
  `FieldTheory.IsAlgClosed.Basic` / `AlgebraicClosure`: `IsAlgClosure`, `AlgebraicClosure`.
- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`: `Padic.FiniteCoefficientFields`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and
  `sfIntegralConstructibleCategory` in `WeilConjectures`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `FiniteFieldDatum.sfRationalCategory` in `WeilConjectures`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficientStages`: the general `Stage`,
  `stageSystem_existsUnique`, `specialization_transition`,
  `specialization_transitionShift`, and fixed transition comparison instances.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `specialization_stageSystem`,
  `specialization`, `specialization_pairs`, `specialization_transport`,
  `specialization_homCoordinates`, `specialization_additive`, `shift_existsUnique`,
  `transitionIso_commShift`, and `distinguished_iff`, in the general namespace above.
- `Sheaf.Paper.SfAlgebraicallyClosedCoefficients`: the intrinsic `shift_existsUnique`,
  its `hasShift`, `inclusionCommShift`, `transitionIso_commShift`, `pretriangulated`,
  `distinguished_iff`, and `commonStage_cone`, in the intrinsic namespace above.
- `Sheaf.CategoryTheory.ExactStagePairData`: `CategoryTheory.StageSystem.ExactStagePairData`;
  `Sheaf.CategoryTheory.StageSystemCommonStageCones`: `commonStageCone` and
  `CommonStageDistinguished`; `Sheaf.CategoryTheory.StageSystemVerdier`:
  `CategoryTheory.StageSystem.commonStage_verdier_existsUnique`.
- Mathlib `CategoryTheory.Triangulated.Basic`, `.Pretriangulated`, `.Functor`:
  `Triangle`, `Pretriangulated`, `Functor.mapTriangle`, `Functor.IsTriangulated`;
  Mathlib `CategoryTheory.Shift.CommShift`: `Functor.CommShift`; Mathlib
  `CategoryTheory.Pi.Basic`: `Pi.eqToEquivalence`.

The current blueprint `sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/_section.md`
was read, particularly (2) and (4). The more specific normalization and specialization
assertions are the retained construction in the node's source.note and existing module
at lines 927–976, as its stage-1 review explicitly records. No source correction is needed.

Edge cases checked by reading the binders and defining formulas: arbitrary/empty Y;
independent scheme, closure and datum universes; n=0, negative n, and n+m (the full
`CommShift` coherence is quantified); E=L and repeated fields (no strict inequalities);
zero and identity arrows/cones (no nonzero assumptions); any supplied cone rather than
an existentially chosen replacement. The index is nonempty via the base coefficient
field and directed by compositum, already recorded in the dependency.

Searches performed on 2026-10-27 with msearch.py:

- LeanFinder: "The equality specialization of normalized coefficient pair categories
  has a unique identity normalized coherent integer shift comparison and preserves
  and reflects distinguished triangles". Eight hits, including
  `Functor.map_distinguished_iff`, `Functor.distTriang_iff`, and generic triangulated
  equivalence lemmas; none specifies these coefficient systems or their normalization.
- Loogle: `CategoryTheory.Functor.CommShift.ofIso`. Four hits, the construction and
  compatibility/component lemmas. These transport comparisons along an arbitrary
  functor isomorphism; they do not specify this identity-normalized specialization.
- Mathlib grep: `specialization_commShift_existsUnique|specialization_distinguished|CommShift.*ofIso`.
  Two hits, DerivedCategory/Basic.lean:159,162, generic `ofIso` constructions.
- LeanSearch: "Equality transport of coefficient pair categories is exact with a unique
  identity shift comparison and fixes finite stage cone arrows". Eight generic hits,
  including shift zero, shift equivalence, triangulated-equivalence symmetry and
  mapping-cone shift isomorphisms; no coefficient-specific statement.
- rg of `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for
  `specialization_commShift_existsUnique|specialization_distinguished|specialization_exact`:
  the exact retained declarations are in GeneralAlgebraicallyClosedCoefficients.lean,
  lines 937, 960, 972; none in WeilConjectures or the upstream names index.
  The item-id search in both source trees has no occurrence. The existing declarations
  and all relevant dependency docstrings/signatures were opened, not inferred from names.

No missing notion, unusable dependency, statement dispute, or statement correction was found.
Validation is the prescribed deliver2.py dry run, which uses scompile.py to check every
recorded existing declaration in module mode against the published server library.

## Second reading by NA

No second reading by a worker: this dispatcher assignment requires direct delivery;
the maintainer's independent review is the independent reading. The author checked
all clauses against the node and the existing source as detailed above.
