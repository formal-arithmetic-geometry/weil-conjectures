## Worker report

Existing-declaration attachment; no Lean module is added and no proof is completed.
The item is stated by the following declarations in
`Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` (namespace
`WeilConjectures.GeneralAlgebraicallyClosedCoefficients`):

- `specialization_homCoordinates`, lines 903–911: the complete coordinate clause.
- `specialization_additive`, lines 924–925: additivity for the prescribed preadditive
  structures. `Functor.Additive.map_add` is exactly the asserted sum formula.
  `CategoryTheory.Functor.preservesZeroMorphisms_of_additive` and `Functor.map_zero`
  give its zero formula directly. Mathlib's instance is at
  `Mathlib/CategoryTheory/Preadditive/AdditiveFunctor.lean:68`.

These are existing statements, not a claim of axiom closure: the coordinate theorem
currently has `sorry`. The additive theorem already has a proof in the source; it is
reused unchanged, as required by the existing-declaration rule.

Read the full item, its three proof steps, every statement dependency's statement
and Lean record or Mathlib match, the relevant recorded source declarations and
normalization docstrings, and the latest blueprint
`sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/_section.md` (the displayed Hom
colimit and item 4). The source module was also fetched from the live server using
`scompile.py --source Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`; its
specialization declarations agree with the local source.
No repair note for this item was present.

Hypothesis and clause correspondence:

| Node text | Lean rendering in the existing module |
| --- | --- |
| Finite-field datum D | Section variable `(D : FiniteFieldDatum.{d})`, line 767; no relationship between its universe and the other two universes is imposed. |
| Prime l distinct from p | `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)` in the same section. |
| Algebraic closure Ω of Q_l | `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]`. |
| Arbitrary scheme Y, independent universe, no map to k | `(Y : AlgebraicGeometry.Scheme.{u})`, with `universe d u v w`. No finite type, noetherian, or base-field structure binder occurs. |
| Directed finite coefficient subfields I | `AlgebraicallyClosedCoefficients.Index l Ω`, the existing finite intermediate-field subtype `Padic.FiniteCoefficientFields l Ω`. |
| Fixed intrinsic raw rational stages | `GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E` is `sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y`; the finite-field version unfolds to the same category. `Coefficient` is the prescribed small model, allowing independent u and v. |
| Normalized systems S and S_D with proof parameters 0 and p | `stageSystem l Ω Y` and `SfAlgebraicallyClosedCoefficients.stageSystem D l hl Ω Y`, with the prescribed tensor transition/associator specifications. |
| Equality η and the particular equality-transport e | `specialization_stageSystem D l hl Ω Y` is the equality; `specialization` (lines 839–842) is literally `Pi.eqToEquivalence (fun S : StageSystem (Stage l Ω Y) ↦ S.PairCategory)` of that equality. |
| P and P_D | `Pair l Ω Y` and `SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y`, the existing literal-pair quotient categories of those systems. |
| The unique representative-normalized coordinates c and c^D | The two existing `homCoordinates` definitions choose the unique equivalences specified by their respective `homCoordinates_existsUnique` theorems. Both specifications send `mkHom L hA hB f` to `colimitOf A B L hA hB f`. |
| For every A, B and f | Explicit `(A B : Pair l Ω Y) (f : A ⟶ B)` in `specialization_homCoordinates`. |
| c^D(e(f)) = c(f), after equality identification | The theorem's `HEq` relates exactly `SfAlgebraicallyClosedCoefficients.homCoordinates (e.obj A) (e.obj B) (e.map f)` and `homCoordinates A B f`. Its result types are the two prescribed dependent colimits identified by the stage-system equality; there is no arbitrary comparison map or extra premise. |
| e(f+g) = e(f)+e(g) for all parallel arrows | `(specialization D l hl Ω Y).functor.Additive`, the statement of `specialization_additive`; unfolding Mathlib's `Functor.Additive` gives exactly this universal formula. |
| e(0) = 0 | The standard `preservesZeroMorphisms_of_additive` instance applied to that same functor, then `Functor.map_zero`; no zero object is chosen anew. |
| Already prescribed preadditive structures | Both source and target `homAddCommGroup` definitions are `(homCoordinates A B).addCommGroup` (general module lines 387–390; finite-field module lines 1006–1012). Their `preadditive` instances use these groups. `specialization_additive` has no new group-structure or arbitrary additive-instance parameter. |

Dependency declarations inspected and reused by these existing statements:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- Mathlib `NumberTheory.Padics.PadicNumbers`: `Padic`; Mathlib
  `FieldTheory.IsAlgClosed.Basic`: `IsAlgClosure` (field extension algebraic and
  algebraically closed). These are the matched notions for the l-adic and closure nodes.
- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`: `Padic.FiniteCoefficientFields`,
  the finite-dimensional intermediate-field subtype, with the base/compositum.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and its full category;
  these use derived completeness and constructible positive reductions with one common
  finite cohomological interval.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory` (the raw
  `ScalarLocalization`, no Karoubi completion) and `FiniteFieldDatum.sfRationalCategory`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficientStages`: `Stage`,
  `stageSystem_existsUnique`, `stageSystem`, and `specialization_transition`.
- `Sheaf.CategoryTheory.ExactStagePairData`: `CategoryTheory.StageSystem.ExactStagePairData`;
  its underlying pair category is the already existing `StageSystem.PairCategory`,
  reused here through each `Pair` abbreviation. No new exact-stage datum is required
  for this assertion about those fixed pair categories.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: the recorded specialization
  dependency's `specialization_stageSystem`, `specialization`, `specialization_pairs`,
  `specialization_transport`, and `specialization_comparisons`.
- `Sheaf.Paper.GeneralPairHomCoordinates`: `pairHomCoordinates`, on exactly the same
  quotient, transport maps, normalized coordinates and fixed group structures.
- `Sheaf.Paper.SfAlgebraicallyClosedCoefficients`: the recorded intrinsic finite-field
  interface's `stageSystem`, `Pair`, `transportHom`, `ColimitHom`, `homCoordinates_existsUnique`,
  `homCoordinates`, `homAddCommGroup`, and `preadditive`.
- Mathlib `Algebra.Colimit.Module`: `AddCommGroup.DirectLimit` and `DirectLimit.of`;
  Mathlib `CategoryTheory.Preadditive.Basic`: `CategoryTheory.Preadditive`.

Edge cases checked by reading the quantifiers and definitions: the empty scheme is
allowed; zero arrows and f=g=0 are included; A and B may use different coefficient
fields; a representative may be enlarged to any common later field; identity and
repeated fields are included in the system equality; the bottom field exists, so
no spurious nonempty representative-index assumption is imposed on the theorem.
The universes d, u, v are independent. No geometric finite-field datum on Y is added.
No statement dispute or correction is needed.

Searches actually run for this item:

- `msearch.py ... leanfinder "Equality transport between normalized coefficient pair
  categories preserves normalized Hom colimit coordinates and addition"`: eight
  hits, mostly scheme normalization/coproduct identities and free monoidal
  normalization; none is the coefficient specialization statement.
- `msearch.py ... loogle "CategoryTheory.Functor.Additive, CategoryTheory.Functor.map_zero"`:
  zero hits for that combined query.
- `msearch.py ... grep "specialization_homCoordinates|specialization_additive|eqToEquivalence"`:
  six Mathlib hits, on generic equality equivalences; no coefficient-specific theorem.
- `msearch.py ... leansearch "An additive functor preserves zero morphisms and addition
  on each morphism abelian group"`: eight hits including `Functor.Additive`,
  `Functor.Additive.map_add`, and `Functor.preservesZeroMorphisms_of_additive`.
  These confirm the zero/sum interpretation, not the coefficient normalization clause.
- `rg -n 'specialization_homCoordinates|specialization_additive|lem-pur-general-specialization-hom-additivity'
  lean/WeilConjectures lean/Sheaf dag/lean_names_upstream.json`: exactly the two
  coefficient-specific declarations above, both in the existing General module;
  no upstream duplicate or node-id attachment. The equivalent node-id search was
  included in this same recursive search. Also ran the prescribed literal
  `grep -rn` node-id search on `lean/WeilConjectures`, which returned no matches.

The exact project match takes priority over writing another theorem. Only the item's
`lean` field changes; its statement, dependencies and accepted split stay unchanged.
No new nodes and no dependency modules are supplied.

## Second reading by NF

This is a second pass by the same dispatcher worker; no other agent was started,
following the explicit dispatcher instruction. The maintainer's independent review
remains the independent reading.

Reopened the node's two conclusion paragraphs and the source at lines 767–925.
Checked that the section binders include exactly D, l prime, l ≠ D.p, Ω an algebraic
closure, and arbitrary Y with independent universes. Checked the body of
`specialization`, not just its name: it is the required equality transport. Checked
both coordinate definitions and their representative specifications: the `HEq`
is on their actual colimit values, and includes arbitrary f. Checked the two
`homAddCommGroup` bodies: their laws predate specialization. Finally opened Mathlib's
`Functor.Additive` and its zero-preserving instance: the additive conclusion gives
both universally quantified arrow formulas, with no extra hypothesis.
No mismatch was found and no Lean code or mathematical node text was changed.

Validation: `scompile.py NF lem-pur-general-specialization-hom-additivity
scratch/CheckSpecialization.lean` passed on the server, with no warnings. The sandbox
check took 44.4 s and the library check 3.5 s, both within 60 s. The scratch probe
uses independent d, u, v, applies both existing theorems, synthesizes `Additive`
and `PreservesZeroMorphisms`, and checks `Functor.map_add` and `Functor.map_zero`.
The zero-preserving synthesis selects the existing triangulated-functor instance;
the separately inspected Mathlib additive-functor instance also gives the same
zero conclusion directly from the attached additive statement. The probe contains
no theorem or definition and is outside `lean/`, so it is not delivered.
`deliver2.py NF lem-pur-general-specialization-hom-additivity --no-push` printed
`OK (dry run)` at f19023ceb5e: preflight and existing-declaration compilation passed.
