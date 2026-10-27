## Worker report

The module `Sheaf.CategoryTheory.ExactDerivedAdjunctionUnitShift` states
`CategoryTheory.Adjunction.mapExactDerivedCategory_unit_commShift`, with one
`sorry` and no new definitions. The first conjunct states the cochain unit
shift equation; the second states its descent for the specified localized
adjunction. Neither shift equation is an assumption. The five-step natural
language proof is included in the declaration docstring.

Hypotheses and clauses, matched to the unchanged node:

| Node | Lean rendering |
| --- | --- |
| Abelian categories A and B | `{A : Type uA} {B : Type uB}`, independent `[Category.{vA} A]`, `[Category.{vB} B]`, `[Abelian A]`, `[Abelian B]` |
| Ordinary unbounded derived categories and Q | Independent `[HasDerivedCategory.{wA} A]`, `[HasDerivedCategory.{wB} B]`; `DerivedCategory A`, `DerivedCategory B`, and `DerivedCategory.Q` used by the recorded adjunction construction |
| Additive exact L and P | `{L : A ⥤ B} {P : B ⥤ A}`, `[L.Additive]`, `[P.Additive]`, and preservation of finite limits and finite colimits for each |
| Specified original adjunction, unit and counit | `(a : L ⊣ P)`, with `a.unit`, `a.counit` |
| Termwise cochain application | `L.mapHomologicalComplex (ComplexShape.up ℤ)` and the same construction for P, used by `a.mapHomologicalComplex` |
| Exact-derived functors and fixed localization comparisons | `L.mapDerivedCategory`, `P.mapDerivedCategory`, and their `mapDerivedCategoryFactors` comparisons, used in `a.mapExactDerivedCategory` |
| Specified localization of degreewise adjunction | `a.mapExactDerivedCategory`, the independent-universe declaration owned by the dependency node; no arbitrary derived adjunction binder |
| Every integer shift | The `ℤ` parameter of each `NatTrans.CommShift` quantifies over every `a : ℤ` in its `shift_comm` field |
| Identity-in-each-degree e_L and e_P, natural isomorphisms | The inferred `Functor.commShiftMapCochainComplex` structures use `Functor.mapCochainComplexShiftIso`, defined by `NatIso.ofComponents` of `HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)`; its hom and inverse degree components are explicitly identified by `mapHomologicalComplex_commShiftIso_hom_app_f` and `_inv_app_f` |
| Zero and addition coherence | Fields `Functor.CommShift.commShiftIso_zero` and `commShiftIso_add` of those same standard instances; these are already supplied mathematical structure, not additional compatibility hypotheses |
| Terms L(X^(m+a)), P(Y^(m+a)) and signed differential | `CochainComplex`'s standard integer shift and `mapHomologicalComplex`; the standard comparison is a cochain isomorphism precisely by additivity applied to the signed differential, as read in `mapCochainComplexShiftIso` |
| Degreewise unit is a cochain map, component eta_(X^(m+a)) | Existing `a.mapHomologicalComplex (.up ℤ)` has unit components `a.unit.app (X.X m)` with `comm'` given by naturality; at the shifted complex its component is `a.unit.app (X.X (m+a))` using the standard shift indexing |
| Cochain unit equation | First conjunct `NatTrans.CommShift (a.mapHomologicalComplex (ComplexShape.up ℤ)).unit ℤ` |
| Localized unit equation, with fixed induced comparisons | Second conjunct `NatTrans.CommShift a.mapExactDerivedCategory.unit ℤ`; both exact-derived functor shift instances come from `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` |
| Equality of natural transformations on entire D(A) | `NatTrans.CommShift.shift_comm` is a natural transformation equality on the complete source category, not a restriction to Q-images or bounded objects |
| No additional resolution, monoidal or boundedness assumptions | The displayed binders end with the specified original adjunction and contain exactly the structural and exactness assumptions above |

For precision, expanding either conjunct's `shift_comm` at a complex/object X
and integer n gives

`(eta.app X)[n] = eta.app (X[n]) ≫ P.map ((L.commShiftIso n).hom.app X) ≫ (P.commShiftIso n).hom.app (L.obj X)`.

Here L and P denote the cochain or the exact-derived functors, respectively.
The identity functor's comparison is the identity; the composite functor's
comparison is exactly `P.map e_L ≫ e_P`, by
`Functor.commShiftIso_comp_hom_app`. This is the node's two equations, in
Lean's left-to-right composition order. The existing comparison and unit
constructions already provide the surrounding degreewise/coherence clauses;
restating their defining identities as additional sorry theorems would add
no mathematical content.

Dependency declarations read and used:

- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, in `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `lem-weil-pbc-exact-functor-derived-factorization`: its `mathlib_match`,
  `CategoryTheory.Functor.mapDerivedCategoryFactors`, plus `mapDerivedCategory`
  and its standard shift instances in
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- `def-weil-exact-derived-adjunction`: the recorded additional declaration
  `CategoryTheory.Adjunction.mapExactDerivedCategory` in
  `Sheaf.CategoryTheory.ExactDerivedAdjunction`. Its full body localizes
  `a.mapHomologicalComplex`, with the two factorization isomorphisms in the
  specified orientations. The dependency also owns the common-universe
  specialization `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction`;
  using the recorded generalization preserves independent universes without
  requiring a dependency repair.
- Proof dependency `lem-weil-pbc-localization-universal-property`:
  `CategoryTheory.Localization.natTrans_ext` in
  `Mathlib.CategoryTheory.Localization.Predicate` is imported as a proof import.
- The cochain adjunction's full definition and component lemma were read in
  `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`, publicly imported
  through the specified exact-derived adjunction dependency.

Source: read the newest blueprint under `literature/blueprint/latest/`,
`blueprint/sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md`.
It discusses coherence inherited from evaluation and adjunction units/counits.
The node explicitly labels its signed cochain/descent argument as an extracted
obligation, not a verbatim theorem; the module retains that distinction. The
node's recorded source path predates the unit-directory rename in latest.
No mathematical statement correction is needed.

Edge cases checked before writing: n=0 uses the standard zero comparison;
n=1 and n=-1 give the usual negative differential and the same unit component;
characteristic 2 removes the signs on both sides equally. The zero complex and
zero functors with their specified adjunction satisfy the same component
computation. Positive, negative and zero integer shifts are all quantified,
and every complex/derived object is covered without boundedness. All six
category and derived morphism universes are independent and explicitly bound.
There is no arbitrary or adjoint-transported replacement of the right shift
comparison. No STATEMENT-DISPUTED issue was found.

Searches for reuse (2026-10-24):

- `msearch.py leanfinder`, query: "The fixed degreewise adjunction of additive
  exact functors has a unit commuting with integer cochain shifts and its
  localization to the unbounded derived category". Eight hits: exact-functor
  shift and factorization instances, `mapDerivedCategoryFactors[h]`, and
  `Adjunction.derived[_unit]`/`derived'[_unit]`; none gives this fixed unit equation.
- `msearch.py loogle`, query:
  `CategoryTheory.Adjunction, CategoryTheory.NatTrans.CommShift`. Four hits:
  `Adjunction.CommShift.commShift_unit`, `commShift_counit`, `mk`, `mk'`.
  These assume adjunction shift compatibility or its unit equation, which
  this node must establish, so none is an exact match.
- `msearch.py leansearch`, query: "The unit of the localized degreewise
  adjunction of exact additive functors commutes with integer cochain shifts".
  Eight hits include `CompatibilityUnit`, `compatibilityUnit_unique_right`,
  adjoint-transported shift comparisons, `IsTriangulated.commShift`,
  `CommShift.commShift_unit`, `mk'`, and `shift_unit_app_assoc`. These are
  general compatibility interfaces or require extra hypotheses.
- `msearch.py grep`, query:
  `mapExactDerivedCategory|mapHomologicalComplex.*commShift|unit.*commShift`
  under `Algebra/Homology`. Seven hits give the standard shift comparisons
  and their degreewise identity lemma, not the localized adjunction unit result.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `mapExactDerivedCategory|exactDerivedAdjunction|unit.*[Cc]ommShift` and the
  blueprint id. Found the owning adjunction definition and specialization,
  unrelated exact-right-derived/K-flat statements, and private unit shift
  proofs for right derived functors with K-injective assumptions. Those have
  different functors/hypotheses; no exact reuse.
- `rg` over `dag/lean_names_upstream.json`, `lean/WeilConjectures`, `lean/Sheaf`
  for the chosen theorem name and this blueprint id returned no hits.

Validation: `scompile.py Q116 lem-pur-exact-adjunction-unit-shift-descent`
compiled the delivered file in both sandbox and library modes (2.3 s and
1.1 s); no errors or non-sorry warnings. The theorem proof is only `sorry`.
No new nodes, dependency modules, or statement changes are needed.

## Second reading by Q116

Self-check of the completed file against the node: the two conjuncts were
expanded using the actual `NatTrans.CommShift` signature and the identity and
composite functor comparison lemmas, recovering both equations with the
correct orientation. Read the fixed adjunction definition again to check
that the second conjunct refers to localization of the given degreewise
unit, and read `mapCochainComplexShiftIso` and its instance to check the
identity, signed differential, zero and addition clauses. All hypotheses
match the table above. No mismatch or change was found. This is a worker
self-check; the independent maintainer review follows delivery, as specified
in the dispatcher brief.
