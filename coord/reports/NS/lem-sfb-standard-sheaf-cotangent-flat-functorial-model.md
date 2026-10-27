## Worker report

The delivery states `TopCat.SheafCotangent.exists_flatFunctorialModel` in
`Sheaf.Topology.StandardSheafCotangentFlatModel`. Its sole postponed theorem
asserts simultaneous existence of the fields of `FlatFunctorialModel C S`.
The model groups its strict-map clauses in `functoriality : StandardSheafFunctoriality C S`
and its scalar clauses in `scalar : StandardScalarFunctoriality C S`; the four
flatness/stalk/vanishing clauses are direct fields. Field names in the table
below refer to these specified subrecords where appropriate. Grouping the
records limits repeated kernel checking without changing their assertions.
The module constructs only labels, labeled differential vectors, transparent
specializations of existing objects, and explicitly normalized arrows. It does
not choose any construction from a `Nonempty` assertion. All theorem proofs
remain `sorry`.

Source read: `literature/stacks-project/cotangent.tex`, standard sheaf resolution
and definition of the cotangent complex (08SR, 08SS), the following commutative
square construction, inverse image (08SV), and the flatness observation in the
proof of the ringed-space triangle (08T4). The existing node's eleven-step proof
is retained, and all eleven steps appear in the theorem docstring. K-flatness
uses the bounded-above-flat criterion (06YQ, rather than the stale 06YS tag).

Clause-by-clause rendering:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| Any topological space and map of commutative ring sheaves | `T : TopCat.{u}` and `f : Arrow (T.Sheaf CommRingCat.{u})`, universally quantified in the model fields. `f.left`, `f.right`, and `f.hom` are A, B, and the given map. |
| Module sheaves and their derived categories | The recorded `ringedSiteModules`, Mathlib `CochainComplex` and `DerivedCategory`, and `HasDerivedCategory` binders for the selected localizations. These localization choices are available from `HasDerivedCategory.standard`, not additional mathematical assumptions. |
| Standard P and alternating-face K, including zero positive terms | `standardSheafComplex C S f` is exactly `sheafComplex (S.sheaves T f).sections`. The dependency's `StandardSheafModel` identifies it with `negativeComplex` of its actual differential simplicial module, itself identified with differential scalar-extension sheaves; `positive_zero` states the positive vanishing explicitly. Its section model is the sectionwise standard complex, not an arbitrary replacement. |
| Every stalk and every nonpositive degree is free on the stated variables | `stalk_basis T f t n` supplies `Module.Basis (standardVariables (stalkArrow f t) n)` over `(stalkArrow f t).right`, on the actual module stalk presentation supplied by `S.stalks`. The vectors are fixed by `comparison.inv` applied to `variableDifferential`: exactly `1 ⊗ dX_e`, with the coefficient-first tensor convention. `S.stalks.underlying` and `.scalar` identify that presentation with the actual stalk and germ action. |
| Flatness of every term | `flat T f i` uses the recorded `SheafOfModules.IsFlatOnSite`, whose tensor functor is the actual sheafified tensor and whose exactness means finite limits and colimits. |
| K-flatness of K | `kflat T f` uses the recorded `CochainComplex.IsKFlatIndependentCoefficients`, quantifying over all acyclic complexes and their total sheaf tensor. |
| Every B to C, with no coefficient-flatness assumption | `D : SheafOfModules.DerivedChangeOfRingsCochainModel φ` binds the recorded presentation; `represents` says its actual counit on K is invertible. `D.obj_eq` pins ordinary extension to `changeOfRings`; the resulting isomorphism is the canonical derived extension comparison, in the source-to-ordinary-model direction. |
| Coefficients and free generators map recursively | `StandardPolynomialMap.section_formula` is normalized by `standardSquareMap`, whose degree-zero rule sends coefficients by the left map and labels by the right map, and whose successor rule iterates that assignment. It holds on every sectionwise polynomial, not only selected generators. |
| Faces, degeneracies, augmentations | `StandardPolynomialMap.map` is a simplicial natural transformation, hence commutes with every simplicial operator; `.base` and `.augmentation` give the other two commutative squares. The dependency fixes the standard faces and degeneracies. |
| Induced differential formula | `chain_generator` gives the formula on local `complexGenerator` tensors in each degree, using the same standard ring-square map. The dependency's generator normalizations identify them with the actual differential sheaf tensors. |
| Strict identities and compositions | `polynomial_id`, `polynomial_comp`, `chain_id`, and `chain_comp` are equalities of actual maps. These include continuous squares. |
| Ordinary tensor linearization and canonical derived arrows | `StandardLinearization.map` is a chain map over the actual ordinary extension functor `D.E`. Its `.formula` on every local tensor is `c * map(x)`. The cast uses `D.obj_eq`, not an unrelated functor. `standardDerivedArrow` is defined as `D.ε.app K ≫ DerivedCategory.Q.map m.map`, precisely the source's canonical arrow on the standard model. `represents` makes its first factor the prescribed comparison isomorphism. |
| Open restriction and continuous inverse image | All polynomial formulas and `chain_generator` quantify over `RingSquare v f g` for arbitrary continuous `v`. They are natural sheaf maps, so commute with open-set restrictions. `polynomial_inverse` states invertibility of the adjoint polynomial comparison for `inverseImageSquare`. `inverseStandardMap` is exactly the adjoint fixed by `S.inverse.normalization`; `inverse_naturality` is its actual chain-map commutative square with any ring square. `S.inverse_comp` supplies composition coherence of the same comparisons. Open inclusions are included. |
| Consecutive coefficient extensions, with the prescribed reassociation | `successive_tensor` applies both linearizations to `d ⊗ (c ⊗ x)` and compares the result with the direct linearization applied to `(d * r(c)) ⊗ x`. This is exactly the symmetric-order version of `(x ⊗ c) ⊗ d ↦ x ⊗ r(c)d`. Local pure tensors generate the sheafified extensions. No reassociation is freely chosen. |
| Same compatibility after continuous inverse image | `successive_tensor` holds for every space and every pair of squares, in particular for the inverse-image arrows and the inverse images of the two squares. `inverse_naturality` identifies their maps with the inverse images of the original maps under the fixed comparisons. Thus the equation includes the transported case, not merely an independent choice of maps on the new space. |

Dependency declarations used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `DerivedCategory.Q`, `HasDerivedCategory`.
- `Sheaf.Topology.SheafCotangentComparison`: `Comparison`, `sheafComplex`,
  `sectionArrow`, `sectionElement`, `polynomialSection`, `RingSquare`,
  `identitySquare`, `composeSquare`, `inverseImageArrow`, `inverseImageSquare`,
  `inverseAdjunction`, `pullbackComplex`, `pushforwardComplex`, `stalkArrow`;
  the full signatures and coordinate/normalization fields were read.
- `Sheaf.RingTheory.CotangentResolutionCoherence`: `Coherence`, `standardTerm`,
  `standardSquareMap`, `complexGenerator`, `standardComplex`, `negativeComplex`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel`, owned by the landed
  definition node `def-sfb-derived-change-of-rings-cochain-model`. Its prescribed
  object function, universal counit and K-flat computation are used under
  universal quantification over `D`. Existence is a proof input, not a field
  repeated in this statement.
- `Sheaf.Paper.SemilinearSystemModels`:
  `WeilConjectures.SemilinearSections.extensionUnit`; the scalar-tensor helper
  specializes this already recorded unit by multiplying by the coefficient.
  It does not reimplement module sheafification or its unit.

The already-landed definition nodes for the cochain presentation, semilinear
scalar unit, and cotangent coherence data are added to `stmt_deps` under the
standing rule permitting additions of recorded nodes. The mathematical statement, proof,
proof dependencies, and all other node fields are unchanged. No dependency
record is repaired and no new independent notion/node is needed. The helpers
are specific coordinates or canonical arrows of this item's own assertion and
are all listed in `lean.declarations`. A graph traversal checked that neither
added dependency reaches this item.

Proof imports include the bounded-above-flat criterion, module-stalk tensor
comparison, module-stalk exactness, and module pullback/tensor comparison. The
Kähler polynomial-basis input is a Mathlib leaf:
`KaehlerDifferential.mvPolynomialBasis` in `Mathlib.RingTheory.Kaehler.Polynomial`;
its arbitrary variable type, vector formula, and derivative coordinates were read.

Edge cases checked before writing: empty T (the stalk clause is vacuous, while
flatness and K-flatness remain assertions); zero rings (no `Nontrivial`
assumption is introduced); arbitrary infinite variable sets; n = 0 (labels are
B_t, not P_0); all positive degrees; A = B (the standard model is retained,
not replaced by the zero complex); identity squares and identity continuous
maps; non-flat B to C (only K's K-flatness is used); all characteristics; open
inclusions; arbitrary continuous maps. No finite-type or bounded-below hypothesis
is added. All binders and universes are explicit and `autoImplicit` is false.

Searches performed using the assigned msearch.py wrapper:

- LeanFinder: "The standard simplicial polynomial cotangent complex of sheaves
  of rings has flat terms, is K flat, and its canonical maps are strictly
  functorial". Eight hits, including presheaf differentials and formally smooth
  Kähler projectivity; none gives this assertion.
- Loogle: "CochainComplex.IsKFlatIndependentCoefficients, Module.Basis,
  SheafOfModules.changeOfRings". No hits; the project predicate is not in the
  Mathlib search index.
- Mathlib grep: "cotangent|Cotangent", RingTheory. Twenty-five displayed hits
  concern naive cotangent spaces and algebra extensions, not the sheaf assertion.
- LeanSearch: "standard cotangent complex of sheaves flat K-flat functorial".
  Eight hits on representably flat functors, naive H1 and cotangent base change;
  none matches.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for `SheafCotangent`,
  standard K-flat models, and proposed names: found the comparison and its
  consumers, not this theorem; found the scalar-extension unit and reused it.
  The exact node ID has no upstream source match. The existing declaration
  index was searched as well.

No mathematical statement dispute or statement correction was found.

## Second reading by NS

The assigned worker made a separate self-check of the node and Lean file.
No independent worker reading is claimed: since 2026-10-17 the worker delivers
directly and the maintainer's independent review is the required review.

The pass checked each row above, especially the label type at n = 0, the
inverse direction of the stalk coordinate isomorphism, the scalar-first tensor
order, use of the existing module stalk action, strict equality of actual maps,
and the direction of the canonical derived-extension counit. It added an
explicit inverse-image chain naturality square rather than relying on prose,
and changed the scalar helper to reuse the established extension unit. It
also checked that `S` and `C` are the dependency's canonically normalized
presentations, not extra flatness or map hypotheses, and that coefficient
extension remains quantified over arbitrary new coefficient rings.

## Returned-delivery repair

Repaired H2 from immutable head `dd0bc11b81a7`: replaced the added statement
dependency `lem-pur-derived-change-of-rings` by the owning landed definition
`def-sfb-derived-change-of-rings-cochain-model`, and replaced the public import
of `OrdinaryDerivedChangeOfRings` by `DerivedChangeOfRingsCochainModel`. Removed
`StandardScalarFunctoriality.extension`, which repeated the dependency's
existence theorem. The remaining clauses universally quantify over the
cochain-model structure and use its actual `E`, `obj_eq`, and `ε`; existence of
that structure remains the unchanged proof dependency in step 6. Its theorem
is available from the directly imported owning module, so the ordinary-ring
wrapper is unnecessary.

Addressed the advisory by adding the already-landed definition node
`def-trf-cotangent-resolution-data`, which owns the `Coherence` binder and
its standard coordinate declarations. No dependency node is edited. Comparing
the saved packet with the current shared node shows changes only in `lean`
and additions to `stmt_deps`; the source statement and accepted split remain
unchanged. The delivery wrapper rebases the packet onto the current server base.

The repair self-check verified that no remaining declaration uses the removed
field, all scalar clauses still quantify over arbitrary coefficient maps, and
the canonical counit and normalized chain maps remain unchanged. The edge-case
and clause correspondence above therefore continues to apply.

Validation after the repair: `scompile.py` passed both the sandbox check
(39.3 seconds) and the library-module check (46.0 seconds), with no compiler
errors or warnings. The recorded theorem signature matches the file verbatim;
all lines meet the width rule, and the sole postponed theorem remains
`exists_flatFunctorialModel`. The three added statement dependencies were
checked against the current DAG and introduce no cycle.
