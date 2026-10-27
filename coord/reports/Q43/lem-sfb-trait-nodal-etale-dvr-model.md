## Worker report

Stage 2 statement of `lem-sfb-trait-nodal-etale-dvr-model`, in
`Sheaf.AlgebraicGeometry.TraitNodalEtaleDvrModel`, declaration
`AlgebraicGeometry.exists_trait_nodal_etale_dvr_model`. Its only proof is `sorry`.
No definition, additional theorem, new node, dependency repair, or mathematical
statement correction is introduced. The existing stage-1 split reviewed by O1 is
preserved in full. Being split does not supply its missing Lean statement; this
delivery adds that statement, addressing the previous unchanged-item refusal.

I read all seven proof steps and both source passages in
`literature/stacks-project/models.tex`, labels
`lemma-etale-local-at-worst-nodal` (0CDD) and
`lemma-blowup-at-worst-nodal` (0CDE). I read all statement-dependency nodes and
the signatures and documentation of their recorded declarations. The existing
compact-object example is a withdrawn module in the current live clone; the
module header and public-section conventions follow the current published
`PureDimension`, `StrictSemistableCurve`, and `NodalPointEtaleLocality` modules.
The current released stage-1 re-split note preserves the statement. It is
separate from this stage-2 ownership repair; the stage-1 proof is retained.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| A DVR R, with chosen uniformizer pi | `R : Type u`, `[CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`, `π : R`, `hπ : Irreducible π`. The recorded `IsDiscreteValuationRing.irreducible_iff_uniformizer` identifies this exactly with generation of the maximal ideal. |
| S is Spec R; f is flat and locally of finite presentation | `X : Scheme.{u}`, `f : X ⟶ Spec (.of R)`, `[Flat f] [LocallyOfFinitePresentation f]`. |
| Every nonempty geometric fibre is reduced and pure of dimension one | `hfib` quantifies over algebraically closed `Ω : Type u` and every geometric map `g : Spec (.of Ω) ⟶ Spec (.of R)`; it asserts `IsReduced (pullback f g)` and `(pullback f g).IsPureDimension 1`. Both properties hold for an empty scheme, so this imposes exactly the required condition on nonempty fibres and permits empty fibres. Testing all algebraically closed geometric points is the geometric-fibre formulation; in particular it includes the chosen algebraic closures in the dependency definition. |
| Every nonsmooth geometric-fibre point has the specified completion over Ω | `hnodal` quantifies over every `z : ↥(pullback (C := Scheme.{u}) f g)` and uses `z ∉ (pullback.snd f g).smoothLocus`. The `Nonempty (@AlgEquiv Ω ...)` is between the maximal-ideal `AdicCompletion` of the stalk and `MvPowerSeries (Fin 2) Ω` modulo the ideal spanned by `X 0 * X 1`. The source algebra structure is the canonical `completedLocalScalarMap`; thus the isomorphism respects Ω, rather than being merely a ring isomorphism. There is no extra closed-point restriction. |
| Every point of the special fibre | `x : X` with `hx : f x = IsLocalRing.closedPoint R`. This describes the image of the special fibre without choosing a residue-field-valued lift. |
| A DVR R' with an injective local étale map from R | Existential `R' : Type u` with its `CommRing`, `IsDomain`, and `IsDiscreteValuationRing` structures, and `φ : R →+* R'`; the conjuncts are `Function.Injective φ`, `IsLocalHom φ`, and `Etale (Spec.map (CommRingCat.ofHom φ))`. |
| The image of pi is a uniformizer in R' | `Irreducible (φ π)`, using the same recorded DVR equivalence. |
| An R'-scheme U and a point above x | `U : Scheme.{u}`, `u : U`, `p : U ⟶ X` and `p u = x`. Its R'-structure is explicitly `q ≫ (StrictSemistableModel.nodal c).baseMap`. |
| An étale S-map to X and to the indicated affine model | Existential `p`, `q` with `Etale p ∧ Etale q`. The equality `p ≫ f = q ≫ ...baseMap ≫ Spec.map ...φ` makes both maps S-morphisms for that very R'-structure. |
| A is either R'[a,b]/(ab) or R'[a,b]/(ab-pi^n), n ≥ 0 | `q` targets `(StrictSemistableModel.nodal (A := .of R') c).scheme`, and `c = 0 ∨ ∃ n : ℕ, c = (φ π) ^ n`. The existing `strictNodalRing` is precisely `MvPolynomial (Fin 2) R'` modulo the principal ideal `(X 0 * X 1 - C c)`. A natural number is the specified nonnegative integer exponent. |
| If the generic fibre is smooth, zero parameter is unnecessary; at nonsmooth x the exponent is ≥ 1 | The final implication assumes `Smooth (pullback.snd f (Spec.map ... (algebraMap R (FractionRing R))))` and asserts `∃ n : ℕ, c = (φ π) ^ n ∧ (x ∉ f.smoothLocus → 1 ≤ n)`. Thus one chosen chart satisfies the conditional refinement, including smooth x with n=0. `FractionRing R` fixes the canonical fraction field; smoothness is invariant under an isomorphism with any other fraction field. |
| No quasi-compactness, excellence, completeness, or residue-field perfection | No such hypotheses or instances are present. In particular the completion occurs only in the geometric singularity hypothesis; R is never assumed complete. |

Dependency declarations used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`,
  `IsDiscreteValuationRing.irreducible_iff_uniformizer` (interpretation of both
  occurrences of `Irreducible`).
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.snd`, used with the actual geometric point.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, `Scheme.Hom.smoothLocus`.
- `Mathlib.RingTheory.AdicCompletion.Basic`, together with the ring structure in
  `Mathlib.RingTheory.AdicCompletion.Algebra`: `AdicCompletion`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `MvPowerSeries.X`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.Algebra.Polynomial.Basic`: the polynomial convention; the existing
  two-variable model uses `MvPolynomial` from `Mathlib.RingTheory.MvPolynomial.Basic`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, the algebraically closed
  field notion also recorded by `def-weil-algebraic-closure`.
- `Sheaf.TraceFormula.StrictSemistableCurve`: `strictNodalRing`,
  `StrictSemistableModel.nodal`, `.scheme`, `.baseMap`. Its existing node
  `def-trf-strict-semistable-curve` is appended to `stmt_deps` solely to reuse this
  real quotient algebra and its coefficient-induced projection. The theorem
  does not assume the much stronger `StrictSemistableCurve` structure.
- `Sheaf.AlgebraicGeometry.NodalPointEtaleLocality`:
  `Scheme.Hom.completedLocalScalarMap`, with its canonical scalar structure on
  the completion. Its existing definition-node owner `def-trf-completed-local-scalar-map` is
  appended to `stmt_deps` so this helper is reused rather than copied.
- `Mathlib.RingTheory.Localization.FractionRing`: `FractionRing` for the generic fibre.

The stated proof dependencies are plain imports: smooth étale source locality
(`Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource`), smooth composition and étale
composition/cancellation (`Mathlib.AlgebraicGeometry.Morphisms.Smooth` and `.Etale`,
already public for statement use), étale base change and finite-limit preservation
(`Mathlib.CategoryTheory.Limits.MorphismProperty`), the maximal-ideal identity
(`Mathlib.RingTheory.Unramified.LocalRing`), étale smooth zero-dimensional fibres
(`Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`), and flat lfp openness
(`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`).
`lem-sfb-dvr-nodal-etale-local-form` currently has neither a `lean` record nor a
`mathlib_match`; it is proof-only here, so its nonexistent module is not imported.
Its place in the proof plan is retained in the docstring and unchanged DAG proof.

Edge cases checked before writing:

- Empty X, an empty special fibre, and empty geometric fibres are allowed.
  The pointwise conclusion is vacuous if there is no special-fibre point.
- Disconnected geometric fibres are allowed: no `ConnectedSpace` or nonemptiness
  assumption was borrowed from `HasNodalGeometricFibres`.
- The persistent node `ab=0` is allowed without smoothness of the generic fibre.
- The smooth model `ab=1` is retained by n=0; at a nonsmooth x the conditional
  positive-exponent clause rules it out, while `ab=pi` and `ab=pi^2` are retained.
- The refinement uses nonsmoothness over S, not nonregularity of the total space:
  `ab=pi` has regular total space but must still allow exponent one here.
- No characteristic assumption, including in characteristic two, occurs.
- All schemes, fields, and rings use the common arbitrary universe u; the
  geometric tests are not placed in an independently smaller universe.
- Both structural maps are the canonical coefficient maps, not arbitrary maps;
  the equality in the conclusion enforces the required commutative diagram.

Searches (2026-10-22):

1. `msearch.py ... leanfinder "Etale local equations for a nodal curve over a discrete valuation ring with fixed uniformizer and smooth generic fibre"`: 8 hits, including `StandardEtalePair`, `StandardEtalePresentation.P`, and `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`. No fixed-uniformizer nodal chart theorem.
2. `msearch.py ... loogle "IsDiscreteValuationRing, Algebra.Etale"`: 0 hits.
3. `msearch.py ... grep "nodal|semistable|uniformizer.*etale" AlgebraicGeometry`: 0 Mathlib hits.
4. `msearch.py ... leansearch "A nodal curve over a DVR has pointed etale charts xy equals zero or a power of a chosen uniformizer"`: 8 hits, including `Scheme.Etale`, `IsEtale`, and Weierstrass good-reduction results; none states this theorem.
5. `rg` in the named `lean/WeilConjectures` and `lean/Sheaf` trees for the item id:
   no upstream match; only two proof-docstring references in `NodalTraitRegularization`.
6. Concept searches in both source trees for nodal, completion, and `strictNodalRing`:
   found `NodalGeometricFibres`, which wrongly adds connected nonempty fibres for
   this purpose, and found the reusable standard-model and scalar-map declarations
   above. Neither is the item's theorem. Exact proposed declaration-name searches
   in both trees and `dag/lean_names_upstream.json` returned no match.
7. DAG searches for `strictNodalRing` and `StrictSemistableModel` found the existing
   strict-semistable node; its recorded declarations were read, so no new notion
   or duplicate definition node is needed.

Validation: the prescribed `scompile.py Q43 lem-sfb-trait-nodal-etale-dvr-model`
compiled the final file in both sandbox and library module modes, with exit 0,
no errors or unexpected warnings (4.3 s and 5.2 s). The first attempt exposed
ambiguous coercion of a pullback to a type; explicitly writing
`↥(pullback (C := Scheme.{u}) f g)` and typing both power-series variables repaired
that elaboration without changing the mathematics.

No `STATEMENT-DISPUTED` flag or source-based statement correction is needed.
Only `lean` and the two allowed additions of published declaration-owner nodes
to `stmt_deps` differ from the read-only live node.

## Second reading by Q43

I reread the final node and final file after compilation, checking every row of
the correspondence above against the literal signature. This is a second pass
by this worker, not an independent-agent review: the dispatcher's explicit
instruction forbids starting other agents, and the maintainer supplies the
independent review. The first pass caught and repaired the coercion ambiguity.
The final pass checked that the Ω-algebra condition has not been weakened to a
bare ring isomorphism, that all nonsmooth geometric points are covered, and that
neither nonemptiness nor connectedness was imported from the existing nodal
predicate. It also checked the n=0, n=1, zero-parameter and empty-fibre cases,
and confirmed that the same chart satisfies the conditional generic-smooth
refinement. No mathematical mismatch remained and no statement correction was
made.

## Repair of return on eb9729b413fe

H2: replaced the statement dependency `lem-trf-nodal-point-etale-locality`
with the live definition node `def-trf-completed-local-scalar-map` (Q139,
reviewed 2026-10-19). I read its complete statement, existing Lean record,
and the definition body in `Sheaf.AlgebraicGeometry.NodalPointEtaleLocality`.
The four-arrow coefficient composite is exactly
`AlgebraicGeometry.Scheme.Hom.completedLocalScalarMap`; its construction does
not use the nodal-locality theorem. The declaration-owner list above now names
the definition node. The module and its theorem signature remain byte-identical
to the returned packet, and the mathematical statement and proof plan are unchanged.

The initial saved-packet dry run passed compilation and preflight. Comparing
with the current live node found only the delivery's Lean record and two owner
dependencies, plus current maintainer-owned `lean_audit` bookkeeping; the latter
has been retained from the current live node. Re-reading the final file confirms
the same DVR, geometric-fibre, nodal-completion, pointed-chart, and smooth-generic
clauses tabulated above. The second-reading section is the worker's self-check;
the maintainer supplies the independent review.
