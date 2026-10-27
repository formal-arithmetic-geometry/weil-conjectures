## Worker report

Recorded an exact existing declaration; no Lean module, definition, or proof is added:
`AlgebraicGeometry.Scheme.IdealSheafData.isIso_relProjHom_reesData_of_isInvertible`,
module `WeilConjectures.Blowup.FlatBaseChange`, source lines 180–185.
The complete signature in context is:

```lean
universe u
variable {X : Scheme.{u}} {L : X.IdealSheafData}
theorem isIso_relProjHom_reesData_of_isInvertible (hL : L.IsInvertible) :
    IsIso L.reesData.relProjHom
```

The node's current statement and blueprint_update were read against
`literature/blueprint/latest/blueprint/sec-nagata-compactification/sk-lem-nagata-sketch-blowups/lemma-nagata-relative-proj-invertible-tensor-powers.md`
and its `.proof.md`. The blueprint explicitly lists this existing theorem. The source
theorem is global: its implicit scheme variable has no affine, Noetherian, separated,
integral, or nonempty hypothesis. The old audit's phrase “the affine case” does not
accurately describe its current signature.

Hypothesis and clause correspondence:

- “on Y”: the arbitrary `X : Scheme.{u}` (renaming the bound variable changes nothing).
- “ideal L”: `L : X.IdealSheafData`, Mathlib's affine-compatible quasi-coherent ideal
  data, with its ideal inclusions; this is not an arbitrary invertible module.
- “invertible”: exactly `hL : L.IsInvertible`, using the dependency's recorded
  `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible` from
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible` (lines 57–63).
  This interface uses affine-local regular principal generators. It has exactly the
  mathematical meaning of local freeness of rank one for an ideal subsheaf:
  a basis identifies A with I and, after the injective ideal inclusion, sends r to ra,
  which is injective, so a is a non-zero-divisor. Conversely, for I=(a) with a regular,
  multiplication A→I is bijective and is a rank-one basis. Refining a trivializing
  neighbourhood to affine opens supplies the recorded pointwise formulation.
  Regularity is therefore a consequence of the ideal inclusion, not an added
  hypothesis on the node's invertible ideal.
- “Rees algebra direct sum over n≥0 of L^n”: `L.reesData`, the recorded closed
  upstream declaration of `def-nagata-sheaf-rees-algebra`, in
  `WeilConjectures.AlgebraicGeometry.RelativeProj.Rees` (lines 142–169).
  Its affine sections are `reesAlgebra (L.ideal U)` with `reesGrading (L.ideal U)`;
  Mathlib's reesAlgebra is the subalgebra of A[T] whose coefficient of T^n lies in I^n.
  This is the direct sum of ideal powers, including I^0=A, and not the tensor algebra
  of an arbitrary module. Restriction is the coefficientwise restriction map.
  The source's `powMulMap` and `reesMonomial_mul_reesMonomial` identify homogeneous
  multiplication with the ideal-power multiplication required by the dependency.
- “relative Proj”: `L.reesData.relProj`, using
  `AlgebraicGeometry.Scheme.GradedAlgebraData.relProj` in
  `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic` (lines 117–121), the
  declaration recorded by `def-nagata-relative-proj`. The graded algebra is given
  by its actual affine-section rings with degreewise base-change restrictions.
- “structure morphism ... →Y”: `L.reesData.relProjHom` (Basic, lines 123–126),
  the canonical glued structure map from this relative Proj to X. Thus the theorem
  asserts invertibility of the specified arrow, rather than merely existence of
  an unrelated scheme isomorphism.
- “is an isomorphism”: `CategoryTheory.IsIso` on that exact morphism. This is the
  complete conclusion; there is no twist or additional conclusion in the current node.

Dependency sources read: `IsInvertible` including its docstring and
`Ideal.IsRegularPrincipal`; `GradedAlgebraData` including the full structure signature,
`relProj`, `relProjHom`, their chart and restriction interfaces and docstrings;
`reesData`, `powMulMap`, and `reesMonomial_mul_reesMonomial` including their full
signatures and docstrings. The rees dependency has no lean record, but its closed
slopmaster2 audit explicitly supplies these upstream declarations, as the brief permits.
All three statement dependencies are used through their existing interfaces; no
new node or dependency repair is needed.

Edge cases checked mathematically against the definitions: X empty is allowed (the
pointwise invertibility condition is vacuous and the resulting map is empty→empty);
the unit ideal yields A[T] and Proj=A locally; a nontrivial invertible ideal need not
have a global generator, since both IsInvertible and the gluing are local; a generator
which is a zero divisor cannot be a basis of an ideal subsheaf on a nonzero affine
open. The zero ideal on a nonempty scheme is not invertible. The degree-zero piece
is A, including on empty affine opens with zero section ring. Arbitrary scheme
universe u is retained. No characteristic restriction or affineness is imposed.

Searches made, 2026-10-26:

- msearch.py LeanFinder: “The structure morphism from relative Proj of the Rees
  algebra of an invertible ideal sheaf is an isomorphism”. Eight Mathlib hits:
  `ProjectiveSpectrum.Proj.isIso_toSpec`, `toSpec_base_isIso`, chart isomorphisms,
  and associated inverse identities. They concern absolute standard charts and
  do not state this relative Rees theorem.
- msearch.py Loogle: `AlgebraicGeometry.Proj`. Twelve absolute-Proj/basic-chart
  declarations, including basicOpenIsoSpec and toSpecZero; no exact relative match.
- msearch.py LeanSearch: “The blowup of an invertible ideal sheaf is isomorphic to
  the original scheme”. Eight hits concerning ideal-sheaf comap, subschemes and
  general scheme gluing, with no exact match.
- msearch.py grep (Mathlib/AlgebraicGeometry):
  `relProjHom.*[Ii]nvertible|[Ii]nvertible.*relProj|[Rr]ees.*[Ii]so`: zero hits.
- Direct rg of Mathlib for `isIso.*[Rr]ees|[Ii]nvertible.*[Rr]ees|[Rr]ees.*[Ii]nvertible`:
  no exact theorem. Read Mathlib/RingTheory/ReesAlgebra.lean for its real construction.
- Direct rg of lean/WeilConjectures and lean/Sheaf for the item id, the exact theorem
  name and the invertible/Rees combinations: exact theorem found only in
  WeilConjectures/Blowup/FlatBaseChange.lean; no competing Sheaf declaration.
  Read its full signature, docstring and proof; the proof transports the invertible
  blow-up result across relProjReesIso, respecting the structure map.

No STATEMENT-DISPUTED issue, statement correction, or node fault remains.
The existing declaration is reused under brief-stage2 §5, so there is no new file
requiring a per-file compilation. The prescribed deliver2 dry run validates this
existing-declaration delivery. Only the item's lean record and this report change.

## Second reading by Q07

A second reading was performed in this worker session; no separate worker was
started, in accordance with the dispatcher's prohibition. The maintainer's review
will be independent. Reopened the node and the exact source theorem and checked
all binders: arbitrary scheme X, ideal L, and precisely the invertibility premise.
Checked the only conclusion against the node: IsIso of reesData.relProjHom is the
specified global structure morphism of the relative Proj of ideal powers. Rechecked
that the affine-local regular-generator definition is equivalent to the stated
rank-one ideal condition, that reesData uses ideal powers rather than tensor powers,
and that the map lands in the original X. The node title and old partial audit do
not override its current Rees/global statement. No mismatch or change was found.
There are no new definitions, dependency modules, or statement corrections to review.
