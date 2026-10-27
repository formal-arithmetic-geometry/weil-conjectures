## Worker report

The module `Sheaf.AlgebraicGeometry.LargeAlgClosedJacobson` states
`AlgebraicGeometry.Scheme.exists_algClosed_extension_jacobson_rational`, with exactly
one postponed proof, `by sorry`. It introduces no definitions or additional nodes.
Only the item's `lean` record changes. No statement correction or dispute is needed.

The source was read directly in `literature/stacks-project/varieties.tex`,
`lemma-make-Jacobson` (Tag 0479): every scheme over a field becomes Jacobson and
has algebraic closed-point residue extensions over any sufficiently large field
extension. Also read `spaces-more-groupoids.tex`, `lemma-group-space-scheme-over-kbar`
(Tag 0B8E), which explicitly applies this with an algebraically closed extension
to obtain rational closed points. Algebraic closedness is imposed on the new
field, not algebraicity of that field over the original field.

Clause-by-clause rendering:

- A field `k` is `(k : Type u) [Field k]`.
- An arbitrary scheme over `Spec k` is `(U : Scheme.{u})
  (f : U ⟶ Spec (.of k))`. There are no further hypotheses on `U` or `f`.
- Existence of a field extension is `∃ (K : Type u) (_ : Field K)
  (_ : Algebra k K), ...`. The map is `algebraMap k K`; field maps are injective.
- Algebraic closedness is `IsAlgClosed K`. In particular `IsAlgClosure k K`
  is deliberately not used: the source permits arbitrary transcendence degree.
- `U_K` is Mathlib's chosen scheme fibre product
  `pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))`.
- Clause (i) is `JacobsonSpace ↥(pullback ...)`. Its full definition, read in
  `Mathlib.Topology.JacobsonSpace`, is
  `∀ {Z}, IsClosed Z → closure (Z ∩ closedPoints X) = Z`.
  Thus it says exactly that the ambient closed points lying in every closed
  subset are dense there, including the empty subset.
- Clause (ii) quantifies over every `x` in that same pullback and assumes
  `x ∈ closedPoints ↥(pullback ...)`. It concludes `Function.Bijective` of
  `(pullback.snd f ...).residueFieldAlgebraMap x`, the canonical homomorphism
  from `K` into the point's residue field. Bijectivity of a ring homomorphism
  is exactly that it is an isomorphism; no arbitrary field isomorphism is used.
  `pullback.snd` is the structural projection to `Spec K`.
- The conjunction after the existential requires one and the same field
  extension to have both properties.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs` (mathlib match).
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-algebraic-closure`: `IsAlgClosed` from its mathlib match in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`. The node's separate algebraic-closure
  construction is not required by this statement.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and `pullback.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, with the scheme
  pullback instance from `Mathlib.AlgebraicGeometry.Pullbacks`.
- `def-weil-closed-points`: `closedPoints`, `Mathlib.Topology.JacobsonSpace`
  (mathlib match; exactly `IsClosed {x}`).
- `def-weil-residue-field`: `Scheme.residueField` and `Scheme.Hom.residueFieldMap`,
  `Mathlib.AlgebraicGeometry.ResidueField`. The field-specialized canonical map
  `Scheme.Hom.residueFieldAlgebraMap` is the existing construction in
  `WeilConjectures.ZetaSeries` (read its full signature and definition): it
  composes the canonical field-to-prime-residue map, `Spec.residueFieldIso`
  inverse, and the structure morphism's `residueFieldMap`. This is also the
  interface prescribed by the STATE residue-field convention.

The modules of all stated proof dependencies are imported, without `public`
when used only for the proof: `Mathlib.SetTheory.Cardinal.HasCardinalLT`,
`Sheaf.FieldTheory.AlgClosedExtensionCardinalLowerBound`,
`WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso`,
`Sheaf.RingTheory.CardinalGeneratorNullstellensatz`, and
`Mathlib.RingTheory.Spectrum.Prime.Jacobson`. The remaining proof dependencies
are already statement imports. The docstring carries all five proof steps,
including cardinal selection, tensor generators, local Jacobson criteria,
residue identification and algebraic-closedness argument.

Edge cases checked before writing:

- Empty scheme: the field existential remains required; the Jacobson condition
  holds and the closed-point assertion is vacuous. No nonemptiness binder.
- Empty closed subset: covered by the exact `JacobsonSpace` definition.
- Infinite affine covers and schemes with arbitrarily large coordinate rings:
  the field can be chosen after bounding the disjoint union of the cover's
  rings, rather than after selecting only one chart. For `Scheme.{u}`, the
  underlying points, coordinate rings and point-indexed cover are `u`-small;
  one strict cardinal bound and a sufficiently large field still exist in
  `Type u`. Thus the existential universe excludes no scheme in the input
  category. Every universe and variable is explicitly bound, with
  `set_option autoImplicit false`.
- Nonreduced, nonseparated and non-quasi-compact schemes and every field
  characteristic are included; none of these properties occurs as a hypothesis.
- Taking only the algebraic closure of `k` can fail for arbitrary schemes;
  the statement allows a transcendental extension and adds no algebraicity
  restriction on `K/k`.

Searches for an existing statement, using the prescribed `msearch.py` wrapper:

- LeanFinder: `Every scheme over a field becomes Jacobson with rational closed
  points after a sufficiently large algebraically closed field extension`.
  Eight hits, including `LocallyOfFiniteType.jacobsonSpace`, the Jacobson fibre
  theorem and Jacobson spectrum instances. All impose additional finite-type
  hypotheses or discuss an already-given scheme; none supplies this extension.
- Loogle: `"Jacobson", "IsAlgClosed"`: zero hits.
- Mathlib grep: `make.?Jacobson|base.?change.?Jacobson|exists.*[Jj]acobson|[Jj]acobson.*[Ii]sAlgClosed`:
  thirteen hits about Jacobson ideals, spectra and the unrelated Jacobson-Noether
  theorem; no matching field-extension theorem.
- LeanSearch: `Any scheme over a field becomes Jacobson with rational closed
  points over a sufficiently large algebraically closed extension`; result
  eight hits on finite-type Jacobson theorems and equivalent topological criteria; no match.
- `rg` in the exact read-only `lean/WeilConjectures` and `lean/Sheaf` trees
  for the item id and the same Jacobson/existence patterns: no statement match.
  The item id appears in proof-plan references in
  `SeparatedGroupSpaceGeometricScheme`, `SemiabelianGeometricPowerIntegrality`,
  and `TorusFixedSchemeSmooth`; these are consumers, not an existing statement.
  The full proposed declaration name was also checked for collisions.

## Second reading by N5

This is a worker self-check; the dispatcher's instructions prohibit starting
another agent, and the delivery is subject to the maintainer's independent review.
Re-read the original node alongside the completed signature. The existential
binders give a field with a `k`-algebra structure; `IsAlgClosed K` does not confuse
algebraic closedness with being an algebraic closure. Both conclusions refer to
the identical fibre product. Its second projection, not its first projection,
gives the exact canonical `K → κ(x)` map. `JacobsonSpace` expands to the ambient
closed-point density required by clause (i), not just density in the whole space.
The `closedPoints` guard matches exactly the quantification in clause (ii), and
bijectivity is attached to that specified map. No additional hypotheses or
clauses were found, and no statement changes were made.
