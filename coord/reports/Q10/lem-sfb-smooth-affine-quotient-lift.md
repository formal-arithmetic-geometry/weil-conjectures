## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothAffineQuotientLift` states
`AlgebraicGeometry.exists_affine_smooth_lift_of_surjective`, with its proof postponed
by `sorry`. It introduces no definition and changes only the item's `lean` field.
The seven-step natural-language proof is in the theorem docstring.

The inherited BLOCKED ending confused the reviewed Q02 stage-1 split with a stage-2
statement. The current node has no Lean record, the queue assigns stage 2, and no
repair note or Q10 return exists for this item. The Q02 ledger line at 12:48 records
the split, with `reviewed` rather than `reviewed_lean`. This delivery retains that
accepted split and all other node fields.

Hypothesis and conclusion correspondence:

- Arbitrary commutative rings: `R R₀ : CommRingCat.{u}`, with explicitly declared
  universe `u`; no nontriviality or finiteness assumptions.
- The given ring map: `φ : R ⟶ R₀`. Its surjectivity is precisely
  `hφ : Function.Surjective φ.hom`.
- The given affine scheme: `T₀ : Scheme.{u}` and `[IsAffine T₀]`.
- Its specified structure morphism and smoothness: `f₀ : T₀ ⟶ Spec R₀` and
  `[Smooth f₀]`. This uses the dependency's recorded Mathlib class.
- The lifted affine scheme: `∃ (T : Scheme.{u}) (_ : IsAffine T)`.
- Its smooth structure morphism: `(f : T ⟶ Spec R), Smooth f`.
- The requested isomorphism: `∃ a : pullback f (Spec.map φ) ≅ T₀`.
  Contravariance makes `Spec.map φ : Spec R₀ ⟶ Spec R`.
- It is an isomorphism over `R₀`, with the original specified structure map:
  `a.hom ≫ f₀ = pullback.snd f (Spec.map φ)`.
  This is the compatibility condition for an isomorphism in the slice over
  `Spec R₀`; the inverse compatibility follows from the isomorphism identities.
- No nilpotent-kernel, local, Noetherian, field, nonzero, or nonempty hypothesis is
  present. The statement does not prescribe a preferred lift or uniqueness.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, from
  `Mathlib.AlgebraicGeometry.Scheme`; affineness is Mathlib's `IsAffine` from
  `Mathlib.AlgebraicGeometry.AffineScheme` (a scheme isomorphic to its affine spectrum).
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`, from
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`, from
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`. Its affine-local ring-map definition
  is the dependency's recorded equivalent of Stacks 02H6. The relative-dimension
  and étale declarations were also read; those additional notions are not needed here.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and `pullback.snd`, from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; scheme pullbacks
  are supplied by `Mathlib.AlgebraicGeometry.Pullbacks`.

The public smoothness and pullback imports provide these statement dependencies.
The module also imports all currently stated proof-dependency modules: the Mathlib
smooth-flat, tensor-quotient, tensor-tower, prime-spectrum and localization modules,
and `WeilConjectures.RingTheory.SmoothLocalCompleteIntersection`,
`WeilConjectures.RingTheory.FlatModuleAtPrime`,
`WeilConjectures.AlgebraicGeometry.FlatSmoothFibreSmoothAtPrime`,
`WeilConjectures.RingTheory.SingularIdeal`, and
`WeilConjectures.RingTheory.SingularIdealLocalizationSmooth`.
`lem-sfb-syntomic-algebra-surjection-lift` has no recorded Lean declaration or
Mathlib match yet; it is a proof dependency only, so no missing notion is needed
for this statement and no import of an invented module is made.

Source checked: `literature/stacks-project/smoothing.tex`,
`proposition-lift-smooth`, Tag 07M8, assertion (2) and its proof. It lifts a smooth
algebra through an arbitrary surjection, first lifting syntomically and then
localizing at an element congruent to 1. The affine spectrum translation gives
exactly the theorem above, including the isomorphism over the quotient ring.

Edge cases checked before writing: the identity quotient admits the original
scheme as its lift; the zero quotient has empty spectrum and forces `T₀` empty;
an empty `T₀` over a nonzero ring has the empty affine lift; no step needs a
nilpotent kernel, so `ℤ → ℤ/p` is included. The single scheme universe is Mathlib's
usual ambient category convention, arbitrary in `u`; no test-object universe or
smallness restriction occurs. All rings and schemes of any chosen size can be
regarded in a common universe. No false or ambiguous clause was found.

Searches made (before writing):

- `msearch.py leanfinder`, query “Every smooth affine scheme over a quotient ring
  lifts to a smooth affine scheme over the original ring”: eight hits, consisting
  of local standard smoothness, smoothness of ring maps and formal smoothness;
  none constructs this lift.
- `msearch.py loogle`, query `AlgebraicGeometry.Smooth, "lift"`: zero hits.
- `msearch.py grep`, query `smooth.*quotient|lift.*smooth|smooth.*lift` in
  `AlgebraicGeometry`: zero hits.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for
  `smooth.*quotient|lift.*smooth|smooth.*lift` and the item id: nearby results
  concern formal lifting of maps, ind-smoothness, or standard smooth presentations.
  In particular `WeilConjectures.RingTheory.StandardSmoothQuotientLift` was read:
  its `Algebra.exists_standardSmooth_quotient_lift` assumes a *standard* smooth
  algebra and does not state this general smooth-affine theorem.
- `rg` over `dag/lean_names_upstream.json` and the two source roots for
  `07M8`, this item id, and `exists_affine_smooth_lift_of_surjective`: no existing
  declaration of this statement or collision with the chosen full name.

No new nodes, dependency repairs, statement correction, or STATEMENT-DISPUTED flag
is required.

## Second reading by Q10

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
