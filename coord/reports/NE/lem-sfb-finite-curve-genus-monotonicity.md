## Worker report

This delivery states `AlgebraicGeometry.genus_le_of_nonconstant_smooth_proper_curve` in
`Sheaf.AlgebraicGeometry.FiniteCurveGenusMonotonicity`. Its only proof is `sorry`.
No definition, hypothesis, or conclusion of the node is changed, and no new node is needed.
The declaration docstring records all five proof steps of the reviewed stage-1 node.

Hypothesis and clause comparison:

- The algebraically closed field is `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`, with no
  restriction on its characteristic.
- The two schemes over Ω are `(C D : Scheme.{u})` with the two `Over (Spec (.of Ω))`
  instances. Each is smooth and proper by its own `Smooth` and `IsProper` instance
  on the structure morphism.
- Geometric integrality is the two `GeometricallyIntegral` instances on those same
  structure morphisms. This includes integrality and nonemptiness of each scheme.
- Dimension one is `(hC : C.IsPureDimension 1)` and `(hD : D.IsPureDimension 1)`.
  For an integral scheme there is one irreducible component, the whole space, so
  the recorded pure-dimension definition is exactly dimension one here.
- Finite type is already implied by properness: `IsProper` extends
  `LocallyOfFiniteType`, while universally closed morphisms are quasi-compact.
  No redundant additional finite-type assumption is imposed.
- The map is `(f : C ⟶ D)`, and `hf` says its composite with the target structure
  map equals the source structure map. This is precisely an Ω-morphism.
- `hnonconstant` rules out a section `p : Spec Ω ⟶ D` of the target structure map
  whose composite with the source structure map is `f`. Thus it excludes exactly
  factoring through an Ω-rational point, as the node defines nonconstant.
- The conclusion is `Scheme.arithmeticGenus Ω D ≤ Scheme.arithmeticGenus Ω C`.
  The recorded declaration of def-pc-genus defines this as the natural-number
  dimension of H¹ of the structure sheaf, exactly the node's cohomological genus.
  The recorded def-sc-genus uses the equivalent differential-form genus; we read
  its full docstring, which names `Scheme.genus_eq_arithmeticGenus` as the bridge.
  We use the existing cohomological definition, not a second genus definition.
- No finite, separable, tame, degree-invertibility or positive-characteristic
  hypothesis is added to `f`. Inseparable maps are covered. The node's final
  explanations of normality, separability, and semilinear group actions are glossary
  text inherited from the parent; none introduces another object or clause of
  this genus comparison, and this theorem quantifies over no group action.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs (def-weil-field).
- `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic (def-weil-algebraic-closure).
- `AlgebraicGeometry.GeometricallyIntegral`, Mathlib.AlgebraicGeometry.Geometrically.Integral
  (def-pc-geometrically-irreducible). Its field-valued geometric fibres are integral.
- `AlgebraicGeometry.IsIntegral`, Mathlib.AlgebraicGeometry.Properties
  (def-pc-integral-scheme), provided by geometric integrality; no redundant binder.
- `AlgebraicGeometry.IsProper`, Mathlib.AlgebraicGeometry.Morphisms.Proper
  (def-weil-proper-morphism), and `AlgebraicGeometry.LocallyOfFiniteType` from
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType (def-weil-finite-type-morphism).
- `AlgebraicGeometry.Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth
  (def-sbc-smooth-morphisms).
- `AlgebraicGeometry.Scheme.IsPureDimension`, Sheaf.AlgebraicGeometry.PureDimension
  (def-weil-pure-dimension).
- `AlgebraicGeometry.Scheme.arithmeticGenus`,
  WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar (def-pc-genus), publicly
  available through WeilConjectures.AlgebraicGeometry.Curve.
- `AlgebraicGeometry.Scheme.Hom.genus`, WeilConjectures.AlgebraicGeometry.Curve
  (def-sc-genus), read alongside its documented cohomological identification.
- `Algebra`, Mathlib.Algebra.Algebra.Defs (def-pc-field-extension), is needed in the
  proof plan's Frobenius field self-extension, not as an extra hypothesis here.

Proof dependency availability: `lem-sc-flat-base-change-coherent` records
`AlgebraicGeometry.Scheme.Modules.nonempty_H_pullback_linearEquiv` in
WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar. Its signature and full proof
reference were read; its module is already publicly imported through Curve. The two
new stage-1 proof prerequisites `lem-sfb-curve-frobenius-separable-factorization` and
`lem-sfb-curve-riemann-hurwitz-numerical` have neither a Lean record nor a Mathlib
match at the inspected base. They are therefore named in the proof docstring but
have no module to import yet. They are not missing notions of this statement.

Edge cases checked before writing:

- Genus-zero target: the inequality follows from natural-number nonnegativity;
  the proof plan separates this case before using the sign of 2g(D)-2.
- Genus-one target: the numerical term is zero and nonnegative ramification gives
  genus at least one for the source.
- Identity/isomorphism: nonconstant on a dimension-one integral curve; genera agree.
- A constant map to a rational point is excluded by exactly the existential in
  `hnonconstant`, even when the source has positive genus.
- A point or empty scheme is excluded by the original integrality/dimension-one
  assumptions, not by an extra inhabitedness restriction.
- Relative Frobenius in positive characteristic remains allowed and preserves genus.
  No `CharZero`, prime choice, or separability instance restricts this theorem.
- The single universe `u` follows `Scheme.{u}`, `Spec`, and the existing cohomological
  genus API. No independently small test universe or vacuous quantified field is used.

Searches performed:

- `msearch.py` leanfinder: "The genus of the target of a nonconstant morphism between
  smooth proper geometrically integral curves over an algebraically closed field is
  at most the genus of the source". Eight hits, on Weierstrass point maps, smooth
  relative dimension, and affine-space integrality; none is this genus inequality.
- `msearch.py` loogle: `"genus"`; zero hits.
- `msearch.py` grep in AlgebraicGeometry:
  `genus.*(le|monoton)|arithmeticGenus.*≤|RiemannHurwitz|riemann_hurwitz`; zero hits.
- `rg` in WeilConjectures with the same genus patterns and the node id found genus
  definitions, base-change results and Riemann--Roch degree bounds, no comparison.
- `rg` in Sheaf found references to this node in HighGenusEquivariantCover and
  unrelated genus/base-change modules, no declaration of this assertion.
- Every statement-dependency record and its relevant full declaration/docstring was
  read. The source places were checked directly in the local Stacks curves.tex:
  Riemann--Hurwitz (2205--2253), purely inseparable smooth genus (2624 onward), and
  Frobenius/separable factorization (2671 onward).

No STATEMENT-DISPUTED flag or mathematical node fault was found. The live node's
`reviewed` record is its completed stage-1 review, not a Lean statement attachment.
A previous attempt reported that the stage-2 gate rejected this record; this delivery
preserves it and changes only `lean`, as required.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
