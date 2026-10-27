## Worker report

The module `Sheaf.AlgebraicGeometry.GiesekerTenCanonicalHilbertStability` states
`AlgebraicGeometry.gieseker_ten_canonical_hilbert_stability`.  It first defines
`TenCanonicalHilbert.pluckerHilbert`, a transport of the ten-canonical Hilbert
representation into the Hilbert--Plücker interface.  The transport preserves the
representing object, all polynomial components and inclusions, the coproduct and
projectivity, and transports the component classification property across the
coordinate equality
`19 * (g - 1) - 1 = (19 * (g - 1) - 2) + 1`.

The theorem binds `g : ℕ` and `hg : 2 ≤ g`, matching the field and genus hypotheses.
It asserts an integer `M`, uniform before the field and presentation.  For every
field `k`, ten-canonical presentation `D`, and `m ≥ M`, it supplies a
`HilbertPlucker.Presentation` `E`.  The conjunct
`∀ z : D.J.left, D.inclusion.left z ∈ E.stable` renders that the whole complete
locus is Hilbert stable.  The existential `j` with
`j ≫ E.semistable.ι = D.inclusion.left` renders its immersion into the
semistable open, and `IsClosedImmersion j` renders closedness in that open.
The presentation's `stable` and `semistable` opens and its `pgl_line` are the
recorded positive tensor-power PGL linearization; its `semistable_points` and
`stable_points` fields render invariant-section semistability and closed-orbit,
dimension-zero-stabilizer stability over algebraically closed extensions.

More explicitly, `D.hilbert.index_eq` fixes the polynomial to
`TenCanonicalHilbert.polynomial g = C (20 * ((g : ℚ) - 1)) * X + C (1 - (g : ℚ))`.
Thus the degree is exactly `d = 20(g-1)`, and the transported Hilbert coordinates
have count `r = 19(g-1)`.  `D.hilbert.HP D.hilbert.index` is the given projective
Hilbert component, with its representing equivalence and universal-family
classification; it is not an arbitrary ambient scheme.  `D.inclusion` and
`D.locally_closed` supply exactly the locally closed locus J.  `D.series`,
`D.frames_classify`, `D.represents`, and `D.all_points` identify its points with
complete ten-canonical embeddings of the recorded stable unpointed curves.
`D.hyperplane_twist` explicitly permits a line from the test base.

For the new existential `E`, `HilbertPlucker.quotient` is the actual monomial restriction map,
`E.surjective` makes it onto, `E.rank` and `E.value` give rank exactly P(m),
and `E.base_change` identifies its geometric fibres with H⁰(C,O_C(m)).
`E.hilbert_map`, `E.hilbert_quotient`, `E.plucker`, `E.plucker_coordinates`,
and `E.embedding` specify the Hilbert and Plücker embeddings in the quotient
convention.  `E.hyperplane` identifies the pulled-back hyperplane line with
`HilbertPlucker.determinant`; `E.pgl_line` is its r-th tensor-power
linearization.  This exponent is positive since g ≥ 2.  `E.cover` fixes its G as
PGL through the recorded central-cover interface and `E.coordinate_action`
normalizes its action to changing projective coordinates on the actual
universal ideal.  Thus no arbitrary group action or unrelated polarization is
substituted for the ones in the statement.  No field perfection, characteristic,
invertibility of r, or invertibility of automorphism orders is assumed.

Statement dependencies used are:

- `Sheaf.AlgebraicGeometry.TenCanonicalHilbertParameter`,
  `AlgebraicGeometry.TenCanonicalHilbert.Presentation`;
- `Sheaf.AlgebraicGeometry.HilbertPluckerPGLLinearization`,
  `AlgebraicGeometry.HilbertPlucker.Presentation`;
- `def-weil-field`, rendered by Mathlib's `Field` class;
- `def-sfb-stable-pointed-moduli-groupoids`,
  `AlgebraicGeometry.StablePointedModuli`;
- `lem-sfb-projective-hilbert-polynomial-representability`,
  `AlgebraicGeometry.exists_projective_hilbert_polynomial_representation`;
- `lem-sfb-ten-canonical-hilbert-parameter`,
  `AlgebraicGeometry.ten_canonical_hilbert_parameter`.

The proof-only modules are imported where their declarations are available:
`StablePointedCurve`, `BalancedNodalTraitStableCanonicalLimit`,
`GiesekerPotentialStability`, `NodalLogCanonicalReconstruction`,
`NoetherianImageBoundaryDvr`, and `SemistableLogPluricanonicalLattices`.
`StablePointedIsomFinite` is not imported: its source is in rework and absent from
the live tree (reviewer FIX).  Their theorem dependencies remain postponed by the
statement's `sorry` proof, as required for stage 2.

Edge cases checked include `g = 2`, the minimal coordinate count `r = 19`, arbitrary
characteristic including characteristics dividing `19(g-1)`, empty and
nonreduced test schemes in the linearization, and arbitrary algebraically closed
field extensions.  The coordinate transport uses equality of finite index
cardinalities, so it does not exclude any allowed genus.

Searches made: `msearch.py ... leanfinder` for “Gieseker stability and closedness
of the tenth canonical stable curve Hilbert locus in every characteristic” (no
matching project declaration; unrelated universally-closed morphism hits);
`msearch.py ... loogle 'AlgebraicGeometry.IsClosedImmersion'` (12 Mathlib
morphism-property hits, no Gieseker stability theorem); `msearch.py ... grep
'Gieseker|gieseker|ten_canonical_hilbert|Hilbert.*[Ss]tab'` (no existing
matching declaration); `rg` over `lean/WeilConjectures` and `lean/Sheaf`
(found only the supporting Hilbert–Plücker, ten-canonical parameter, and
Gieseker-potential declarations).  The source was checked in Morrison,
*GIT Constructions of Moduli Spaces of Stable Curves and Maps*, §3.3,
Proposition 10 and Corollary 11, pp.16–17.

No `STATEMENT-DISPUTED` flag or node fault was found.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
