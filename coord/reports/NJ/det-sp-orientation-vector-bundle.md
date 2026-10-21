## Worker report

The module `Sheaf.Paper.VectorBundleDiagonalOrientation` states the node as
`WeilConjectures.PurityFiniteSetting.vectorBundleDiagonalOrientation`. Its proof is
`sorry`. The proposition `VectorBundleDiagonalOrientationConclusion` expands the
actual arrows, and `vectorBundleDiagonalProjection_smooth` is a statement-only
helper for the source-implied geometric prerequisite (the preparation paragraph of
this same node's proof). Its proof is also `sorry`; its docstring supplies the
local-frame proof. There are no definitions with postponed data.

Hypothesis and clause correspondence:

- The finite-field datum, fixed algebraic closure k of F_q, and the distinct prime
  l are carried by `P : PurityFiniteSetting.{u}`. The positive coefficient level is
  `P.level` with `P.level_pos`. The quotient is `P.Coefficient`, the prescribed size
  lift of `O_E/(varpi^n)`. `_hE : P.extension = ⊥` specializes the coefficient
  extension to Q_l, hence this is the node's Z/l^n coefficient ring. The value of
  n is arbitrary positive, not restricted to a Kummer divisibility condition.
- `S : Scheme.{u}`, `aS : S ⟶ Spec (.of P.field.k)`, and the two instances
  `[LocallyOfFiniteType aS] [QuasiCompact aS]` express finite type over k.
  No separatedness, connectedness or reducedness of S is assumed.
- `d : ℕ` includes zero. `F : S.Modules` and
  `[F.IsFiniteLocallyFreeOfRank d]` specify the node's bundle. Its total space and
  projection are the recorded `VectorBundleZeroSection.scheme S d F` and
  `VectorBundleZeroSection.π S d F`; its zero section is already constructed in
  that dependency. The node asserts no further equality involving the section.
- `isNoetherian_of_locallyOfFiniteType aS` supplies the Noetherian base required
  by the bundle construction. The recorded `Etale.vectorIntegration_geometry`
  supplies affineness and local finite type of the projection, so separatedness,
  quasi-compactness and compactifiability follow by the existing instances. The
  helper supplies smooth pure dimension d, derived by the node's affine-frame
  argument. These are internal `letI` declarations in a definition of a Prop,
  not extra theorem hypotheses or hidden let-bound terms in the theorem signature.
- The diagonal orientation is exactly the dependency's
  `P.diagonalDualizingObject d (VectorBundleZeroSection.π S d F) aS`.
  That definition selects the unique normalized isomorphism in
  `existsUnique_diagonalDualizingObject`, with its diagonal/DNC local normalization;
  this delivery introduces no replacement orientation.
- The integration is exactly `Etale.vectorBundleIntegration` at the annihilating
  exponent `P.diagonalExponent = l^n`, with its published gluing and affine-space
  normalization. `P.diagonalExponent_annihilates` and
  `P.diagonalExponent_isUnit aS` supply its coefficient and invertibility conditions.
- Its ordinary exceptional transpose is the actual
  `Etale.rightDerivedUpperShriekAdjunction ... .homEquiv _ _` applied to that map.
  Its source is the pullback presentation of A(d)[2d]; precomposing with
  `vectorIntegrationBaseCoefficientPullback ... .inv` converts this to the
  dependency's `P.diagonalTwistEtale` presentation.
- Apply `ProEtale.comparisonUpperStar ... .mapDerivedCategory.map` and then
  `P.diagonalDualizingComparison ... .inv`. This is the prescribed finite
  exceptional comparison, landing in `sfFiniteExceptionalAt` applied to the
  coefficient unit on the small pro-etale site. The recorded
  `lem-pur-vector-integration-site-comparison` identifies precisely this transported
  ordinary adjunct with the pro-etale integration transpose; it is not an
  arbitrary comparison iso or an arbitrary map between the same endpoints.
- The conclusion says `theta.inv = P_pi.hom`, where the right side is the explicit
  transported adjunct just described. Since theta is an isomorphism and the node's
  P_pi is its integration-transposed purity isomorphism, this is exactly equivalent
  to `theta = P_pi.symm`. It is an equality of derived morphisms, not just equality
  of cohomology classes, existence of an iso, or a scalar-unspecified orientation.
- The only additional coordinate parameter is universally quantified
  `t : Etale.OrdinaryFiniteTwistTransport ...`. This structure consists of the
  canonical normalized root/line pullbacks, characterized by the inclusion into
  units and the pure-root-tensor equation. It is the same presentation quantifier
  used by `DiagonalOrientationNormalization`. It is inhabited by
  `Etale.exists_ordinaryFiniteP1Adjunction` at the displayed positive exponent;
  there is no vacuous assumption or arbitrary choice of orientation here.

Dependency declarations read and used:

| Node | Module | Declaration/interface |
| --- | --- | --- |
| def-pur-conventions | Sheaf.Paper.PurityFiniteSetting | WeilConjectures.PurityFiniteSetting; Coefficient; level_pos |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType / QuasiCompact | AlgebraicGeometry.LocallyOfFiniteType; AlgebraicGeometry.QuasiCompact |
| def-asd-vector-bundle-zero-section | Sheaf.AlgebraicGeometry.VectorBundleZeroSection | AlgebraicGeometry.VectorBundleZeroSection.scheme; π; zero; trivializationMap_spec |
| thm-pur-diagonal-dualizing-object | Sheaf.Paper.PurityDiagonalDualizingObject | diagonalDualizingObject; diagonalDualizingComparison; DiagonalOrientationNormalization |
| def-amb-vector-integration | Sheaf.AlgebraicGeometry.VectorBundleIntegration | AlgebraicGeometry.Etale.vectorBundleIntegration; vectorIntegration_geometry; vectorIntegrationBaseCoefficientPullback (reexported Charts owner) |
| lem-pur-vector-integration-site-comparison | Sheaf.Paper.VectorIntegrationSiteComparison | AlgebraicGeometry.ProEtale.VectorIntegrationSite.finiteTypeSiteComparison; vectorTensorComparison; finiteTypeSiteCompatibility |
| cor-pur-vector-bundle-purity | Sheaf.Paper.VectorBundlePurity | WeilConjectures.PurityFiniteSetting.vectorBundlePurity; VectorBundlePurityConclusion |

The last two dependencies fix the meaning and normalization of the explicit
integration adjunct. Their modules are public imports. All already-stated proof
dependency modules are imported privately, except those already public statement
dependencies. `lem-pur-projection-purity-agreement` has no recorded Lean declaration
and therefore no module to import. Its role is retained in the complete theorem
proof docstring. No missing notion or unusable statement-dependency interface was
encountered, and no new node or dependency record repair was needed.

Edge cases checked before writing: the empty scheme (no nonemptiness binder), d=0
(the empty tensor product is the coefficient unit and integration is the identity
trace), arbitrary disconnected/nonreduced bases, nonseparated finite-type bases,
and n=1 or any larger positive level. Universes match the recorded small-site
framework: schemes in u, site objects in u+1 and coefficient modules in u+1. No
independent universe equation was added. The comparison structure t exists for
these exponents and does not make the statement vacuous. The inverse-arrow equality
implies invertibility of the adjunct rather than requiring another isomorphism as
an assumption.

Searches made with the prescribed msearch.py wrapper:

- leanfinder: "The diagonal orientation of a vector bundle equals the inverse of
  the purity map adjoint to integration along its fibers". Eight hits concerning
  topological vector-bundle trivializations, none about scheme exceptional inverse
  image or integration orientations.
- loogle: `AlgebraicGeometry.Scheme, CategoryTheory.Iso`. Twelve scheme-isomorphism,
  underlying-homeomorphism and affine-chart results; no dualizing comparison.
- grep of Mathlib: `diagonal.*[Oo]rientation|orientation.*[Vv]ector|diagonalDualizingObject`.
  Four hits about linear/Euclidean orientations, none about scheme purity.
- leansearch: "The diagonal purity orientation of an algebraic vector bundle
  agrees with the inverse of the adjoint of integration along fibers". Eight hits
  about topological vector bundles, linear orientations and manifolds; no match.
- rg of lean/WeilConjectures and lean/Sheaf for the node id, orientation/vector,
  and diagonalDualizingObject: existing diagonal-orientation and smooth-purity
  constructions and some consumers, but no statement of the requested equality.
  The local helper `bundle_smooth` in VectorIntegrationMate is private and is
  unavailable to consumers; the delivered named statement expresses that same
  source-implied geometric prerequisite without copying any definition.

Source read: the current blueprint statement and three-step proof at
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-orientation/`,
and the node's expanded six-step proof, which the theorem docstring follows.
No statement correction or unresolved mathematical dispute was found. All fields
of the node except `lean` are preserved.

Validation: scompile.py compiled the single module successfully both as sandbox
and library module, with the default per-file 60-second limit (7.6s and 6.3s).

## Second reading by NJ

This is a second pass by the same dispatcher-started worker; the brief prohibits
starting another agent. The maintainer's independent reading remains the external
review. I reopened the node and module and checked the direction, category, domain,
coefficient specialization and trace normalization, clause by clause as above.
The important direction check is that `theta.inv` has source A_V(d)[2d] and target
Rpi! A_S, just like the adjunct. The coefficient pullback comparison therefore
appears with `.inv`, while the exceptional comparison also appears with `.inv`
after comparison pullback. This gives the node's theta = P_pi^{-1}, not theta = P_pi.
The equality uses the actual canonical diagonal declaration and actual globally
glued trace, and includes the comparison-unit factor rather than omitting it.
No absolute separatedness, admissibility datum, ramification divisibility or
nonzero-rank assumption was introduced. There was no mismatch requiring a change.
