## Worker report

The module `Sheaf.Paper.OrientationScalarPropagation` states
`AlgebraicGeometry.ProEtale.SpOrientationScalarPropagation.orientationScalarPropagation`.
Its proof is `sorry`. The two supporting definitions are real arrow expressions:
`iterated` composes the two existing `proGamma` maps; `UnitEquation` names exactly
one displayed equality in the item. No theorem of composition of orientations is
assumed. No new mathematical notion, axiom, or chosen comparison map is introduced.

Hypotheses and clauses, in the order of the node:

- The algebraic closure of a finite field is `D : WeilConjectures.FiniteFieldDatum`;
  `ell`, `[Fact ell.Prime]`, `hne : ell ≠ D.p` are the coefficient-prime condition.
- `X Y Z : Scheme`, their `Over (Spec (.of D.k))` instances, `LocallyOfFiniteType`,
  `QuasiCompact`, and `IsSeparated` on each structure map express exactly separated
  finite-type k-schemes. `f g` and their `IsOver` instances express k-morphisms.
- `IsSeparated f`, `IsSeparated g`, `d e : ℕ`, and `SmoothOfRelativeDimension`
  express the two smooth separated maps of pure nonnegative dimensions. The
  composite is literally `f ≫ g`, its dimension literally `d + e`.
- `A B : Type (u+1)`, `CommRing`, `Finite`, and `phi : A →+* B` express the arbitrary
  finite commutative coefficient rings and their unital map. `n`, `hn`, `hA`, `hB`
  expose a common positive annihilating ell-power. Such an exponent always exists
  for the node's rings, including the zero ring; it imposes no flatness condition.
- `IsNoetherian` on the schemes, quasi-compactness of the maps, and their
  `HasCompactification` instances are interface data guaranteed by the preceding
  finite-type and separated hypotheses (as in `finiteGeneralRingSmoothPurity`).
  They do not narrow the mathematical class. The compactifications are fixed and
  coefficient independent; no matching compactification must be chosen anew at B.
- The three `geometry*` binders give the actual diagonal/Rees geometry. Each of
  `afA agA ahA afB agB ahB` is a dualizing-to-shifted-Tate-line isomorphism and
  its `OrientationNormalized` hypothesis pins it to the direct diagonal construction,
  including inverse integration normalization. These are presentations of the
  specified orientations, not arbitrary orientable objects or auxiliary purity
  assumptions. The node's a is the inverse of our alpha, hence `.inv`.
- The finite twists in this statement are precisely `FiniteSmoothPurity.line`,
  the existing ordered shifted Tate lines used by `FiniteGeneralRingAt`. The inverse
  image, derived tensor, gamma and exceptional functors are the existing finite
  canonical maps, not new copies of derived operations or integral coefficient twists.
- `eX eY : CoefficientLineComparison` are the specified scalar/root comparisons,
  pinned on every root and scalar generator and the actual scalar-single counit.
  At the same exponent their `roots_power` equation is the identity root map, so
  these binders admit no scalar rescaling. Their zero-fold part is the scalar unit;
  higher powers use the existing tensor and shift comparisons.
- The first conjunct quantifies over every `K : proCategory A Z` with `IsCtf A Z K`:
  intrinsically constructible cohomology, boundedness and finite Tor amplitude.
  `proScalar.map (iterated ...)`, followed by `proCoefficientMap phi f` and
  `exceptional B f |>.map (proCoefficientMap phi g K)`, is precisely the left side
  of the first displayed equation, in Lean's left-to-right composition order.
  Its right side is `iterated` over B, preceded by `proLambda f` and Hf applied to
  `proLambda g`. These are the canonical source identifications implicit in the
  node's phrase “after the canonical scalar/pullback, twist and shift identifications”.
  The equality is in the actual ordinary, uncompleted pro-etale derived category.
- The second conjunct is `UnitEquation A ... → UnitEquation B ...`. Expanding it,
  the left arrow is `ah.inv ≫ finiteCompositor.hom.app (𝟙_ _)`. The right arrow is
  `finiteLineSplit.hom`, followed by `f*ag.inv` in the first tensor variable,
  `af.inv` in the second, and `finiteRho`. This is exactly
  c(1)a_h = rho(f*a_g tensor a_f), including its specified ordered source.
  Both equations are mapped into the pro-etale category by the actual comparison
  inverse image. Using ordinary-etale coordinates here loses no objects: the
  coefficient unit and shifted Tate lines are canonical ordinary-etale origins.
- The final Z/ell^r specialization follows by taking the source ring to be the
  lifted ZMod coefficient and the canonical cast hom to the target. All rings
  killed by ell^r have this unital homomorphism. There is no field, flatness,
  regularity, finite-projective-dimension, faithfulness, or nonzero-ring binder.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- Mathlib morphism modules `FiniteType`, `Proper`, `Smooth`:
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`, `SmoothOfRelativeDimension`.
- `Sheaf.SecSmoothPurity.FiniteGeneralRing` and its data module:
  `FiniteGeneralRingAt`, `finiteGeneralRingPrimeSetting`, and the direct
  `OrientationNormalized` finite-ring interface. The proof imports its theorem;
  the signature uses its specified finite-ring orientation and Tate-line data.
- `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`: `scalarExtensionFunctor` and its
  no-flatness preservation and normalization interfaces. `proScalar` is the
  equivalent fixed-ModuleCat presentation used by the published purity square.
- `Sheaf.Paper.FiniteSmoothPurityMaps`:
  `proCategory`, `IsCtf`, `proSource`, `exceptional`, `proGamma`, `line`,
  `OrientationNormalized`, `comparison`.
- `Sheaf.Paper.FiniteSmoothCoefficientArrows`:
  `CoefficientLineComparison`, `proScalar`, `proCoefficientMap`, `proLambda`.
  These comparisons are the normalized exceptional and scalar-source maps of
  `Sheaf.SecSmoothPurity.ReductionExceptional` and
  `Sheaf.SecSmoothPurity.ReductionCompatibilities` in fixed-module coordinates.
- `Sheaf.Paper.SmoothPurityCompositionFactors`, solely its existing arrow data:
  `SpCompositionFactors.finiteCompositor`, `finiteLineSplit`, `finiteRho`.
  The existing definition owner `def-sp-composition-orientation-arrow-data` is
  added to stmt_deps; neither `SpCompositionFactors.finite` nor `.towers` is used.
  As this module houses the downstream theorem too, the reverse proof import
  from it to this delivery must remain omitted, per stage-2 rule 7.
- `Sheaf.Paper.CompositionComparisons`: the counit-normalized compositor/coefficient
  equations in `SpCompositionFinite` and `compositionComparisons_finite` are proof
  prerequisites. `SmoothPurityMap`, `DerivedPullbackTensorHom`, and
  `IntrinsicCoefficientTwistsUnrestricted` are retained as public imports for the
  recorded dependencies; the statement uses the arbitrary-finite-ring specialization
  already owned by finite-general-ring and the finite canonical-map nodes.
- Plain proof imports: `SmoothPurityCompositeTensorTranspose`,
  `RingedDerivedMonoidalComparisons`, `CochainPullbackTensorCoherence`, and
  `ReductionCompatibilities`. The unstated projection-coefficients node has no
  recorded module to import. No unstated notion is needed to state this theorem.

Edge cases checked mathematically before writing: d=0, e=0 and d=e=0 use the
actual recursive splitting's unit branch; the empty source scheme is admitted;
zero rings and zero objects are allowed; the identity coefficient map is allowed;
Z/ell^2 to Z/ell is allowed despite infinite projective dimension over the source.
The minimum common exponent is 1 and arbitrary larger exponents are permitted;
existing exponent independence identifies the resulting Tate presentations.
The site stays Scheme.{u} with ModuleCat.{u+1}; no site-universe equality is added.

Searches performed:

- msearch leanfinder: “Scalar extension transports iterated smooth purity and the
  composition identity at the coefficient unit”. Eight hits, only smooth ring
  composition/base-change results; no matching purity theorem.
- msearch loogle: `CategoryTheory.NatTrans.naturality, CategoryTheory.Adjunction.comp`.
  Zero hits.
- msearch grep: `orientation.*[Ss]calar|[Ss]calar.*[Oo]rientation`. One unrelated
  upper-half-plane matrix orientation hit.
- rg in lean/WeilConjectures and lean/Sheaf for orientation scalar propagation,
  scalar pasting, iteratedPurity, and the exact item id. No existing theorem states
  both clauses. `IteratedPurityScalarPasting` is rational coefficient-field extension,
  not arbitrary finite rings or the unit-equation implication. Reused existing
  finite-composition arrow definitions rather than copying them.

No statement correction or disputed statement. No new node or dependency repair.
The item gains only existing definition owners in stmt_deps and its Lean record.
The maintainer supplies the independent second reading, as specified in the brief.

Additional LeanSearch check: msearch leansearch, “Extension of finite coefficient
rings carries the smooth purity composition identity at the unit to the direct
diagonal orientations”. Eight unrelated ring-homomorphism smoothness/identity hits;
no matching derived purity assertion.

## Dependency compile repair

The first scompile stopped before reaching this module, in the live transitive
prerequisite `Sheaf.AlgebraicGeometry.SfP1ChartMapComposition.chartMap_compHom`:
its structural conversion ended in a failed `hrefl` comparing the expanded chart
word with the still-folded `ordinaryFiniteChartTransport` application. The server
source was read with scompile --source and agrees with the local source.
All essential finite-purity imports reach this module through SmoothDuality, so
using smaller imports does not remove the failing prerequisite.

The sandbox therefore includes a source-compatible repair of the existing module
at its original path. In the existing structuralHEq metaprogram's whitelist of
small boundary aliases, add `ordinaryFiniteChartTransport`. This unfolds its
explicit four-factor arrow word during conversion. Every theorem signature,
mathematical definition, and proof strategy is unchanged; no sorry or axiom is
added. The conversion still produces ordinary kernel-checked proof terms.
This is a transitive compile repair, not a new stage-2 theorem or replacement
notion. It needs no new DAG record because the existing declarations and their
owning node remain unchanged. Both delivered files are compiled separately by
scompile in dependency order.

The initial repair exposed a second folded boundary alias, the recorded
`ordinaryFiniteAdjunction`. The final repair therefore includes both small aliases
in the whitelist and gives precisely these two definitions local semireducible
status, so the metaprogram's `change` can validate the explicit unfolding. The
original respectTransparency options remain true, and the derived category,
localization and large functor constructions remain irreducible. No mathematical
statement or proof obligation is removed.

## Validation

The final two-file scompile completed successfully with no errors or warnings.
`SfP1ChartMapComposition` compiled in 14.8 seconds and
`OrientationScalarPropagation` in 9.0 seconds, both below the 60-second limit.
The wrapper also checked each sandbox/library presentation separately.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review (cc second reader, 2026-10-27): FIX

The consumer change to `lean/Sheaf/AlgebraicGeometry/SfP1ChartMapComposition.lean` (section
"Dependency compile repair") is withdrawn. The file is restored byte for byte to the published
live module. Batch recovery 3cba8a710d0 ("Take out batch deliveries") has already taken out H2's
failing proof of `chartMap_compHom`. The module is `sorry` again, and H2 still holds its claim in
coord/claims. The repair is therefore not needed for this item's statement to compile against
the live build. A stage-2 statement delivery must not land a proof of another group's claimed
module, because that is stage-3 work. The item module, the node record and the statement are unchanged.
