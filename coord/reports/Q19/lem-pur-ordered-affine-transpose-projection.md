## Worker report

The delivery states `AlgebraicGeometry.ProEtale.OrderedAffineTranspose.orderedAffineTranspose_projection`
in `Sheaf.Paper.OrderedAffineTransposeProjection`. Only its theorem proof is `sorry`.
Every helper has real data, and the theorem docstring carries all six proof steps of the node.
The item's JSON changes only in `lean`. No new node, dependency repair, or statement correction.

Sources read: the item and every statement-dependency node; the recorded Lean source of the ordered
comparison and affine-line comparison in full; the finite setting, finite-Tor interface, coefficient
twist and exceptional coefficient interfaces, the supplied projection interface; and current
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-composition/prop-pur-affine-space-composition-law.proof.md`.
The latest proof's coordinate-permutation claim is not used: the item's accepted split requires
only consecutive ordered blocks.

Hypothesis and clause correspondence:

- The full finite-field and coefficient conventions are `P : PurityFiniteSetting.{u}`. It retains
  the finite-field datum, distinct coefficient prime, finite intermediate coefficient field, and
  positive level. `AffineLinePurity.Ring P` is the existing lifted quotient at zero-based index
  `P.level - 1`, canonically reindexed by `AffineLinePurity.ringEquiv` to the positive-level quotient.
  There is no ramification divisibility hypothesis or fixed Kummer-level restriction.
- `Y`, `aY : Y ⟶ Spec (.of P.field.k)`, `LocallyOfFiniteType aY`, `QuasiCompact aY`, and
  `IsSeparated aY` say exactly separated finite type over k. Noetherianity/compactness of every
  intermediate base is derived from `tower_geometry`/`tower_noetherian`; none is a new hypothesis.
- `iteratedAffineLine Y d`, `iteratedAffineLineProj Y d`, `lastProjection`, and `towerBase` are
  exactly the ordered affine model already fixed by the recorded comparison. In particular
  dimension zero is literally Y and its projection is identity. AffineSpace is Mathlib's
  polynomial affine space, with PUnit coordinates at each line step.
- `tate P Y d` is the existing `twistAction` applied to the compared coefficient unit on X_d:
  d ordered tensor copies of `shiftedLine`, hence A(d)[2d], including d=0. `sourceIso` consists
  of canonical associators and unit maps and identifies the recorded `orderedSource` with
  `projectionSourceObject` at that Tate coefficient. There is no second definition of a twist.
- `K : Plus (Ring P) Y`, its ordinary representative `Ke`, `hKe : etaleFiniteTor ... Ke`, and
  `eK : comparison.obj Ke ≅ K.obj` are exactly the recorded comparison's input presentation of
  D^b_ctf. The representative is quantified arbitrarily; it does not replace K or restrict to
  a special class of representatives. The existing finite-Tor comparison and origin theorem
  cover every finite-Tor constructible pro-etale input.
- `transpose` is literally compact.map(`affineSpacePurityComparison`) followed by the published
  `rightDerivedUpperShriekCounit`. `compact` and `counit` normalize d=0 to identity, exactly as
  `orderedSource` and `exceptional` already do. No ambient exceptional adjunction is assumed.
- `integration` is tau evaluated at A_Y, with the source changed from F_d(A_Y) to T_d by
  `tateSourceIso`, the canonical inverse-image-of-unit comparison. Its coefficient is the actual
  constant degree-zero unit, not an arbitrary derived object. `unitPlus` is obtained from the
  existing plus single functor. Its finite-Tor evidence is an application of the existing
  `Etale.constructibleFiniteTor_unit` transported along `unitEtaleIso`, not a new lemma or axiom.
- `projection` is the canonical forward coefficient-first projection from
  `VectorIntegrationSite.projection` with exactly its two tensor symmetries, followed by
  compact.map(sourceIso.inv). At zero it is the coefficient right unitor. The first conjunct
  asserts its invertibility at every d and the exact equality of tau with its inverse, tensor
  of `integration`, and `moduleRightUnit`. The isomorphy evidence is existential inside the
  conclusion, never an extra hypothesis or independently chosen morphism.
- The second conjunct is I_0=id, expressed by HEq solely to compare the normalized dependent
  endpoints. The two endpoints definitionally reduce to the coefficient unit; HEq is equality
  of these actual arrows, not an isomorphism-existence assertion.
- The third conjunct identifies I_1 with `lineNormalizedIntegration`. This helper transports the
  standing compact-support source to the affine-chart compactification using the proper/open
  comparison and ordinary compactification comparison, then uses the existing
  `AffineLinePurity.integration` (actual open-extension counit followed by normalized projective
  trace). `lineUnitSourceIso` is the canonical pullback-unit/left-unitor map. Thus the normalization
  is the specified map and does not merely assert existence of an integration.
- The last conjunct is `∀ a b, BlockLaw ... a b`. Here g is the length-b projection over Y and f
  is the length-a projection over X_b. On the left the inner map is exactly
  Gamma_f,Rg!K after F_f(Gamma_g,K); on both sides the normalized compact functors and counits
  are evaluated on Rg_!Rf_!F_fF_gK. By `AffineSpacePurity.compositionInverse`'s defining formula,
  transposing after c_g,f inverse and precomposing with compact-support composition is exactly
  this pasted counit. Expanding that definition, rather than inserting it and cancelling it,
  avoids introducing a different compositor. The right side is precisely
  Rg_!(tau_f,F_gK) followed by tau_g,K, with hB transporting the literal F_gK endpoint.
  B/Be/eB retain any bounded finite-Tor ordinary representative of F_gK, just as the original
  Gamma API retains Ke/eK; all such choices are quantified. Applicability follows from the
  same pullback/tensor preservation used in node proof Step 1, so these are not restrictions
  on a,b,K. Both zero-block cases use the normalized identity functors and counits. There is
  no permutation or stronger regrouping claim.

Dependency declarations used (recorded modules are public transitive imports through
`AffineSpacePurityComparison`; direct proof-only dependencies are imported without public):

| Node | Module and declaration/interface |
| --- | --- |
| def-pur-conventions | Sheaf.Paper.PurityFiniteSetting: WeilConjectures.PurityFiniteSetting |
| def-sbc-affine-space | Mathlib.AlgebraicGeometry.AffineSpace: AlgebraicGeometry.AffineSpace, over |
| def-coefficient-twists-detailed | Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted and its public finite-twist imports; the recorded comparison's shiftedLine/twistAction |
| def-weil-exceptional-inverse-image | Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients; finite specialization through the recorded comparison's exceptional and the published rightDerivedUpperShriekCounit |
| def-weil-finite-tor-amplitude | Sheaf.Paper.FiniteTorAmplitudeSites, finiteTorConstructibleEtale and the existing Etale.DerivedCategory.constructibleFiniteTor used by the Gamma API |
| def-pur-affine-space-comparison | Sheaf.Paper.AffineSpacePurityComparison: orderedSource, affineSpacePurityComparison, sourceReassociation, exceptional, compositionInverse, tower_geometry, tower_noetherian |
| def-exchange-projection | Sheaf.Paper.ExchangeProjectionSuppliedDomains; existing finite component VectorIntegrationSite.projection at the actual compactification |
| def-pur-affine-line-purity-comparison | Sheaf.Paper.AffineLinePurityComparison: integration, sourceWitness, Ring, primeUnit; its public coordinate helpers source_eq/moduleRightUnit |

All recorded proof-dependency modules are imported. The generic mate/conjugate/composite
adjunction dependencies use Mathlib.CategoryTheory.Adjunction.Mates and Basic. No local notation,
private declarations, local instances, auto-bound universes, added axiom, or proof of a new theorem.
The auxiliary type variable is explicitly `universe u`; the small site retains object universe
u+1 and morphism universe u, with ModuleCat.{u+1} coefficients throughout.

Edge cases: d=0 gives identity source, compact functor, exceptional functor, counit and comparison;
the projection is the coefficient unitor. d=1 retains the actual projective-line trace restricted
by the open counit. a=0 and b=0 are permitted in BlockLaw with identity operations. The empty base
scheme and the zero complex are not excluded. Every positive coefficient level is retained,
including levels not divisible by the ramification index. No flatness over Z/ell^r is required.

Searches performed with the prescribed msearch.py wrapper:

- leanfinder: "The transpose of the ordered affine space purity comparison equals inverse
  projection formula followed by tensor integration"; eight affine reindexing and affine-space
  associator results, no exact match.
- loogle: "CategoryTheory.Adjunction.counit, CategoryTheory.conjugateEquiv"; five generic
  conjugateEquiv counit/application lemmas, no concrete affine-purity result.
- grep: "ordered.*transpose|affineSpacePurityComparison|comp_counit_app"; twelve generic
  adjunction and unrelated transpose results, no match.
- leansearch: "The counit transpose of an ordered affine tower purity map is tensor-linear by
  the projection formula"; eight coalgebra/linear-dual results, no match.
- rg in lean/WeilConjectures and lean/Sheaf for affineSpacePurityComparison, ordered transpose /
  ordered projection and the item id: only the recorded comparison and consumers; no existing
  declaration states all the present clauses. Read the related ordinary-etale
  IntegrationTransposeComposition: it takes an arbitrary ambient adjunction and projection
  invertibility for all complexes, so it is not the class-restricted concrete theorem here.

Validation: scompile.py compiled the core module cleanly in both sandbox and named-library mode.
Final complete import/docstring version is checked again by scompile.py and deliver2.py preflight.
Only the expected declaration-uses-sorry warning is allowed. No statement dispute found.

## Second reading by Q19

This is the worker's explicit final rereading; no independent reader is claimed, since the
launcher's instructions prohibit starting other agents and assign independent review to the
maintainer. Reopened the node and the completed module and compared all clauses above. Corrected
the initial unit-evidence instance lookup, the orientation of the site pullback comparison,
and the zero-source coordinate unfolding. Confirmed forward projection uses the existing two
symmetries and its inverse is asserted in the conclusion, not assumed. The block clause expands
only the defining pasted counit, with arbitrary retained F_gK representatives; it introduces no
coordinate invariance. Every helper is listed in lean.declarations and has the item's blueprint
docstring. Only the main theorem is postponed; no new independent mathematical notion is added.
