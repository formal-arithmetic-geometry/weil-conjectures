## Worker report

The module `Sheaf.Paper.TrfWitnessedOpenPullback` states
`WeilConjectures.witnessed_open_pullback`, with `sorry` as its entire proof.
`WitnessedOpenPullbackData` is the conclusion record: it retains all three natural
isomorphisms, their canonical localization normalizations, and the three specified
`Scheme.FixedEtaleOriginWitness` pairs. It introduces no replacement site, coefficient
ring, derived category, inverse image, or extension functor. No statement correction,
new DAG node, or dependency repair is needed.

Hypothesis and clause correspondence:

- The finite datum A=A_{E,n} is `T : TraceFormulaCoefficientConventions`; the ring is
  `ULift.{u+1,u} T.coefficientRing`. The lift implements the established module universe
  of the small sites and changes neither the ring nor its modules mathematically.
  `T` retains the finite-field datum, prime different from characteristic, finite
  coefficient extension in its chosen algebraic closure, and positive exponent.
- The four separated finite-type k-schemes are `U X V Y : Over (Spec (.of T.datum.k))`.
  Each has the three binders `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on
  its structure map. Finite type is locally finite type plus quasi-compactness.
- `u : U ⟶ X`, `j : X ⟶ Y`, `i : U ⟶ V` are morphisms over that same field;
  the open hypotheses are `IsOpenImmersion j.left` and `IsOpenImmersion i.left`.
- The input K is in `DerivedCategory.Plus` of fixed-scalar module sheaves on
  `Scheme.ProEt.topology X.left`. The given pair (L,alpha) is the *data*
  `w : Scheme.FixedEtaleOriginWitness ... K`, with L=`w.complex`, alpha=`w.iso`.
  No witness is selected from a bare existence statement.
- `kappa` is a natural isomorphism from etale inverse image followed by comparison
  inverse image to comparison inverse image followed by pro-etale inverse image,
  with the bounded-below inclusion precomposed on both sides. The exact termwise
  pro-etale inverse image is the Lu* specified by def-weil-pbc-proetale-operations.
- `deltaJ` and `deltaI` are the analogous natural isomorphisms for the two open
  extensions. Both use the published sheaf extensions followed by
  `mapDerivedCategory`, precisely the degreewise operations of the node.
- `kappa_normalization`, `deltaJ_normalization`, `deltaI_normalization` equate these
  data to `Functor.mapDerivedCategoryNatIso` of the *specified* sheaf comparison,
  conjugated by `mapDerivedCategoryCompIso` and restricted along D+. The former
  construction is `Localization.liftNatIso` of `NatIso.mapHomologicalComplex`.
  Thus these equalities assert the complete termwise-localization normalization,
  not merely existence of some natural isomorphism. Its published factorization
  equations and localization uniqueness supply independence of representatives.
- `pulled` has target `(ProEtale.upperStar ... u).mapDerivedCategoryPlus.obj K`.
  `pulled_complex` retains L_u exactly; `pulled_iso` retains
  `kappa.app L ≪≫ (Lu*).mapIso alpha`. `HEq` is used only because the antecedent
  field's type depends on its retained complex; the accompanying equality fixes
  that complex, so this is equality of the specified isomorphism after transport.
- `extendedJ` has target j_!K; its `*_complex` and `*_iso` fields retain j_et!L
  and `deltaJ.app L ≪≫ j_!.mapIso alpha`.
- `extendedI` has target i_!M; its fields retain i_et!L_u and
  `deltaI.app L_u ≪≫ i_!.mapIso (kappa.app L ≪≫ (Lu*).mapIso alpha)`.
- Every input/antecedent/target is typed in `DerivedCategory.Plus`; each operation
  is the existing `mapDerivedCategoryPlus` restriction of the exact functor.
  Thus boundedness is cohomological and imposes no bound on arbitrary representing
  complexes. The comparison functors are exact too, so their sources are bounded below.

Dependency declarations used:

| Node | Module and declarations |
| --- | --- |
| def-trf-coefficient-conventions | Sheaf.Paper.TraceFormulaCoefficientConventions: WeilConjectures.TraceFormulaCoefficientConventions, .coefficientRing, .datum |
| def-weil-scheme-morphism-properties | Convention node; Mathlib Over, LocallyOfFiniteType, QuasiCompact, IsSeparated |
| def-weil-open-immersion | Mathlib.AlgebraicGeometry.OpenImmersion: AlgebraicGeometry.IsOpenImmersion |
| def-weil-pbc-derived-categories | WeilConjectures.AlgebraicGeometry.DerivedCategories and reexports: Etale.DerivedCategoryModule, DerivedCategory.Plus |
| def-weil-pbc-proetale-operations | Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations and reexports: proEtaleConstantRingDerivedPullback and the fixed-scalar ProEtale.upperStar realization |
| def-weil-pbc-site-comparison-morphism | Sheaf.AlgebraicGeometry.ProEtaleSiteComparison: Scheme.proEtaleSiteComparisonModules, its ProEtale.comparisonUpperStar left adjoint |
| def-weil-pbc-etale-origin-witness | Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness: Scheme.FixedEtaleOriginWitness |
| lem-weil-pbc-comparison-pullback | Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence: ProEtale.supportSiteComparisonCoefficientPullbackIso |
| lem-cbc-proetale-extension-zero-comparison | Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison and its upstream reexport: ProEtale.openImmersionLowerShriekComparisonUpperStarIso |
| def-weil-pbc-extension-by-zero | WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs: Etale.openImmersionLowerShriek |
| def-weil-extension-by-zero | Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero: sfIntrinsicModuleEquivalence and sfIntrinsicExtensionByZero; the latter is exactly conjugation of the published ProEtale.openImmersionLowerShriek used here |

The input witness's recorded interface deliberately uses fixed-scalar modules. Both
ordinary pullback and extension are used in those same coordinates, as are the recorded
sheaf comparison maps. The intrinsic pro-etale extension is visibly the fixed-scalar
extension conjugated by `sfIntrinsicModuleEquivalence`; the constant coefficient
pullback is likewise the fixed action transported through the coefficient identification.
No extra identification, arbitrary map, or stronger coefficient hypothesis is assumed.

The proof-only imports are the recorded modules for inverse-image exactness,
site-pullback exactness and intrinsic extension exactness. The remaining proof inputs
(exact factorization, preservation of cohomological lower bounds, localization universal
property and etale open exactness) are already reexported by statement imports. The
main theorem docstring gives all seven steps of the node's proof, with those node IDs.

Edge cases checked: empty U/X/V/Y (no nonemptiness binder); zero complexes and zero
antecedents; identity u and identity opens; repeated opens or arbitrary u; positive
level n=1; no restriction on the characteristic beyond the retained coefficient datum;
arbitrarily negative cohomological lower bounds. A complex representing a D+ object
need not itself vanish in sufficiently negative degrees. No smallness or site-universe
equality was added. The natural isomorphisms are restricted to D+ as in the statement.

Searches (2026-10-18):

- msearch leanfinder: "Derived etale origin witnesses transported by inverse image
  and open extension by zero". Eight unrelated standard-etale algebra hits; no match.
- msearch loogle: `CategoryTheory.Functor.mapDerivedCategory`. Twelve generic exact
  functor/derived category hits; used the existing constructions, no witness theorem.
- msearch grep: `etaleOrigin|etale_origin|comparisonUpperStarCompUpperStarIso`.
  No Mathlib hits.
- msearch leansearch: "Natural derived comparison of etale and pro etale inverse
  image transports explicit bounded below etale origin witnesses through open
  extension by zero". Eight etale scheme/ring/stalk hits; no matching theorem.
- rg in upstream WeilConjectures and project lean/Sheaf: searched the node ID,
  FixedEtaleOriginWitness, etaleOriginWitness, and the mapDerivedCategoryNatIso
  expressions for pullback/open comparisons. No existing statement has all three
  retained witness pairs and termwise normalizations. Found generic comparison
  constructions in OpenBaseChangeSiteTransport (different strict-tower coefficient
  transport endpoints) and BoundaryDualityInput (pullback comparison only).
- Read actual live upstream finite-coefficient sources with scompile.py --source,
  since those paths are absent from the older slopmaster2 checkout. The published
  fixed witness, comparison, and extension signatures determined the endpoints.

Validation: `scompile.py` successfully compiled the full conclusion record in a
sandbox-only isolation file after the `@id` annotation repair (sandbox pass 6.1 s;
library confirmation 12.2 s; no warnings). That scratch file was removed before
delivery. The complete module then passed the compilation gate of the prescribed
`deliver2.py --no-push` run, which compiles both sandbox and library forms with the
standard 60-second limit. An earlier published-import compilation failure during a
concurrent maintenance refactor disappeared on the subsequent published snapshot;
no shared or live source was changed by this worker. Only `lean` changes in the
item's node copy, and its recorded signature matches the source verbatim.

## Second reading by Q18

Local rereading by the writing worker, not a claim of independent review: matched each
of the three pairs to its target, exact antecedent and composite isomorphism; checked
the orientation of kappa and both deltas, the D+ restriction, and the normalization
of all three maps. The recorded support comparison needs an explicit `@id` type
annotation to expose its definitionally equal fixed-scalar endpoints for instance
resolution. No mathematical hypothesis or statement was changed. The maintainer's
independent delivery review remains the independent reading specified in the brief.
