## Worker report

Item: lem-sfb-internal-hom-dual-tor-amplitude. Module:
`Sheaf.Paper.InternalHomDualTorAmplitude`; primary declaration:
`AlgebraicGeometry.ProEtale.internalHom_dual_tor_amplitude`.

The shared checkout already contains the Q109 statement and reviewer fix. Reading the
current dependency records revealed that sk-def-localizing-closure has since gained
`IsLocalizingAdmissibleCoefficient`, whose algebraic-closure case is all continuous maps
into PadicAlgCl with its specified topology. The previous expanded hypothesis instead
used the upstream finite-subextension-valued algebraic-closure object. This delivery
updates the existing module in place to the dependency's exact predicate, adds the
published proof-dependency imports, and expands the proof docstring to all seven steps.
Only the node's lean field changes. No new definition or dependency node is needed.
No repair-note file or NB return entry for this item was present in the shared checkout.

Hypothesis and clause correspondence:

- Prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- Field of positive prime characteristic different from ell: `(k : Type u) [Field k]`,
  `[Fact (ringChar k).Prime]`, `[Fact (ringChar k ≠ ℓ)]`.
- S is a separated finite-type k-scheme: `S : Scheme.{u}`, `S.Over (Spec (.of k))`,
  `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` on its structural morphism.
  These are the explicit setting binders of sk-def-sfb-dc-setting, without new data.
- Lambda is a commutative condensed ring: `Λ : Mon (Sheaf (coherentTopology
  Profinite.{u}) Ab.{u + 1})` and `[IsCommMonObj Λ.X]`.
- Its six admissible cases A, Z_ell, O_E, Q_ell, E, Qbar_ell:
  `_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ.X`. Read its entire definition in
  Sheaf.Paper.LocalizingAdmissibleCoefficients: finite rings killed by an ell power,
  continuousMapRingObj for Z_ell and Q_ell, finite intermediate fields E, their
  padicIntegersRingObj, and continuousMapRingObj (PadicAlgCl ell). Isomorphisms are
  isomorphisms of ring objects. No coefficient case is omitted.
- B = Lambda_S: every ambient module uses `condensedRingObj Λ.X S`.
- P lies in the unbounded derived module category: the explicit type of P is
  `DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) ...)`.
- A pro-etale cover: `hP` begins `∃ 𝒰 : Scheme.Cover.{u}
  Scheme.proetalePrecoverage S`. The Mathlib precoverage is propQC WeaklyEtale,
  precisely the fpqc weakly-etale condition, not merely pointwise surjectivity.
- On every chart, the bounded coefficient complex: `∀ i : 𝒰.I₀, ∃ F :
  CochainComplex ... ℤ`; `∃ c d, ∀ n, n < c ∨ d < n → IsZero (F.X n)` gives
  boundedness, and `∀ n, FiniteProjectiveCondensedModule Λ (F.X n)` gives finite
  projective scalar terms. Bounds/ranks may vary with i and degree.
- Why these are exactly complexes of finite projective R = Lambda(*) modules:
  maps between finite copies of the regular condensed module are matrices in R.
  Splitting an idempotent matrix gives a finite projective R-module; applying scalar
  extension recovers its condensed retract. Maps between retracts are the same
  matrices with the two idempotent relations. Thus the entire complex, including
  differential and d squared zero, comes from a complex over R. Conversely every
  finite projective R-module is a finite-free retract, preserved by scalar extension.
  This is the finite-projective case of the finite-matrix convention in the recorded
  CondensedConstantConstructibility module. Lambda need not be discrete.
- Termwise scalar extension on a chart and its comparison to P: `scalarExtensionComplex`
  uses the actual mapMod of `upperStarFromPoint`; the derived pullback of P is
  isomorphic to `DerivedCategory.Q.obj` of this complex. On finite-free retracts
  this is B_U tensor over the discrete constant R with the constant F. It does not
  identify B_U with the discrete constant ring. Its hG witness is zero preservation
  of the fixed canonical functor (additive inverse image), not a freely chosen map.
- The dual is RHom_B(P,B): `relativeInternalHomDual` evaluates the recorded
  `CondensedRing.derivedHom Λ.X S` at `Opposite.op P` and
  `(DerivedCategory.singleFunctor _ 0).obj (Mod.regular (condensedRingObj Λ.X S))`.
  This is the relative closed derived structure, not Hom over Z.
- Uniform integers a <= b: `∃ a b : ℤ, a ≤ b ∧ ...`, before either `∀ N`.
- First vanishing: `∀ N ... ∀ q, q < a ∨ b < q → IsZero` of the homologyFunctor
  at q on `CondensedRing.derivedTensor` applied to P and `singleFunctor _ 0 N`.
- Dual vanishing: the identical test, with `relativeInternalHomDual Λ S P`, and
  `q < -b ∨ -a < q`. All module sheaves are tested, without flatness restrictions.
- Finite Tor amplitude of both is exactly the preceding two quantified vanishings,
  per sk-def-sfb-constructible and DerivedCategory.torAmplitudeIn/finiteTorAmplitude.
- Empty S: `(IsEmpty S → a = 0 ∧ b = 0)` permits the explicitly requested common
  choice zero, without requiring S nonempty or the cover inhabited.

Dependency declarations read and used:

- sk-def-sfb-dc-setting: the setting docstring of
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible;
  its explicit structural-morphism binders are reused. Its chosen compactification
  is irrelevant to this lemma and is not added as a hypothesis.
- def-weil-pbc-proetale-site: Mathlib.AlgebraicGeometry.Sites.Proetale,
  AlgebraicGeometry.Scheme.ProEt, ProEt.topology, Scheme.proetalePrecoverage.
- sk-def-localizing-closure: Sheaf.Paper.LocalizingAdmissibleCoefficients,
  AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient; its imported
  localizing closure construction remains unchanged.
- def-pc-perfect-ring-complex: Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral,
  DerivedCategory.IsPerfectRingComplex; its bounded finite-projective representative
  condition is rendered in the equivalent finite-free-retract condensed form above.
- def-weil-pbc-strict-perfect-coefficient-package:
  Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses,
  SheafOfModules.StrictPerfectCoefficientRepresentationOfUniverses and the imported
  StrictPerfectCoefficientPackageOnSite; the termwise splitting criterion is reused
  for condensed module objects, without creating a second ordinary module package.
- sk-def-sfb-derived-tensor-hom:
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom,
  AlgebraicGeometry.ProEtale.CondensedRing.derivedHom, derivedTensor and their
  parameterized adjunction. Framework source read in shared lean/WeilConjectures,
  as required by coord/pefw-upstream-framework.md.
- sk-def-sfb-constructible: Sheaf.Paper.CondensedConstantConstructibility,
  HasFiniteConstantLocalModel and ConstantModelConstructibleFiniteTor;
  the recorded finite-scalar-matrix convention and generic Tor predicates apply.
- The helpers retain the existing mapHomologicalComplex, Mod.finiteFree and
  Mod.regular constructions. All three helper names are listed in lean.declarations.

Published proof dependencies are imported privately, including finite-type and site
facts, FlatOnSite, FiniteFreeInternalHomExact, RingedInternalHomSignedCalculus,
BoundedExactTermHomQuasiIso, DerivedInternalHomOfUniverses, HomComplex,
WeilConjectures' sheaf InternalHom, RingedSiteTorFlatModel,
LocalizedModuleExactForSystems, and RingedTopoiCanonicalTensorPullbackOfUniverses.
The nodes lem-sfb-module-object-ringed-site-derived-comparison and
lem-sfb-sheaf-cover-local-isomorphism currently have no recorded lean module;
there is consequently no published module to import for those proof-only steps.
They remain explicit in the proof docstring. They are not needed to type this statement.

Edge cases checked before editing: empty scheme/empty cover; zero P; zero-rank finite
free retracts; the zero coefficient ring in the finite A case; single-degree complexes
(reflection changes a degree r to -r); varying local bounds; arbitrary nonflat N;
all six coefficient families including nondiscrete Qbar. The conclusion imposes no
nonemptiness or flatness hypothesis. Site objects remain in universe u+1, site morphisms
in u, with abelian coefficients in u+1; no extra universe equality is imposed.

Searches for existing statements:

- msearch.py leanfinder: 'A locally constant perfect complex on a quasi compact pro
  etale site and its derived internal Hom dual have finite Tor amplitude': 8 hits,
  ordinary projective-source derived Hom, cohomology bounds and LightCondensed
  projectivity; none states this uniform two-interval result.
- msearch.py loogle: 'CondensedRing.derivedHom, TorAmplitude': no hits; Loogle reports
  CondensedRing.derivedHom is not in its Mathlib index.
- msearch.py grep: 'TorAmplitude|torAmplitude|finiteTor', Algebra/Homology: no hits.
- msearch.py leansearch: 'The derived internal Hom dual of a locally constant perfect
  complex on a quasi compact ringed site has finite Tor amplitude with reflected
  bounds': 8 hits on basic derived categories, complex limits, Ext and ordinary
  dualTensorHomEquiv; no exact result.
- rg of internalHom_dual_tor_amplitude, FiniteProjectiveCondensedModule,
  relativeInternalHomDual and the item id in the upstream WeilConjectures and shared
  lean/Sheaf: only the already published own module. It is updated in place, never
  duplicated. The full published source was additionally confirmed through
  scompile.py --source Sheaf.Paper.InternalHomDualTorAmplitude.

Validation: prescribed scompile.py NB/item on the delivered module exits 0, with no
warnings or errors (sandbox 3.5 seconds, library 3.6 seconds). autoImplicit is false;
all universes and variables are explicit. The only postponed proof is the named
internalHom_dual_tor_amplitude theorem, with the matching DAG and full proof docstring.
Definitions contain real constructions. No mathematical node fault or disputed claim.

## Second reading by NB

A separate rereading in this worker session compared the complete original node, all
seven dependency records and their declarations, the published old module, and the
sandbox module. No additional agent was started, as the dispatcher explicitly forbids
it; the maintainer supplies the independent review of this self-delivery.

The rereading checked the prime and structural-morphism assumptions, each of the six
admissible coefficients, that local scalar matrices are chosen before scheme pullback,
the bounded finite-free-retract model, the canonical pullback and termwise extension,
RHom into B[0], the order of quantifiers, the reflected endpoints, and the empty scheme.
The substantive mismatch found was the old Qbar coefficient object; using the current
recorded admissibility predicate repairs it without changing the natural-language node.
The older condensed-retract presentation is mathematically equivalent to the stated
finite projective scalar model by the explicit matrix/idempotent argument above; no
arbitrary coefficient complex or arbitrary scalar-extension map is being assumed.
All helper data are defined, and only the theorem has sorry. Added proof imports compile
together without duplicate declarations. The source blueprint and seven-step proof
remain unchanged. The final lean.statement is extracted verbatim from the delivered
signature, not copied from an earlier binding.
