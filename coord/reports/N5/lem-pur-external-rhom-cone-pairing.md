## Worker report

This repairs the returned immutable head 215b7740dcb6. The retained module states
`AlgebraicGeometry.Etale.ExternalRHom.external_rhom_cone_pairing`; its only
postponed proof is that named theorem. All helper definitions have real data.
The mathematical node statement and proof plan are unchanged.

### Return findings and repairs

F1: The item no longer cites `lem-pur-ordinary-kunneth-finite-ring` or
`lem-weil-pbc-etale-constant-ring-module-equivalence` as statement dependencies.
Two new definition nodes bind their already-existing helper definitions, without
copying them or asserting either theorem: `def-pur-derived-constant-pullback-comparison`
and `def-pur-etale-constant-scalar-realization`. Both have `existing: true`.
The canonical ring transport remains the recorded `realizationRingIso` from
`def-sfb-site-derived-constant-module-functor`. The imports of the modules containing
the existing definitions are retained.

F2: The second-reading section below is a substantive second pass through the node
and revised module. The dispatcher explicitly prohibits starting another agent;
this is a self-check, not a claim that another worker independently reviewed it.

F3: All K-flat tests in `HasChainNormalization` and `HasKoszulBraiding` now use
`CochainComplex.IsKFlatIndependentCoefficients`. All flat-term tests use
`SheafOfModules.IsFlatOnSite`, as `IsBoundedFlat` already did. The named
`ringedRealization` composes the existing ordinary scalar-realization functor with
the existing canonical constant-ring restriction of scalars; `ringedComplex`
applies this functor degreewise. Its additive instance is the identity on sections.
For ordinary A-complexes U,V, `pointRealization` and `pointComplex` specialize the
existing `commutativeSiteConstantModuleFunctor` to the one-object discrete site
with bottom topology. Sheaves there are ordinary modules: the only covering sieve
is maximal and evaluation at its sole object identifies the constant realization
with the identity. Thus the recorded site predicates express exactly ordinary
A-module flatness and K-flatness, including every acyclic A-complex as a test.
No scheme nonemptiness is used to reflect flatness. Site and coefficient arguments
are explicit, avoiding unconstrained universe metavariables.

F4: `HasSignedHomShift` now first requires
`NatTrans.CommShift ((globalHom A X).flip.map k) ℤ` for EVERY derived target map
`k : K ⟶ K'`. The remaining conjunct retains the signed normalization on every
bounded-below K-injective model. Naturality along an isomorphism
`external A a b K L' ≅ (siteQ A P).obj J` transports that normalization to F,
so its connecting square cannot use an unrelated shift at F. This requires no
extra hypothesis: the theorem existentially supplies the natural shift family S.

F5: The file imports the upstream `DerivedCategoryBraided` module and installs
its `DerivedCategory.braidedCategory` as a local instance via the named
`derivedBraiding` specialization at the fixed sheaf category. This shares
the existing canonical structure arguments between evaluations. There is no braiding
binder B and no existential braiding in the theorem. All evaluations, transposes,
model comparisons and Koszul normalization use that existing derived braiding.
The local instance is exactly the interface requested by the return; it introduces
no private construction or unstated parameter into the exported signature.

### Each hypothesis and clause

* Ring, universes and schemes: `(A : Type (u+1)) [CommRing A]`, with
  `X Y P : Scheme.{u}` and `a : P ⟶ X`, `b : P ⟶ Y`. No characteristic,
  nontriviality, properness, or finite-type assumption is added.
* Ordinary constant-A sheaves and unbounded complexes: `Modules A X` is
  `Sheaf X.smallEtaleTopology (ModuleCat.{u+1} A)`; `Complexes A X` is its
  integer-indexed `CochainComplex`. `siteQ` and `moduleQ` are the existing
  derived-category localization functors.
* Bounded-below K,L,F: `IsPlus` means `∃ n, DerivedCategory.IsGE K n`.
  The theorem and `PreservesCoefficientCones` require it for both targets and
  their external derived tensor, separately.
* Bounded flat E,H: `IsBoundedFlat` quantifies over arbitrary integer lower and
  upper bounds and says `IsZero` outside them; each term satisfies the recorded
  site flatness predicate under the canonical realization. `HasBoundedFlatModel`
  allows isomorphic derived models for all objects of a coefficient triangle.
* Inverse image: `pull` is the left-derived recorded `upperStar`. `pullComplex`
  is its ordinary degreewise counterpart. `external` is derived tensor of the
  two pulled objects; `externalComplex` is ordinary direct-sum total tensor.
* Global derived Hom: `globalHom` composes the native closed derived internal
  Hom with `rightDerivedGlobalSections`. `globalAdjunction`, `transpose` and
  `evaluation` use the existing constant/sections and tensor/Hom adjunctions.
  `homComplex` uses Mathlib's Hom cochains and Hom differential, giving global
  A-linear morphisms, not another internal sheaf-Hom construction.
* The equivalent K-injective model: `HomModel` is a comparison isomorphism
  satisfying `IsHomModel`, its universal evaluation identity. The theorem asserts
  a model exists for every coefficient complex and every bounded-below
  K-injective target. No arbitrary comparison map is assumed.
* Canonical pairing: `pulledEvaluation` uses the recorded constant-pullback
  isomorphism and native monoidal pullback constraint. `pairing` is the transpose
  of the tensor of these maps with the canonical tensor interchange.
* U,V: `HasChainNormalization` universally quantifies over quasi-isomorphisms
  from U,V to the two global Hom complexes, and their recorded K-flat and flat-term
  conditions via the one-point realization. `IsChainEvaluation` fixes every
  local section in every integer bidegree, with unsigned ordinary evaluation.
* Lifted evaluations: the same definition quantifies over every N,M,u,v,c,c',
  using recorded site K-flatness and flat terms, quasi-isomorphisms c,c', and
  `Nonempty (Homotopy (u ≫ c) t)` and the Y analogue. Symmetry of homotopy matches
  the factorization lemma's orientation. No strict factorization is required.
* Target model: T is `externalComplex A a b N M`; i is a quasi-isomorphism from
  T to K-injective J. `targetModel` inverts only Q(c),Q(c') and then uses
  `externalModel` and Q(i). It never substitutes the ordinary tensor of I,I'.
* Koszul chain formula: the existential κ has `IsChainEvaluation` equal to the
  actual `chainPairEvaluation`. Its native cochain `tensorμ` interchanges the
  V-degree s and E-degree q factors, giving exactly (-1)^(s*q), followed by i.
  The second equality in `HasChainNormalization` identifies its localization
  with the defined derived transpose under every specified Hom/model comparison.
* Four variances: `IsNatural` quantifies over f:E'→E, g:H'→H, k:K→K', l:L→L',
  and writes their square using `homMap`. Both coefficient variables are
  contravariant and both target variables covariant.
* Open restriction: `CommutesWithOpenRestriction` includes a cartesian induced
  restriction of P for an open immersion in either factor, keeping the other
  factor an identity. `restrictionTensorIso` composes native pullback composition
  and tensor constraints; `restriction` is transposed pulled evaluation.
* Signed shifts: `HasSignedHomShift` retains `Cochain.leftUnshift`, whose
  coefficient [1] shift contains (-1)^n. `negativeHomShiftIsoOf` uses the
  canonical opposite-shift comparison. The native tensorRight/tensorLeft shift
  comparisons in `leftSource/Target` and `rightSource/Target` have, respectively,
  no sign and (-1)^degree of the left factor. Target naturality is now explicit.
* Both coefficient triangles: `PreservesCoefficientCones` uses distinguished
  triangles in the opposite category. For EACH variable it requires both image
  triangles distinguished, and a `TriangleMorphism` with all three components
  fixed to the corresponding `pairing`. Its third commutativity field is the
  required connecting-arrow square for the specified cone component.

### Dependency declarations read and used

The original statement dependencies retain their recorded declarations:
`Scheme` (Mathlib.AlgebraicGeometry.Scheme), `DerivedCategory` and Q
(Mathlib.Algebra.Homology.DerivedCategory.Basic), `Pretriangulated` and
`Triangle` (Mathlib.CategoryTheory.Triangulated), `upperStar`
(WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs), native derived tensor
(WeilConjectures.SixFunctors.Etale.Derived.Tensor), `CochainComplex`,
`Functor.mapHomologicalComplex`, `QuasiIso`, `CochainComplex.IsKInjective`,
`SheafOfModules.IsFlatOnSite` (Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite),
`CochainComplex.IsKFlatIndependentCoefficients` (Sheaf.Algebra.Homology.KFlat),
`CategoryTheory.homComplex` (Sheaf.Algebra.Homology.HomComplex), and the generalized
internal-Hom framework (Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses).
The size-convention node is a metaconvention, not a missing Lean declaration.
The Hom cochains are global sections, so the native global Hom differential is
used in the wrapper rather than mistaking the recorded internal sheaf complex
for an A-complex.

`CochainComplex.exists_kFlat_map_factorization` is imported from its recorded
Sheaf.Paper.KFlatMapFactorization module. Its full signature uses exactly the
same recorded site predicates now used here. Its mathematical statement is
explicitly cited by the item's original node, so this dependency is retained.

Additional definition dependencies: `derivedConstantGlobalSectionsAdjunction`
from Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap
(`def-kun-constant-projection-morphism`); `realizationRingIso`,
`commutativeSiteConstantModuleFunctor` and its additive instance from
Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
(`def-sfb-site-derived-constant-module-functor`); the two existing definitions
bound by the new definition nodes below. The native derived braiding is
`DerivedCategory.braidedCategory` in
WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided.
Proof-only imports retain the node's recorded proof plan.

### Edge cases

Zero ring, zero modules, empty schemes and zero complexes remain included.
Negative cochain degrees and arbitrary integer bounds are retained. The one-point
realization of U,V is independent of whether X,Y,P are empty. Arbitrary homotopy
factorizations, arbitrary quasi-isomorphic flat K-flat lifts, identity open
restrictions, zero/identity target maps and degenerate coefficient triangles are
covered. Target-shift naturality includes arbitrary isomorphisms and in particular
comparison with a K-injective model; no equality F = Q(J) is assumed.

### Searches

The saved packet searched with leanfinder for the external derived Hom tensor
pairing, loogle for MonoidalClosed/DerivedCategory/NatTrans, and Mathlib grep for
externalHom/externalRHom/homComplex. It found no exact theorem. Direct upstream
and project searches found only the generic closed/sections and signed-calculus
interfaces. The original Mathlib HomComplexShift source check established that
`leftUnshift` already includes the required sign.

The repair repeated searches before adding definition nodes: leansearch for
constant derived sheaves, inverse image and constant-ring scalar extension;
leanfinder for their canonical comparisons; loogle for constantSheaf and
leftDerivedFunctorNatIso; Mathlib grep for upperStarConstantSheafIso,
etaleConstantModuleFunctor and derivedConstantPullbackIso. Leansearch found the
ordinary constantSheaf/constantCommuteCompose API; leanfinder found generic
module realization; loogle had an unknown-name diagnostic; grep found no Mathlib
copies. Direct source/project grep located the exact existing definitions, which
are reused. A parsed search of ALL DAG Lean records found those helpers only in
the theorem nodes named in F1 (and an incidental theorem user); no definition
node owns either notion. `blueprint_refs.py` returned no standalone constant-pullback
or scalar-realization definition unit. Search outputs are retained verbatim in
the new nodes' `mathlib_searches`.

No mathematical node correction, dependency-module replacement, or
STATEMENT-DISPUTED claim is needed. The return concerns the Lean interfaces and
DAG definition bindings, not the source statement.

## New nodes

`def-pur-derived-constant-pullback-comparison` records the EXISTING
`AlgebraicGeometry.Etale.derivedConstantPullbackIso` in
Sheaf.AlgebraicGeometry.OrdinaryKunnethFiniteRing, with `existing: true`.
It defines the canonical constant-to-pulled-constant natural isomorphism by
ordinary constant comparison, derivation and exact derived composition. It has
no finite-ring Kunneth assertion. The generic coefficient category specializes
to ModuleCat A with existing instances. Its source is the canonical constant
comparison used in the blueprint lem-pur-kunneth-supported proof paragraphs 1
and 3 and Stacks 0G7E/08J9. The searches above found the definition but no
definition node carrying it; no Lean duplicate or extra module is written.

`def-pur-etale-constant-scalar-realization` records the EXISTING
`AlgebraicGeometry.Scheme.etaleConstantModuleFunctor` in upstream
WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence, with
`existing: true`. Its source is Stacks Modules on Sites, 093I/03CV. It defines
constant-scalar extension by module sheafification on the unchanged underlying
abelian sheaf, including the functor's maps; it asserts no equivalence theorem.
The same searches found the exact functor and no definition-only DAG binding.
Its full current source was read with `scompile.py --source`.

## Second reading by N5

This is a separate self-check after the edits, under the dispatcher's prohibition
on another agent. I reopened the whole node statement and revised module. The
following are concrete results of that reading, not an independent-reader claim.

1. The first paragraph's A,X,Y,P,a,b and common-universe convention match the
   explicit binders and ordinary sheaf category. D is unbounded, while only
   K,L,F carry `IsPlus`. Bounded flat E,H have arbitrary bounds; every flatness
   predicate now resolves to the same ringed-site definition as the factorization
   dependency. The point-site treatment of U,V avoids testing only after
   restriction to an empty scheme. I found and corrected missing explicit site
   arguments on flatness, which had left coefficient-universe metavariables.
2. The displayed definition of H is exactly `globalHom`; its K-injective
   equivalence is the existential HomModel clause with universal evaluation
   normalization. `pairing` follows the displayed transpose description, and
   all its constant/pullback maps are canonical existing definitions. I checked
   the new definition records against the declarations they bind: they carry
   only these definitions, and the two theorem dependencies in F1 are gone.
3. Every choice in the normalization paragraph is universal in
   `HasChainNormalization`: U,V,f,g, two evaluations, N,M,u,v,c,c', two homotopies,
   J,i and the three Hom models. N,M use recorded K-flatness plus recorded flat
   terms. T is their pulled ordinary tensor. The equality for κ compares exactly
   Q(U⊗V) with the target Hom complex using canonical localized resolution maps.
   The interchange remains the cochain Koszul braiding, so the exponent is s*q,
   including negative degrees. No ordinary I⊗I' model has reappeared.
4. The final paragraph's four naturalities and both induced open restrictions
   match `IsNatural` and the two clauses of `CommutesWithOpenRestriction`.
   Both coefficient-cone clauses fix τ.hom₁, τ.hom₂ AND τ.hom₃ to the stated
   evaluations. Thus the cone term cannot be an arbitrary completion of two
   squares. The target Hom shift previously was pinned only at literal Q(I);
   the new `NatTrans.CommShift` clause now identifies its value at every
   isomorphic bounded-below F with that normalization. Identity maps impose
   no nontrivial extra hypothesis, and arbitrary target maps are covered.
5. The source right-tensor shift is unsigned; the second-variable source shift
   is the existing left-tensor shift with (-1)^r. The Hom shift remains
   Mathlib leftUnshift with its (-1)^n, and the opposite-triangle convention
   retains the same rotation sign on source and target. These give the
   reviewed E-shift exponent s*q+s and H-shift exponent s*q+q+r. I replaced
   the existential B with the exact upstream Koszul derived braiding and
   checked all explicit `(braiding := B)` arguments were removed.

The self-check found no source-statement change. Only the five returned defects
and explicit elaboration arguments were repaired. Compilation and preflight
results are recorded below.

## Validation

The required initial saved-packet dry run failed at the unchanged 60-second
compile limit on both local overlay and server confirmation. After the five
repairs, the first revised compile diagnosed an underconstrained site universe
on M's flat-term predicate. Every K-flat and flat-term site/ring argument is now
explicit. The revised scompile.py run passed without diagnostics for both the sandbox
(58.9 seconds) and actual library module path (59.6 seconds), within the unchanged
60-second per-file limit. The first repaired delivery dry run returned OK at 0513447e1c after server
confirmation. A named specialization of the same canonical derived braiding
then compiled at 54.6/57.5 seconds. Its two class-reducibility warnings were
repaired with the recommended `@[instance_reducible]` attribute, matching the
upstream braiding definition. The final packet is checked again by the required
delivery dry run; no profiler options or diagnostic commands remain in the module.

The final required `deliver2.py --no-push` returned OK at c608da6ae5: server
preflight and all per-file compilation checks passed, including the existing
definition bindings, without warnings. The final module has 77 recorded
declarations, only the named final theorem uses sorry, and its stored signature
is verbatim. The delivery wrapper repeats these checks before pushing.
