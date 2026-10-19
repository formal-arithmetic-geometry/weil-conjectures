## Worker report

The delivery states `sbc-def-admissible-lattices` in
`Sheaf.Paper.AdmissibleLattices`. Definitions have actual data; only named helper
theorems postpone proofs. The target statement is unchanged. Two genuine unstated
category prerequisites are supplied, following the human's 2026-10-16 instruction.
The intrinsic constructible-sheaf interface receives a coefficient-size/presentation
repair under §1(B).

Clause-by-clause rendering:

- The prime is `(l : ℕ) [Fact l.Prime]`; the finite extension is `(E : Type u)
  [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`.
- `PbcIntegralRing l E` is the harmless `ULift` of the recorded
  `Padic.coefficientExtensionIntegers l E`. `pbcUniformizer` lifts precisely
  `Padic.coefficientExtensionUniformizer`. `pbcIntegralDatum.ideal` is its principal
  ideal. Quotient level `PbcQuotient (pbcIntegralDatum l E) n` is the actual quotient
  by its `(n+1)`st power. ULift changes no ring or module mathematics.
- `T` is a `Scheme.{u}`, with `[IsNoetherian T]`,
  `hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m`, and
  `hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t)`.
- The square is `_sq : ChosenCartesianSquare h e f g`, with all four corner schemes
  and the four arrows bound explicitly. The smoothness and qcqs assumptions are
  `[Smooth f] [QuasiCompact g] [QuasiSeparated g]`.
- The completed ring is `pbcAdicCompletion`, the actual limit of the recorded finite
  continuous-function coefficient sheaves. These are identified with constant finite
  sheaves by the normalized dependency comparisons. The module publicly imports the
  profinite coefficient inverse-image declaration; the ordinary finite operations
  are the existing canonical finite-coefficient operations, transported by realization.
- The integral category is `PbcIntegralCategory`, the full subcategory defined by
  intrinsic derived completeness, uniformly bounded constructible normalized
  reductions, and existence of compatible etale-origin witnesses. Its morphisms
  are all ambient morphisms. `PbcRationalDerivedCategory` specializes the existing
  raw `ScalarLocalization` to this category and uniformizer. Its objects wrap precisely
  integral objects and Hom is `Localization.Away varpi ⊗[A] Hom`, canonically
  `E ⊗[A] Hom` by the recorded integers-localization theorem. No Karoubi envelope.
- `IntegralLattice.integral` is the integral object, and
  `IntegralLattice.rationalization` is a chosen isomorphism from its image under the
  canonical scalar-localization functor to the specified rational object.
- `IntegralLattice.reduction` applies `pbcCompletedReduction`, i.e. derived scalar
  extension along `pbcAdicProjection`, and then the inverse of the canonical derived
  associated-module-sheaf equivalence. Thus the tensor base is the completed ring,
  not the constant abstract valuation ring.
- `IntegralLattice.IsFiniteLevelEtaleAdmissible` is `∀ n, ∃ M` in the dependency's
  etale bounded constructible category, followed by `Nonempty` of the isomorphism
  from the recorded comparison inverse image to that reduction. These witnesses
  are proof witnesses, absent from `IntegralLattice`.
- `IntegralLattice.IsSquareConstructiblyAdmissible` conjoins that property with
  `∃ a b : ℤ, a ≤ b ∧ ∀ n`, followed by the four output tests on `S`, `X`, `Y`, `X`.
  In displayed order these are `pbcWitnessDirectImage g`, pullback along `f` after
  that direct image, pullback along `e`, and direct image along `h` after the latter.
  These existing functors conjugate precisely the dependency's ordinary uncompleted
  derived finite-coefficient operations by its canonical coefficient equivalence.
- `sbcIntrinsicConstructibleIn` requires intrinsic constructibility of every
  `DerivedCategory.homologyFunctor` value and `IsZero` outside the inclusive interval.
  The single interval is chosen before all levels and all four tests. Each intrinsic
  sheaf predicate existentially chooses its own stratification, so no common
  stratification or integral direct-image identification is imposed.

Dependency declarations and sources read:
`Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso` /
`ChosenCartesianSquare.baseChangeInverseImageIso` (including the square structure);
Mathlib `AlgebraicGeometry.Smooth`, `QuasiCompact`, `QuasiSeparated`, `IsNoetherian`,
`topologicalKrullDim`, and `DerivedCategory.homologyFunctor`;
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` /
`Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
`coefficientExtensionRing`, `finite_coefficientExtensionRing`;
`Sheaf.Paper.AdicCoefficientDatum` / `AdicCoefficients.completedRing`,
`finiteRingComparison`, and quotient coefficient maps;
`Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage` /
`Scheme.proEtale_profinite_coefficient_inverse_image`;
`Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes` /
`Etale.BoundedConstructibleDerivedCategory`;
`Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison` and
`ProEtaleFiniteModules` / the recorded coefficient realizations and comparison;
`Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage` /
`finiteCoefficientDerivedDirectImage`, `finiteCoefficientDerivedPullback`;
`Sheaf.Paper.ProEtaleConstructibleSheaf` /
`Scheme.IsConstructibleProEtaleModuleSheaf`;
`Sheaf.Paper.ProEtaleFixedModuleLocalConstancy` /
`Scheme.IsLocallyConstantProEtaleFixedModuleSheaf`;
`Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk` /
`Scheme.proEtaleGeometricFixedModuleStalk`;
`Sheaf.Paper.BoundedConstructibleTower` / `AdicTower`,
`IsUniformlyBoundedConstructibleAdicTower`, `pbcReductionNormalization`,
`pbcReductionTransition`, `pbcCompletedComparison`;
`Sheaf.Paper.IntrinsicCompletionCompleted` /
`IsCompletedIntrinsicallyDerivedComplete`;
`Sheaf.Paper.WitnessCompatibility` / `PbcWitnessedTower`, the canonical comparison
and coefficient-reduction mates, `pbcWitnessDirectImage`, `pbcWitnessPullback`;
`Sheaf.CategoryTheory.ScalarLocalization` / `ScalarLocalization`,
`ScalarLocalization.localization`;
`Sheaf.Algebra.Category.ModuleCat.Sheaf.HomModule` / `SheafOfModules.homLinear`.

The category prerequisite records had no Lean declaration or Mathlib match. The
prescribed `scompile.py --source` checks confirmed the proposed category modules
were unavailable on the server. A read-only check of the current server DAG and
its delivery refs found no implementation or pending delivery for those two ids.
The source blueprint unit was read locally in full. No unit correction is needed.

Edge cases checked before writing: `n=0` means quotient by the first uniformizer
power; equal integer bounds retain degree `a`; every negative degree is included;
zero objects have zero reduction and satisfy the expected property; empty schemes
admit a positive one-piece stratification with empty stratum and vacuous stalk conditions; zero
finite coefficient rings are allowed by the generic transports; the interval is
uniform over all four families and all levels, while stratifications vary. Integral
objects retain chosen rationalization isomorphisms, so automorphisms are not erased.
No flatness of quotient maps or finite Tor dimension of arbitrary output is assumed.

Searches made with the prescribed `msearch.py`:
- LeanFinder: "Integral lattice in a rationalized constructible derived category
  with etale reductions and uniform bounds". Eight unrelated results, including
  `Algebra.etaleLocus_eq_compl_support`, `BDeRham`, and bounded representatives;
  no integral lattice or category definition.
- Loogle: `CategoryTheory.Functor.essImage, CategoryTheory.ScalarLocalization`:
  unknown project identifier; then valid `CategoryTheory.Functor.essImage`:
  essential-image infrastructure, twelve hits, no target definition.
- Mathlib grep: `AdmissibleLattice|admissible.?lattice|IntegralLattice`: zero hits.
- LeanSearch: "integral lattice rationalization derived category constructible
  etale finite reductions": service unavailable, Internal Server Error.
- Upstream WeilConjectures and side Sheaf source grep for the item id and
  `IntegralLattice`/`PbcBoundedConstructibleComplete`: no target implementation.
  `IntegralLatticePair` in LatticeSheafLocallyConstant is a sheaf-level lattice
  presentation, not a pair in the raw rational derived category.
- Existing modules were searched for normalized towers, etale origins, completions,
  scalar localization, fixed coefficient realizations, and geometric stalks. This
  found and reused the generic declarations listed above. No Mathlib duplicate
  definition was introduced.

## Dependency modules

`def-weil-pbc-bounded-constructible-complete`:
`Sheaf.Paper.BoundedConstructibleComplete` supplies the missing full subcategory.
It uses the recorded actual inverse-limit ring and canonical scalar extensions.
The uniform normalized tower and compatible etale origins are existential properties.
Coefficient realization is defined by associated-module sheafification. The generic
restriction comparison is fixed after forgetting to the underlying additive sheafification;
its source and target identifications are explicit reflexive isomorphisms. Its derived
coefficient reduction comparison is the mate of that specified comparison. This
avoids choosing an unspecified tensor comparison. Every postponed helper has a
source and natural-language proof docstring. The finite-extension coefficient datum
has the actual lifted valuation ring, actual uniformizer ideal, and actual quotients;
its postponed theorem supplies only properties of those already specified objects.

The complete-category clauses map as follows. `PbcIsIntrinsicallyComplete`
transports to the recorded constant-quotient inverse-limit presentation and asks for
invertibility of `IsCompletedIntrinsicallyDerivedComplete` on a representative and
an actual finite generating tuple. `PbcHasUniformConstructibleReductions` identifies
all quotient-linear levels and semilinear transitions with those of an `AdicTower`
satisfying `IsUniformlyBoundedConstructibleAdicTower`; its common local models,
stratification, and bounds are exactly those in the dependency. This condition
applies to the integral category, not to the four output families. In contrast, the
output families are tested by their separate intrinsic cohomology sheaves.
`PbcHasCompatibleEtaleOrigins` existentially uses `PbcWitnessedTower`, whose retained
pairs are the existing `EtaleOriginWitness` objects. Its comparison isomorphisms,
etale coefficient reductions, beta maps, and comparison compatibility are those of
that supplied interface. The displayed equation with `pbcFunctionReduction` and
`pbcReductionNormalization` fixes its theta maps to the reductions of this particular
completed object. Iterated adjacent reductions carry the identity and quotient
cocycles. `PbcIntegralCategory` adds exactly the prime, finite-extension and
Noetherian finite-dimensional invertible-prime base scope required in the node.

`def-weil-pbc-rational-category`:
`Sheaf.Paper.PbcRationalCategory` supplies the missing raw rationalization. The
constant-to-completion map gives a ring homomorphism to compatible global sections.
The recorded module-Hom linear structure is restricted through that homomorphism,
then inherited by derived categories and the full subcategory. The existing
`ScalarLocalization` is used directly. Its equivalence with the Hom-tensor-E formula
is the recorded localization-of-integers interface, not a new definition or axiom.

`def-weil-proetale-constructible-sheaf`:
`Sheaf.Paper.ProEtaleFixedModuleConstructible` repairs the coefficient size and
module presentation of the original intrinsic definition. The original takes
`A : Type u` and ringed modules, whereas the finite quotients used here have size
`u+1` and the comparison functor uses fixed module sheaves. The repair uses exactly
finite constructible locally closed strata, local constancy after actual inverse
image to each stratum, and finite geometric stalks. It publicly preserves the
original declaration and uses the already recorded fixed-module local-constancy
and stalk interfaces. It does not substitute an etale-essential-image condition.


## Validation

Resumed the prior sandbox attempt on 2026-10-16. Re-read the item, its current
statement dependencies, the archived master blueprint definition and the two category
prerequisite definitions. Repeated the LeanFinder, Loogle, Mathlib grep and LeanSearch
queries above; the same results were obtained, with LeanSearch still unavailable.
The only addition to the item's statement dependencies is the already landed
`def-weil-pbc-witness-compatibility`, whose canonical finite coefficient operations
and compatible-origin tower are used by this delivery. No node statement changes.

All four delivery modules passed the prescribed `scompile.py` invocation together,
with each compiled separately in dependency order. Current-server confirmation
compiled `BoundedConstructibleComplete` in 7.1 seconds, `PbcRationalCategory` in
3.0 seconds, `ProEtaleFixedModuleConstructible` in 2.3 seconds, and
`AdmissibleLattices` in 3.1 seconds. No warnings were emitted. Local compilation
initially encountered a duplicate `CochainComplex.IsKFlatIndependentCoefficients`
in the mirrored tower import closure; the wrapper's current-server confirmation
successfully compiled that closure and every delivered module. No import or source
workaround was applied to the published library.

## Second reading by Q06

Independent reading on 2026-10-16. I opened the sandbox node and all four modules,
the fourteen statement-dependency records, and the declarations used below. The
source is the master blueprint definition at order 1444, read in the launcher's
literature mirror. I also read the older smooth-base-change TeX, lines 1230–1261:
its Karoubi-pair lattice differs intentionally from the master definition. This
delivery correctly follows the master's raw-rationalization lattice, rather than
silently importing the older idempotent datum. No statement correction is made.

Here is my independent object/hypothesis/clause checklist and its Lean rendering.
Every item passes.

1. The four schemes and arrows are `T`, `{X Y S}`, `{h : Y ⟶ X}`,
   `{e : Y ⟶ T}`, `{f : X ⟶ S}`, `{g : T ⟶ S}`. The chosen Cartesian
   identification is `_sq : ChosenCartesianSquare h e f g`. I read
   `ChosenCartesianSquare` and `baseChangeInverseImageIso`; the arrow order is
   the node's order, not the differently labelled older source square.
2. Smoothness belongs to `f`, qcqs to `g`: `[Smooth f] [QuasiCompact g]
   [QuasiSeparated g]`. These are the recorded Mathlib notions. There is no
   properness, separatedness, finite-type assumption on `g`, or extra base
   hypothesis on `S`, `X`, or `Y`.
3. The coefficient prime and finite extension are `(l : ℕ) [Fact l.Prime]`,
   `(E : Type u) [Field E] [Algebra (Padic l) E]
   [FiniteDimensional (Padic l) E]`. I opened `CoefficientExtension`,
   `CoefficientExtensionFinite`, and `IntegersLocalizationUniformizer`.
   `PbcIntegralRing`, `pbcUniformizer`, and `pbcIntegralDatum` use the recorded
   integer subring and its recorded chosen uniformizer, with an `ULift` only
   to put coefficients in the small site's required value universe.
4. The category-domain hypotheses on `T` are exactly `[IsNoetherian T]`,
   `hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m`, and
   `hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t)`. The stalk condition is
   invertibility on the scheme. It does not demand a field structure on stalks.
5. `PbcQuotient (pbcIntegralDatum l E) n` is `A/(varpi^(n+1))`.
   `pbcAdicCompletion` is the actual inverse limit of `pbcAdicRings` and
   `pbcAdicProjection` is its limit projection. I read these definitions and
   `AdicCoefficients.finiteRingComparison`: the continuous-function coefficient
   presentation and constant finite coefficients have their specified canonical
   comparison. The recorded profinite inverse-image interface is publicly imported.
6. The integral category is the full subcategory `PbcIntegralCategory`; the
   rational category is `PbcRationalDerivedCategory`. `IntegralLattice.integral`
   is an integral object, and `IntegralLattice.rationalization` is a chosen
   isomorphism from its image under `pbcRationalization` to the given `K`.
   I read `ScalarLocalization` itself: its objects wrap the original objects,
   its morphisms are localization-tensor-Hom, and its localization functor is
   identity on objects and tensors morphisms with one. No Karoubi completion
   or identification up to mere isomorphism replaces the chosen lattice datum.
7. `IntegralLattice.reduction` first applies `pbcCompletedReduction` to the
   ambient object `L.integral.obj`, then the inverse of the canonical derived
   associated-module equivalence. The scalar extension is along the completed
   ring's projection, so this really represents the displayed completed tensor.
8. `IsFiniteLevelEtaleAdmissible` says `∀ n : ℕ, ∃ M` in the recorded
   `Etale.BoundedConstructibleDerivedCategory`, with `Nonempty` of an isomorphism
   from `(comparisonUpperStar ... T).mapDerivedCategory.obj M.obj` to the
   reduction. I opened the bounded constructible predicate and the recorded
   comparison/realization declarations. The witnesses are existential properties,
   rather than retained fields of `IntegralLattice`.
9. The four outputs in `IsSquareConstructiblyAdmissible` have respectively
   targets `S`, `X`, `Y`, `X`. They are `pbcWitnessDirectImage g`,
   `pbcWitnessPullback f` after that image, `pbcWitnessPullback e`, and
   `pbcWitnessDirectImage h` after that pullback. I opened these functors and
   `finiteCoefficientDerivedDirectImage`, `finiteCoefficientDerivedPullback`:
   they are ordinary uncompleted ambient derived operations, transported by
   the existing coefficient realization, with no constructible output assumed.
10. The predicate conjoins finite-level admissibility with `∃ a b : ℤ,
    a ≤ b ∧ ∀ n : ℕ`, followed by all four tests. Thus one inclusive interval
    is chosen before the level and works for every output. Each test is
    `sbcIntrinsicConstructibleIn`: for every integer `i`, intrinsic constructibility
    of `(DerivedCategory.homologyFunctor _ i).obj K`, and `IsZero` when
    `i < a ∨ b < i`. I checked the Mathlib homology-functor signature.
    Each sheaf chooses its own stratification; neither a common stratification
    nor integral pushforward/reduction identifications have been added.

Dependency-module reading (there are no newly created DAG nodes):

- `def-weil-pbc-bounded-constructible-complete`: the module's three predicates
  match the current node's three clauses. `PbcIsIntrinsicallyComplete` uses the
  recorded intrinsic-completion map, with an existential generating tuple and
  representative. `PbcHasUniformConstructibleReductions` uses `AdicTower` and
  `IsUniformlyBoundedConstructibleAdicTower`; its equations identify every
  semilinear transition with the actual reduction transition. I opened both
  declarations, including the common local model and interval. Finally
  `PbcHasCompatibleEtaleOrigins` uses `PbcWitnessedTower`, whose origins are
  bounded below, not arbitrarily assumed bounded constructible. Its theta
  equation identifies those normalizations with this object's canonical ones.
  All witnesses occur in a `Prop`, and the full subcategory retains all ambient
  morphisms. I read the master category definition and Stacks `proetale.tex`,
  `section-suitable-derived` and `definition-Dbc` (lines 5757–5800). The node
  expressly distinguishes its completed-ring/uniform-tower convention from
  Stacks' constant-ring locally finite-Tor-dimension convention; the module
  correctly implements the node and asserts no extra comparison with Stacks.
- `def-weil-pbc-rational-category`: the constant-section action is constructed
  from `adicDatumScalar` and the specified completed-ring comparison. Its
  section naturality is the named postponed theorem. Linearity is inherited
  by the derived category and full subcategory. The raw scalar-localization
  definition gives precisely the node's object and Hom formula, through the
  recorded uniformizer-localization theorem (and the harmless lift of scalars).
  I read the master's order-1305 definition as well as this dependency node.
- `def-weil-proetale-constructible-sheaf`: I compared the new fixed-module
  interface with the node and the original ringed-module declaration. The
  latter's `A : Type u` and ringed presentation cannot directly accept these
  quotient coefficients in `Type (u+1)`. The repair has exactly a positive
  finite locally closed constructible stratification, actual inverse image
  along its immersion, the recorded fixed-module local-constancy predicate,
  and finite geometric module stalks. I opened these predicates, the stalk
  colimit, and `LocallyClosedStratification` including its inherited partition
  fields. The explicit constructibility conjunct is harmless even where the
  inherited current stratification already supplies it. It is not replaced
  by membership in an etale essential image. The original interface remains
  available by public import, and `lean.note` explains the presentation repair.

Edge cases: `n = 0` is the residue-ring level, not the zero-power quotient.
`a = b` allows a single degree, and negative degrees are all quantified over.
The zero object is not excluded; it can have any chosen rationalization
isomorphism permitted by the lattice type. Empty schemes are allowed, with
one empty stratum satisfying the positive-stratum convention and vacuous
geometric-point tests. Generic realization and constructibility allow the zero
coefficient ring. No characteristic beyond primality and invertibility on `T`
is excluded. There is no finite/nonempty index type replacing all levels.
The site has objects in `Type (u+1)` and morphisms in `Type u`; module coefficients
and stalk colimits live in `u+1`, while geometric-point fields live in the
recorded bound `u`. All universes and variables are explicitly bound, with
`autoImplicit false`; no equality of site object and morphism universes is imposed.

Independent searches: LeanFinder for "Lattice object in scalar localized category
with constructible finite reductions" returned generic linear localizations and
localized modules, not this notion. Loogle for
`CategoryTheory.Functor.essImage.getIso` returned only the generic witness-isomorphism
accessor. The Mathlib grep query "scalar.*localization|integral.*lattice|derived.*complete"
returned generic algebraic constructions. Direct `rg` on Mathlib, upstream
`WeilConjectures`, and side `lean/Sheaf` for `IntegralLattice`, admissible lattices,
`PbcIntegralCategory`, and `PbcRationalDerivedCategory` found only the distinct
sheaf-level `IntegralLatticePair`, not this derived-category datum. LeanSearch
for "Integral lattice in scalar localization of derived constructible complete
sheaves" was unavailable (Internal Server Error); no absence conclusion is
drawn from it. I also opened the newer module-object framework's
`ProEtale.IsConstructibleModuleObject` and `ProEtale.boundedConstructible`:
these use local finite presentations and ordinary bounded cohomology, with no
intrinsic derived completeness or compatible uniform reduction tower, and
therefore do not supply the two missing category prerequisites. The prescribed
current-server source query still reports `BoundedConstructibleComplete` unavailable.

No mathematical mismatch was found, so the Lean modules and node signatures
are left unchanged. I added this independent clause-by-clause reading. All
definition data are actual constructions; any choice from a postponed theorem
is fixed by its uniqueness/normalization condition. Each helper theorem has a
source, matching blueprint id, and a natural-language proof; its proof remains
`sorry`. The definition node has no proof steps to restate. Module/declaration
docstrings, line lengths, imports, and recorded signatures were checked.

Second-reader validation: the signature parser confirms verbatim equality for
all four `lean.statement` records. The prescribed four-file `scompile.py` run
passed current-server confirmation with no warnings: integral category 6.9 s,
rational category 3.2 s, constructible-sheaf interface 1.9 s, lattice module
2.9 s. The local mirror first lacked an `AdicCoefficientDatum` object file;
the wrapper's normal server fallback compiled that dependency closure and all
delivery modules, each within its unchanged 60-second limit. No library source
or tool workaround was applied.
