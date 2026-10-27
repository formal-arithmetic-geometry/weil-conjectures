## Worker report

The delivery states `AlgebraicGeometry.clopenStrictSystemSupport` in
`Sheaf.Paper.ClopenStrictSystemSupport`. Its sole postponed proof is the theorem's
`sorry`; the docstring reproduces all seven proof steps and their dependencies.
The helper data structures bundle the actual functors, equivalences, adjunctions and
natural isomorphisms in the conclusion. The helper coherence predicates explicitly
write their canonical equations; subtypes combine the data and equations. Their data
are not `sorry`, no coefficient-system notion is redefined, and no object is chosen
from a postponed existence theorem. The theorem concludes existence of these packages.
No statement correction, disputed statement, new DAG node or dependency repair is needed.

I resumed the existing draft and unfinished compile log after interruption. No delivery
had occurred. I repaired the missing right-derived localization normalization, removed
development profiling, fixed line lengths, and cached published small-site/additive
witnesses. The component `CoefficientEvaluationImage` supplies exactly the system and
level derived images and adjunction evaluation; unrelated coefficient-descent results
of the full derived-image package are not assumed or restated. No time limit was raised.

### Hypotheses and categories

- `F : WeilConjectures.FiniteFieldDatum`, `l`, `[Fact l.Prime]`, `_hl : l ≠ F.p`,
  and the finite-dimensional `Padic l` field algebra `E` give the fixed finite-field
  and coefficient data. The ring and uniformizer are exactly
  `Padic.coefficientExtensionIntegers l E` and
  `Padic.coefficientExtensionUniformizer l E`. There is no separately chosen ring.
  `n : ℕ` throughout the imported system API denotes the positive exponent `n+1`.
- The two `Scheme.Over (Spec (.of F.k))` structures and the `LocallyOfFiniteType`
  and `QuasiCompact` instances on their structure maps say X and Y are finite type
  over k. `g.IsOver`, `IsSeparated g`, `LocallyOfFiniteType g`, and `QuasiCompact g`
  say exactly that g is a separated finite-type k-morphism. No separatedness of
  the structure morphism of Y is assumed.
- `I`, `[Finite I]`, `Xi`, `j`, and the two immersion instances give the finite
  family of clopen immersions. `_hdisjoint` is pairwise disjointness of their ranges;
  `_hcover` says their union is all X. No nonemptiness assumption occurs anywhere.
- `c : Compactification g` is the chosen factorization; `c.precomp (j i)` has
  ambient `c.Z`, open arrow `j i ≫ c.i`, and proper arrow `c.g`, exactly c_i.
- `strictEtaleCoefficientSystem` is the dependency's actual `CoefficientSystem` on
  `T.smallEtaleTopology`, with constant quotient-ring sheaves and semilinear
  transitions. `strictEtaleLevel`, `coefficientEvaluation`, and `StrictEtaleEvaluation`
  are the same dependency's exact evaluations and unbounded derived evaluations.
  `DerivedCategory` is the ordinary unbounded derived category, with the existing
  `HasDerivedCategory` instances; no category of evaluated diagrams replaces it.

### Every conclusion clause

1. `StrictEtaleClopenOrdinaryData.image i` is the published geometric module/system
   inverse/direct image interface for `j i`. It fixes actions on morphisms, constants,
   scalar restriction, transitions, and evaluated ordinary adjunction transposes.
   `equivalence` is an equivalence from actual systems to the dependent product.
   `restriction` identifies its functor with the family of geometric restrictions.
   `reconstruction` identifies its inverse with the product of direct-image insertions.
   The ordinary coherence conjunction asserts finite-limit and finite-colimit preservation for
   each insertion and its levels. Restriction exactness is already `systemExact`
   and `inverseExact` of the imported ordinary-image interface; exactness of the
   displayed equivalence follows also from being an equivalence of abelian categories.
2. `offComponent` and the invertible component counit identify direct image with
   zero insertion. `reverseAdj` and `image.systemAdj` are the two orders of adjunction.
   Their component unit/counit equation fixes the reverse unit as the inverse of
   the ordinary restriction/direct-image counit, so these are the canonical
   coordinate adjunctions, not arbitrary rescalings. The level equations do the same.
   `evaluatedUnit` and `evaluatedCounit` spell out the reverse-adjunction evaluation
   squares; the original order's evaluation follows from `image.systemTranspose`.
   `emptyZero` says every system is zero when I is empty.
3. `StrictEtaleClopenDerivedData.image` is `CoefficientEvaluationImage` for that
   same ordinary image, with evaluations `S.PX` and `(Si i).PX`. It contains the
   representative factorization of restriction, the universal total derived direct
   image, its adjunction transpose, and the evaluated adjunction equations. Transition compatibility holds because
   the functors and maps act on actual strict systems before localization; their
   localization comparisons retain the same termwise maps.
   `directFactors` and `levelDirectFactors` identify insertion with termwise exact
   direct image after localization. `directLocalization` and
   `levelDirectLocalization` make these comparisons inverse to the universal
   right-derived map. This prevents arbitrary choices of localization comparisons.
   `equivalence`, `restriction`, and `reconstruction` give the stated unbounded
   derived product equivalence and finite-product inverse. `reverseAdj` and
   `reverseLevelAdj` supply the other adjunction order. `insertionTranspose` and its
   level version identify that adjunction on complexes with the ordinary adjunction,
   so its units and counits descend termwise. The evaluation squares identify both
   maps after evaluation. `offComponent` and `emptyZero` retain zero and empty cases.
4. `S : StrictEtaleCompactSupport ... c` and the family `Si` use the published
   compact-support interface: `functor = derivedOpen ⋙ properDerived.system.direct`.
   These are conclusion witnesses to the canonical construction, not added hypotheses.
   The support data's `sameTarget`, `sameAmbient`, and `sameProper` require literally
   the same evaluation packages and proper derived image for the common proper part.
5. `ordinary` is an isomorphism of strict-system functors
   `E_i ⋙ a_! ≅ (a j_i)_!` BEFORE localization. `right` and `levelRight` give the
   corresponding restriction compositor. `levelRightUnderlying` fixes it as the
   canonical geometric pullback compositor, via the published module-underlying
   isomorphisms. `rightEvaluation` is its evaluation square. `unit` and `levelUnit`
   are exactly the ordinary composite-adjunction unit normalization, determining the
   extension compositor uniquely. On the extension-presheaf generators this is the
   identity on the component, zero off it, as follows from Stacks 03DI's adjunction
   formula. Since it is a natural transformation on actual systems, its components
   commute with every semilinear transition and all system morphisms; this is not
   merely a claim about selected maps on evaluations. `ordinaryEvaluation` fixes
   its finite evaluations to the same ordinary unit-normalized level compositor.
6. `derived` and `levelDerived` are its localized natural isomorphisms. `factors`
   and `levelFactors` state their equality with the termwise ordinary compositor
   on complexes, under the specified localization comparisons.
7. `support` is b_i, and `levelSupport` its ordinary finite-level version.
   `supportMap` and `levelSupportMap` say their homs are the whiskering of the open
   compositor by the common actual proper derived functor. HEq only accommodates
   the differing presentations of equal proper data and composite functor parentheses.
   `evaluatedSupport` explicitly compares the image of b_i under evaluation with
   the finite-level comparison, using the published open/proper evaluation maps.
   All these are natural isomorphisms of functors and thus include their action
   on every morphism. No independent arrow is chosen after evaluation.

### Dependency declarations read and used

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, its Ring
  and Coefficient constructions; the theorem uses the underlying finite-field and
  canonical padic coefficient constructions, rather than fixing one finite level.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, `IsSeparated`,
  `UniversallyClosed`; `Morphisms.FiniteType`: `LocallyOfFiniteType` and the imported
  `QuasiCompact`; `OpenImmersion`: `IsOpenImmersion`; `Morphisms.ClosedImmersion`:
  `IsClosedImmersion`. I read their signatures and docstrings.
- `WeilConjectures.Compactification.RefinementCategory` and its Defs import:
  `Compactification`, `Compactification.Refinement`, its category, and `precomp`.
- `Sheaf.Paper.CoefficientSystemDerivedComparison` and its public ImageData interface:
  `coefficientSystemDerivedComparison`, `CoefficientSystemOrdinaryImage`,
  `CoefficientSystemDerivedImage`, `CoefficientDerivedImage`, `coefficientUnderlying`,
  evaluation/factorization and transition packages. I read the full ordinary-image
  fields and the universal derived-image and evaluated adjunction fields.
- `Sheaf.Paper.EtaleCoefficientSystemAdjoint`: `strictEtaleCoefficientSystem`,
  `strictEtaleLevel`, `strictEtaleSetAdjunction`, `StrictEtaleOrdinaryImage`,
  `StrictEtaleCompactSupportData/Coherence`, its projections, `functor`, `levelFunctor`,
  `evaluation`, and `etaleCoefficientSystemAdjoint`. The support data and normalization
  are those of this dependency, not a separate definition of compact support.
- Added landed definition dependency `def-per-site-comparison-pullback-data`, whose
  recorded module `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence` is
  publicly imported. Its recorded declaration
  `ProEtale.supportSiteEtaleComparisonComp (Type (u + 1)) (j i) c.i` supplies the
  canonical composition identification. Its inverse in `levelRightUnderlying`
  compares restriction along `j i` and `c.i` with restriction along their composite.
  This is a definition by adjoint conjugation, with the same body as the previous
  unprefixed construction; no theorem assertion is needed for this clause.

All twelve original proof dependencies are imported in their recorded modules (plain
imports for proof-only material): `Etale.sheaf_clopen_product`, exact-functor derived
localization, `Localization.lift`, open-extension adjunction, `unit_conjugateEquiv_symm`,
`Adjunction.comp`, `openImmersionLowerShriekComp_coherence`, `localizedSystemExact`,
`extensionByZeroPresheaf`, and `PresheafOfModules.sheafification`, together with the two
system comparison modules already public. These preserve the seven-step proof plan.

### Sources, searches, and edge cases

I read Zheng's PDF pp. 34--36, especially Constructions 5.14--5.15 and Lemma 5.16;
Stacks `etale-cohomology.tex`, `lemma-constant-smooth-statements` (0A5B), and
`sites-modules.tex`, `lemma-extension-by-zero` (03DI) and
`lemma-extension-by-zero-exact` (03DJ); and the retained Q121 argument, old steps 5--6.
The clopen-system refinement is explicitly the node's argument, rather than a claim
that the brief Stacks disjoint-union paragraph already states the strict-system result.

Actual logged searches: LeanFinder, “Finite clopen decomposition of strict etale varying
coefficient systems and the compact support open extension compositor”, gave eight
hits about clopen topological covers, standard etale presentations and profinite
limits; none states this theorem. Loogle, `"SheafOfModules", "prod"`, returned twelve
free-presheaf/generator results, not the theorem. msearch grep,
`strict.*(system|tower)|semilinear|extensionByZero` in `CategoryTheory/Sites`, gave no
hits. I searched `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
for the node id and proposed names: no existing declaration. The existing
`FiniteClopenDerivedDecomposition` and `ClopenStrictSystemComparison` concern the
pro-etale/integral coefficient family and do not state this finite-family strict
etale theorem. Earlier successful LeanSearch and Loogle/LeanFinder queries remain
in the sandbox's search log; in particular LeanSearch returned ordinary topological
sheaf-product and finite-product category lemmas, not varying-coefficient systems.

Checked edge cases: I empty implies X empty by the cover hypothesis; the ordinary
and derived `emptyZero` clauses express the zero category, without demanding a
chosen zero object be definitionally every object. Empty components have zero
restriction and insertion. For a one-element family, restriction and insertion
are inverse equivalences, and the unit-normalized compositor reduces to ordinary
open composition. Level n=0 means A_1, so A_0 has not been inserted accidentally.
No quotient map is required flat, no normalization/cartesianness is imposed on the
strict systems, no boundedness is imposed on the derived input, and no separatedness
of Y over k has been added. The finite index type uses the schemes' universe;
any finite family can be represented there, including the empty family.

Validation: only `clopenStrictSystemSupport` is postponed. Every helper definition
is complete and every variable/universe is explicitly bound (`autoImplicit false`).

The final `scompile.py` run passed both preliminary and library-name compiles
(22.9 s and 15.3 s). It emitted no errors or warnings. Development profiling is removed.

## Repair of returned delivery 058a2cbebdde

The maintainer returned H2 and a theorem-statement-dependency finding for the
canonical restriction compositor in `levelRightUnderlying`. I replaced the added
`lem-weil-pbc-comparison-pullback` statement dependency with the existing landed
`def-per-site-comparison-pullback-data`; publicly imported its recorded module
`Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`; and used its recorded
`ProEtale.supportSiteEtaleComparisonComp (Type (u + 1)) (j i) c.i`.
I read the full signatures, docstrings and conjugate-isomorphism bodies of both
compositors: they use the same pullback adjunctions and restriction composition map.
The inverse and its application to the underlying sheaf remain in the same equation.
The saved packet's initial dry run passed, but retained the returned defect; this
repair makes the requested dependency and declaration changes explicitly.
The current read clone differs from this packet only in `stmt_deps` and `lean`.
The delivery wrapper rebases the repaired packet on current server main.

## Second reading by Q63

I checked the preserved statement against the node and the repaired equation.
The finite field, prime unequal to its characteristic and finite coefficient extension
remain the coefficient binders. Finite-type X and Y use locally-finite-type and
quasi-compact structure maps, while only g is separated. The finite index family,
clopen immersions, disjoint ranges and covering equation permit empty components
and the empty cover. The ordinary and derived product equivalences, both adjunction
orders and termwise evaluation clauses remain those item conclusions described above.
`levelRightUnderlying` still pins the right compositor to canonical geometric
restriction composition; `unit` and `levelUnit` pin the open-extension compositor;
`factors` and `levelFactors` pin its localization; `supportMap`, `levelSupportMap`
and `evaluatedSupport` pin its whiskering by the common proper derived image and
finite-level evaluation. The replacement definition has identical mathematical data.
The theorem signature and all other conclusion predicates retain their original text,
except for this compositor name. Only the item theorem is postponed.

Repair validation (2026-10-23 UTC): `scompile.py Q63
lem-pur-clopen-strict-system-support` compiled the repaired file in sandbox mode
(34.0 s) and under its library module name (19.2 s), both within the unchanged
60-second limit, with no errors or warnings. The self-check confirms the node
changes only `stmt_deps` and `lean`, the recorded theorem signature is verbatim,
all lines are at most 100 characters, and the sole `sorry` is the item theorem.
