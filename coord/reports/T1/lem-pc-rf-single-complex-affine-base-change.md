## Worker report

The module `Sheaf.Algebra.Homology.SingleComplexAffineBaseChange` states
`RingTensorCohomology.singleComplex_affine_baseChange_isIso`, with proof `sorry`.
It uses the module formulation explicitly given in the node and in the affine proof of
[Stacks Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8). The cited Stacks checkout
is absent on this machine, so I opened the published tag, including its affine proof.
There are no new definitions, dependency replacements, or statement corrections.

Hypothesis and clause correspondence:

- The affine cartesian square is specified by the commutative rings `R A B` and
  `[Algebra R A] [Algebra R B]`. Here `B` denotes R', and A' is `A ⊗[R] B`.
  Their spectra and the two projections give precisely the affine cartesian square;
  taking A' to be the tensor product chooses its canonical affine presentation.
  Arbitrary isomorphic affine cartesian squares are covered by transport along
  the canonical ring isomorphism. There is no flatness assumption.
- `M : CochainComplex (ModuleCat A) ℤ` and
  `N : CochainComplex (ModuleCat (A ⊗[R] B)) ℤ` are the two unbounded complexes.
  They represent K and K' under the affine quasi-coherent derived equivalence.
  The scheme categories and the equivalent module formulation are not independent
  additional data in the node: I use its expressly stated module formulation.
- `P`, `p : P ⟶ M`, `_hp : QuasiIso p`, and `_hP : ...kFlat P` specify an arbitrary
  K-flat resolution. This is a representative choice, not a K-flatness restriction
  on M. Every complex has such a resolution. `P` extended to A' therefore
  represents the node's `M ⊗ᴸ_A A'`.
- `h : Q.obj (extendScalars ... P) ⟶ Q.obj N` is the given arrow in D(A'),
  equivalently the arrow `L(g')^* K ⟶ K'`. It is a derived morphism, so the
  statement does not restrict h to a chain map or require N to be injective.
- `L : ModuleCat.BaseDerivedTensorCohomologyModel R A B P (A ⊗[R] B)` is a
  presentation of the total derived scalar extension to B, its counit, canonical
  tensor-algebra action, and comparison. This model exists for every P and every
  pair of R-algebras, without Tor independence. Quantifying over the model makes
  the theorem independent of choices. The `HasDerivedCategory` binders merely
  supply the common derived-category constructions, with all universes explicit.
- For EVERY prime x' of A' and EVERY integer i, `hlocal` requires `IsIso` after
  extension of scalars to `Localization.AtPrime q'.asIdeal`. The map being
  localized is `L.comparison i`, followed by the homology of h, with the canonical
  `homologyFunctorFactors` isomorphisms between complex and derived homology.
  Thus it is the A'-linear cohomology map of the canonical comparison followed
  by h, not an arbitrary map on cohomology.
- This localization condition is exactly the node's stalk condition, using the
  identifications already recorded by `exists_affineDerivedBaseChangeLocalization`
  and `derivedTensor_localization_cohomology`. The images x,s',s are determined
  by q' and the ring maps, not additional freely chosen primes. The source is
  identified with `H^i(M_x ⊗ᴸ_{R_s} B_{s'})` extended from
  `A_x ⊗_{R_s} B_{s'}` to `A'_{x'}`. Exact localization identifies the target with
  `H^i(N_{x'})`. The localization isomorphisms are compatible with the first
  comparison, and functoriality and exactness of localization give compatibility
  with h. Consequently conjugating by these identifications preserves `IsIso`.
  This is the equality/identification used in the final paragraph of the affine
  proof of Tag 0DJ8; it introduces no extra local condition.
- The conclusion `IsIso (...)` is in D(B) = D(R'). Its first arrow is `L.counit`
  evaluated on the restricted P; the ordinary tensor identification
  `Q.map L.ordinaryIso.hom` identifies its target with the restriction of
  `P ⊗_A A'`. The `quotientCompQhIso` and `mapDerivedCategoryFactors` arrows only
  align the canonical localization presentations. Finally exact restriction of
  scalars applied to h gives the second arrow. Hence the full composite is the
  node's `M ⊗ᴸ_R R' ⟶ M ⊗ᴸ_A A' ⟶ N` in D(R'), not an existential isomorphism
  of objects and not merely a map with the same source and target.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`;
  these interpret the node's affine square geometrically.
- `Sheaf.AlgebraicGeometry.BaseChangeConventions`: its recorded base-change
  convention uses `Limits.pullback`; the affine presentation here is its ring
  tensor product. `Scheme.Modules.moduleBaseChange` is the sheaf-module convention,
  not a replacement for the affine ring tensor product.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`; the affine equivalence
  translates these to the module derived categories in the theorem.
- `Sheaf.AlgebraicGeometry.DerivedPullback`: `derivedPullback`, and
  `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`: `schemeDerivedDirectImage`.
  Their affine tensor and restriction interpretations explain the module comparison.
- `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`:
  `derivedPullback_tilde_iso`, whose formula on arbitrary K-flat resolutions
  identifies the domain of h with the derived pullback in the node.
- Added existing statement dependency `def-pc-module-kflat-complex`:
  `CategoryTheory.MorphismProperty.kFlat` from
  `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`, with its cochain-complex
  specialization imported through `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat`.
- Added existing statement dependency `def-pc-base-derived-tensor-cohomology-model`:
  `ModuleCat.BaseDerivedTensorCohomologyModel` from
  `Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel`. Its fields
  `derived`, `counit`, `ordinaryIso`, `cohomology`, and `comparison` appear directly.
- Added existing statement dependency `lem-pc-affine-derived-base-change-comparison-map`:
  `RingTensorCohomology.exists_affineDerivedBaseChangeComparison` and
  `exists_affineDerivedBaseChangeLocalization` from
  `Sheaf.Algebra.Homology.AffineDerivedBaseChangeComparison`. These specify the
  comparison and the localization identities used to express the stalk hypothesis.
  This node was already a proof dependency; its statement is not duplicated.

Only modules needed to elaborate the module formulation are imported. In particular,
no otherwise unused scheme imports are added just to mention their affine interpretations.
The Grothendieck monoidal flat-resolution import supplies the tensor/coproduct instances
needed for the recorded K-flat predicate. The exact-functor import supplies restriction
on derived categories, and the AtPrime import supplies the localization in `hlocal`.

Edge cases checked: zero complexes give zero comparison maps and the usual identity
of zero objects. No primes when A' is the zero ring corresponds to the empty X';
all A'-modules and the target and source cohomology are then zero, so the empty
stalk condition is appropriate. Both directions of unboundedness are allowed;
cohomology degrees range over ℤ. Neither ring map is assumed flat, injective,
surjective, or Tor independent. No perfection, finite generation, noetherianity,
or properness is imposed. The condition includes every prime, not only closed
points. Ring and module universes are explicit and localization stays in the
ring universe; no smaller test universe can make the condition vacuous.

Searches:

- `msearch.py leanfinder`, query "For affine schemes a derived base change comparison
  is an isomorphism if all localized cohomology maps are isomorphisms": eight generic
  affine-local and base-change property hits, no complex criterion.
- `msearch.py loogle`, query `ModuleCat.extendScalars, IsIso`: no hits, unknown
  identifier `IsIso` reported by the service.
- `msearch.py leansearch`, query "derived module tensor base change comparison
  isomorphism detected by localization at primes": service unavailable (Internal
  Server Error); no mathematical verdict drawn from this failed search.
- `msearch.py grep`, query `extendScalars.*(restrict|[Bb]ase)|restrict.*extendScalars`
  under Mathlib `Algebra/Category/ModuleCat`: ten hits concerning scalar-change
  adjunctions, exactness and maps; no derived comparison criterion.
- `rg` in the source `WeilConjectures` for
  `single.*complex|stalk.*[Bb]ase|baseChange.*[Ss]talk|affine.*[Bb]ase`:
  unrelated single-complex and étale/affine base-change results, no match.
- `rg` of project `lean/Sheaf` with the same base-change patterns found the
  existing affine comparison and tensor localization infrastructure, not this criterion.
- Exact node-id search in the source library: no match. Exact proposed declaration
  name search in Mathlib, source, project modules and `dag/lean_names_upstream.json`:
  no match. No new definition or node is needed.

The theorem docstring carries all four proof steps from the node with their dependencies.
The node's mathematical statement and proof are unchanged. Only the Lean record and
three added existing statement dependencies are delivered.

## Second reading by T1

I independently read the item node and delivered signature, every statement dependency's
node and recorded declarations, and the existing model and comparison modules.
The local Stacks checkout is absent. I read the published [Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
and [Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9), and fetched `perfect.tex`
from the Stacks source into the sandbox scratchpad. In particular I read the introduction
of `section-cohomology-base-change`, `equation-bc`, all of
`lemma-single-complex-base-change-condition`, and the statement and affine reduction of
`lemma-single-complex-base-change`. The introduction assumes a commutative diagram,
quasi-coherent derived objects, and the given derived morphism. It does not assume
Noetherianity, flatness, or boundedness. The affine square is automatically qcqs where
0DJ9 requires it.

My object/hypothesis/conclusion checklist, matched to Lean:

1. Four affine schemes in a cartesian square, from ring maps R to A and R to R':
   `R A B : Type u`, their three `CommRing` instances and two `Algebra` instances
   render exactly these data, with `B = R'` and `A' = A ⊗[R] B`.
   General ring maps induce these algebra structures; no injectivity is imposed.
   Tensor-product presentation is the canonical affine fibre product, not a
   Tor-independent special case. Verdict: matches the node's module formulation.
2. K and K' in the quasi-coherent derived categories, corresponding to arbitrary
   complexes M and N: `M : CochainComplex (ModuleCat A) ℤ` and
   `N : CochainComplex (ModuleCat (A ⊗[R] B)) ℤ` render precisely the expressly
   permitted affine translation. Both complexes are unbounded. The recorded
   `schemeDerivedCategory`, `schemeDerivedQCohProperty`, and
   `schemeDerivedQCohCategory` use the derived category of sheaves of modules and
   quasi-coherent cohomology. Verdict: matches; no boundedness or coherence added.
3. The given arrow L(g')*K to K': `P`, `p : P ⟶ M`, `_hp : QuasiIso p`, and
   `_hP : (HomologicalComplex.quasiIso ...).kFlat P` specify an arbitrary
   representative resolution. `h : Q.obj (extendScalars ... P) ⟶ Q.obj N`
   is a morphism in D(A'), not necessarily a chain map. I opened
   `derivedPullback_tilde_iso`: its `M P s hs hP` binders give exactly this
   representative, for every K-flat resolution. The upstream `MorphismProperty.kFlat`
   preserves quasi-isomorphisms under tensor on both sides. Verdict: matches;
   existence of resolutions means no additional condition on M.
4. Canonical derived comparison and its A'-linear cohomology:
   `L : ModuleCat.BaseDerivedTensorCohomologyModel R A B P (A ⊗[R] B)`
   is a universally characterized model, not an arbitrary map. I read
   `universal`, `ordinaryIso_tmul`, `cohomologyIso`, `cohomologyIso_smul`, and
   `comparison_eq`. They fix derived extension, the ordinary associativity map,
   the canonical tensor-algebra action, and the comparison on cohomology.
   `nonempty_baseDerivedTensorCohomologyModel` supplies such data without flatness.
   Verdict: matches; model choice does not strengthen the mathematical hypotheses.
5. Each prime x' and its images x,s',s, and every integer i:
   `hlocal : ∀ (q' : PrimeSpectrum (A ⊗[R] B)) (i : ℤ), ...`
   includes all primes and degrees. Image primes are fixed by the two inclusions
   and their common R-map, not quantified independently. Verdict: matches.
6. The canonical stalk map is an isomorphism:
   `extendScalars (algebraMap ... (Localization.AtPrime q'.asIdeal))` applied to
   `L.comparison i ≫ homologyFunctorFactors.inv.app ... ≫
   (homologyFunctor ... i).map h ≫ homologyFunctorFactors.hom.app N`
   localizes the full canonical A'-linear composite. The factorization isomorphisms
   go from complex homology to derived homology before h, and back afterwards.
   I read both `exists_affineDerivedBaseChangeComparison` and
   `exists_affineDerivedBaseChangeLocalization`; the latter fixes the A'-action,
   both localization identities and their comparison square. The model's action
   and comparison have those same characterizations. Exact localization of the
   A'-complex N identifies the target with H^i(N at q'). Together these give
   precisely the node's tensor expression for the stalk source and its canonical
   arrow. Verdict: matches, with no arbitrary cohomology-map hypothesis.
7. Conclusion: the induced composite is an isomorphism in D(R'):
   `IsIso (L.counit.app ... ≫ quotientCompQhIso.hom.app ... ≫
   Q.map L.ordinaryIso.hom ≫ mapDerivedCategoryFactors.inv.app ... ≫
   (restrictScalars includeRight.toRingHom).mapDerivedCategory.map h)`.
   The source is derived extension of the restriction of P from R to B;
   the counit lands in ordinary extension of that restriction; ordinaryIso
   identifies this with the restriction of P extended from A to A'. The final
   exact restriction-of-scalars functor applies h. Thus the target is N restricted
   to B. The intermediate isomorphisms only align Q/Qh and exact restriction.
   I also opened `derivedPullback` (chosen total derived tensor pullback),
   `schemeDerivedDirectImage` (ringed-space derived pushforward), and
   `Scheme.Modules.moduleBaseChange` (tensor pullback along baseChangeMap).
   These agree with the affine tensor/restriction interpretations, and introduce
   no private competing notion. Verdict: the specified comparison is asserted
   invertible; no existential isomorphism or extra converse is substituted.

Edge cases: no index set or n occurs. Degree zero is included by `i : ℤ`.
Zero complexes and zero rings are permitted by the unrestricted `CommRing` binders.
If A' is zero, its prime spectrum is empty; both sides have zero cohomology,
including source cohomology with its unital A'-action, so the empty stalk condition
is correct. Empty affine schemes are therefore included. All characteristics are
allowed. Universes `u w` are explicitly bound; rings and module carriers can be
placed in a common larger universe, while `w` describes the chosen localization
categories. There is no independently smaller universe of test primes or algebras.
`HasDerivedCategory` supplies categorical constructions, not a finiteness assumption.

Independent searches used different phrasing from the worker:

- LeanFinder: "An unbounded derived tensor comparison is invertible when cohomology
  localizations at all prime ideals are invertible": eight hits, concerning Tor,
  localization at quasi-isomorphisms, and K-projective models. None states this
  ring tensor comparison criterion.
- LeanSearch: "Detect isomorphisms in derived categories of modules by localization
  of cohomology at prime ideals": service unavailable (Internal Server Error).
  This is recorded as a failed service, not evidence of absence.
- Mathlib grep: `isIso.*[Ll]ocaliz|[Ll]ocaliz.*isIso|[Bb]ijective.*[Ll]ocaliz`:
  hits include `bijective_of_localized_maximal` and localization equivalences.
  I opened `Mathlib/RingTheory/LocalProperties/Exactness.lean`: the maximal
  criterion concerns a single linear map, not this derived composite.
- Direct rg on `WeilConjectures` and project `lean/Sheaf` additionally searched
  `[Bb]ase[Cc]hange.*[Cc]ohom|[Cc]ohom.*[Bb]ase[Cc]hange`.
  I opened `ModuleCohomologyBaseChange.lean`: its map is ordinary tensor of
  homology to homology of ordinary tensor, a different notion. Other hits are
  étale/pro-étale comparisons or existing comparison infrastructure, not this
  criterion. Exact declaration/id searches in upstream Lean and its name index
  found no existing declaration of the item.

No new definition nodes or dependency modules are present in this delivery;
all added dependencies already exist on the base. No statement correction is
present, so there are no corrected-statement citer verdicts to audit. I found
no mathematical mismatch and changed no Lean or node data. The only change
is this independent second-reading report. The theorem retains its sole `sorry`
and no definition data or extra proved statement was introduced. Both docstrings
name the source and blueprint id; the theorem docstring includes all four proof
steps and their dependencies. No private notation, local instance, hidden let,
or unbound variable appears. The signature in `lean.statement` equals the text
from `theorem` up to `:=` verbatim. The prescribed single-file server compile
completed cleanly in 2.6 seconds with no warnings.
