## Worker report

Delivered module: `Sheaf.Paper.HomComparisonAffineInputs`, declaration
`AlgebraicGeometry.Etale.homComparisonAffineInputs`. This is one theorem, with its
entire proof `by sorry`; no definitions, instances or additional axioms are introduced.
The original node is changed only in `lean`. No new nodes, dependency repairs, or
statement correction are needed. No statement dispute was found.

Sources read: the current blueprint at
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/thm-sf-hom-comparison-constructible.proof.md`
(first two sentences), the complete assigned node and its five proof steps, and every
statement dependency's recorded interface and source declaration. The assigned node's
additional explicit clauses spell out the local reduction used by that blueprint proof.
The theorem docstring carries all five proof steps and their dependency ids.

In the descriptions below, A denotes exactly
`ULift.{u + 1} (Padic.coefficientExtensionRing l E n)`; F_i denotes exactly
`Etale.upperStar (ModuleCat.{u + 1} A) (j i)`. These are report abbreviations,
not new Lean definitions or file-local notation.

Hypotheses, matched individually:

- Global finite-field datum: `D : WeilConjectures.FiniteFieldDatum.{u}` gives p,
  q, the finite base field and its fixed algebraic closure `D.k`.
- Prime l different from p: `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`.
- Finite coefficient extension: `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. The existing coefficient extension ring uses
  its valuation ring and chosen uniformizer. There is no new choice of coefficients.
- Positive level: `(n : ℕ) (hn : 1 ≤ n)`. The existing theorem
  `Padic.finite_coefficientExtensionRing l E n hn`, transported by `Equiv.ulift`,
  supplies the actual Finite argument wherever constructibility requires it.
  No extra finiteness hypothesis is imposed.
- Finite-type k-scheme: `(X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of D.k))`
  with `[LocallyOfFiniteType f] [QuasiCompact f]`. There is no separatedness
  hypothesis on X and no affine-overlap hypothesis.
- K and M: both are `DerivedCategoryModule A X`; `_hK` and `_hM` use the exact
  recorded `DerivedCategory.isBoundedConstructible`, with the explicit derived
  Finite instance above. They are objects of the full D(X_et,A), with membership
  predicates rather than a different derived category.
- Integer cohomological intervals: `(r s t v : ℤ)` and `_hKr`, `_hMt`, respectively
  assert `IsZero ((DerivedCategory.homologyFunctor _ h).obj K)` when
  `h < r ∨ s < h`, and the corresponding assertion for M when `h < t ∨ v < h`.
  Lean v is the node's upper bound u, renamed to avoid the universe name.
- Tor interval: `(a b : ℤ) (_hab : a ≤ b)` and `_hTor` use exactly
  `DerivedCategory.hasTorAmplitudeIn A X a b K` from the etale flat-model convention.

Conclusions, matched individually:

- Global bounded flat model: the first conjunct gives
  `∃ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat A)) ℤ`,
  `IsBoundedFlatComplex A a b P`, and `Nonempty (K ≅ DerivedCategory.Q.obj P)`.
  The existing bounded-flat predicate states both termwise categorical flatness
  and vanishing of terms outside the exact original interval [a,b]. Its flatness
  is the shared `ObjectProperty.flat` interface exposed by the flat-sheaf dependency.
- Finite affine open cover: `∃ (m : ℕ) (U : Fin m → Scheme) (j : ∀ i, U i ⟶ X)`;
  all j_i satisfy `IsOpenImmersion`, and every x is `j i y` for some i and y.
  The chart conjunction asserts `IsAffine (U i)`, `IsSeparated (j i ≫ f)`,
  `LocallyOfFiniteType (j i ≫ f)` and `QuasiCompact (j i ≫ f)`.
- Empty X: `IsEmpty X → m = 0` explicitly permits choosing the empty cover.
- Exact restriction: K_i and M_i are the actual expressions
  `F_i.mapDerivedCategory.obj K` and `.obj M`. The ordinary functor F_i is the
  existing exact module-valued etale inverse image; on open immersions it is
  the canonical localization restriction, not an arbitrary functor.
- Constructible chart inputs: for each i the theorem asserts the same
  `isBoundedConstructible` predicate on K_i and M_i, their original degree
  vanishing intervals [r,s] and [t,v], and
  `hasTorAmplitudeIn A (U i) a b K_i`. Bounded constructibility together with
  this fixed ordered Tor interval is precisely membership in D^b_ctf plus the
  specified Tor bound; no finite-Tor hypothesis is required of M_i.
- Every chosen stratification: quantify over arbitrary `N = K ∨ N = M`,
  every h, and every `S : X.FiniteLocallyClosedStratification` whose strata
  are constructible and whose restrictions of H^h(N) are finite locally constant
  as A-module sheaves. The conclusion gives an R on U_i and an equivalence
  `Fin R.n ≃ {k : Fin S.n // Nonempty ↥(pullback (S.immersion k) (j i) : Scheme)}`.
  For every surviving k, R's domain equals the actual fibre product, its
  immersion is heterogeneously equal to `pullback.snd`, and its subset equals
  the preimage of the original subset. Thus this retains every nonempty
  intersection and deletes exactly the empty ones, retaining the stratum's
  scheme structure. R is again a finite locally closed partition, its subsets
  are constructible, and the restriction of H^h(F_i N) to every stratum is
  finite locally constant. HEq expresses only transport across the separately
  displayed equality of domains; it adds no change to the scheme maps.
- Finite locally constant here is the shared `Scheme.IsFiniteLocallyConstantSheaf`
  for `ModuleCat A`. For finite A,
  `Scheme.finite_locally_constant_module_values_iff` identifies this predicate
  with exactly the explicit locally constant datum with finite A-module values
  used in `IsConstructibleEtaleModuleSheaf`. This is module-linear finiteness,
  not just a statement about the underlying set sheaf.
- Every flat representative and every representing isomorphism: the last
  conjunct quantifies over *any* P with `IsBoundedFlatComplex A a b P`,
  *any* `e : K ≅ DerivedCategory.Q.obj P`, and every i. It gives an actual
  `eU : K_i ≅ DerivedCategory.Q.obj (F_i.mapHomologicalComplex (.up ℤ)).obj P`,
  the same bounded-flat property [a,b] for that restricted complex, and the
  equality `eU = F_i.mapDerivedCategory.mapIso e ≪≫
  F_i.mapDerivedCategoryFactors.app P`. This specifies the exact induced
  isomorphism from the source, rather than accepting an arbitrary local map.

Dependency interfaces used (recorded declarations, not replacements):

| DAG dependency | Module | Declaration |
| --- | --- | --- |
| def-weil-finite-field-fiber | Sheaf.Paper.FiniteFieldFiber | WeilConjectures.FiniteFieldDatum |
| def-weil-l-adic-coefficient-extension | Sheaf.NumberTheory.Padics.CoefficientExtensionFinite | Padic.finite_coefficientExtensionRing; inherited Padic.coefficientExtensionRing |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType | AlgebraicGeometry.LocallyOfFiniteType; AlgebraicGeometry.QuasiCompact |
| def-weil-open-immersion | Mathlib.AlgebraicGeometry.OpenImmersion | AlgebraicGeometry.IsOpenImmersion |
| def-weil-affine-spectrum | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Spec |
| def-weil-proper-morphism | Mathlib.AlgebraicGeometry.Morphisms.Proper | AlgebraicGeometry.IsSeparated |
| def-weil-pbc-constructible-complexes | WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes | AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible |
| lem-sf-flat-model | Sheaf.Paper.FiniteCoefficientFlatModel | AlgebraicGeometry.Etale.finiteCoefficient_hasTorAmplitude_iff_flatModel; inherited IsBoundedFlatComplex, DerivedCategory.hasTorAmplitudeIn |
| def-pc-cochain-complex-modules | Mathlib.Algebra.Homology.HomologicalComplex | CochainComplex |
| def-pc-flat-sheaf-modules | Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite | CategoryTheory.ObjectProperty.flat |
| def-pur-localized-ringed-site | Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous | SheafOfModules.overFunctor; used through the existing equivalent fixed-coefficient restriction, not a replacement |
| def-weil-abstract-derived-category | Mathlib.Algebra.Homology.DerivedCategory.Basic | DerivedCategory; DerivedCategory.Q |
| def-constructible-stratification | Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification | AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification |

All stated proof dependencies' recorded modules (or their mathlib_match files)
are imported. The exact derived factorization and exact upperStar are public
because their canonical constructions also occur in the signature. The other
proof-only dependencies are plain imports. In particular the literal canonical
local comparison is `CategoryTheory.Functor.mapDerivedCategoryFactors` from
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.

Edge cases checked before and after writing:

- Empty X: m=0, all chart and restriction clauses are vacuous; the global model
  remains asserted. No Inhabited or Nonempty instance is required anywhere.
- Empty original strata and empty intersections: the subtype of nonempty fibre
  products removes exactly these. Empty S and R are permitted over the empty scheme.
- Zero K or M and reversed cohomological intervals: the bounds are vanishing
  conditions; no unstated order r≤s or t≤v has been imposed. Singleton Tor intervals
  a=b are allowed. The given a≤b condition is preserved exactly.
- n=1 is allowed; n=0 and l=p are excluded exactly by the node's hypotheses.
- Nonseparated finite-type X is allowed; separatedness is asserted only for the charts.
- P may have nonconstructible flat terms: the final universal clause does not add
  termwise constructibility, nor does it replace P by a newly chosen model.
- Two different representing isomorphisms give their respective induced eU;
  the quantifier over e occurs before the existential eU.
- Universe u is explicitly declared and all binders are explicit, with
  `set_option autoImplicit false`. ULift is the canonical coefficient size
  transport already used by the recorded etale flat-model interface.

Searches performed, with tool output summarized:

1. msearch.py leanfinder: `finite affine open cover restriction bounded constructible
   etale complex finite Tor amplitude bounded flat model`. Eight hits, including
   Scheme.affineCover, OpenCover.affineRefinement and the affine finite-subcover
   instance. None states the assigned combination of input, stratification and
   universal flat-model conclusions.
2. msearch.py loogle: `Scheme.OpenCover, IsAffine, Functor.mapDerivedCategoryFactors`.
   No hits (unknown identifier Scheme.OpenCover). Retried with the fully qualified
   `CategoryTheory.Functor.mapDerivedCategoryFactors`: twelve hits, with the exact
   derived localization comparison in Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor.
3. msearch.py grep: `finite.*[Aa]ffine|mapDerivedCategoryFactors`, subdirectory
   AlgebraicGeometry. Twenty-five hits, including finite affine-cover and
   finite-type APIs; no complete matching declaration.
4. msearch.py leansearch: `A finite type scheme over a field admits a finite affine
   open cover`. Eight hits including Scheme.affineCover, Scheme.affineOpenCover,
   Scheme.AffineOpenCover and isLocallyNoetherian_of_affine_cover. These supply
   geometric ingredients, not the complete assigned statement.
5. rg on lean/WeilConjectures and lean/Sheaf: searched
   `hom.comparison.affine|homComparisonAffine|AffineInputs`, the node id,
   `HasTorAmplitude|hasTorAmplitude|upperStar|pullback|flat` in relevant modules,
   `FiniteLocallyClosedStratification`, `LocallyConstantDatum`, and finite-value
   module predicates. Found the recorded flat-model, bounded constructibility,
   exact inverse-image and stratification APIs used above; no duplicate theorem.
   Explicit `rg` of the node id under WeilConjectures found no declaration.
6. rg on Mathlib and both project roots for
   `homComparisonAffineInputs|hom_comparison_affine_inputs` and inspection of
   dag/lean_names_upstream.json found no existing declaration under that name.

Validation: scompile.py NI lem-sf-hom-comparison-affine-inputs compiled the final
module in sandbox and library forms against the server publication (7.0 s and
9.6 s). No compiler error or unexpected warning. One initial elaboration repair
made the type of the pullback in the nonempty-strata subtype explicitly Scheme,
so Lean cannot infer a pullback in Type. No hypothesis or conclusion changed.

## Second reading by NI

This is a separate self-check of the node and final module after the successful
compile, not a claim of an independent agent review. The dispatcher explicitly
prohibits starting another agent; the maintainer performs the independent review.

Re-read the original hypotheses against the actual theorem binders: the fixed
finite-field and coefficient extension, l≠p, positive n, finite type without
separatedness, both bounded-constructible inputs, both cohomological intervals,
and the ordered Tor interval all occur exactly as listed above. Re-read each
conclusion: the finite cover includes the empty-X choice; chart separation and
finite type are asserted for the composite to Spec k; restricted K and M retain
the original bounds; arbitrary stratifications retain their nonempty actual
fibre products; arbitrary P and e yield the exact displayed induced eU. In
particular the eU equality was checked against the orientation of
mapDerivedCategoryFactors, and the quantifier order retains different choices
of e. No mathematical mismatch was found. The only correction was the explicit
Scheme type annotation described above. The finite-locally-constant API was
checked against finite_locally_constant_module_values_iff, and its name in the
module documentation was corrected to that actual declaration.
