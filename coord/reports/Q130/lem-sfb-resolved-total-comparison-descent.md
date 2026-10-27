## Worker report

Module: `Sheaf.CategoryTheory.ResolvedTotalComparisonDescent`. Main statement:
`CategoryTheory.ResolvedTotal.resolved_total_comparison_descent`. The node's mathematical
statement and its accepted stage-1 split are unchanged. Every theorem is `by sorry`.
All other declarations have explicit construction data. `set_option autoImplicit false`
is enabled; all six universes and all variables are explicitly bound.

Hypothesis and clause correspondence:

- Grothendieck abelian A and B: independent `Type uA`, `Category.{vA}` and `Type uB`,
  `Category.{vB}`, `Abelian`, and `IsGrothendieckAbelian` instances. No equality of site,
  object, hom or derived-category universes is imposed. `HasDerivedCategory.{wA}` and
  `HasDerivedCategory.{wB}` are the recorded localization size convention.
- Left exact additive F: `F : A ⥤ B`, `[F.Additive]`, `[PreservesFiniteLimits F]`.
  Preservation of finite limits is the dependency's recorded left-exact convention.
  K-injective resolutions are inferred from Grothendieck abelianness, not assumed as an
  additional hypothesis.
- Delta, all its maps, and strict diagrams: Mathlib `SimplexCategory` and
  `CosimplicialObject (CochainComplex A ℕ)`. Naturality transformations are strict maps
  of the entire diagrams, including all degeneracies as well as cofaces.
- Nonnegative complexes: `CochainComplex A ℕ`, extended by zero using
  `ComplexShape.embeddingUpNat.extendFunctor` whenever passed to the ordinary unbounded
  `DerivedCategory`. `integerTotal` and `mappedIntegerTotal` perform this extension.
- Finite signed total T: `totalFunctor` is `alternatingCofaceMapComplex` followed by
  `HomologicalComplex₂.totalFunctor` with all three shapes `up ℕ`. Its outer differential
  is the alternating coface sum; its inner differential has sign `(-1)^n`. The published
  `hasTotal_up_nat` instance uses precisely the finite diagonal n+q=r. `mappedTotal`
  first postcomposes every column with `F.mapHomologicalComplex`, then uses that same T.
- u:K→J and v:L→M: `Replacement K` and `Replacement L` carry `diagram`,
  `augmentation`, columnwise `QuasiIso`, and `Injective ((diagram.obj n).X q)` for every
  n,q. These are exactly the two hypotheses on a replacement, with no mono condition,
  chosen injective resolution, extra boundedness hypothesis or arbitrary comparison.
- β: the existential natural isomorphism `β` is fixed by the first conjunct, on every
  finite-sum inclusion in degree n+q. This is summand preservation; its natural-isomorphism
  type already gives the finite-total naturality square. `extendComparison` uses the
  existing `mapExtendIso` and extends β by zero; it is real isomorphism data.
- RF,Q,ρ and χ: use the ordinary `F.rightDerivedFunctor` and `DerivedCategory.Q`.
  `derivedUnit` is the actual published unit, transported with `quotientCompQhIso`.
  The second conjunct says χ_u followed by Qβ_J inverse and that unit equals RF(QT(u)).
  Since the unit is invertible on the injective total, this is precisely
  χ_u=RF(QT(u)) ≫ ρ_T(J) ≫ Qβ_J in Lean composition order. Thus χ is fixed by its
  normalization, not an arbitrary isomorphism assumption or a choice from bare existence.
- Column c: the third conjunct gives the corresponding unit-normalized column comparison.
  `mapExtendIso` only identifies extension-by-zero with applying F, so the equation is
  c_u=RF(Qu) ≫ ρ_J with those canonical transports.
- Every strict square gu=vf: the fourth conjunct quantifies K,L,R,S,f,g and exactly
  `R.augmentation ≫ g = f ≫ S.augmentation`; its first equation is χ_u ≫ QT(Fg) =
  RF(QT(f)) ≫ χ_v. Its second equation, for every n, is the corresponding column square.
- Identities and composites: `resolvedMap` transports RF(QT(f)) by χ, and the fifth
  and sixth conjuncts assert its identity and composition laws. Together with the strict
  square these identify the actual mapped strict lift maps and their composites.
- Any functorial nonnegative injective resolution: `common_resolution_legs` quantifies
  arbitrary I,η,hη,hI with exactly componentwise quasi-isomorphisms and termwise injectivity
  for all complexes. It lists the four strict arrows η_J, I(u), I(w), η_N and asserts
  columnwise quasi-isomorphisms and `QuasiIso` of each mapped finite total. The augmentation
  squares are the definitional naturality squares of η; no arbitrary square is supplied.
- Induced four-leg isomorphism: `commonResolutionIso` takes `asIso` of Q applied to each
  actual mapped leg, reverses the second and fourth, and composes in the displayed order.
  The seventh conjunct says this very isomorphism is `(χ K R).symm ≪≫ χ K S`.
- Every augmentation-preserving finite zigzag: `AugmentedZigzag` has an identity case
  and forward/backward extension by a strict augmentation-preserving map. Every vertex
  is a `Replacement K`, so every intermediate augmentation is a columnwise quasi-isomorphism
  into nonnegative termwise injective columns. `mapped_leg_quasiIso` is exactly the node's
  assertion for any such leg. `legIso` uses that theorem and the existing extension
  quasi-isomorphism equivalence to invert Q of the actual mapped leg. `zigzagIso` evaluates
  those arrows recursively. The eighth conjunct identifies every path value with χ_wχ_u⁻¹.
  The empty path and arbitrary finite alternating orientations are included. Hence both
  I-independence and arbitrary-zigzag independence are asserted, not just a chosen path.
- Identity and cocycle for e: the ninth and tenth conjuncts explicitly give e_uu=1 and
  e_uw ≫ e_wz=e_uz for the normalized comparison.
- Compatibility with strict-square naturality: the final conjunct quantifies two source
  replacements, two target replacements and two strict lifts g,g' of the same f. Its
  equality is QT(Fg) ≫ e_vv' = e_uu' ≫ QT(Fg'), exactly the node's final clause.

The helper theorems `mapped_leg_quasiIso` and `common_resolution_legs` are respectively
step 5's arbitrary-leg clause and step 4's explicit-four-leg clause of this same node.
Both are listed in `lean.declarations` and have full natural-language proof docstrings.
There are no unnamed postponed proofs and no definitions that choose unspecified data.

Dependency declarations read and used:

- `def-sp-double-complex-total`: `WeilConjectures.CategoryTheory.DoubleComplexTotal`;
  Mathlib's `HomologicalComplex₂`, `HomologicalComplex₂.totalFunctor`, `ιTotal`, and
  the published natural-index `hasTotal_up_nat` instance from
  `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`. The filtration-specific recorded
  primary declaration is not needed by this node; the recorded shared total itself is used.
- `def-sp-grothendieck-abelian`: `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`,
  `CategoryTheory.IsGrothendieckAbelian` (including its exact-colimit and generator fields).
- `def-sp-injective-resolutions`: `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`,
  `CategoryTheory.Injective`; the source and signature of `InjectiveResolution` were read.
  Here the hypothesis is termwise injectivity of a resolution of a complex, not the
  narrower object-resolution bundle `InjectiveResolution Z`.
- `def-sp-left-exact-additive`: `Functor.Additive`, `PreservesFiniteLimits`, and the
  equivalence with preservation of kernels in `Mathlib.CategoryTheory.Preadditive.LeftExact`.
  The individual R^n functor is not substituted for the stipulated total derived functor.
- `sk-def-sfb-derived-categories`: imported its recorded
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`, and read the construction,
  unit, uniqueness and ObjIso declarations. As that record explicitly permits, on the
  Grothendieck categories here the ordinary upstream `F.rightDerivedFunctor` is used with
  its actual `rightDerivedFunctorUnit`, and `quotientCompQhIso` fixes its normalization.
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution` supplies the
  canonical resolution-existence instance; it must be public for these statement types.
- Proof dependency `def-weil-abstract-derived-category`: existing
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`, `Q`, and the
  cohomology factorization; these are already exposed by the statement imports.
- Proof dependency `lem-sfb-injective-finite-total-derived-comparison` has no Lean record
  or module in the current local DAG, and a live `scompile.py --source` check found no
  `Sheaf.CategoryTheory.InjectiveFiniteTotalDerivedComparison`. It is a proof-only
  dependency: there is therefore no module to import yet (stage 2 §3.7 says to import
  proof dependencies that are stated). No undefined object is taken from that theorem:
  the finite total is the existing Mathlib construction, and this node's β,χ,c are
  quantified with their full canonical characterizations in the main statement itself.
  My earlier progress update proposed a separate prerequisite module; inspection showed
  none was necessary to state this item. That separate module was not created.

Sources opened: Stacks `derived.tex` lemma-functorial-injective-resolutions and remark-match,
lemma-injective-acyclic, lemma-two-ss-complex-functor; the current blueprint
`latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3).
The main docstring carries all seven accepted proof steps, including inversion of unit
naturality, two-out-of-three for I(u), comparison on every leg, telescoping, and the final
strict-lift compatibility calculation.

Edge cases checked mathematically: zero F; identity F; zero diagrams; total degree zero
(the single (0,0) summand with positive sign); zero negative integer degrees after extension;
u=w; identity strict squares; composable strict squares; empty zigzag; single forward or
backward leg; arbitrary finite orientation pattern; equal choices of I and different choices
of I. The resolution functor is not required to be additive: only functorial with η and
injective quasi-isomorphic values, as in the node. No object-universe equality is forced.

Searches (2026-10-24; results saved by the prescribed search wrapper):

- LeanFinder: “Naturality and independence of injective replacements for total complexes
  of cosimplicial diagrams under a right derived functor”: eight hits, headed by
  `InjectiveResolution.toRightDerivedZero'_naturality` and object-resolution naturality.
  These are for individual object resolutions, not strict cosimplicial finite totals or
  augmented-zigzag descent.
- Loogle: `CategoryTheory.InjectiveResolution.iso_hom_naturality,
  HomologicalComplex₂.totalFunctor`: zero hits.
- Grep through Mathlib CategoryTheory: `(cosimplicial|total).*(resolution|Resolution).*(natur|compar)|
  [Rr]esolution.*zigzag`: zero hits.
- LeanSearch: “A common functorial injective resolution compares finite total complexes of
  cosimplicial nonnegative complexes naturally and independently of choices”: eight hits,
  `injectiveResolutions`, `injectiveResolution`, `InjectiveResolution.of`, `self`, etc.;
  none includes the total comparison or common augmented zigzag.
- `rg` through both `lean/WeilConjectures` and `lean/Sheaf` for resolved-total, finite-total,
  cosimplicial and comparison-descent names; read `CosimplicialInjectiveTotalReplacement`,
  `DerivedCechImageTotalization` and `CechInjectiveColumnModel`. The first gives existence
  and signed total comparison, the others concern specialized ringed-site Cech models;
  none states this abstract strict-square and arbitrary-zigzag descent result.
- `grep -rn lem-sfb-resolved-total-comparison-descent lean/WeilConjectures`: no hit.
  `tools/lean_names_upstream.py show lem-sfb-resolved-total-comparison-descent`: no matching
  statement. Existing map/total and extension compatibility constructions were read and
  reused instead of copied.

Validation: the prescribed `scompile.py Q130 lem-sfb-resolved-total-comparison-descent`
compiled both the sandbox probe and the actual module in 3.7s/3.6s, cleanly. The initial
compile repairs corrected the root namespace of `QuasiIso`, used explicit `ιTotal`, supplied
`quasiIso_extendMap_iff` when localizing extended mapped totals, and exposed the existing
Grothendieck resolution instance publicly. No statement correction or disputed clause.

## Second reading by Q130

The dispatcher explicitly prohibits starting another agent, and the brief assigns the
independent review to the maintainer. This section records my own second reading and does
not claim an independent worker read the file. With both the JSON statement and the module
open, I checked the correspondence above, including every conjunct of the main theorem.

The substantive point caught on rereading was that an additional explicit
`HasKInjectiveResolutions A` hypothesis would unnecessarily burden this Grothendieck
statement. I removed it and used the existing inferred Grothendieck instance. I also checked
that β has its finite-summand normalization, χ and c are tied to the actual derived unit,
backward arrows really are inverses of localized mapped legs, every intermediate vertex
has an augmented columnwise quasi-isomorphic injective replacement, and the final square
uses two lifts of the same f. All these requirements are now present. The three `sorry`
theorems are clauses of this very node with proof docstrings. The read-only project tree
was not edited; all writes were confined to the assigned sandbox and prescribed wrappers.
