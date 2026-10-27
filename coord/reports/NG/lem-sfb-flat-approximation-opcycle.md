## Worker report

The module `Sheaf.Algebra.Homology.FlatApproximationOpcycle` states
`SheafOfModules.isFlatOnSite_cokernel_of_bounded_flat_approximation` with its sole
proof `sorry`. It introduces no definitions. The source is Stacks Project
`literature/stacks-project/sites-cohomology.tex`, Tag 08G7,
`lemma-perfect-precise`, lines 12774–12815: the argument up to flatness of E', before
finite presentation is used. The six accepted DAG proof steps are included in the
theorem docstring, including the splice resolving the lower kernel and the actual
map from the spliced complex to the good truncation, rather than an invalid map
to P.

Clause-by-clause translation:

- A site small relative to its modules is `{C : Type u} [Category.{v} C]
  [EssentiallySmall.{r} C] (J : GrothendieckTopology C)`. The site object,
  morphism, and coefficient universes are independent. This implements
  `def-weil-size-convention`; no equality between these universes is imposed.
- Its sheaf of commutative rings is `(R : Sheaf J CommRingCat.{r})`.
- Its module category is the recorded `CategoryTheory.ringedSiteModules.{r}` of
  the underlying ring sheaf `(sheafCompose J (forget₂ CommRingCat RingCat)).obj R`.
  This is exactly Mathlib's `SheafOfModules`, not another module category.
- The existing `hasSheafify_coefficientUniverse` and
  `wEqualsLocallyBijective_coefficientUniverse` are enabled as local instance
  attributes. They follow from relative essential smallness, introduce no new
  data, and supply Mathlib's canonical abelian structure. There are no extra
  geometric or exactness assumptions.
- `[HasDerivedCategory.{w} ...]` selects the chosen localization with morphisms
  in the independent derived-category universe. `(K : DerivedCategory ...)`
  is the given unbounded derived object.
- `(a b : ℤ) (_hab : a ≤ b)` gives the integers and their order, including equality.
- `_hTor` quantifies over every module sheaf `N` in the coefficient/module
  universe and every integer `j`. `j < a ∨ b < j` is exactly `j ∉ [a,b]`.
  The conclusion is `IsZero ((DerivedCategory.homologyFunctor _ j).obj ...)`.
  Its argument is the published `siteDerivedTensorIndependentCoefficients J R`
  applied to `(K, (DerivedCategory.singleFunctor _ 0).obj N)`. This is the K-flat
  derived tensor with N in degree zero, not a hypothetical tensor functor or an
  ordinary tensor with a non-flat complex.
- `P : CochainComplex ... ℤ` is the actual complex of the same module sheaves.
- `_hbounded : ∃ l n : ℤ, ∀ j : ℤ, j < l ∨ n < j → IsZero (P.X j)` says its
  terms vanish outside some finite interval. It does not silently strengthen
  the upper bound to b or weaken boundedness to cohomological boundedness.
- `_hflat : ∀ j : ℤ, IsFlatOnSite (J := J) (R := R) (P.X j)` says precisely
  that tensoring with each term is exact, using the recorded flatness predicate.
- `_hzero : ∀ j : ℤ, j < a - 1 → IsZero (P.X j)` gives the required lower support.
- `f : DerivedCategory.Q.obj P ⟶ K` is a morphism in D(R), not a chain map.
- `_hf : ∀ j : ℤ, a ≤ j → IsIso ((DerivedCategory.homologyFunctor _ j).map f)`
  gives exactly the cohomology isomorphisms in degrees at least a, including a.
- The conclusion is `IsFlatOnSite ... (cokernel (P.d (a - 1) a))`: the literal
  cokernel sheaf of the specified differential. Mathlib's cokernel is taken in
  the abelian category of module sheaves. There is no claim of sectionwise
  surjectivity and no finite-generation, finite-presentation, local-freeness,
  or local-projectivity hypothesis or conclusion.

Dependency declarations used in the signature and public interface:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib's `SheafOfModules` with its morphisms and abelian instance.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`; its `homologyFunctorFactors` identifies the
  representative cohomology with ker(d)/im(d). The degree-zero derived embedding
  is `DerivedCategory.singleFunctor` from the publicly imported derived API.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`, and the public universe
  infrastructure `SheafOfModules.hasSheafify_coefficientUniverse` and
  `SheafOfModules.wEqualsLocallyBijective_coefficientUniverse`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, the
  recorded signed direct-sum totalization underlying the K-flat tensor.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`, `.X`, `.d`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`, exactness of the actual sheaf tensor functor.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `SheafOfModules.siteDerivedTensorIndependentCoefficients`, the previously
  recorded K-flat localization tensor, characterized by its resolving comparison
  and unique-extension property. Its owning landed node
  `lem-weil-pbc-site-derived-tensor-descent` is added to `stmt_deps`; no other
  dependency or statement is changed.

Every recorded proof-dependency module is imported with ordinary visibility:
`KFlatResolutionIndependentCoefficients`, `RingedKFlatSingleTensorComparison`,
upstream `TensorClosed` and `BoundedFlatReplacement`,
`TruncationsAndHomotopyColimits`, upstream `Triangulated.TStructure.Homology`,
Mathlib `DerivedCategory.TStructure` and `DerivedCategory.Plus`,
`BoundedFlatIndependentCoefficients`, and `SiteFlatOpcyclesTorCriterion`.
`def-weil-abstract-derived-category`, which is also a proof dependency, already
has its required public import. These imports retain the accepted stage-3 plan.

Edge cases checked before writing:

- a = b and arbitrary negative a are included; the Tor window can have length one.
- P = 0 is included (choose any coincident support bounds); the conclusion is the
  zero cokernel, which is flat. No Nonempty assumption on the site is needed.
- P^(a-1) = 0 is included, giving flatness of P^a as expected.
- The zero ring sheaf and the empty site are allowed.
- On the point site over Z, the two-term differential Z --2--> Z in degrees a-1,a
  has non-flat cokernel Z/2. Taking K to be Z/2 concentrated in degree a gives
  the required approximation cohomology isomorphisms, but tensoring K in the
  derived sense with Z/2 has nonzero cohomology in degree a-1. Thus this natural
  false-positive candidate fails precisely the Tor hypothesis. This checks that
  the derived Tor assumption is not lost or replaced by ordinary tensor of P.
- Non-finitely generated flat terms are allowed: no `Finite`, `Projective`, or
  free-presentation binder occurs. The lower kernel need not be flat; the
  docstring explicitly resolves it before using the universal tensor criterion.

Searches actually run:

- `msearch.py ... leanfinder "On a ringed site, a bounded flat complex approximating
  a derived object of Tor amplitude a to b in degrees at least a has flat cokernel
  of the differential into degree a"`: OK, 8 hits. The hits are bounded derived
  representative and fraction lemmas, e.g.
  `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`; none states this theorem.
- `msearch.py ... leansearch "Flat cokernel of bottom differential of a bounded
  complex of flat sheaves approximating a derived object with finite Tor
  amplitude"`: OK, 8 hits. Short-complex cokernel/homology constructions and
  ordinary-module tensor exactness, not this derived-approximation assertion.
- `msearch.py ... loogle '"flat", "opcycles"'`: OK, 0 hits.
- `msearch.py ... grep
  'flat.*(opcycles|approximation)|(opcycles|approximation).*flat'`: OK, 0 hits.
- `rg -n -i` with the same conceptual pattern and the literal item id in
  `lean/WeilConjectures` and `lean/Sheaf`: related results include
  `ObjectProperty.flat_opcycles_of_exactAt`, the site universal-tensor criterion,
  strict-perfect local shortening, and ordinary-module opcycle criteria. Their
  hypotheses are ordinary universal tensor exactness, a fixed-ring category,
  or strict-perfect/local data; none is this arbitrary-ringed-site theorem
  starting from a morphism to K in D(R).
- Searched `dag/lean_names_upstream.json` and both source trees for the proposed
  declaration and `flat_approximation`; no declaration with the proposed name or
  an exact existing statement was found. The literal node id has no prior Lean
  declaration. Read the recorded declarations and their docstrings, including
  the actual independent-universe tensor and flatness definitions.

No disputed statement, source correction, new definition node, or dependency
repair is needed.

Validation: `scompile.py NG lem-sfb-flat-approximation-opcycle` compiled this module
in sandbox mode (18.7 s) and its actual library module path (10.2 s), with no
errors or warnings. All lines are at most 100 characters, `autoImplicit` is false,
and the only declaration proof is `sorry`.

## Second reading by NG

The dispatcher brief assigns the independent review to the maintainer and
prohibits starting another agent. This section records the worker's second pass,
not a claim of an independent review. Reopened the node and final module and
checked the clause list above against the actual binders: independent site and
coefficient sizes; commutative R; D(R) and its cohomology; a ≤ b; all degree-zero
module tests outside [a,b]; bounded, termwise flat P; vanishing below a-1; the
single derived morphism f; cohomology isomorphisms including degree a; and
flatness of the exact specified cokernel. No mismatch was found. The explicit
boundedness hypothesis remains even though the proof only needs its upper bound.
The tensor's owning existing node was added to stmt_deps to make the signature's
canonical derived construction an explicit recorded dependency. No statement
correction or additional mathematical hypothesis was introduced.
