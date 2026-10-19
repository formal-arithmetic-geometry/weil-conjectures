## Worker report

The module `Sheaf.TraceFormula.ComparisonTruncatedCohomology` states
`CategoryTheory.RefinedTopologyComparison.comparisonTruncatedCohomology` with one
`sorry`. The natural-language statement, dependencies, and proof are unchanged.
The nine-step proof in its docstring follows the node and Stacks Project,
Cohomology on Sites, Tag 0EZB (`lemma-V-implies-cohomology-general`). I read
`section-compare-general`, including the definition of the comparison situation,
and the complete proof of 0EZB in `literature/stacks-project/sites-cohomology.tex`.
No statement correction or disputed mathematical assertion was needed.

The other declarations are concrete helpers for the very comparison being stated,
listed in `lean.declarations`. There is no choice of an unspecified comparison map
or natural isomorphism, and no postponed proof in a definition. All helper instances
use already available results or typeclass inference. No further theorem is stated.

Each hypothesis and clause is rendered as follows:

| Node clause | Lean rendering |
| --- | --- |
| Category small in the common universe of sites and coefficients | Explicit `universe u`, `{C : Type u} [SmallCategory C]`, coefficients `AddCommGrpCat.{u}`. The existing Grothendieck-abelian construction supplies the derived categories with morphisms in this common universe. No extra size-equality hypothesis or additional site limit hypothesis is imposed. |
| Two site structures | `τ τ' : Precoverage C`, with `hτsite : τ.IsSiteForCoverings` and `hτ'site : τ'.IsSiteForCoverings`; these are the recorded site axioms, including existence only of covering pullbacks. |
| Every coarser covering is finer | `hτ : τ' ≤ τ`, on actual covering presieves. Their associated sieve topologies are `τ.toGrothendieck`, `τ'.toGrothendieck`. |
| Slice objects, commutative triangles, and inherited coverings | Mathlib's `Over X` and `J.over X`, already used by `sliceComparison`. |
| Canonical comparison geometric morphism | The existing `sliceComparison τ τ' hτ X`, not an input datum. It is constructed in `Sheaf.TraceFormula.ComparisonInductionStep`. Its direct image is `ObjectProperty.ιOfLE` on unchanged presheaves; its inverse is `sheafToPresheaf ⋙ presheafToSheaf`; its adjunction restricts the usual sheafification adjunction. |
| Relocalization | Existing `relocalization τ'.toGrothendieck f`. Its inverse is `J.overMapPullback AddCommGrpCat f`, i.e. restriction through `Over.map f`; its direct image is the canonical right adjoint. |
| Ordinary right-derived higher direct images using injective resolutions | `.direct.rightDerived i` in `hderivedImage` and `hr`; these are Mathlib's injective-resolution derived functors indexed by `i : ℕ`. |
| Class of morphisms | `P : ∀ ⦃X Y : C⦄, (X ⟶ Y) → Prop`. |
| Full subcategories of coarser abelian sheaves | `A' : ∀ X, Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat → Prop`; an object predicate specifies the full subcategory without restricting its morphisms. |
| Contains zero | `hzero : ∀ X, A' X 0`. |
| Closed under isomorphisms | `hiso`, using `Nonempty (H ≅ K)` and implication from membership of `H` to membership of `K`. |
| Closed under kernels and cokernels between members | Separate `hkernel` and `hcokernel` bind arbitrary `f : H ⟶ K` and require both endpoint memberships. This does not impose the stronger Serre condition of arbitrary subobjects/quotients. |
| Closed under extensions | `hextension` for every `ShortComplex`, its `ShortExact` hypothesis, and memberships of `X₁`, `X₃` imply membership of `X₂`. |
| Assumption (1) | `hbaseChange`: for `f` with `P f` and arbitrary `g : Y' ⟶ Y`, there exist `T`, `p : T ⟶ X`, `q : T ⟶ Y'`, with `IsPullback p q f g ∧ P q`. This states both existence and membership of the base-changed arrow without a file-local instance or a `let` in the statement. |
| Assumption (2) | `hrelocalization`, for every arrow `f`, takes membership in `A' Y` to membership of the canonical relocalization inverse image in `A' X`. |
| Assumption (3) | `htauSheaf` requires `Presheaf.IsSheaf (τ.toGrothendieck.over X) H.obj` for every `A' X H`. It uses the same underlying presheaf of `H`. |
| Assumption (4) | `hderivedImage`, for every `P f`, every `H` in `A' X`, and all `i : ℕ` including zero, requires membership of `R^i f_* H` in `A' Y`. |
| Finer essential image `A_X` | Written directly in `hr` as existence of `H'` in `A' X` and `Nonempty (H ≅ (sliceComparison ...).inverse.obj H')`. Arbitrary isomorphic images, not only literal inverse-image objects, are included. |
| Nonnegative bound | `r : ℕ`. |
| `(V_r)` at every object and every essential-image sheaf | `hr`, quantified over `X`, `H`, its essential-image witness, and `i : ℕ` with `1 ≤ i` and `i ≤ r`, concludes `IsZero` of the ordinary `rightDerived i` object. |
| Bounded-below derived object | `L : DerivedCategory.Plus (Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u})`. |
| Vanishing in negative cohomological degrees | `hconnective : L.obj.IsGE 0`; by `DerivedCategory.isGE_iff` this is exactly vanishing of all `H^i(L)` for `i < 0` in the recorded standard t-structure. |
| Cohomology in `A'_X` for `0 ≤ i ≤ r` | `hcohomology`, indexed by every integer `i` satisfying those two bounds, uses `DerivedCategory.Plus.homologyFunctor` on `L`. No condition is imposed above `r`. |
| Hypercohomology by an injective resolution and sections | `sliceHypercohomology J X r` is `(sliceSections J X).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor AddCommGrpCat r`. `sliceSections` is the existing `sheafSections` at the terminal slice object `Over.mk (𝟙 X)`. Thus deriving it computes the cohomology of sections of a bounded-below injective resolution. |
| Canonical pullback via the derived unit and Leray identification | `sliceDerivedSectionsComparison` first applies derived coarser sections to `(sliceComparison ...).adj.derivedPlus.unit`, then composes with `Functor.rightDerivedFunctorPlusCompIso'`. The ordinary section-functor identity is literally `Iso.refl _`, because comparison direct image retains the presheaf. `sliceHypercohomologyComparison` applies the degree-`r` cohomology functor. |
| The displayed arrow is an isomorphism | The conclusion is `IsIso ((sliceHypercohomologyComparison τ τ' hτ X (r : ℤ)).app L)`. Its source and target unfold to exactly the two displayed hypercohomology groups, with the canonical termwise inverse image of `L` on the right. |
| Natural in `L` | `sliceHypercohomologyComparison` is a fixed `NatTrans`, assembled from existing natural transformations and functor associators. Its `naturality f` is the commuting square for every derived morphism `f`; restricting to the objects satisfying the theorem's conditions gives a natural isomorphism because the theorem asserts that each such component is invertible. Naturality is part of the actual map, not an existential choice or an unrelated isomorphism. |

Dependency declarations used in the statement and construction:

- `def-weil-size-convention`: metatheoretic universe convention, no Lean definiendum;
  rendered by the explicit universe and the existing Grothendieck abelian localization.
- `def-weil-pbc-sites-and-cohomology`:
  `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`; Mathlib `Sheaf`, `Over`,
  `GrothendieckTopology.over`, `Precoverage.toGrothendieck`.
- `def-trf-geometric-morphism`:
  `Sheaf.CategoryTheory.Sites.GeometricMorphism`,
  `CategoryTheory.GeometricMorphism` and its `inverse`, `direct`, `adj`, `leftExact`.
- `def-weil-pbc-sheafification`:
  `Mathlib.CategoryTheory.Sites.Sheafification`,
  `presheafToSheaf`, `sheafToPresheaf`, `sheafificationAdjunction`;
  these are used through the already constructed `sliceComparison`.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`;
  its `Plus` full subcategory and `Plus.homologyFunctor` are used here.
- `def-sbc-standard-tstructure-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.TStructure`,
  `DerivedCategory.TStructure.t`, `DerivedCategory.IsGE`, `DerivedCategory.isGE_iff`.
- Existing canonical comparison/relocalization API:
  `Sheaf.TraceFormula.ComparisonInductionStep`,
  `CategoryTheory.RefinedTopologyComparison.sliceComparison`, `relocalization`,
  `comparison`, `comparisonDirect`, `abelianSheafify`, `geometricDirectAdditive`.
  I read their full definitions, including the underived adjunctions.
- Derived unit:
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`,
  `CategoryTheory.Adjunction.derivedPlus`.
- Canonical Leray comparison:
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp`,
  `CategoryTheory.Functor.rightDerivedFunctorPlusCompIso'`, whose definition is
  normalized by the derived-functor units. Its hypothesis that direct image preserves
  injectives is supplied from the exact left adjoint by the existing theorem
  `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`.
- The chosen derived categories are supplied by
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory`,
  `HasDerivedCategory.ofIsGrothendieckAbelian`. No existence theorem is added.

The statement module imports the recorded proof interfaces for exact derived
functors, derived adjunction shifts, shift-compatible triangle morphisms, sheaves
in degree zero, shift identification, the truncation criterion, truncation
triangles, natural long exact sequences, the five lemma, and derived pushforward
composition. The full nine-step proof plan is in the theorem docstring.

Import-cycle note for the maintainer: the existing comparison and relocalization
helpers are declared together with the downstream theorem `comparisonInductionStep`.
This delivery must import that module to reuse those helpers. Under stage 2 rule 7,
do not add the reverse proof-only import of this module to
`Sheaf.TraceFormula.ComparisonInductionStep`: that particular proof import would
close a Lean import cycle. No DAG dependency is added to the induction theorem,
and the statement does not assume or use its conclusion. The induction theorem's
later proof will need the common helper layer extracted before that reverse import
can be enabled. This delivery does not duplicate or relocate the existing notions.

Edge cases checked before writing and again against the compiled signature:

- `r = 0`: `1 ≤ i ≤ r` is empty; the cohomology condition includes precisely degree
  zero; the actual degree-zero comparison is retained.
- Zero complex and zero coefficient sheaf are included. Weak Serre membership
  contains the actual zero and all its isomorphic copies.
- Equal topologies and identity relocalizations are included: `hτ` may be equality,
  and no properness, nonidentity, nonempty covering, or strict inequality is assumed.
- Empty categories and empty covers are permitted by the existing site axioms;
  the conclusion simply quantifies over a given `X`. No terminal object of `C`
  is assumed, since its slice has the canonical terminal object.
- Arbitrary higher cohomology of `L` above `r` is permitted. This is not restricted
  to complexes supported only in `[0,r]` or to termwise nonnegative complexes.
- Only pullbacks required by site axioms and assumption (1) are requested; there is
  no global `HasPullbacks C` assumption and no chosen pullback instance in the signature.
- Kernels/cokernels require both endpoint memberships, preserving the weak Serre
  condition. No arbitrary subobject closure has been added.
- Assumptions (1), (2), (4) remain explicit even though the proof of this implication
  uses only (3) and `(V_r)`. The fifth refinement assumption of the larger Stacks
  situation is neither in this node nor silently added to its Lean statement.
- Every variable and universe is explicit, with `autoImplicit false`; the theorem
  contains no `let`, `show ... from`, private definition, or local notation/instance.

Searches for an existing exact declaration and for duplicate helper names:

1. `msearch.py ... leanfinder` with
   `Vanishing higher comparison direct images gives hypercohomology comparison for connective complexes on two Grothendieck topologies`:
   eight hits, primarily continuous functors and hypercover preservation; no match.
2. `msearch.py ... loogle` with `"rightDerivedFunctorPlus", "unit"`:
   eight hits for general right-derived-functor units and their properties; no
   topology comparison under `(V_r)`.
3. `msearch.py ... grep` with `hypercohomology|WeakSerre|weakSerre`,
   restricted to `CategoryTheory`: zero hits.
4. `rg` over the upstream `WeilConjectures` source, side `lean/Sheaf`, and the
   upstream-name index for the item id and comparison/cohomology phrases:
   no exact declaration for this node. The related side comparison induction and
   refined vanishing modules supplied the canonical functors reused here.
5. More focused `rg` for `WeakSerre`, `weak Serre`, `section-compare-general`,
   `0EZ3`, and `0EZB` found the weak-Serre cohomology framework and the same comparison
   modules, not this finite-bound comparison theorem.
6. `rg` over Mathlib, upstream `WeilConjectures`, side `lean/Sheaf`, and
   `dag/lean_names_upstream.json` for `sliceSections`, `sliceHypercohomology`,
   `sliceDerivedSectionsComparison`, `comparisonTruncatedCohomology`: no prior names.
   `Mathlib.CategoryTheory.Sites.Sheaf.sheafSections` was read and used directly
   to implement the specialization to terminal slice objects.

Validation: all compilation was through the prescribed `scompile.py` wrapper,
with separate sandbox and final-module checks. The first pass identified a missing
instance exposing additivity of the specialized section functor. Adding that
instance by unfolding to the existing section functor resolved it. The complete
statement and concrete canonical map then compiled cleanly. No proof was attempted.
The delivery wrapper supplies the maintainer's independent review; no second agent
was started, as required by the dispatcher brief.

## Second reading by Q117

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
