## Worker report

Attach the exact existing theorem
`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isAdicStratifiedLisseSheaf_kernel_cokernel`
in `WeilConjectures.SixFunctors.ProEtale.Adic.Abelian`, lines 429–436.
The delivery changes only the item's `lean` field and supplies this report. There is no
new module, new definition, dependency repair, or statement correction.

The full signature, with the surrounding prime parameter made explicit for reading, is:

```lean
{l : ℕ} [Fact l.Prime] {Y : AlgebraicGeometry.Scheme.{u}}
[TopologicalSpace.NoetherianSpace Y]
{F G : AlgebraicGeometry.ProEtale.AdicSheaf l Y}
(hF : AlgebraicGeometry.ProEtale.IsAdicLisseSheaf F)
(hG : AlgebraicGeometry.ProEtale.IsAdicLisseSheaf G)
(φ : F ⟶ G) :
AlgebraicGeometry.ProEtale.IsAdicStratifiedLisseSheaf
  (CategoryTheory.Limits.kernel φ) ∧
AlgebraicGeometry.ProEtale.IsAdicStratifiedLisseSheaf
  (CategoryTheory.Limits.cokernel φ)
```

The node record contains the declaration's literal source signature, including its
local declaration name and line breaks, as required for an existing attachment.

Clause-by-clause reading:

- Prime and coefficient topology: the surrounding `{l : ℕ} [Fact l.Prime]`
  is the prime in the node. `PadicAlgCl l` is `AlgebraicClosure ℚ_[l]`
  (Mathlib.NumberTheory.Padics.Complex, lines 53–76). Its normed-field instance is
  the spectral norm extending the p-adic norm. The continuous-function type below
  uses precisely this norm topology, without discreteness or completion.
- Small pro-etale site: `AdicSheaf l Y` uses
  `Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)` in
  Adic.Module, lines 50–55. `Scheme.ProEt` is the recorded dependency declaration
  in Mathlib.AlgebraicGeometry.Sites.Proetale, lines 95–102: weakly etale schemes
  over the fixed scheme, with the induced pro-etale topology. The site and module
  universes are inherited unchanged; `Y : Scheme.{u}` has arbitrary explicit `u`.
- Functions and finite-dimensional locality: `PadicAlgCl.locallyFiniteFunctions`
  in Adic.ConstantSheaf, lines 74–80, is the subalgebra of
  `C(T, PadicAlgCl l)` with predicate
  `∀ x, ∃ U ∈ 𝓝 x, FiniteDimensional ℚ_[l] (Submodule.span ℚ_[l] (f '' U))`.
  Using a neighbourhood rather than an open neighbourhood is equivalent here:
  every neighbourhood contains an open neighbourhood, and shrinking preserves
  finite-dimensionality of the span. No global finite-dimensionality is assumed.
- Restrictions: `locallyFiniteFunctionsComp` (ConstantSheaf, lines 165–172) is
  precomposition. `adicFunctionsPresheaf` (lines 225–232) applies it to the underlying
  continuous map of each scheme morphism. `adicConstantSheaf` (lines 317–327)
  restricts this actual sheaf to the small site. Its section formula at lines
  329–335 is `ModuleCat.of _ (ULift (locallyFiniteFunctions l U.left))`.
  The universe lift changes no functions or operations.
- Category of modules: `AdicSheaf l Y` is `Mod` over `adicConstantSheaf l Y`, with
  its pointwise ring multiplication supplied by Adic.Ring. This is the native
  module-object presentation already recorded by
  `def-sf-native-weil-derived-framework`, rather than a newly invented sheaf
  category or an identification with another coefficient theory. An internal
  module over this sheaf of algebras is a sheaf with sectionwise module action;
  its arrows are action-compatible sheaf arrows. Thus this is the specified
  category of B_Y-modules. The general-site dependency `ringedSiteModules` is a
  transparent abbreviation for Mathlib `SheafOfModules`; the native framework's
  recorded `AdicSheaf` supplies the module-object presentation used here. No new
  equivalence or comparison theorem is assumed or introduced by this attachment.
- Lisse objects: `IsAdicLisseSheaf` in Adic.Constructible, lines 80–88, says
  `∃ R ∈ Scheme.proetalePrecoverage Y, ∀ f, R f → ∃ n : ℕ, Nonempty (...)`,
  where the isomorphism identifies `adicUpperStar l f` of the object with
  `⨁ fun _ : Fin n ↦ AdicSheaf.unit l V`. `AdicSheaf.unit` is the regular B_V-module
  (Adic.Module, lines 61–64). The existential rank is inside the quantification
  over covering arrows, so it may vary with the covering member and may be zero.
- Topological hypothesis: `[NoetherianSpace Y]` is the only scheme restriction.
  Mathlib.Topology.NoetherianSpace, lines 50–52 and 80–97, identifies its
  well-founded strict-superset relation on opens with the well-founded strict order on
  closed subsets, exactly the descending-chain condition in the node.
  There is no `IsLocallyNoetherian`, normality, reducedness, connectedness,
  constant rank, or nonemptiness assumption.
- Morphism: `{F G : AdicSheaf l Y}`, `hF`, `hG`, and `(φ : F ⟶ G)` render the
  two arbitrary lisse modules and arbitrary module morphism. Neither injectivity
  nor surjectivity is imposed.
- Kernel partition: the first conjunct is
  `IsAdicStratifiedLisseSheaf (kernel φ)`. Its definition (Adic.Constructible,
  lines 115–126) quantifies `ι : Type`, `[Finite ι]`, schemes `Z k`, and arrows
  `i k : Z k ⟶ Y`, with `∀ k, IsImmersion (i k)`, constructible images,
  `∀ x, ∃! k, x ∈ Set.range (i k).base`, and lisse pullbacks of the original
  kernel to every stratum. Finite indices in `Type 0` lose no finite family,
  since every finite index set can be relabelled by `Fin n`.
- Locally closed subschemes: Mathlib's `IsImmersion` extends `IsPreimmersion`
  and includes `isLocallyClosed_range` (Mathlib.AlgebraicGeometry.Morphisms.Immersion,
  lines 39–50); its images are locally closed in precisely the recorded
  `IsLocallyClosed` sense. It encodes subschemes rather than merely arbitrary
  locally closed topological subsets.
- Constructible subsets: the stratification explicitly uses
  `Topology.IsConstructible (Set.range (i k).base)`, the recorded declaration from
  Mathlib.Topology.Constructible, lines 173–179. It is the Boolean algebra
  generated by retrocompact opens, matching the dependency node's finite
  differences-of-retrocompact-opens formulation.
- Cokernel partition and independence: the second conjunct repeats the same
  existential stratified-lisse predicate for `cokernel φ`. Each conjunct has
  its own existential witnesses; equality of partitions is not required.
  Although the existing proof constructs a common refinement, the theorem's
  statement asserts exactly the two independent existences requested.

Dependency declarations read and used through the existing theorem's definitions:

- `def-weil-pbc-proetale-site`: Mathlib.AlgebraicGeometry.Sites.Proetale,
  `AlgebraicGeometry.Scheme.ProEt` and `Scheme.ProEt.topology`.
- `def-weil-sheaf-of-modules-category`: Sheaf.CategoryTheory.RingedSiteModules,
  `CategoryTheory.ringedSiteModules` (full abbreviation and docstring read), and
  its Mathlib match `SheafOfModules`; the native module-object presentation is
  the one explicitly recorded in the following framework dependency.
- `def-sf-native-weil-derived-framework`: the recorded public entry module is
  WeilConjectures.WeilSheaf.LowerShriek. Its declaration list explicitly records
  `ProEtale.AdicSheaf`, `ProEtale.adicConstantSheaf`,
  `PadicAlgCl.locallyFiniteFunctions`, `ProEtale.IsAdicLisseSheaf`, and
  `ProEtale.IsAdicStratifiedLisseSheaf`, with the signatures/docstrings and
  defining expressions read in Adic.Module, ConstantSheaf and Constructible.
  The equivariant and derived operations are not needed for the present
  unequivariant, underived assertion on Y itself.
- `def-weil-locally-closed-subset`: Mathlib.Topology.Defs.Basic,
  `IsLocallyClosed` (line 119), used by `IsImmersion`.
- `def-weil-constructible-subset`: Mathlib.Topology.Constructible,
  `Topology.IsConstructible` and `IsRetrocompact` (lines 178 and 52).

Edge cases checked against definitions and the existing proof:

- Empty scheme/closed support: the proof of
  `exists_stratification_kernel_cokernel` starts with `ι = Empty` when the
  closed support is empty. The finite partition definition accepts it.
- Zero rank: `n : ℕ` includes zero; the zero object is lisse by the empty direct
  sum (`IsAdicLisseSheaf.of_isZero`). Zero arrows and isomorphisms require no
  exceptions to the statement.
- Varying ranks and disconnected schemes: no common rank or connectedness
  is required by the lisse definition or theorem.
- Nonreduced or nonnormal schemes, including schemes with a Noetherian space
  but non-Noetherian local rings: the theorem asks solely for `NoetherianSpace`.
- A non-Noetherian profinite example is outside the explicit hypothesis;
  neither the theorem nor this attachment silently generalizes to it.
- The actual objects stratified are `kernel φ` and `cokernel φ`, restricted via
  native module inverse image; they are not substituted by arbitrary chosen
  modules or by kernels/cokernels in another coefficient category.

The existing proof was read at Abelian.lean:337–436. It follows the node's
proof: exact pullback identifies restrictions of kernel/cokernel; induction on
closed supports uses a closed subscheme and a nonempty generic open; its
proper closed complement is handled inductively; adjoining the open stratum
preserves finiteness, constructibility and unique membership. Taking the whole
closed subset and extracting the two conjuncts gives the recorded theorem.
This delivery adds no proof and makes no assertion that other native results
or other coefficient comparisons have been completed.

Searches actually run (2026-10-22):

- msearch LeanFinder, query “Kernels and cokernels of morphisms of lisse native
  adic sheaves have finite locally closed constructible lisse stratifications
  on a Noetherian topological scheme”: eight hits on Noetherian schemes,
  ordinary module sheaves and condensed modules; no Mathlib match.
- msearch Loogle, query `"IsAdicStratifiedLisseSheaf"`: zero hits.
- msearch grep, query
  `IsAdicLisseSheaf|IsAdicStratifiedLisseSheaf|locallyFiniteFunctions`: zero
  Mathlib hits.
- msearch LeanSearch, query “Kernels and cokernels of lisse adic sheaves admit
  finite constructible stratifications on Noetherian schemes”: eight hits,
  including ordinary module sheaves and scheme ideal kernels; no exact match.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for
  `isAdicStratifiedLisseSheaf_kernel_cokernel|exists_stratification_kernel_cokernel`
  finds the exact native Adic.Abelian theorem at 429 and its closed-support
  strengthening at 337. The analogous FieldCoefficient theorem is a different
  coefficient setup. No duplicate statement was found in `lean/Sheaf`.
- Direct grep by this node id in `lean/WeilConjectures` finds no annotation;
  direct rg of `dag/lean_names_upstream.json` finds no name entry. These
  negative index searches do not override the positive source-level match.
- Targeted source rg for `locallyFiniteFunctions`, `adicConstantSheaf`,
  `IsAdicLisseSheaf`, `IsAdicStratifiedLisseSheaf`, and `IsImmersion` located
  and allowed reading of their actual definitions, as described above.

No statement dispute or mathematical node fault was found.

Validation passed: a module-mode scratch probe imports the existing module and uses
`#check @...` plus `#print axioms ...`, compiled only through scompile.py.
The server printed the full expected signature; both the sandbox and published-library
checks succeeded (3.2 s and 4.0 s), without warnings. The axiom printout is exactly
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
The delivery wrapper additionally checks the attachment with its own server
probe and runs the maintainer's stage-2 preflight. The scratch probe is not
part of the delivery.

## Second reading by Q49

No second worker was started: the dispatcher brief explicitly forbids subagents
and directs the worker to deliver to the maintainer's independent review.
The clause-by-clause reading above compares the node, the theorem signature,
and the full coefficient/lisse/stratification definitions. It found no missing
hypothesis or strengthened conclusion; no statement was changed. In particular,
the two separate existential partitions and the topological-only Noetherian
hypothesis were rechecked. The maintainer supplies the independent reading.
