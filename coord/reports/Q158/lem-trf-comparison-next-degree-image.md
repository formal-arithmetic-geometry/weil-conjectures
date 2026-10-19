## Worker report

The module `Sheaf.TraceFormula.ComparisonNextDegreeImage` states
`CategoryTheory.RefinedTopologyComparison.comparisonNextDegreeImage`, with its
whole proof `sorry`. The node statement is unchanged. Its two auxiliary
definitions construct actual maps; neither contains postponed data or a theorem.

Source read: `literature/stacks-project/sites-cohomology.tex`,
`section-compare-general`, `situation-compare`, and
`lemma-V-implies-cohomology-extra-general` (Tag 0EZC, including its full proof).
The source's proof uses only conditions (1)--(4), as the node states; condition
(5), which is used for the later induction, is not added here.

The hypothesis and conclusion correspondence is as follows.

| Node clause | Lean rendering |
| --- | --- |
| A category small in a universe containing sites and coefficients | `{C : Type u} [SmallCategory C]` and `AddCommGrpCat.{u}`, explicit `universe u` |
| Two sites and every coarser covering is finer | `τ τ' : Precoverage C`, `hτsite`, `hτ'site : IsSiteForCoverings`, and `hτ : τ' ≤ τ` |
| Slice objects, triangles, induced coverings | `Over X`, its Mathlib category, and `τ.toGrothendieck.over X` (respectively `τ'`) |
| Canonical comparison, identity direct image, finer sheafification inverse | The existing `sliceComparison τ τ' hτ X`, built from `comparison` and `comparisonDirect`, not a supplied geometric morphism |
| Relocalization along any arrow | The existing `relocalization τ'.toGrothendieck f`, whose inverse is `overMapPullback` and whose adjoint is the cocontinuous sheaf adjunction |
| Ordinary higher direct images | Mathlib `Functor.rightDerived`, computed on injective resolutions; existence is inferred for these Grothendieck abelian sheaf categories |
| Class of morphisms P | `P : ∀ ⦃X Y : C⦄, (X ⟶ Y) → Prop` |
| Full subcategories A'_X | `A' : ∀ X, Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat → Prop`, so morphisms are all sheaf morphisms between member objects |
| Contains zero | `hzero : ∀ X, A' X 0` |
| Closed under isomorphisms | `hiso`, with `Nonempty (H ≅ K)` |
| Kernels and cokernels of maps between members | Separate `hkernel` and `hcokernel`, not closure under arbitrary subobjects/quotients |
| Extensions | `hextension`, using a `ShortComplex`, `S.ShortExact`, and membership of the end terms |
| (1) Existence of base changes and stability of P | `hbaseChange` gives an object T, projections p,q, `IsPullback p q f g`, and `P q`; no global pullback hypothesis and no hidden let binder |
| (2) All relocalization inverse images preserve A' | `hrelocalization` for every X,Y,f and every member H |
| (3) Every A' object already satisfies the finer sheaf condition | `htauSheaf` is `Presheaf.IsSheaf (τ.toGrothendieck.over X) H.obj` |
| (4) All nonnegative higher direct images for P remain in A' | `hderivedImage`, quantifying over `i : ℕ` including zero |
| A_X is the essential image of A'_X under epsilon inverse | The existential H', `A' X H'`, and `Nonempty (H ≅ ...inverse.obj H')` in `hr` and `hH` |
| r ≥ 0 and V_r | `r : ℕ`; `hr` quantifies over every X,H in A_X and `1 ≤ i → i ≤ r → IsZero ...` |
| X and H in A_X | Final binders `X`, `H`, `hH` |
| The specified canonical cohomology pullback | `sliceComparisonCohomologyMap ... (r + 1) (Over.mk (𝟙 X))` |
| Injective | The first conjunct `Function.Injective` of that actual map |
| Its image is exactly the locally zero classes | For every ξ, existence of a preimage η iff a covering `Presieve.ofArrows U a ∈ τ' X` kills every restriction of ξ |
| Vanishing on each covering member | `(H.cohomologyPresheaf (r + 1)).map (Over.homMk (a i)).op ξ = 0` |
| Commutes with restriction in C/X | The final equality of composites for every `U V : Over X` and `f : U ⟶ V` |

The map `comparisonCohomologyMap J K h H n U` applies the exact inverse image
of the existing comparison adjunction to Ext classes. It then precomposes with
`presheafToSheaf J` applied to `toSheafify K` of the free abelian representable
on U and postcomposes with the comparison counit at H. Thus its source and target
are precisely the existing `Sheaf.H'` object cohomology groups. The generator
arrow is fixed by the sheafification unit, so this is the canonical pullback,
with the required coefficient counit, in all degrees. The construction is
choice-independent in the same sense as Mathlib's sheafification and Ext APIs.
`sliceComparisonCohomologyMap` specializes it to the recorded slice comparison.
The inverse is left exact by the geometric datum and preserves colimits as an
actual left adjoint; additivity follows from the existing additive direct image
and `Adjunction.left_adjoint_additive`. No extra exactness hypothesis is imposed.

Dependency declarations read and used:

- `def-weil-size-convention`: its convention record has no declaration; explicit
  universe polymorphism supplies it.
- `def-weil-pbc-sites-and-cohomology`:
  `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`; Mathlib `Sheaf.H'` and
  `Sheaf.cohomologyPresheaf` from `Sites.SheafCohomology.Basic` supply its
  cohomology component.
- `def-trf-geometric-morphism`:
  `Sheaf.CategoryTheory.Sites.GeometricMorphism`,
  `CategoryTheory.GeometricMorphism` with its functors, adjunction and finite-limit
  preservation. Its source and full signature were read.
- `def-weil-pbc-sheafification`:
  `Mathlib.CategoryTheory.Sites.Sheafification`,
  `CategoryTheory.presheafToSheaf`, `CategoryTheory.toSheafify`,
  `CategoryTheory.sheafificationAdjunction`, with their full signatures/docstrings.
- Existing helper declarations, recorded in the `lean.declarations` of
  `lem-trf-comparison-induction-step`: the existing
  `CategoryTheory.RefinedTopologyComparison.sliceComparison`, `comparison`,
  `comparisonDirect`, and `relocalization`, all read in full from
  `Sheaf.TraceFormula.ComparisonInductionStep`.

Available proof-dependency modules are imported without `public`: the
Grothendieck spectral-sequence, cocycle and bottom-resolution comparison
modules; the higher-direct-image and object-cohomology resolution modules;
ordinary site cohomology pullback; the existing total-complex and exact-couple
convergence modules; and the ringed-site Grothendieck theorem. The Mathlib
locally-bijective sheafification result is imported for that Mathlib dependency.
`sk-thm-groth-ss` has no recorded declaration, so no import can yet be added for it.
The seven-step proof in the theorem docstring retains the node's entire proof
plan, including identification of both canonical edges.

Import-cycle bookkeeping: the existing constructors live in
`ComparisonInductionStep`, together with the downstream theorem. This delivery
imports that module solely to reuse those definitions. The later reverse proof
import from `ComparisonInductionStep` to this module must be omitted under
`stages/2-statements.md` §3(7); otherwise it would form an import cycle. No
mathematical DAG cycle is added: the original statement dependencies stay
unchanged, and the induction theorem is not made a statement dependency. The
constructor declarations are already recorded on that node, so adding another
definition node would duplicate its interface record. The constructors are not
copied or replaced. The current induction theorem itself is never used.

Edge cases checked: r=0 gives an empty vanishing interval and degree-one
injectivity, exactly as in the filtration proof; empty covering families remain
allowed, with vacuous componentwise vanishing and the site's usual empty-cover
consequence; zero coefficients remain allowed; identity/arbitrary arrows and
all slice-object restrictions remain included; P and the member categories may
be empty apart from required zero objects; no all-pullbacks or nonempty-site
hypothesis was inserted. All positive and zero derived degrees in condition (4)
are retained. The weak Serre assumptions are not strengthened to a Serre
subcategory. No false-statement issue or statement correction was found.

Searches: `msearch.py` LeanFinder query "cohomology comparison finer topology
injective image locally zero classes" returned ordinary local-injectivity and
group-cohomology inflation results, not this statement; Loogle query
`Functor.mapExt, rightDerivedComp` returned no hits (unknown `Functor.mapExt`);
Mathlib grep `rightDerivedComp|mapExt` in CategoryTheory returned no hits.
Direct source grep found Mathlib `Functor.mapExtAddHom` in
`Algebra/Homology/DerivedCategory/Ext/Map.lean`, which is used. The required
upstream grep for this node id returned no hits. Searches for
`RefinedTopologyComparison|sliceComparison|comparisonNextDegree` in the
upstream name index, WeilConjectures sources and `lean/Sheaf` found only the
existing comparison constructors and the previously landed induction/vanishing
statements. Those statements do not assert the next-degree injection/image
criterion. Additional LeanSearch and LeanFinder queries for the canonical finer/coarser
comparison returned general sheafification and subpresheaf results; Mathlib grep
`sliceComparison|relocalization|comparisonDirect` in CategoryTheory/Sites returned
no hits. Direct grep of the upstream sources, project modules, and DAG found the
exact existing constructors in ComparisonInductionStep and their owning node
record. Thus no new definition or definition node is needed.
`tools/blueprint_refs.py search` was run for comparison and coarser topology;
the latter found no blueprint nodes. `ancestor` gives `lem-trf-local-term-locality`.

Validation uses only the prescribed `scompile.py` wrapper, including the real
map definitions and the entire theorem signature. The only postponed theorem
of this delivery is `comparisonNextDegreeImage`, with whole proof `sorry`.
All declarations bind their universe and variables explicitly; every Lean line
is within 100 characters. The initial delivery dry run passed. After removing the redundant proposed
definition record and storing the signature verbatim, the final packet is
checked again by the prescribed delivery wrapper before pushing.

## Second reading by Q158

This is the worker's self-check, not an independent second worker's review;
the dispatcher explicitly prohibits starting another agent and the maintainer
performs the independent review. Reopened the node and final Lean signature and
checked each row above against both. In particular: only conditions (1)--(4)
appear; the vanishing ranges and degree r+1 agree; the image statement is an iff
with an actual covering family; and the restriction equation covers every arrow
of the slice. The canonical map has real data from sheafification, exact Ext
transport and the counit. The existing induction node records precisely
the imported constructor declarations. A final metadata reading found all four
in its `lean.declarations`; removed the redundant proposed definition node and
restored the original statement-dependency list before the final dry run. Corrected an initial missing scoped zero-object
notation during compilation; no mathematical change was needed.
