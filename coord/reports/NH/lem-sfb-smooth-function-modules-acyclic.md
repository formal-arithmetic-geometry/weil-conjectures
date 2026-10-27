## Worker report

The module `Sheaf.Geometry.Manifold.SmoothFunctionModulesAcyclic` states
`SmoothDimensionStrata.paracompact_and_modules_acyclic`, with proof `sorry`.
It asserts both the topological conclusion and positive-degree vanishing for arbitrary
unital modules over the actual sheaf of smooth complex functions. The item's statement,
proof and proof dependencies are unchanged; its statement dependencies gain the new
smooth dimension-strata definition described below.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The space is `(N : Type u) [TopologicalSpace N]`; `u` is explicit and arbitrary.
- Hausdorff is `[T2Space N]` and second countable is `[SecondCountableTopology N]`.
- Smooth real, finite-dimensional, without boundary, with possibly varying component
  dimension, is `[D : SmoothDimensionStrata N]`. Its open disjoint covering `piece n`
  has `ChartedSpace (EuclideanSpace ℝ (Fin n)) (piece n)` and
  `IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ (piece n)`.
  This is presentation data for exactly the smooth manifold in the node: group all
  components of dimension n into the open dimension-n locus. Conversely, its charts
  are smooth charts on N since those loci are open; disjoint strata have no overlapping
  charts requiring an extra compatibility condition. Every connected component lies
  in one stratum. No global dimension bound, connectedness or compactness is imposed.
- The topological conclusion is the first conjunct `ParacompactSpace N`, Mathlib's
  open-cover/locally-finite-refinement predicate; it is not an input hypothesis.
- The ring sheaf E_N is `D.complexSheaf`. Its explicitly constructed presheaf has
  `obj U = RingCat.of (∀ n, C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
  D.openInPiece n U.unop; 𝓘(ℝ, ℂ), ℂ⟯)` and the existing Mathlib smooth restriction
  ring homomorphisms. These are real-smooth functions with complex values, not
  complex-analytic functions. The product describes the unique complex function on
  the disjoint cover of U. All ring operations are pointwise and unital.
- Every module F is the universal binder `(F : ringedSiteModules.{u} D.complexSheaf)`.
  This is transparently Mathlib's `SheafOfModules`, including the unital module law.
  There is no local-freeness, coherence, finite-generation or finite-rank hypothesis.
- Its underlying abelian sheaf is
  `((SheafOfModules.toSheaf D.complexSheaf).obj F)`; no module-derived functor is used.
- For every positive integer degree, the binders are `(r : ℕ), 0 < r → ...`.
  Positive integer degrees are exactly positive natural degrees in this cohomology.
- Vanishing is `Subsingleton (CategoryTheory.Sheaf.H' ... r (⊤ : Opens N))`.
  H' is the dependency's cohomology-over-an-object, at the whole space, in abelian
  sheaves. Its underlying additive group is trivial precisely when it is subsingleton.
  Standard sheaf Grothendieck and HasExt instances are inferred from imported Mathlib
  modules; there is no extra existential, derived-category choice or HasExt hypothesis.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`,
  transparently `SheafOfModules`; `SheafOfModules.toSheaf` is Mathlib's forgetful functor.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`; its record explicitly retains the
  Mathlib `Sheaf`, `Sheaf.H'`, and cohomology-presheaf interface for cohomology. We use
  the open-set Grothendieck topology and that unchanged cohomology interface.
- `def-sfb-smooth-real-manifold`: Mathlib `ChartedSpace` and `IsManifold`, with the exact
  boundaryless Euclidean real model specified by its mathlib_match; reused on each stratum.
- Proof imports: `Mathlib.Geometry.Manifold.PartitionOfUnity`, especially
  `exists_contMDiffMap_zero_one_nhds_of_isClosed`; the compactness/paracompactness
  Mathlib declarations `sigmaCompactSpace_of_locallyCompact_secondCountable`,
  `paracompact_of_locallyCompact_sigmaCompact`, `NormalSpace.of_paracompactSpace_r1Space`;
  `Sheaf.Topology.ClosedSectionNeighborhoodExtension`,
  `TopCat.Sheaf.exists_neighborhood_extension_of_isClosed`; and
  `Sheaf.Topology.SoftAbelianSheafAcyclic`, `TopCat.Sheaf.subsingleton_H'_top_of_soft`.
  Their full signatures and docstrings were read. The theorem docstring carries all
  five proof steps from the item, using dimension strata for the equivalent component
  assembly. Only the statement imports are public.

Edge cases checked: N may be empty (all strata empty, no Nonempty binder), dimension
zero is allowed (`n : ℕ` includes 0), empty dimension strata are allowed, disconnected
N may have unbounded dimensions, F may be the zero module or an arbitrary non-finite
module, and r=1 is included. The assertion deliberately makes no vanishing claim in
r=0. Closed-set cutoff cases including empty closed sets use the existing neighborhood
cutoff theorem; unitality is what identifies the section where the cutoff is one.
Nothing assumes compactness, a uniform dimension, or a bound on module ranks.

Searches made, with actual search tools:

- LeanFinder: “Every sheaf of modules over smooth complex valued functions on a manifold
  is acyclic for sheaf cohomology”: eight hits, all smooth sheaf constructions, no
  acyclicity result.
- Loogle: `"smoothSheafRing"`: one hit, the existing fixed-model construction; read its
  full signature and the surrounding source.
- Mathlib grep via msearch: `acyclic|cohomology` in Geometry/Manifold/Sheaf: zero hits.
- LeanSearch and LeanFinder varying-dimensional queries, Mathlib grep, project grep and
  blueprint searches are also recorded verbatim in the new node's mathlib_searches.
- `rg` of `smoothSheaf|ComponentwiseSmooth|variable.?dimension` in both
  `lean/WeilConjectures` and `lean/Sheaf`: no varying-dimensional smooth scalar sheaf.
  The related `AlgebraicGeometry.SmoothAnalytic.FunctionSheaf` was read; it is a
  holomorphic-function realization on an algebraic analytification, a different notion.
- Search of Mathlib's manifold algebra files for `ContMDiffRing` found only the
  same-base-field instance `instFieldContMDiffRing`. There is no ready instance for
  real-smooth complex multiplication. The named proof obligation is included below.
- Search for the item id in `lean/WeilConjectures` found no existing statement.

Source checked online: Demailly's agbook.pdf, printed pp.203–205, IV §4, the discussion
following (4.4), (4.8), (4.12), (4.15), (4.18), (4.19). The soft-module argument requires
only the smooth cutoff and unital module/sheaf laws, so it imposes no uniform dimension
or rank condition. No STATEMENT-DISPUTED flag or correction is needed.

Both delivered modules compiled separately, in dependency order, through `scompile.py`
against the published live library. There are no errors or unexpected warnings.

## New nodes

`def-sfb-smooth-dimension-strata` defines a smooth structure by its disjoint open
Euclidean dimension strata, reusing the existing fixed-dimensional manifold node,
and constructs its sheaf of smooth complex scalar functions. Source: Demailly I §1
and IV §4 Example (4.12), with the componentwise convention and assembly already
present in this item's statement and proof. Mathlib has only fixed-model smooth
sheaves. The blueprint search for “smooth manifold” returned zero blueprint nodes;
DAG search found the existing fixed-dimensional `def-sfb-smooth-real-manifold`, used
rather than copied. Project searches found no varying-dimensional real smooth notion.
Thus the added structure and product construction fill a missing notion without
redefining the underlying manifold, smooth-map or sheaf categories.

The new module's data is fully constructed. `complex_contMDiffRing` is a named
proof obligation that real complex addition/multiplication are smooth; its docstring
supplies the polynomial-coordinate proof. The definition node explicitly includes
this assertion. `complexPresheaf_isSheaf` is the named proof obligation for the
explicit presheaf's sheaf condition; its docstring gives the componentwise local-gluing
proof. The resulting `complexSheaf` uses this proof only; no data is chosen from an
existence theorem and no datum is sorry. The definition node records every declaration.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
