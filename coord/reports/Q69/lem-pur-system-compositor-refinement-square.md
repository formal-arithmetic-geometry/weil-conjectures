## Worker report

The module states the refinement square and every remaining clause of the unchanged
node. All postponed assertions have sorry proofs. All map definitions are concrete
composites of the existing geometric proper/open mates and normalized compositors.
There is no choice of an arbitrary comparison, no finite-level detection of equality,
and no normalization or Tor-amplitude assumption on the input system.

Hypotheses and clauses, with the node and source open:

- The finite field and algebraic closure are `D : FiniteFieldDatum.{u}`. The prime
  is `l` with `Fact l.Prime` and `hl : l ≠ D.p`. The finite coefficient extension
  is `E₀ : Type u`, `Field E₀`, `Algebra (Padic l) E₀`, and
  `FiniteDimensional (Padic l) E₀`. The existing `compactSupportSystemLevel` and
  `compactSupportSystemQuotient` are the lifted actual positive quotients and their
  quotient maps; index n means exponent n+1, so the first level is exponent one.
- X,Y,Z have the explicit `Over (Spec (.of D.k))`, `LocallyOfFiniteType`,
  `QuasiCompact`, and `IsSeparated` structure-map instances. The maps f,g have
  explicit `IsOver`, `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`.
  The ambient schemes of compactifications inherit the structure via their proper
  maps. The intermediate open V is proper over Y. Thus the ambient geometric
  assumptions require no extra hypotheses on chosen refinements.
- The actual category is `SemilinearProperOpen.Derived C τ X`, the ordinary
  unbounded derived category of module sheaves on the ringed sequence site.
  Its actual `P`, `R`, `adj`, `J`, `sComp`, `sId`, `jComp`, and `jCongr` are
  the simultaneous-section operations, retaining the quotient transitions.
- A triangle is the existing `Compactification.Triangle f g`. Its `cf.i`, `q`,
  `cg.i`, `cf.g`, `p`, `cg.g` are respectively j,b,i,q,p,s in the node.
  Its `cf.comm`, `cg.comm`, `i_q`, `p_g`, and `isPullback` give qj=f, si=g,
  bj=j_h, sp=r_h, and the specified Cartesian proper/open face. These extra
  names for composite arrows add no assumption: the node defines them by the
  same composites. `systemTriangleOpenQC` derives qc of b from that pullback;
  compactification opens are qc because their structure-map composites are qc.
- F,G,H are `systemCompactificationImage` at `T.cf`, `T.cg`, `T.cfg`.
  `systemTriangleBeta` is exactly the recorded `compatibleCompositorWord`,
  followed only by the two triangle equality transports. It is not another
  compositor or a lift chosen from its finite evaluations.
- A refinement is `SystemTriangleRefinement T₁ T₂`: `rf`, `rg`, `rh` are w,u,v.
  Their existing `i_hom` and `hom_g` fields give six endpoint equations; the
  two mixed fields `b_comm` and `p_comm` add vb₁=b₂w and p₂v=up₁.
  One composite equation is redundant as it is in the node's three induced
  compactification refinements. No refinement face is required Cartesian.
  The upstream `Triangle.Hom` would require extra Cartesian rf and rg faces,
  so it is deliberately not used as this node's quantifier.
- `systemRefinementGamma` is J₂ applied to the inverse normalized identity
  direct-image identification, followed by the existing intrinsic `gamma` for
  (j₁,id,u,j₂). `systemRefinementCompositor` is the canonical proper compositor
  with the equality r₁=r₂t. `systemRefinementTheta` is that compositor followed
  by R₂ of the inverse mate, precisely the displayed definition of theta.
  `systemRefinementGamma_isIso` states its bounded constructible invertibility.
- `compatibleCompositorDomain l E₀ X M` is used verbatim from the normalization
  dependency: every level separately has constructible homology and an interval
  of vanishing. `systemCompactificationImage_domain` supplies the corresponding
  domain of F₁M for theta_g. There is no new hypothesis on F₁M.
- `systemCompositorRefinementSquare` is the exact square. Lean composes left to
  right: beta₁ ≫ theta_h = theta_g ≫ G₂(theta_f) ≫ beta₂. Its domain is M and
  its codomain is H₂M in the actual derived system category.
- `systemCompatibleTriangles_common` quantifies `ι : Type v` with `Finite ι`,
  without `Nonempty ι`: it supplies a genuine compatible triangle and the exact
  refinements to every supplied triangle, including for the empty family.
- `systemSpanComparison` is theta_a inverse followed by theta_b.
  `systemSpanComparison_independent` quantifies both common objects and both
  pairs of arrows. `systemSpanComparison_trans` gives the three-span cocycle.
  These are system equalities before evaluation.
- `systemCompositorInChoices_exists` supplies a compatible triangle with proper
  refinements to arbitrary specified compactifications c,d,e of f,g,gf.
  `systemCompositorInChoices` conjugates beta_T using precisely these leg maps.
  Its `independent` theorem compares arbitrary triangles and all six legs.
  Since beta_T is the geometric word by the normalization dependency, this is
  its expression in exactly the specified choices, independent of refinement.
- `systemFiniteTransport` and `systemFiniteSource` reuse the recorded canonical
  evaluation transports and retain the same finite origin witness.
  `systemRefinementTheta_evaluation` pins its scalar ring to the actual quotient
  and its scalar map to the identity; it identifies evaluation with the inverse
  of the canonical finite etale refinement, through those transports.
  `systemCompositorInChoices_evaluation` similarly identifies evaluation with
  `coherenceEtaleCompositor w.Λ c d e`. This is the specified finite compositor
  of `thm-sf-comp-composition` in the chosen compactifications (the same spelling
  used in the normalization dependency). Evaluation of the main equality is then
  exactly the finite refinement/composition square, because it is a functor.

Dependency declarations read and used:

- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`, its
  projections and universal pullback encoding `IsPullback`.
- Mathlib.AlgebraicGeometry.Sites.Proetale: `Scheme.ProEt`, its weakly etale
  objects, `ProEt.topology`. Site object/morphism universes remain u+1/u.
- WeilConjectures.Compactification.RefinementCategory: `Compactification.Refinement`,
  its `hom`, `i_hom`, `hom_g`, automatic properness, identity and composition.
  WeilConjectures.Compactification.Triangle: `Triangle` and its full signature;
  its existing Hom was inspected and cannot encode arbitrary refinements here.
- Sheaf.Paper.FiniteFieldFiber: `WeilConjectures.FiniteFieldDatum`.
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite:
  `Padic.finite_coefficientExtensionRing`, the original quotient-ring constructions.
- Sheaf.Paper.ProEtaleFixedModuleConstructible:
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf`, used through the recorded domain.
- Sheaf.Paper.SemilinearDerivedSections: `SemilinearDerivedSectionsData`,
  `semilinearDerivedSections`, and `evaluation_mate`, the actual section calculus.
- Sheaf.SixFunctors.SemilinearProperOpenMatePasting: `Derived`, `P`, `R`, `J`,
  `adj`, `gamma`, `sComp`, `sId`, `jComp`, `jCongr`, `E`, and finite evaluation.
- Sheaf.Paper.SystemCompatibleCompositorNormalization:
  `compatibleCompositorWord`, `compatibleCompositorDomain`, `compositorLevel`,
  `compositorSupportTransport`, `compositorFiniteSource` and the normalization theorem.
- Sheaf.Paper.SystemCompactificationProjectionSubstitution:
  `refinementGamma`, `refinementCompositor`, `refinementTheta`, and refinement coherence
  were read in full. Their `TensorOperations l E` presentation has E : Type (u+1),
  whereas the compositor uses finite E₀ : Type u and the concrete geometric sequence
  presentation. The present helpers spell the identical canonical words on that
  existing compositor category; no arbitrary TensorOperations is assumed and no
  equality of independent universe levels is imposed. The original dependency is
  imported unchanged. These helpers are part of this node's specified comparisons.
- Sheaf.Paper.RefinementComparisonIsomorphism:
  `refinementComparisonIsomorphism`, `refinementComparisonAtWitness`,
  `properTransportRefinement`; inverse proper/open mate and compositor in that order.
- Sheaf.Paper.CanonicalOriginCompactSupportComposition: `originComposition`,
  `originCompositionAmbient`, and its canonical etale realization. The finite formula
  uses `coherenceEtaleCompositor` in the specified choices, as its normalization does.
- Sheaf.Paper.CompactSupportNativeSystemEvaluation: actual quotient `compactSupportSystemLevel`
  and `compactSupportSystemQuotient`; Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport:
  `StrictTower.ScalarEtaleOrigin`, `HD`, `originIso`; Sheaf.Paper.FiniteSiteTowerPaste:
  the existing finite etale coordinates. Their existing ownership nodes are added
  to stmt_deps. The semilinear operations, comparisons and gamma cite their three
  definition owners; the triangle and plain compositor definitions cite the two
  new existing-declaration owners described below.
- Proof-only imports: Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower,
  Sheaf.AlgebraicGeometry.SemilinearCompositorCoherence,
  Sheaf.Paper.FiniteCompactSupportConstructibility,
  Sheaf.AlgebraicGeometry.CompactificationCategory. The remaining proof imports are
  already public statement imports, including constructible-origin and composition.

Edge cases checked before writing: non-Cartesian refinement faces are allowed;
identity refinements and compactifications are included; empty open immersions are
allowed; zero systems and the empty scheme require no nonzero/nonempty hypothesis;
positive level one is n=0; there is no fixed cohomological interval in n; the finite
family can be empty and may have an independent index universe v. Every universe
and variable is explicitly bound; autoImplicit is false.

Searches actually run:

- msearch leanfinder, query `compatibility of compact support compositor with refinements
  of compatible compactification triangles`: eight hits about compactly supported
  continuous maps (comp_assoc, comp, compLeft, coe_comp_to_continuous_fun,
  coe_compLeft, HasCompactSupport.comp_left, compLeft_apply,
  toContinuousMap_compLeft). None states this derived-system assertion.
- msearch loogle, `CategoryTheory.mateEquiv_hcomp`: one exact generic mate-pasting
  theorem. This is a proof tool, not a compactification-system statement.
- msearch grep, `refinement.*compositor|compositor.*refinement`, CategoryTheory:
  zero hits.
- msearch leansearch, `compactification composition natural transformation compatible
  refinements`: eight general topological, site plus-construction, and category hits;
  no geometric compact-support system square.
- rg of lean/WeilConjectures and lean/Sheaf for the item ID and refinement/compositor
  variants: found finite comparison and coherence tools and the two recorded system
  dependencies, but no declaration of this node. All exact types were inspected.
- blueprint_refs.py search `compatible triangle refinement`: zero blueprint nodes.
  DAG and Lean search found upstream Triangle.Hom, whose Cartesian requirements
  would incorrectly strengthen this statement. The present small structure is a
  helper for this item's data, not a new independent mathematical notion.

Source read: literature/stacks-project/more-etale.tex, lemma-shriek-composition,
lines 3159--3370, especially the A--F calculation and common domination. Its
calculation is reproduced step by step in the main theorem docstring; remaining
assertions have the corresponding node proof Steps 1,5,6,7 in their docstrings.
The specified latest blueprint path was searched; this is an agent-created helper
whose own full statement is not a blueprint unit statement.

No statement correction or mathematical dispute. Compilation and the prescribed
delivery preflight are run on the live project server through the wrappers.


## Repair of returned delivery b2c83aa4bed8

H2 is repaired by removing the two statement dependencies added in the returned
delivery, lem-cbc-compactifiable-compatible-tower and
lem-sf-semilinear-proper-open-mate-pasting. Their conclusions are not used to state
this item. The latter is replaced by def-sp-semilinear-constant-ring-operations
(Derived/J/R), def-sf-semilinear-proper-open-comparisons (sComp/sId/jCongr), and
def-coef-semilinear-proper-open-mate (gamma). The former is replaced by the new
definition owner def-pur-compatible-compactification-triangle. The recommended
owner def-pur-system-compatible-compositor-words is also added.

Compared the retained returned sandbox with current main: only lean and stmt_deps
differ on the item. All original statement dependencies remain, including the
normalization theorem. The item's statement, proof and proof_deps remain verbatim.
The accepted Lean module is byte-identical to the retained returned version; its
SHA256 is 01d17fa7464ed802a4c0cfcc025e771b7b699ef0fb6adf77508bf34892fa487a.

## New nodes

- def-pur-compatible-compactification-triangle owns the unchanged upstream
  AlgebraicGeometry.Compactification.Triangle in
  WeilConjectures.Compactification.Triangle, line 54, with existing: true.
  Its three compactifications, open map, other map, two equalities and Cartesian
  face are exactly the structure's fields. This owner makes no existence or
  refinement-face assertion. Searched LeanSearch, LeanFinder, Mathlib grep,
  upstream/Sheaf sources, definition nodes and blueprint_refs; no definition
  node owns it. The full searches and returned results are in mathlib_searches.
- def-pur-system-compatible-compositor-words owns the ten unchanged plain
  definitions in Sheaf.Paper.SystemCompatibleCompositorNormalization: the five
  requested by the return plus the auxiliary level comparisons, support
  evaluation, finite target and bounded-constructibility predicate that specify
  them. The word is the actual gamma/sComp/jComp composite. The domain is
  levelwise, and the finite transports retain the supplied scalar map and origin
  identification. No normalization theorem conclusion is asserted by the owner.
  Searched LeanSearch, LeanFinder, Mathlib grep, upstream/Sheaf sources,
  definition nodes and blueprint_refs; found the existing definitions but no
  definition owner. The exact queries/results are in mathlib_searches.

Both new nodes reuse published declarations with existing: true and add no Lean
module or duplicate construction. The item cites both owners directly.

Validation: scompile.py compiled the delivered module against the live server
library successfully, with no diagnostics. The unchanged module retains all
previously reviewed edge cases and exact hypotheses.

The prescribed deliver2.py --no-push dry run returned OK at 22f1a43353f:
preflight and per-file compilation passed, including both existing-declaration
owner probes.

## Second reading by Q69

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
