## Worker report

The module `Sheaf.TraceFormula.ComparisonTruncatedDirectImages` states
`CategoryTheory.RefinedTopologyComparison.comparisonTruncatedDirectImages`.
It also supplies the canonical square and derived comparisons belonging to this
statement. Both the main theorem and the invertibility theorem used to form the
canonical direct-image square have `sorry` proofs. Every definition has real data.
There are no new nodes, dependency repairs, statement changes, or disputed statements.

Source read: `literature/stacks-project/sites-cohomology.tex`,
section-compare-general, equation-commutative-epsilon, situation-compare, and the
whole statement and proof of lemma-V-implies-C-general (Tag 0EZA). The canonical
adjoint is the one specified in the truncation paragraph of Tag 0EZE. The source
situation has a fifth covering-refinement assumption; the item's four-assumption
version is valid because the 0EZA argument never uses that fifth assumption. It
has consequently not been added to the Lean statement.

Hypothesis and clause correspondence:

- The category is `{C : Type u} [SmallCategory C]`; the ambient `u` contains the
  sites and coefficients. `AddCommGrpCat.{u}` supplies ordinary abelian sheaves.
  The chosen derived-category morphism universe is the explicitly bound `d`.
  The two `HasDerivedCategory.{d}` families are choices of localizations, as
  required by the size convention, and exist in a sufficiently large universe;
  they assert no additional geometric or coefficient property.
- The two site structures are `τ τ' : Precoverage C`, with
  `hτsite : τ.IsSiteForCoverings` and `hτ'site : τ'.IsSiteForCoverings`.
  `hτ : τ' ≤ τ` says every coarse covering is a fine covering.
- The slice objects and coverings are Mathlib's `Over X` and
  `τ.toGrothendieck.over X`. The latter topology detects covering sieves on the
  underlying object, so it is the slice topology specified in the node.
- `sliceComparison τ τ' hτ X` is the already published comparison geometric
  morphism. Its direct image is `ObjectProperty.ιOfLE` on the same presheaf;
  its inverse is `sheafToPresheaf` followed by `presheafToSheaf` for the finer
  topology. Its adjunction is restricted from `sheafificationAdjunction`.
- `relocalization τ'.toGrothendieck f` is the already published slice
  relocalization. Its inverse is `overMapPullback`, namely restriction along
  `Over.map f`; its direct image is the cocontinuous sheaf right adjoint.
- `P` is a predicate on arrows. `A' X` is a predicate on objects of the coarse
  abelian-sheaf category, defining a full subcategory without changing morphisms.
- The weak Serre condition is spelled out by `hzero`, `hiso`, `hkernel`,
  `hcokernel`, and `hextension`. The kernel and cokernel hypotheses apply only
  to arrows whose two endpoints are in the class, exactly as required. Extensions
  use `ShortComplex.ShortExact` and the first and third objects.
- Assumption (1) is `hbaseChange`: for every `f` in `P` and arbitrary `g`, it
  supplies `T,p,q` with `IsPullback p q f g` and `P q`. This states existence of
  the required fibre product and membership of its projection; it does not
  impose all pullbacks on the category or a particular choice of pullback.
- Assumption (2) is `hrelocalization`, for every arrow, without requiring `P`.
- Assumption (3) is `htauSheaf`: the underlying presheaf satisfies
  `Presheaf.IsSheaf (τ.toGrothendieck.over X)`.
- Assumption (4) is `hderivedImage`: for arrows in `P`, every `i : ℕ` right
  derived direct image belongs to the target class. `Functor.rightDerived`
  is the ordinary injective-resolution construction, not an arbitrary functor.
- Membership in `A_X` is the explicit existential over `H'` with `A' X H'`
  and `Nonempty (H ≅ (sliceComparison ... X).inverse.obj H')`. It appears
  identically in `hr` and `hH`, so membership includes all isomorphic objects.
- `r : ℕ` is the nonnegative bound. `hr` is exactly `(V_r)`: all objects `X`,
  all such `H`, and degrees `1 ≤ i ≤ r` have zero comparison higher direct
  image, expressed with categorical `IsZero`.
- The conclusion binds arbitrary `X,Y,f` with `hf : P f`, `H` with `hH`,
  and `i : ℕ` with `hi : i ≤ r`; nonnegativity of `i` is intrinsic.
  Its first conjunct is `IsIso` of the specified comparison. Its second is
  `IsIso` of the relative Leray left edge, also explicitly claimed by the node.

Canonical maps, not arbitrary isomorphisms:

- `relocalizationComparisonMate` is formed entirely from the coarse unit and
  fine counit, using the literal sectionwise restriction square. Its direction
  is fine direct image followed by comparison to comparison followed by coarse
  direct image. `isIso_relocalizationComparisonMate` states the commutativity
  clause of the item's square; its docstring explains localization and mates.
- `relocalizationComparisonIso` reverses that mate. Its inverse is uniquely
  determined by the mate and the invertibility theorem, so using that postponed
  proof does not make this definition hollow.
- `derivedRelocalizationComparisonIso` uses
  `rightDerivedFunctorPlusCompIso`, the derived natural isomorphism of this
  very square, and the composition isomorphism on the other side. These are
  normalized by the right-derived-functor units.
- `sheafDerivedAugmentation` is the derived-functor unit on the degree-zero
  single complex, transported by the existing single-complex identification.
  `derivedDirectImageComparison` is precisely `a_H`: apply the coarse derived
  direct image to that augmentation and then the canonical derived square.
- `adjointDerivedDirectImageComparison` is precisely `b_H`: the inverse
  hom-equivalence of `(sliceComparison ... Y).adj.derivedPlus` applied to `a_H`.
- `comparisonBottom` realizes degree `i` of the same augmentation and square
  with `grothendieckBottomEdgeMap` and `NatTrans.rightDerived` of the square.
  The published edge construction uses the same unit-normalized composition
  identification, not a chosen isomorphism of abutment objects.
  `comparisonLeft` is the published `grothendieckLeftEdgeMap` for the other
  factorization. `truncatedDirectImageComparison` is their composite, in that
  order, hence the node's `H^i(a_H)` followed by the relative Leray edge.
- The acyclicity arguments are applications of the existing
  `Functor.isAcyclicComposablePair_of_preservesInjectiveObjects`; preservation
  of injectives is derived from the geometric adjunction and left exactness.
  No comparison map, acyclicity assumption, or isomorphism is an input.

Dependency declarations inspected and used:

- `def-weil-size-convention`: metatheoretic convention; universes `u,v,w,d`
  are explicitly declared. No replacement definition is introduced.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`, read in full; its presieve
  site axioms are the two site hypotheses. Mathlib's existing `Sheaf`,
  `Precoverage.toGrothendieck`, and `GrothendieckTopology.over` give the categories.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`,
  `CategoryTheory.GeometricMorphism`, with its `inverse`, `direct`, `adj` and
  `leftExact` fields, read in full. The site-specific instances expose those
  stored structures to the existing derived-functor API.
- `Mathlib.CategoryTheory.Sites.Sheafification`,
  `CategoryTheory.presheafToSheaf`, `sheafificationAdjunction`, `toSheafify`:
  reused through the existing comparison construction, not redefined.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and
  `HasDerivedCategory`; `Mathlib.Algebra.Homology.DerivedCategory.TStructure`,
  `DerivedCategory.TStructure.t`: read the localization and standard
  t-structure signatures. The bounded-below categories and the Grothendieck
  edge constructions use this standard t-structure.
- `Sheaf.TraceFormula.ComparisonInductionStep`,
  `CategoryTheory.RefinedTopologyComparison.relocalization`, `comparisonDirect`,
  `comparison`, `sliceComparison`, `abelianSheafify`, and
  `geometricDirectAdditive`: their definitions were read in full and reused.
  The theorem `comparisonInductionStep` is not used.
- `WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck`,
  `Functor.grothendieckBottomEdgeMap`, `Functor.grothendieckLeftEdgeMap`,
  `Functor.IsAcyclicComposablePair`, and
  `Functor.isAcyclicComposablePair_of_preservesInjectiveObjects`:
  read their signatures and definitions, including the canonical composition
  identification `grothendieckSpectralObjectHBotTopIso`.
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves`,
  `Adjunction.preservesInjectiveObjects_of_preservesFiniteLimits`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp`,
  `Functor.rightDerivedFunctorPlusCompIso` and
  `Functor.rightDerivedFunctorPlusNatIso`; `...PlusAdjunction`,
  `Adjunction.derivedPlus`; `...PlusSingle` and the upstream right-derived
  single-complex identification. These supply the actual maps `a_H,b_H`.
- The existing proof-dependency modules for slice localization, ringed-topos
  derived composition, exact-functor homology, and spectral sequences are
  imported as the stage-3 plan. The main proof docstring follows all nine DAG
  proof steps, including the final transgression/sheafification argument.

Searches actually run (no exact existing statement found):

- `msearch.py ... leanfinder`, query: "Comparison of higher direct images for
  two topologies from vanishing of higher comparison direct images through
  degree r". Eight results: sheafification compatibility, locally injective
  restriction, and cocontinuity infrastructure; no truncated comparison theorem.
- `msearch.py ... loogle`, query: `"rightDerived", "Sheaf"`. Zero hits.
- `msearch.py ... grep`, query:
  `higherDirectImage|V_implies|compare.*cohomology`. One hit: the comment in
  Mathlib's `AlgebraicGeometry/Sites/ElladicCohomology.lean`; no match.
- `msearch.py ... leansearch`, query: "Higher direct image comparison between
  two topologies in a truncated vanishing range". Eight unrelated sheaf,
  scheme and complex results; no match.
- `rg` of the upstream source for the item id found nothing. Concept searches
  over the project's `lean/Sheaf`, `dag/nodes/sec-trace-formula`, and upstream
  found the already published slice functors in `ComparisonInductionStep`.
  Those constructions were reused. Searches of the selected new names over
  Mathlib, upstream, the side library, and `dag/lean_names_upstream.json`
  found no exact name collision (only unrelated `comparisonLeftAdjoint...`).

Edge cases checked against source and signature: `r=0` makes `hr` vacuous and
still concludes the degree-zero comparison; `r=1` retains the endpoint
transgression rather than assuming it zero; `i=r` is included. Empty categories
make the conclusion vacuous, without imposing nonemptiness; zero coefficients
and zero or empty coefficient subcategories are covered as permitted by hzero.
The identity arrow is not required to lie in P, but is included whenever it
does. No global finite-limit hypothesis is imposed on C. No stronger Serre
closure, finite coefficient condition, or covering-refinement condition is added.

Validation: required `scompile.py` compiled the file as a sandbox and at its
library module path, with no errors or warnings. The final delivery dry run is
recorded below after it completes.

## Second reading by Q160

This is the dispatcher's single worker's second pass, not an independent agent
review; the brief forbids starting another agent. I reopened the item statement,
the Stacks 0EZA argument, the imported functor definitions, and the final file.
All five weak Serre closure clauses have separate binders. Assumptions (1)-(4)
retain their quantifiers: in particular restriction is for every arrow, whereas
derived-image closure is only for P arrows and covers all nonnegative degrees.
The essential-image existential and the full interval of V_r agree in the two
places they occur. The output contains both the comparison and the Leray-edge
invertibility, not merely a Nonempty isomorphism. The derived adjoint uses the
specific a_H and derived adjunction. The chosen square is the counit mate,
not an arbitrary commuting-square isomorphism.

During this pass I replaced a chosen-`HasPullback` binder by an existential
`IsPullback` cone so the statement contains no local instance let; neither
version assumes all pullbacks. I also made the derived morphism universe `d`
explicit throughout. Compilation checked both changes.

The reuse of `ComparisonInductionStep` is deliberately limited to its canonical
functors and instances. This module is currently their published owner, even
though its theorem is downstream in the DAG. Adding a proof import of this new
module back into `ComparisonInductionStep` would close a Lean import cycle and
must be skipped under stages/2-statements.md §3(7). A later extraction of those
existing helper definitions into a shared owner would permit that proof import;
this delivery does not duplicate them or use the downstream theorem.

Final validation: `deliver2.py Q160 lem-trf-comparison-truncated-direct-images
--no-push` printed `OK (dry run): commit 7003c44bf9 passes the preflight and
compiles; nothing pushed`. An earlier attempt failed only because the server
refused an SSH multiplex session; the unchanged retry passed. The local record
check confirmed that only `lean` differs from the base node, its signature is
verbatim, every Lean line is within 100 columns, and the two named theorems have
exactly two `sorry` proofs.
