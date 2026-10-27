## Worker report

`Sheaf.CategoryTheory.PostnikovFiniteCutoffAbutment` states
`DerivedCategory.postnikov_finite_cutoff_abutment`. Its only theorem has proof
`sorry`. The helper abbreviations and canonical maps have real data. The node's
statement, dependencies, and proof are unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A and B have independent object/morphism universes and Abelian instances.
  `[HasDerivedCategory.{w} A]` gives the chosen localization size.
- `DerivedCategory.TStructure.t` is the standard t-structure.
  `postnikovLowerCategory A c` is the FULL category of all `L.IsGE c` objects;
  `DerivedCategory.isGE_iff` says exactly H^j(L)=0 for j<c. Quantification over
  this full category packages the pointwise result and naturality for every
  morphism between objects with the same lower bound.
- `[T.IsHomological]` includes additivity by Mathlib's existing instance.
  `postnikovValue T n` is literally `shiftFunctor _ n ⋙ T`, with canonical
  coherent shifts, not an arbitrary degree-indexed family. `hamp` is precisely
  the amplitude assumption for EVERY b, n, M.
- `X K` is the assumed exact couple already in translated coordinates
  `(P,Q)=(p+r,q)`. `d` and `e` identify its D and E objects with
  `T^(P+Q-r)(tau<=Q L)` and `T^(P+Q-r)(tau>=Q tau<=Q L)`.
  `truncGELT Q (Q+1)` is the canonical single-degree layer H^Q(L)[-Q],
  represented by its standard truncations. No arbitrary object is substituted.
  `ha`, `hg`, `hf` prescribe respectively next inclusion, quotient, and boundary
  of `triangleLTLTGELT Q (Q+1)`. The boundary helper uses the inverse of the
  coherent shift comparison `[1][P+Q-r]=[(P+2)+(Q-1)-r]`.
- Conclusion 1: `IsIso (postnikovCutoffMap T n m K.obj)` for ALL m>=n+r,
  including m=n+r. The next square gives naturality for every morphism u.
  These are isomorphisms in the arbitrary abelian target B; no complex or derived
  isomorphism is replaced by a mere degreewise cohomology assertion.
- The next clauses give actual-value vanishing for n<c-r, D-vanishing for Q<c,
  ALL-page vanishing for p<-r or q<c, finite support c<=q<=n+r, and stabilization
  for s+2>max(q-c+1,p+r). `pageCouple s` means page s+2, so s>=0 covers all
  pages >=2. The kernel/projection square specifies the canonical identification.
- `lim` gives limiting cycles/boundaries; `ab` gives the alpha diagonal colimits.
  `hAb` and the equation at zero normalize their objects to X.D(0,N), i.e.
  original D(-r,N). For N=n+r this is T^n(tau<=n+r L).
  `a` is its iso to T^(N-r)(L). Its equation for EVERY cocone component
  characterizes it by the actual inclusion into L, not an arbitrary iso.
- `IsComplete` and `ConvergesTo` retain the existing half-plane convergence
  convention, including regularity, abutting and inverse-limit completeness of
  the finite filtration. There is NO completeness hypothesis on D(A).
- `F` is the RECORDED `DecreasingFiltration`. `hF` is the displayed image formula
  for every integer p. The equality using `Subobject.exists` states explicitly
  that F is the transport of the half-plane image filtration along a, with
  total degree N=n+r and index P=p+r.
- `IsFinite`, `IsExhaustive`, `IsSeparated`, top for p<=-r, and bottom for
  p>=n-c+1 give all filtration assertions with both endpoints included.
- `g` identifies E_infinity(p,q) with gr^p F T^(p+q)(L). Its equation with
  `toPageInfinity`, the actual cutoff image epimorphism, and graded cokernel
  projection specifies the canonical comparison. The following clause identifies
  EVERY sufficiently late page with that SAME limiting-cycle quotient through
  its cycle projection. Together with the stabilization square, this gives
  coherence with successive page cohomology.
- The last clause quantifies over EVERY u. `f` is the alpha-colimit map;
  its cocone square uses the functorial truncation maps, and its square with a
  identifies its transport as exactly T^(N-r)(u). `lift` is restriction to each
  displayed image, characterized by the monic inclusion. `gr` is induced on
  successive cokernels, characterized by the cokernel-projection equation.
  `z` restricts the induced E2 map to limiting cycles; `tInf` is its induced
  quotient map. The last square intertwines tInf and gr through g. The initial
  maps are exactly those of the functorial truncation triangles, hence the
  morphism of couples induced by u.

Dependency declarations read (full signatures and documentation) and used:

- def-sp-abelian: Mathlib.CategoryTheory.Abelian.Basic, CategoryTheory.Abelian.
- def-weil-abstract-derived-category:
  Mathlib.Algebra.Homology.DerivedCategory.Basic, DerivedCategory and
  HasDerivedCategory, with its independent chosen morphism universe w.
- def-sbc-standard-tstructure-derived-category:
  Mathlib.Algebra.Homology.DerivedCategory.TStructure,
  DerivedCategory.TStructure.t, IsGE and isGE_iff. Mathlib's TruncLEGT and
  TruncLTGE provide truncLE, truncLEι, natTransTruncLEOfLE, truncGELT,
  triangleLTLTGELT, and its distinguishedness theorem.
- def-sp-homological-functor and lem-sp-long-exact-of-triangle:
  Mathlib.CategoryTheory.Triangulated.HomologicalFunctor,
  Functor.IsHomological, homologySequenceδ and homologySequence_exact₁/₂/₃;
  the helper writes the tautological shifted boundary directly.
- def-sp-exact-couple: WeilConjectures.CategoryTheory.ExactCouple,
  BigradedExactCouple, pageCouple, d and derivedEProjection.
- def-sp-convergence: WeilConjectures.CategoryTheory.ExactCoupleConvergence,
  LimitSubobjects, AlphaColimit, imageFiltration, pageInfinity,
  toPageInfinity, cycleBoundaryTower, limitBoundary_le_cycle and ConvergesTo.
- def-sp-filtration: WeilConjectures.CategoryTheory.Abelian.Filtration,
  DecreasingFiltration; its documented compatibility API is imported through
  WeilConjectures.CategoryTheory.CanonicalFiltration. The old PBC filtration is
  only used where it is already the return type of the convergence interface;
  the actual-value F uses the dependency's recorded DecreasingFiltration itself.
- thm-sp-half-plane-convergence:
  WeilConjectures.CategoryTheory.HalfPlaneConvergence, halfPlaneConvergence,
  read including its full signature and comparison equations, imported as a
  proof dependency.
- lem-sf-derived-truncation-triangle: Mathlib TruncLEGT,
  TStructure.triangleLEGE_distinguished (already publicly imported).
- lem-sp-couple-morphism: proof import of its recorded module
  Sheaf.CategoryTheory.ExactCoupleMorphism. Its local source has a withdrawn
  body, so this file states all needed naturality squares explicitly and does
  not claim to invoke an available theorem of that name.

Source reading: Stacks homology.tex,
lemma-spectral-sequence-associated-exact-couple (011T), derived.tex,
remark-truncation-distinguished-triangle (08J5), and both paragraphs of the
main-20261015 blueprint thm-sp-half-plane-convergence.proof.md.

Edge cases checked before writing: L=0; zero T; negative r and c; page two s=0;
p=-r and p=n-c+1; empty support n+r<c (actual value zero, top=bottom consistently);
a pure object H[-c]; T=H^r (cutoff n+r is sharp); any larger m; identity and zero
morphisms. No such case is excluded. No bounded-above assumption is introduced.

Searches (2026-10-23):

- msearch LeanFinder, "Postnikov spectral sequence finite truncation cutoff and
  canonical abutment image filtration for homological functor": eight complex
  truncation-map/functor hits, no theorem stating the item.
- msearch Loogle, `"SpectralSequence", "trunc"`: zero hits.
- msearch grep, `postnikov|Postnikov|halfPlane|abutment` in Algebra/Homology:
  zero hits.
- msearch LeanSearch, "Postnikov truncation finite cutoff homological functor
  abutment filtration": eight truncation-functor hits, no match.
- rg in lean/WeilConjectures and lean/Sheaf for
  `postnikov|Postnikov|finiteCutoff|finite_cutoff`: finite tower/propagation and
  pro-etale limit results, no abstract shifted-amplitude cutoff with actual
  abutment and canonical filtration.
- rg for exact item id in lean/WeilConjectures: none. rg of upstream name index
  and both source trees for proposed helper/main names: none.
- Read nearby BoundedAboveRHomHyperExt: specialized ringed-site RHom, not this
  abstract theorem. FinitePostnikovIsomorphism is finite propagation, not cutoff.

Validation: scompile.py compiled both sandbox and delivered module names cleanly,
with no errors or unexpected warnings. All variables and universes are explicit.
No STATEMENT-DISPUTED flag or statement correction is needed. No new or dependency
node is required; all helpers belong to the owning statement and are listed in
lean.declarations.

## Second reading by Q148

Self-check only: the dispatcher explicitly forbids spawning another worker, and
this assignment receives independent maintainer review. I reread the node beside
the final Lean signature. Integer-index cast errors were repaired with explicit
congrArg equalities. I checked P=p+r and N=n+r in every support, stabilization,
abutment and transport formula, checked m>=n+r including equality, and checked
both filtration endpoints. I added explicit late-page cycle-projection and
natural quotient-map squares so bare existence of an iso or filtration
preservation alone does not replace the canonical/coherent/naturality clauses.
The full-category packaging retains all objects and all morphisms with lower
bound c. All clause correspondences are recorded above; no node changes were
needed.
