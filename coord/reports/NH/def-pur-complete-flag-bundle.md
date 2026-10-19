## Worker report

The module `Sheaf.AlgebraicGeometry.CompleteFlagBundle` defines the complete flag bundle
by rank recursion, using the actual normalized symmetric-algebra projectivization and
the sheaf kernel of its degree-one quotient. Its main declaration is
`AlgebraicGeometry.completeFlagBundle`. All theorem proofs are `sorry`; all definitions
have complete data. The item's natural-language statement and dependency list are unchanged.

Clause-by-clause reading:

- A scheme T, natural rank r, and its finite locally free module F are the binders
  `(r : ℕ)`, `(T : Scheme.{u})`, `(F : T.Modules)`,
  `[F.IsFiniteLocallyFreeOfRank r]` in `completeFlagBundle`. The scheme universe is
  explicit and preserved by the recursion. No field, separatedness or Noetherian
  condition is imposed.
- Module pullback is `Scheme.Modules.tensorPullback` throughout. Composition uses
  `Scheme.Modules.tensorPullbackSectionComp`, in the direction from iterated pullback
  to pullback by the composite. Invertibility is `Scheme.Modules.IsInvertible`.
- The rank-zero and rank-one branches both use `completeFlagIdentity`: its scheme
  is T, its projection is the identity, its initial level is the zero sheaf, and
  all positive levels are the identity pullback of F. `completeFlagBundle_properties`
  asserts that the final inclusion at the actual rank is an isomorphism. Thus at
  rank zero the initial zero sheaf is also the full F, and at rank one F is the
  unique nonzero level. Equalities of sheaves in the prose are expressed by the
  canonical inclusions being isomorphisms, with the identity-pullback comparison
  identifying the ambient sheaf with F.
- At rank n+2, `completeFlagProjectivization T (n+1) F` is a
  `ProjectiveBundleRealization T F`. Its `A` is the symmetric graded algebra,
  with affine algebra equivalences, their grading and restriction equations;
  its scheme is `A.data.relProj`, its q is `A.data.relProjHom`, its L is `L`,
  and its epsilon is `quotient`. This is the dependency's prescribed degree-one
  quotient, not an arbitrary arrow into an arbitrary invertible sheaf.
- To ensure the representative is specified by a universal property,
  `exists_completeFlagProjectivization` asserts existence of that normalized
  realization WITH `IsCompleteFlagProjectivization`. The latter is precisely the
  quotient-line representing property: every invertible epi quotient of f*F
  induces a unique scheme map over T carrying the universal quotient to that
  quotient via a line isomorphism. The defining choice therefore postpones a
  universal-property proof and determines the object up to canonical isomorphism;
  it is not a choice from a bare existence assertion about unspecified data.
- The frame formula and overlap normalization are reused from the dependency:
  `ProjectiveBundleRealization.quotient_generator`,
  `TautologicalTwistData.restriction_generator`,
  `ProjectiveBundleFrameChart.coordinate`, `.generator` and `.transition`.
  `Scheme.SymmetricGradedAlgebraData.sectionEquiv_restriction` fixes the change of
  frame on degree-one symmetric generators. Thus epsilon sends v_i to the
  coordinate ratio times tau_j, tau_j=(X_j/X_k)tau_k on overlaps, and frame changes
  use the same linear substitution on the symmetric algebra.
- `completeFlagKernel` is literally `kernel D.quotient`. Kernels in sheaves of
  modules are sectionwise kernels; no arbitrary isomorphic sheaf is substituted.
  `completeFlagKernel_chart` states both the section sending tau_j to v_j and
  the basis v_i-(X_i/X_j)v_j, indexed by `{i // i ≠ j}`. The statement uses a
  basis v, a free generator tau and coefficients a satisfying the actual quotient
  formula; taking a_i=X_i/X_j gives every specified standard chart, with a_j=1.
  Its basis is on the actual kernel's sections, mapped by `kernel.ι` to the
  displayed vectors. The statement applies on each further chart open as well.
  `completeFlagKernel_pullback_locally_split` states that the actual quotient
  admits local sheaf-morphism sections after every scheme pullback, including
  the identity. `completeFlagKernel_rank` supplies rank n+1 for the next call
  at rank n+2.
- The higher-rank branch calls `completeFlagBundle (n+1)` on this kernel and
  passes the resulting G to `completeFlagExtend`. The resulting scheme is G.scheme,
  its h is G.projection, and p is literally h followed by q.
- `completeFlagExtend.level i` is G.level i for i<r and the full p*F otherwise.
  Its inclusion is G.inclusion followed by h*(kernel.ι epsilon) and the canonical
  pullback-composition comparison. This is the specified filtration, including
  the last kernel level F_(r-1)=h*K and the full final level F_r=p*F.
  `completeFlagBundle_mono` asserts that these are subsheaf embeddings.
- `completeFlagBundle_step_unique` supplies the uniquely determined factor from
  one level to the next. `completeFlagStep` chooses only this uniquely specified
  map; `completeFlagQuotient` is its categorical cokernel in sheaves of modules.
  Thus the earlier Q_i are exactly the recursive G_i/G_(i-1), since both their
  levels and their uniquely specified factor maps are the recursive ones.
  `completeFlagBundle_last_quotient` additionally identifies Q_r with h*L.
- `completeFlagBundle_properties` asserts the zero initial level, full final level,
  invertibility of every one of the r successive sheaf quotients, and local
  freeness of p*F/F_i for every 0≤i≤r. Its docstring explains the local adapted
  frames obtained from the chart splitting and the recursive adapted frame.
  Neither the data nor the statement requires a global splitting.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank` (through the public dependency imports).
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  the upstream `Scheme.Modules.tensorPullback` and the repaired section-normalized
  `Scheme.Modules.tensorPullbackSectionComp`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible` (through the projective geometry import).
- `Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry`:
  `ProjectiveBundleRealization`, its symmetric graded algebra and twist data,
  `ProjectiveBundleFrameChart`, `projectiveBundlePullbackCongr`, and the existence
  theorem used in the natural-language universal-property proof.
- Mathlib's sheaf Abelian category supplies the zero object, kernels and sheaf
  cokernels, with no extra assumptions.

The source was read at `literature/stacks-project/chow.tex`,
`lemma-splitting-principle` (Tag 02UL): it inducts using the short exact sequence
of the tautological quotient of a projective bundle. The choice of quotient-line
convention and the sign of O(1) agree with the recorded projective-bundle dependency.

Edge cases checked: rank zero uses T and the zero sheaf, never Proj of a zero
module; rank one uses T even for a nontrivial line bundle; the first recursive
case rank two has rank-one kernel; empty schemes satisfy the same local definitions;
there is no nonempty-chart or nonempty-base assumption. Invertibility is quantified
only over i<r, so rank zero has no fictitious line quotient. Indexing past r repeats
the full level and does not add a condition on the r-step filtration. The explicit
kernel chart lemma allows arbitrary rank, including its vacuous no-j rank-zero case.

Searches for existing constructions:

- msearch.py leanfinder: "Complete flag bundle of a finite locally free sheaf by
  iterated projective bundles of tautological kernels": eight hits, including
  `Module.Grassmannian`, absolute `AlgebraicGeometry.Proj`, and sheaf generators;
  no relative complete flag-bundle construction.
- msearch.py loogle: `"Flag", "Scheme"`: zero hits.
- msearch.py grep: `flag.*[Bb]undle|[Bb]undle.*flag|CompleteFlag|completeFlag|tautological.*kernel`:
  zero hits in Mathlib.
- msearch.py leansearch: "Complete flag scheme of a locally free sheaf with universal
  line bundle quotients": eight hits on sheaf modules and generators, no flag scheme.
- rg on the specified upstream WeilConjectures and project Sheaf directories for
  `flag.*[Bb]undle|[Bb]undle.*flag|complete.*[Ff]lag|CompleteFlag|tautological.*[Kk]ernel`:
  only the unrelated complete invariant vector-space flags in Triangularizable.lean.
  The exact node-id search in upstream returned no result.
- Exact new declaration-name search in Mathlib, upstream and project Sheaf returned
  no existing `completeFlagBundle`, `CompleteFlagBundleData`, or
  `IsCompleteFlagProjectivization`. The upstream name index also had no complete
  flag-bundle name. No missing independent notion or unusable dependency was found.

No statement correction and no disputed statement.

## Second reading by NH

The dispatcher explicitly requires this worker not to start other agents; no
independent worker reading is claimed here. The maintainer performs the independent
delivery review. The worker reread the node and module clause by clause as documented
above. This rereading added the quotient-line universal-property condition to avoid
choosing data from a bare Nonempty existence theorem; it also added the explicit
chart kernel basis and last-quotient statement. The zero-object notation requires
Mathlib's existing `ZeroObject` scope; this was repaired after compiler feedback.

Validation: the final module compiled cleanly through `scompile.py NH
 def-pur-complete-flag-bundle` in both its sandbox pass (15.0 s) and its library
confirmation pass (10.4 s), with no errors or warnings. All 18 declarations are
listed in `lean.declarations`; the item copy differs from the repository only
in `lean`. Every Lean line is at most 100 characters.
