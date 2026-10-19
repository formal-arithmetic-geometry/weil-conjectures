## Worker report

The module `Sheaf.AlgebraicTopology.SimplicialSet.MinimalQuasicategoryRetract` states
`SSet.Enhanced.exists_minimal_deformation_retract`. Its only declaration is a theorem,
with proof `sorry`; it introduces no definitions or additional nodes. The node's
statement and all dependency lists are unchanged.

Source checked: Lurie, *Higher Topos Theory*, Definition the project server, the terminology
immediately before it, and Proposition the project server with its proof, printed pp. 101--105.
The official PDF was downloaded from https://www.math.ias.edu/~lurie/papers/HTT.pdf
and these pages read using `pdftotext`. The proposition applied to `C → *` gives
exactly the minimal subset, strict retraction and relative equivalence asserted here.

Clause-by-clause correspondence:

- Universes and arbitrary smallness: explicit `universe u` and `(C : SSet.{u})`
  allow any chosen ambient universe U'. No small mapping spaces, presentability,
  compact objects, or distinguished object of C are assumed. The smaller universe U
  is not used by this assertion and needs no extra Lean parameter.
- Quasicategory hypothesis: `[Quasicategory C]` is Mathlib's inner-horn-filling
  condition, as specified by `def-cbc-enhanced-diagrams-cones`.
- Standard simplices and boundaries: `Δ[n]`, `∂Δ[n]`, and `∂Δ[n].ι` are Mathlib's
  standard simplex, its subcomplex of nonsurjective ordinal maps, and its inclusion.
  `boundary_eq_iSup` identifies it with the union of the proper faces, and
  `boundary_zero` identifies the degree-zero boundary with the empty subcomplex.
- The subset and inclusion: existential `M : C.Subcomplex` and its actual `M.ι`
  give a degreewise simplicial subset and its canonical inclusion, rather than an
  arbitrary monomorphism or an unrelated equivalent quasicategory.
- It is a quasicategory: `Quasicategory M.toSSet`.
- Minimality covers `∀ (n : ℕ) (f g : Δ[n] ⟶ M.toSSet)` with no positive-dimension
  restriction. The equation `∂Δ[n].ι ≫ f = ∂Δ[n].ι ≫ g` expresses a common boundary b.
- The relative homotopy is the existential simplicial map
  `H : Δ[n] ⊗ Δ[1] ⟶ M.toSSet`. The product is Mathlib's degreewise product.
  `ι₀ ≫ H = f` and `ι₁ ≫ H = g` are its two endpoint equations.
- Boundary constancy is the map equation
  `(∂Δ[n].ι ▷ Δ[1]) ≫ H = fst _ _ ≫ ∂Δ[n].ι ≫ f`.
  Its right side is precisely b after projection off the interval.
- For each vertex `v : Fin (n + 1)`, the pair consisting of the degenerate
  one-simplex on v and the identity one-simplex of `Δ[1]` is the edge of the product
  tracing that vertex through the interval. Applying `H.app (op ⦋1⦌)` and requiring
  `IsEquivalenceEdge M.toSSet` imposes exactly the specified equivalence-track
  condition, using the dependency's inverse-triangle definition. The conclusion
  of this implication is `f = g`.
- The retraction is existential `r : C ⟶ M.toSSet`; its strict retraction equation is
  `M.ι ≫ r = 𝟙 M.toSSet`, i.e. r after inclusion is the identity on M.
- The coherent natural equivalence is the existential one-simplex
  `e : ((ihom C).obj C) _⦋1⦌`. Its face-one and face-zero equations identify its
  source with `diagramVertex (𝟙 C)` and target with `diagramVertex (r ≫ M.ι)`.
  `IsEquivalenceEdge ((ihom C).obj C) e` imposes the actual inverse-triangle
  witnesses in the functor simplicial set, exactly as `AreNaturallyEquivalent`
  defines a coherent natural equivalence. The witness is kept explicit in order
  to impose the next relative condition on this very equivalence.
- `yonedaEquiv.symm e` is its simplicial map `Δ[1] → Fun(C,C)`;
  `MonoidalClosed.uncurry (yonedaEquiv.symm e)` is its associated map
  `C ⊗ Δ[1] → C`. The equation after precomposing with `M.ι ▷ Δ[1]` says that this
  very homotopy is strictly projection followed by inclusion on `M ⊗ Δ[1]`.
- The final `IsFunctorEquivalence M.ι ∧ IsFunctorEquivalence r` is the node's
  “in particular” clause. The same r and inclusion are inverse: their composite
  on M is strictly identity and their composite on C has the displayed coherent
  equivalence to identity. No arbitrary substitute for either map is used.
- Empty C is allowed: no `Nonempty` or chosen vertex is assumed anywhere.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones` (public import):
  `SSet.Enhanced.IsEquivalenceEdge`, `diagramVertex`, `IsFunctorEquivalence`, and
  the definition of `AreNaturallyEquivalent` (expanded with its witness retained).
  Its Mathlib imports supply `SSet.Quasicategory`, the product, and `ihom`.
- `Mathlib.AlgebraicTopology.SimplicialSet.Boundary` (public import):
  `SSet.boundary`, `boundary_eq_iSup`, `boundary_zero` and the boundary inclusion.
- `Mathlib.AlgebraicTopology.SimplicialSet.Skeleton` (proof import):
  `SSet.relativeCellComplexOfMono`, the exact recorded Mathlib match for
  `lem-coef-infinity-monomorphism-boundary-cells`, used by proof steps 5--7.
- `Sheaf.AlgebraicTopology.MarkedAnodyneLiftingCalculus` (proof import):
  `SSet.Marked.marked_anodyne_lifting_calculus`, used by proof steps 1, 4, 6 and 8.
  Its full signature and docstring were read in the shared source.
- `def-weil-pbc-simplicial-set` is a Mathlib leaf: its recorded declarations
  `SSet`, `SSet.degenerate`, `SSet.nonDegenerate`, `SSet.Subcomplex`, and
  `SSet.Finite` were read at the specified Mathlib source files. The statement
  uses `SSet` and `Subcomplex`; nondegeneracy enters only the proof plan.
- `def-coef-presentable-infinity-category` has no Lean record or Mathlib match.
  This item cites it solely to fix the names of its universes; it invokes none
  of that node's accessibility, compactness, or presentability predicates. Explicit
  universe polymorphism fully implements that convention here. No missing
  mathematical declaration from that node is needed to type this theorem, and
  no interface or private copy of its mathematical definitions was introduced.

Edge cases checked before writing:

- In degree zero, the empty boundary imposes no restriction; the track of the
  unique vertex must be an equivalence. Minimality therefore identifies equivalent
  vertices, rather than silently omitting object-level minimality.
- The empty quasicategory has the empty subset, unique retraction, and unique
  homotopy; the identity of its functor simplicial set still supplies an equivalence
  edge. The statement never requests an object of C.
- A nonminimal category with distinct isomorphic objects cannot satisfy the
  displayed minimality condition in degree zero. A discrete nerve can retract
  onto itself, with constant deformation. Thus the track condition has its intended
  strength and is not arbitrary simplicial homotopy.
- Arbitrarily large mapping spaces inside U' are permitted. There is only the
  ambient universe parameter; no local-smallness, Kan condition on C, full-subset
  condition on M, or presentability assumption was added.
- Constancy is a simplicial map equation in all degrees, not just an equality on
  vertices or an endpoint equality on M.

Searches for an existing statement (2026-10-17 UTC):

- `msearch.py ... leanfinder "Every quasicategory admits a minimal simplicial subset
  which is a deformation retract"`: eight results, including `SSet.Quasicategory`,
  `SSet.KanComplex`, `SSet.modelCategoryQuillen.I`, and horn-filling lemmas; no
  minimal-retract statement.
- `msearch.py ... loogle '"Quasicategory", "minimal"'`: zero hits.
- `msearch.py ... leansearch "Every quasicategory has a minimal deformation retract"`:
  eight results concerning quasicategories and unrelated retract quasi-isomorphisms;
  no match.
- `msearch.py ... grep 'minimal|deformation|retract' AlgebraicTopology/Quasicategory`:
  one hit, retract stability in `InnerFibration.lean`, not this assertion.
- `rg` for minimality/deformation terminology across the project's upstream
  `WeilConjectures` tree and `lean/Sheaf/AlgebraicTopology` and
  `lean/Sheaf/CategoryTheory`: the side project has a different theorem
  `KanMinimalFactorization.lean`, concerning simplexwise product factorizations
  of Kan fibrations, not minimal deformation retracts of arbitrary quasicategories.
  Other upstream hits concern minimal primes or unrelated induction arguments.
- `grep -rn 'lem-coef-infinity-minimal-retract'` in upstream `WeilConjectures`:
  no hits. `rg` of `IsMinimalQuasicategory`, `exists_minimal_deformation_retract`,
  and `HomotopicRelBoundary` in Mathlib, upstream, side Lean, and
  `dag/lean_names_upstream.json`: no existing match or name collision.

No statement dispute, source mismatch, new node, or dependency repair was needed.
The docstring gives the complete eight-step proof plan, naming the recorded
mapping-space and relative-cell dependencies. All universes and variables are
explicit; there are no file-local notations, instances, private helpers or lets.

Validation: `scompile.py Q40 lem-coef-infinity-minimal-retract` compiled this module
both as sandbox and library module, with no errors or warnings (2.6 s and 1.5 s
respectively). The required `deliver2.py --no-push` dry run is run after this report.

## Second reading by Q40

I independently read the node statement, the Lean signature, and HTT Definition the project server and Proposition the project server (the map to a point, printed pp. 101--105 / PDF pp. 118--122). The correspondence is:

- The node fixes universes \(\mathcal U\in\mathcal U'\) and takes an arbitrary \(\mathcal U'\)-small quasicategory \(C\), with no local-smallness or presentability hypothesis. Lean renders this as `(C : SSet.{u}) [Quasicategory C]`; the unused smaller universe is a convention from the dependency and does not constrain this assertion. Verdict: exact.
- `M : C.Subcomplex` is the simplicial subset \(M\subseteq C\), and `M.ι : M.toSSet ⟶ C` is its canonical inclusion. Verdict: exact; this is not an arbitrary monomorphism.
- `r : C ⟶ M.toSSet` is the simplicial retraction, and `M.ι ≫ r = 𝟙 M.toSSet` is the strict equation \(r i=\mathrm{id}_M\). Verdict: exact.
- `e : ((ihom C).obj C) _⦋1⦌` is the coherent natural equivalence edge. The equations `δ 1 e = diagramVertex (𝟙 C)` and `δ 0 e = diagramVertex (r ≫ M.ι)` give the source \(\mathrm{id}_C\) and target \(ir\), in the project’s established face convention; `IsEquivalenceEdge ... e` supplies the coherent equivalence witnesses. Verdict: exact.
- `Quasicategory M.toSSet` states that the retained subset is an infinity category. Verdict: exact.
- For every `n : ℕ` and `f g : Δ[n] ⟶ M.toSSet`, the hypothesis `∂Δ[n].ι ≫ f = ∂Δ[n].ι ≫ g` is equality of the entire boundary. Verdict: exact, including `n = 0` where the boundary is empty.
- The minimality conclusion provides `H : Δ[n] ⊗ Δ[1] ⟶ M.toSSet`, endpoint equations `ι₀ ≫ H = f` and `ι₁ ≫ H = g`, and the boundary equation `(∂Δ[n].ι ▷ Δ[1]) ≫ H = fst _ _ ≫ ∂Δ[n].ι ≫ f`. This is precisely a homotopy relative to the common boundary.
- For every `v : Fin (n + 1)`, the edge obtained by evaluating `H` on the degenerate 1-simplex at `v` and the identity 1-simplex of `Δ[1]` is required to satisfy `IsEquivalenceEdge M.toSSet`. This is the node’s equivalence-track condition. The implication concludes `f = g`, with the same quantifier order as the node. Verdict: exact.
- The displayed equality `(M.ι ▷ Δ[1]) ≫ MonoidalClosed.uncurry (yonedaEquiv.symm e) = fst M.toSSet Δ[1] ≫ M.ι` says that the coherent homotopy represented by `e` is strictly projection followed by inclusion on `M × Δ¹`, hence is constant on `M`. Verdict: exact.
- The final `IsFunctorEquivalence M.ι ∧ IsFunctorEquivalence r` is the node’s “in particular” clause. Verdict: exact; the same `M.ι` and `r` are used.

The hypotheses contain no extra finiteness, Noetherian, local-smallness, Kan, presentability, characteristic, or universe-equality assumptions. No conclusion is weakened or strengthened, and all objects and clauses occur in the node’s order.

Edge cases checked independently: `n = 0` has the empty boundary and still tests the unique vertex track; empty `C` admits the empty subset and unique maps without choosing a vertex; the zero/empty simplicial subset is represented by `Subcomplex`; arbitrary universe `u` is retained; no characteristic or finiteness parameter occurs. A discrete category and a category with distinct isomorphic objects behave as expected under the degree-zero minimality condition.

Existing-definition searches were repeated with `msearch.py` LeanFinder, LeanSearch, and Loogle queries for minimal quasicategories, minimal deformation retracts, and boundary-relative equivalence, plus `rg` over Mathlib’s `AlgebraicTopology/Quasicategory` and the upstream and side `WeilConjectures` trees. The only hits were the generic `SSet.Quasicategory`, model-category generators, retract lemmas, and an unrelated `KanMinimalFactorization`; no declaration states this theorem. The dependency declarations `SSet.Enhanced.IsEquivalenceEdge`, `diagramVertex`, `IsFunctorEquivalence`, and `SSet.Subcomplex` were opened and match the uses above.

No mismatch was found, so no Lean or node statement was changed. The module was recompiled with `scompile.py Q40 lem-coef-infinity-minimal-retract lean/Sheaf/AlgebraicTopology/SimplicialSet/MinimalQuasicategoryRetract.lean`; sandbox and library checks both completed successfully with no errors or warnings.
