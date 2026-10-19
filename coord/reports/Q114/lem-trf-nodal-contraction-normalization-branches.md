## Worker report

The delivery states `AlgebraicGeometry.nodal_contraction_normalization_branches` in
`Sheaf.TraceFormula.NodalContractionNormalizationBranches`. The only postponed proof is
this theorem, with the complete nine-step DAG argument in its docstring. No definition
or theorem is proved here. The mathematical node statement is unchanged.

Source read: Temkin, *Stable modification of relative curves*, Appendix B, Corollary B.2,
printed pp. 57–58, especially the final normalization paragraph on p. 58, from
https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf. The local ordinary-point
calculation is the agent refinement already spelled out in the node's nine proof steps.
The conclusion does not use the genus equality in the earlier part of Corollary B.2.

Hypothesis-by-hypothesis correspondence:

- Algebraically closed ground field: `(k : Type u) [Field k] [IsAlgClosed k]`.
- Proper reduced k-schemes X,Y: `pX`, `pY`, `[IsProper pX]`, `[IsProper pY]`,
  `[IsReduced X]`, `[IsReduced Y]`. Pure dimension one is `hX`, `hY`, using the recorded
  `Scheme.IsPureDimension`.
- Proper surjective k-morphism: `f`, `[IsProper f]`, `[Surjective f]`, and
  `hf : f ≫ pX = pY`.
- Closed rational point: `x`, `hx : IsClosed ({x} : Set X)`. On the finite-type X over
  algebraically closed k this is exactly a k-point, with residue field k. Thus the recorded
  `f.fiber x` is the required scheme-theoretic fibre over Spec k, up to its canonical
  residue-field identification, rather than a set-theoretic fibre.
- B is the reduced induced closed scheme on the fibre support: `B`, `[IsReduced B]`,
  `iB`, `[IsClosedImmersion iB]`, and `hB : Set.range iB = f ⁻¹' {x}`. These are a
  presentation of the uniquely specified B, by the recorded reduced-induced-subsheme
  uniqueness theorem. No extra structure or property is imposed on B.
- B nonempty and connected: `[ConnectedSpace B]`, whose class includes `Nonempty B`.
  Pure dimension one: `hpureB`.
- Isomorphism off B and x: `hoff` says that base-changing f to the open complement of
  `{x}` gives an isomorphism. By hB its source is exactly the open complement of B.
- Nodal open neighbourhood of B: `hnodal` supplies an open U containing `Set.range iB`.
  It tests every closed point y of U which has no smooth open neighbourhood in Y.
  Its conclusion is the existing `Orgogozo.IsOrdinaryDoublePoint pY y`, namely a
  scalar-compatible isomorphism of the actual maximal-ideal completion with
  `k[[u,v]]/(uv)`. Smoothness on U and on Y agree locally.

Representations used to name the objects in the conclusion:

- `CX`, `a`, the integral and closed-immersion instances, `ha`, `haindex` enumerate
  the reduced irreducible components of X exactly once. `CY`, `b`, `hb`, `hbindex`
  do the same for Y. An integral closed subscheme with the given component support is
  precisely its unique reduced induced scheme. These binders choose presentations of
  the components in the original statement, rather than restricting which curves qualify.
- The integral-scheme normalization is the recorded `Scheme.normalization` and its map
  `Scheme.fromNormalization`. It cannot be applied directly to reducible X.
  `N`, `ι`, `hN : IsColimit (Cofan.mk N ι)`, `ν`, `hν` present its normalization as the
  coproduct of those component normalizations, with the specified map to X. This is the
  standard componentwise normalization. The map ν is characterized on each summand;
  it is not an arbitrary finite normal cover. The same presentation convention appears
  in the existing `normalization_projective_components` statement, which I read.
- Index types I,J live in `Type u`. Proper curves have finitely many components; all their
  component sets admit such presentations, including u=0. The statement does not assume
  that either curve is integral, connected, projective, or nodal away from the neighbourhood.

Clause-by-clause correspondence:

- The first existential `e` bijects the subtype of Y components not contained in B with
  the X component indices. `closure (f '' Set.range (b j.1)) = Set.range (a (e j))`
  specifies the actual correspondence induced by f.
- The family `c` identifies the corresponding component normalizations. Its commuting
  equation is exactly identification over X by f. The next clause states that both
  normalizations are smooth and proper over k. Since e is an equivalence, it covers
  every X component.
- `h : N ⟶ Y`, `h ≫ f = ν`, and the equation on `ι (e j)` specify the map from the
  normalization of X induced by the inverses of c and the exterior component inclusions.
  `Set.BijOn h (ν ⁻¹' {x}) (Set.range iB ∩ closure ((Set.range iB)ᶜ))` states the required
  bijection of the points over x with the actual boundary. The complement is explicitly
  inside the closure.
- The next conjunct says this same boundary is nonempty.
- At every boundary point the theorem states `Orgogozo.IsOrdinaryDoublePoint pY y`;
  `∃! j` for a component contained in B and `∃! j` for a component not contained in B;
  and `∃! z` above y on each incident component's normalization. These specify exactly
  one normalization branch on each side. They exclude neither self-nodes elsewhere nor
  multiple components away from the boundary. At a boundary node the two branches
  belong to distinct components because one whole component is in B and one is outside.
- The last implication quantifies over every `n : ℕ` with `1 ≤ n`. Its completion
  isomorphism has quotient ideal generated by all `X i * X j` with `i ≠ j`, and preserves
  the ground-field scalars via the existing `Orgogozo.localScalar`. Thus it is the
  ordinary n-fold point model in the node, including n=1. It concludes
  `IsReduced (f.fiber x)` and an isomorphism `eB : f.fiber x ≅ B` whose composite with
  `iB` is the actual `f.fiberι x`. This is Z=B as closed subschemes over Y, not merely
  equality of supports or reducedness of a replacement fibre.
- No arithmetic genus, rationality, tree, or marking hypothesis appears.

Dependency declarations used (source signatures and docstrings read):

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`:
  `Scheme.normalization`, `Scheme.fromNormalization` (integral schemes).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the algebraic-closure dependency
  explicitly records this as its algebraically closed field predicate. No choice of an
  algebraic closure is required by the item.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, including nonemptiness.
- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`, its ring
  structure and `AdicCompletion.of`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `X`, `C`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`.
- Added landed statement dependency `def-trf-orgogozo-induction-data`, module
  `Sheaf.Paper.OrgogozoInductionData`: `Orgogozo.IsOrdinaryDoublePoint`, `nodeRing`,
  `localScalar`. This reuses its scalar-compatible notion and adds no new node.

Proof-only imports follow the recorded modules of normalization-dominant-lift,
normalization-properties and smooth-normal, curve-normalization-completion,
finite-birational-normal-iso, and finite-iff-proper-finite-fibres. The relevant Mathlib
completion-exactness and faithful-flatness modules are imported as well. The two proof
nodes complementary-pure-subcurve-components and nodal-subcurve-boundary have no Lean
record in the snapshot read, so no module is invented or imported for them. They are not
needed to type this stage-2 theorem.

Edge cases checked before writing: empty X is excluded by the chosen point x. Empty B
is excluded by ConnectedSpace. B=Y would force X to be a point under surjectivity and
hB, contradicting pure dimension one, so no impossible nonempty-boundary conclusion is
introduced. Disconnected X and Y are allowed: components away from x are retained by e.
Components of B may have arbitrary genus and arbitrary internal cycles. Boundary nodes
cannot be self-nodes of an incident component; self-nodes away from the boundary remain
allowed. For n=1 the distinct-index generating set is empty and the ordinary ring is
k[[t]], retaining the smooth-target case. No characteristic restriction is used,
including characteristic two. The actual fibre may initially be nonreduced; only the
ordinary-point implication concludes reducedness.

Searches for an existing statement:

- `msearch.py leanfinder`, query `Proper curve contraction normalization branches boundary
  nodal subcurve`: eight hits, principally relative-normalization/coproduct results and
  a Weierstrass minimal-model result; no contraction-boundary theorem.
- `msearch.py loogle`, query `AlgebraicGeometry.Scheme.normalization`: zero hits,
  unknown identifier in the Mathlib-only index (the integral normalization is upstream).
- `msearch.py grep`, query `nodal|contraction|ordinary.*point`, subdirectory
  `AlgebraicGeometry`: zero hits.
- `msearch.py leansearch`, query `Normalization of a nodal curve contraction identifies
  boundary branches`: eight hits on relative normalization and descent, no match.
- `rg` over upstream WeilConjectures for the item id: no declaration. Searches for
  `nodal_contraction_normalization_branches` and `NodalContractionNormalizationBranches`
  in Mathlib, upstream, the project's Lean and `dag/lean_names_upstream.json`: no match.
- Concept searches in `lean/Sheaf` found `NodalNormalizationAdjunction`,
  `NormalizationProjectiveComponents`, `NormalizationGeonormalInsep`,
  `ProjectiveNodalTower`, and the scalar-compatible Orgogozo definitions. I read their
  relevant declarations. None states this lemma; their constructions are reused where
  applicable rather than privately redefined.

No statement correction, disputed statement, new definition node, or dependency repair.
The only additional statement dependency is the already-landed Orgogozo definition node.

Validation: the prescribed `scompile.py` checks elaborated the statement under both the
sandbox and final module paths. Making all exterior-component subtype binders explicit
resolved the initial elaboration heartbeat failure; no limits were raised. Two long-line
warnings in an intermediate copy were repaired. The final `deliver2.py --no-push` run
reported `OK (dry run)`: server compilation is clean and the maintainer preflight passes.
The final recorded signature matches the source verbatim, maximum Lean line width is 90,
and only `lean` and the authorized added statement dependency differ in the node copy.

## Second reading by Q114

Group self-check (original text, kept): the worker reopened the node and the final signature,
checked that the actual fibre is retained, that the normalization map is specified on every
summand and that the boundary is the intersection with the closure of the complement; it made
the complement parentheses explicit and bound each exterior component subtype explicitly.

Clause-by-clause reading (completed by the maintainer's independent reviewer, 2026-10-18,
node, Lean file and dependency declarations open; delivery-errors H11 repair, no Lean change).

Objects and hypotheses of the node, with their Lean and verdict:

1. $k$ algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`. Correct;
   `IsAlgClosed` is the predicate named in def-weil-algebraic-closure's record.
2. $X,Y$ proper reduced $k$-schemes of pure dimension one: `pX`, `pY`, `[IsProper pX]`,
   `[IsProper pY]`, `[IsReduced X]`, `[IsReduced Y]`, `hX`, `hY` with
   `Scheme.IsPureDimension` (every irreducible component has topological Krull dimension
   `d`, read in `Sheaf.AlgebraicGeometry.PureDimension`). Correct, nothing stronger.
3. $f$ proper surjective $k$-morphism: `f`, `[IsProper f]`, `[Surjective f]`,
   `hf : f ≫ pX = pY`. Correct.
4. $x\in X(k)$ closed: `x`, `hx : IsClosed {x}`. Over algebraically closed $k$ and finite
   type, a closed point is a $k$-point with $\kappa(x)=k$. Correct.
5. $Z=Y\times_X\operatorname{Spec}k$: `f.fiber x` = `pullback f (X.fromSpecResidueField x)`
   (def-pc-scheme-fibre), with `f.fiberι x`. The scheme-theoretic fibre, not a set. Correct.
6. $B=Z_{\rm red}$: `B`, `[IsReduced B]`, `iB`, `[IsClosedImmersion iB]`,
   `hB : Set.range iB = f ⁻¹' {x}`. By the uniqueness clause of
   `Scheme.IdealSheafData.reduced_induced_closed_subscheme` this determines $B$ up to the
   unique isomorphism over $Y$. Correct presentation.
7. $B$ nonempty, connected, pure of dimension one: `[ConnectedSpace B]` (includes
   `Nonempty`), `hpureB`. Correct.
8. $Y\setminus B\to X\setminus\{x\}$ isomorphism: `hoff`, the base change of `f` along
   the open immersion of `{x}ᶜ`; its source is $f^{-1}(X\setminus\{x\})=Y\setminus B$ by
   `hB`. Equivalent.
9. Nodal open neighbourhood of $B$: `hnodal`, an open `U ⊇ range iB` in which every closed
   point without a smooth-over-$k$ open neighbourhood satisfies
   `Orgogozo.IsOrdinaryDoublePoint pY y` (maximal-ideal completion of the stalk ≅
   `MvPowerSeries (Fin 2) k ⧸ (X 0 * X 1)` compatibly with the $k$-scalars). Correct; the
   scalar compatibility is the $k$-algebra meaning of the node's $\cong$.
10. Components and normalizations (presentation binders): `CX`, `a`, `ha`, `haindex` and
    `CY`, `b`, `hb`, `hbindex` enumerate the reduced irreducible components bijectively by
    integral closed subschemes; `N`, `ι`, `hN`, `ν`, `hν` the coproduct of the
    `Scheme.normalization`s (def-sc-normalization, integral case) with its map to $X$
    fixed on every summand. These are universally quantified presentations of canonical
    objects; they always exist (finitely many components, index types in `Type u`), so no
    case of the node is lost and no substitute map is admitted.

Conclusion clauses:

11. Component bijection: `e : {j // ¬ range (b j) ⊆ range iB} ≃ I` with
    `closure (f '' range (b j)) = range (a (e j))`. Exactly the node's correspondence.
12. Smooth proper normalizations identified over $X$ by $f$: `c j` isomorphisms with
    `(c j).hom ≫ ν_X ≫ a = ν_Y ≫ b ≫ f`, and both normalizations `Smooth` and `IsProper`
    over $k$. Correct.
13. Normalization of $X$ maps to $Y$, points over $x$ ↔ boundary: `h : N ⟶ Y`,
    `h ≫ f = ν`, `ι (e j) ≫ h = (c j).inv ≫ ν_Y ≫ b`, and
    `Set.BijOn h (ν ⁻¹' {x}) (range iB ∩ closure (range iB)ᶜ)`. Correct; the boundary is
    $B\cap\overline{Y\setminus B}$ verbatim.
14. Boundary nonempty: separate conjunct. Correct.
15. Each boundary point a node with one branch in $B$ and one outside:
    `IsOrdinaryDoublePoint pY y`, `∃!` component through `y` inside `B`, `∃!` component
    through `y` not inside `B`, and exactly one normalization point over `y` on each incident
    component. With the two branches of a node this is exactly the node's clause.
16. Ordinary $n$-fold point ⇒ $Z$ reduced and $Z=B$: for every `n ≥ 1`, a scalar-compatible
    isomorphism of the completed stalk with `MvPowerSeries (Fin n) k ⧸ (X i * X j, i ≠ j)`
    implies `IsReduced (f.fiber x)` and `eB : f.fiber x ≅ B` with `eB.hom ≫ iB = f.fiberι x`
    (equality as closed subschemes of $Y$). Correct, includes $n=1$.
17. No genus, rationality, tree or marking hypothesis appears. Correct.

Edge cases: empty $X$ excluded by `x`; empty $B$ excluded by `ConnectedSpace`; $n=1$ (empty
generating set, $k[[t]]$); any characteristic; disconnected $X,Y$; self-nodes away from the
boundary allowed; universes: `k`, the schemes and the index types in the one universe `u`
forced by `Spec (.of k)`; no extra universe restriction.

Searches: rg in Mathlib, slopmaster2 `WeilConjectures` and `lean/Sheaf` for
`nodal_contraction`, `contraction`, `normalization.*branch`, `IsOrdinaryDoublePoint`: only
the Orgogozo definitions reused here; no existing statement.

Mismatches found: none in the Lean statement. Changes: this section only (H11), no Lean or
node change. Per-file compile of the delivered module: clean (no error, no warning other than
the sorry).
