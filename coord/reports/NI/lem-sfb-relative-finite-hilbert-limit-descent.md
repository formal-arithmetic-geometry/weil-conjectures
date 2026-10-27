## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeFiniteHilbertLimitDescent` states
`AlgebraicGeometry.RelativeFiniteHilbert.relativeFiniteHilbert_limit_descent`.
Its sole proof is `sorry`. It introduces no definition, changes no mathematical
statement, and uses the published Hilbert objects and arrows directly.

Source checked: `literature/stacks-project/criteria.tex`,
`lemma-limit-preserving` (06CH), the complete proof at lines 1997–2095;
`section-limit-preserving`, especially `equation-limit-preserving` at lines
333–365, and `lemma-representable-by-spaces-limit-preserving` (06CX).
The theorem docstring carries all six DAG proof steps (the node's final
reconstruction is step 6 of the mathematical argument).

Hypotheses and clauses, matched individually:

- An arbitrary base scheme S is `{S : Scheme.{u}}`.
- Explicit universes `u v₁ w₁ v₂ w₂` allow independent total-category object and
  morphism universes. `I : Type u` follows the required small-limit convention.
- The categories X and Y over S are `BasedCategory (Over S)`, and the morphism
  of fibred categories is `F : BasedFunctor X Y`. Its based-functor equality
  specifies that the functor lies over the identity of the scheme base.
- The isomorphism-sheaf and effective object-descent hypotheses for the big
  fppf site are `_hX : IsFppfModuliStack X` and
  `_hY : IsFppfModuliStack Y`. Each includes `IsFibredInGroupoids` and the
  recorded covering-sieve descent property for `Scheme.fppfTopology.over S`.
- Representability of F is expressed by the family
  `R : ∀ T y, Representative (F := F) T y`. This is precisely the dependency's
  fixed-representative convention: an algebraic space, its structural map,
  an equivalence over the scheme base with the explicit relative fibre, and
  compatibility with that structural map. It retains automorphisms and does
  not replace the fibre groupoid by its isomorphism classes. Specifying all
  chosen representatives is the data form of their assumed existence;
  classical choice supplies this family from representability.
- Local finite presentation of each X_y→T on étale scheme charts is `_hlfp`,
  using the already published `SpaceProperty` of
  `fun _ _ f ↦ LocallyOfFinitePresentation f` on `(R T y).projection`.
  In particular the predicate `FlatLfp` is deliberately not used: it would
  add the forbidden flatness assumption.
- Every integer degree d≥1 is `d : ℕ+`, the dependency's degree convention.
- A small nonempty directed inverse system is `(I : Type u) [Preorder I]
  [Nonempty I] [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤ Over S)`.
- The chosen limit T and its projections are `c : Cone D` with `_hc : IsLimit c`.
  Taking the limit in `Over S` includes the given compatible S-structure.
  The forgetful functor creates these nonempty connected limits, so this is
  the node's scheme limit equipped with its S-structure.
- Each T_i is affine by `[∀ i : I, IsAffine (D.obj (op i)).left]`.
- The affine transition-map hypothesis is the displayed instance family
  `[∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f).left]`.
- The initial index is `(i : I)` and its object is
  `(yᵢ : Functor.Fiber Y.p (D.obj (op i)))`.
- The Hilbert object over T is `ξ : Fiber (F := F) (d := d) c.pt`.
  This is the recorded fibre of `RelativeFiniteHilbert.base`; its underlying
  object contains the actual finite locally free cover of degree d, x, y,
  and comparison α in the dependency's inverse-α convention.
- The prescribed isomorphism γ:p_d(ξ)≅y_i|T is represented by
  `γ : ξ.val.y.val ⟶ yᵢ.val` and
  `_hγ : Y.p.IsHomLift (c.π.app (op i)) γ`.
  This is a cartesian total-category arrow, not an isomorphism between objects
  over different schemes. It is exactly an isomorphism to the pullback,
  because every arrow of a category fibred in groupoids is cartesian.
- The eventual index and inequality are `∃ (j : I) (hij : i ≤ j)`.
- The descended object is `ξⱼ : Fiber (F := F) (d := d) (D.obj (op j))`.
- The requested isomorphism a_req:ξ_j|T≅ξ is represented by
  `a : ξ.val ⟶ ξⱼ.val` and the first conclusion
  `(base (F := F) (d := d)).IsHomLift (c.π.app (op j)) a`.
  The existing `RelativeFiniteHilbert.Hom` requires a cartesian scheme square
  and the two cartesian object arrows with their comparison square. Hence a
  is exactly an isomorphism α:ξ≅ξ_j|T followed by the restriction arrow;
  the requested a_req is α⁻¹. No arbitrary morphism substitutes for an isomorphism.
- The requested b:p_d(ξ_j)≅y_i|T_j is represented by
  `b : ξⱼ.val.y.val ⟶ yᵢ.val` and the second conclusion
  `Y.p.IsHomLift (D.map (homOfLE hij).op) b`.
- The final equation is `a.b ≫ b = γ`. Here `.b` is exactly p_d on arrows,
  from the published `target` functor. To compare with the node, write
  a_total = q_H ∘ α and b_total = q_i,j ∘ b₀. Cone naturality and cartesian
  uniqueness identify the displayed equality with
  `(b₀|T) ∘ p_d(α) = γ₀`. Composing with p_d(α⁻¹) gives exactly
  `b₀|T = γ₀ ∘ p_d(a_req)`. This proves the equivalence of the two formulations,
  including the direction of a and the prescribed (not merely existing) γ.
- No flatness or surjectivity of F, no quasi-compactness or separation of its
  representing spaces, and no lci condition is assumed.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `def-weil-size-convention` is a recorded metatheoretic convention; explicit
  universes supply its implementation, without inventing a declaration.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`, used by the recorded fppf-stack predicate.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`, `BasedFunctor` stack conventions,
  `discreteModuli`, `IsRepresentableByAlgebraicSpaces`, and `HasSpaceBaseChange`.
- `Sheaf.CategoryTheory.SiteStackification`:
  `CategoryTheory.IsFppfModuliStack` (used by the Hilbert dependency itself).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`:
  `AlgebraicGeometry.AlgebraicSpace`, including its actual fppf sheaf,
  representable diagonal and étale atlas; `IsEtale` and `IsSurjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` (full signature inspected).
- `Sheaf.AlgebraicGeometry.RelativeFiniteHilbertGroupoids`:
  `RelativeFiniteHilbert`, `Hom`, `base`, `target`, `Fiber`,
  `Representative`, and `SpaceProperty`. The entire module was read,
  including its actual composition, pullbacks, representing equivalence,
  projection compatibility, and the separate stronger `FlatLfp` predicate.

Imports include the recorded available proof-dependency modules for finite
presentation descent, affine transition limits, finite locally free descent,
base-change limits, and Mathlib permanence/rank results. The proof dependency
`lem-sfb-lfp-space-scheme-limit-test` has no current Lean record or Mathlib
match in the read snapshot; it is not a statement dependency and supplies
no object needed to type this statement. It is therefore mentioned in the
proof docstring and not imported from an invented module.

Edge cases checked before writing: d=1 is included and d=0 is excluded exactly
as in the node; the empty base and empty finite cover of any specified degree
remain allowed; constant and one-index systems are allowed; an empty index
system is excluded by the node's explicit nonemptiness. Preorders rather than
partial orders allow equivalent/repeated indices. Nontrivial automorphisms
and arbitrary γ are retained by actual arrows; no coarse quotient appears.
A non-flat F and a non-separated, non-quasi-compact representing space satisfy
no extra hypothesis here. The affine limit hypothesis is a consequence of the
affine stages, not an additional finite-presentation or flatness constraint.

Searches made on 2026-10-24:

- `msearch.py ... leanfinder`: “Relative finite Hilbert stack of a representable
  locally finitely presented map has relative object descent along directed
  inverse limits of affine schemes”. Eight hits concern scheme-map limit
  factorization, locally finite presentation and unrelated locality results;
  none gives Hilbert object descent with the prescribed comparison.
- `msearch.py ... loogle`: `RelativeFiniteHilbert, LocallyOfFinitePresentation`.
  Zero hits; unknown Mathlib identifier `RelativeFiniteHilbert`.
- `msearch.py ... leansearch`: “The relative finite Hilbert stack of a
  representable locally finitely presented map descends objects along directed
  inverse limits of affine schemes”. Eight hits concern scheme permanence,
  flat descent and section continuity; none states this theorem.
- `msearch.py ... grep`: `Hilbert.*[Ll]imit|[Ll]imit.*Hilbert|relative.*hilbert`.
  Zero Mathlib hits.
- `rg` of `RelativeFiniteHilbert|Hilbert.*[Ll]imit|[Ll]imit.*Hilbert` in
  `lean/WeilConjectures` and `lean/Sheaf` finds the existing Hilbert definition,
  its lci consumer and the distinct embedded Hilbert functor, not this theorem.
- `rg` of this node id in `lean/WeilConjectures` finds no declaration.
- `rg` of the proposed full theorem basename in Mathlib, WeilConjectures,
  Sheaf and `dag/lean_names_upstream.json` finds no collision.

Validation: prescribed `scompile.py NI lem-sfb-relative-finite-hilbert-limit-descent`
compiled the sandbox module and its final library module cleanly against the
published server build (3.8 s and 4.5 s). No node fault or mathematical dispute
was found. The item node changes only in `lean`.

## Second reading by NI

This is a second self-reading, not an independent agent review: the dispatcher's
explicit instruction forbids starting other agents. The maintainer supplies the
independent review after delivery. I reopened the item and the compiled file and
checked every binder and conclusion against the correspondence above. In
particular I rechecked the non-flat hypothesis, the positive degree, the inverse
orientation of a, and cancellation of the common cartesian restriction arrow in
the final equation. The `Hom` definition supplies the cartesian cover square and
compatible x component, so the conclusion is about the full Hilbert object,
not only its image y. The representing equivalence is over the scheme base and
retains the structural projection, so R is not an arbitrary pointwise bijection.
No mismatch or change was found in this second reading. There are no new nodes,
dependency repairs, or statement corrections to review.
