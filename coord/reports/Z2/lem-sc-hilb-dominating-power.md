## Worker report

Item `lem-sc-hilb-dominating-power`: no module is written. The statement exists in the source
library as `AlgebraicGeometry.exists_surjective_of_representableBy_hilbertPresheaf_curve`
(`WeilConjectures/AlgebraicGeometry/Hilbert/Curve.lean`), and the node is recorded with it
(`existing: true`), as its siblings lem-sc-hilb-geometrically-integral and thm-pc-hilb-curves are
recorded with declarations of the same module.

Hypothesis by hypothesis:

- `k` a field, `X` a `k`-scheme: `{k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))`
  (the `variable` line of the section).
- `X` a curve over `k` (def-pc-curve), smooth, proper, geometrically integral: the source has
  `[SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIntegral f]`. The two sets of
  hypotheses are equivalent. Node ⇒ source: curve and smooth give smooth of relative dimension 1
  (`AlgebraicGeometry.curve_baseChange_smoothOfRelativeDimension_one`, the landed
  lem-sc-curve-base-change-relative-dimension-one, with `T = Spec k`; this is Step 1 of the
  node's own proof). Source ⇒ node: geometrically integral gives integral, proper gives
  separated and of finite type, smooth of relative dimension 1 on a nonempty integral scheme
  gives dimension 1 and smooth. No `X` is gained or lost.
- `d ≥ 0`: `d : ℕ`.
- `H` a `k`-scheme representing `Hilb^d_{X/k}`: `H : Over (Spec (.of k))`,
  `e : (hilbertPresheaf f d).RepresentableBy H` (def-pc-hilb-functor, def-pc-representable-functor).
- Conclusion: `∃ (Y : Scheme) (q : Y ⟶ Spec (.of k)) (π : Y ⟶ H.left), IsProper q ∧
  GeometricallyIrreducible q ∧ Surjective π ∧ π ≫ H.hom = q`, the node's four clauses.

The source declaration is proved there but rests on `sorry` in the modules it imports, so
`tools/attach.py` (which records a node as already proved) refuses it; the record made here is
the stage-2 record of an existing statement, and the proof stays a stage-3 matter of the source
library.

## Second reading by Z2

Independent reader Z2-hdp (a fresh `codex exec` session), asked to check the claim hypothesis
by hypothesis:

VERDICT: PASS      (the upstream declaration states the node; record it as existing)

1. **The ambient objects match.** The `variable` line above the theorem binds `{k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))`. Thus `k` is a field and `f` is precisely the structure morphism of the node’s `k`-scheme `X`; no algebraic-closure or rational-point hypothesis is hidden.

2. **The hypotheses imply each other.**
   - **Node ⇒ upstream:** `f.IsCurveOverField` supplies integrality and `X.dim = 1`. `Scheme.dim_eq_topologicalKrullDim` converts this into topological dimension one. With `[Smooth f]` and the irreducibility supplied by integrality, `AlgebraicGeometry.smoothOfRelativeDimension_iff_topologicalKrullDim_eq` gives `SmoothOfRelativeDimension 1 f`. Alternatively, the landed `curve_baseChange_smoothOfRelativeDimension_one` gives this after base change along the identity, followed by transport through the canonical pullback isomorphism. Properness and geometric integrality are unchanged.
   - **Upstream ⇒ node:** `SmoothOfRelativeDimension.smooth` gives `Smooth f`. `GeometricallyIntegral.isIntegral_of_subsingleton f` gives `IsIntegral X`, hence nonemptiness. `IsProper` supplies separatedness and local finite type; its `UniversallyClosed` component supplies quasi-compactness, hence finite type. `topologicalKrullDim_eq_of_smoothOfRelativeDimension f 1`, followed by `Scheme.dim_eq_topologicalKrullDim`, gives `X.dim = 1`. These are exactly the fields of `f.IsCurveOverField`.
   
   Consequently, the upstream form neither admits an extra `X` nor excludes an allowed one. In particular, geometric integrality excludes the empty scheme, despite relative-dimension conditions alone being vacuous there.

3. **The remaining inputs match.** `d : ℕ` expresses the nonnegative integer degree, including `d = 0`. `H : Over (Spec (.of k))` bundles the scheme `H.left` and its structure map `H.hom`. `(hilbertPresheaf f d).RepresentableBy H` supplies the natural bijections with `Hom_k(-, H)`, exactly representability of the dependency’s Hilbert functor. Choosing representation data adds no mathematical restriction.

4. **Every conclusion clause matches.** The theorem states
   `∃ Y q π, IsProper q ∧ GeometricallyIrreducible q ∧ Surjective π ∧ π ≫ H.hom = q`,
   with `q : Y ⟶ Spec (.of k)` and `π : Y ⟶ H.left`. These are respectively the requested `k`-scheme, proper structure map, geometric irreducibility over `k`, surjection, and compatibility over `k`. The node does not require an explicit identification `Y ≅ X^d`; that construction appears in the theorem’s docstring and proof.

5. **Recording it is consistent with the siblings and the stage-2 rule.** `lem-sc-hilb-geometrically-integral` and `thm-pc-hilb-curves` use upstream declarations with the same equivalent hypothesis package. Under `coord/brief-stage2.md §1`, record `AlgebraicGeometry.exists_surjective_of_representableBy_hilbertPresheaf_curve` with `"existing": true`. A new statement using `[f.IsCurveOverField] [Smooth f]` would duplicate the existing statement.
