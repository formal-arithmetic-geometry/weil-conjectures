# def-nagata-basechanged-system (L, stage 2)

## Worker report

Worker W-bcs0514 for L, stage 2, item `def-nagata-basechanged-system`. **Existing declaration; no module
written.**

The source repository already has this construction (brief §1, one definition per notion), sorry-free
(`#print axioms`: propext, Classical.choice, Quot.sound; probe compile in 1.6 s against the shared build):
`WeilConjectures/Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean`, section `BaseChangeLimit`
(module `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`, namespace `AlgebraicGeometry`,
slopmaster2 at 71d63dcf6), section variables
`{I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) {i : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj i)`:

```lean
@[simps] noncomputable def baseChangeDiagram : Over i ⥤ Scheme.{u} where           -- line 2181
  obj j := pullback p (D.map j.hom)
  map {j k} f := pullback.map _ _ _ _ (𝟙 Y) (D.map f.left) (𝟙 _)
    (by simp) (by simp [← D.map_comp, Over.w f])
  map_id j := by apply pullback.hom_ext <;> simp
  map_comp f g := by apply pullback.hom_ext <;> simp

@[simps] noncomputable def baseChangeCone : Cone (baseChangeDiagram D p) where      -- line 2196
  pt := pullback p (c.π.app i)
  π.app j := pullback.map _ _ _ _ (𝟙 Y) (c.π.app j.left) (𝟙 _) (by simp) (by simp)
  π.naturality {j k} f := by apply pullback.hom_ext <;> simp
```

It is used by `WeilConjectures/AlgebraicGeometry/ProjectiveSpace/Spreading.lean:102`. The same section also
has `isLimitBaseChangeCone` ([IsCofiltered I], IsLimit c → IsLimit (baseChangeCone D c p)), i.e. Y = lim Y_λ;
the node says this is not part of the definition, so it is not recorded.

Clause by clause:
- "I a directed poset, (S_λ) an inverse system with s_{λμ} : S_μ → S_λ (λ ≤ μ)": `D : I' ⥤ Scheme.{u}` with
  `I' = Iᵒᵖ` for the preorder category of I (`Preorder.smallCategory`, a `Category.{u}` on `Type u`);
  `s_{λμ} = D.map (homOfLE h).op`. This is the form Mathlib's `AffineTransitionLimit.lean` uses (`I ⥤ Scheme`,
  cofiltered I). Directedness is not needed for the data (it is the hypothesis of `isLimitBaseChangeCone`);
  the declaration is more general (any small category), which covers the node.
- "S with projections p_λ, a limit (assumed given)": `c : Cone D`, `p_λ = c.π.app (op λ)`; the data does not
  use limit-ness (`IsLimit c` is not needed), so the node's case (a given limit) is covered.
- "λ0 ∈ I, Y_{λ0} → S_{λ0}": `{i : I'} {Y : Scheme.{u}} (p : Y ⟶ D.obj i)`, `i = op λ0`.
- "I_{λ0} = {λ ≥ λ0}": `Over i`; an object is `op λ` with the (unique) arrow `op λ ⟶ op λ0`, i.e. λ0 ≤ λ, and a
  morphism `j ⟶ k` is an arrow `op μ ⟶ op λ` over `op λ0`, i.e. λ ≤ μ; so `Over (op λ0)` is
  `(Set.Ici λ0)ᵒᵖ` as a category (thin).
- "Y_λ = Y_{λ0} ×_{S_{λ0}} S_λ via s_{λ0λ}": `(baseChangeDiagram D p).obj j = pullback p (D.map j.hom)`.
- "Y = Y_{λ0} ×_{S_{λ0}} S via p_{λ0}": `(baseChangeCone D c p).pt = pullback p (c.π.app i)`.
- "Y_μ → Y_λ induced by id_{Y_{λ0}} and s_{λμ}": `pullback.map _ _ _ _ (𝟙 Y) (D.map f.left) (𝟙 _)`, the unique
  map with `≫ fst = fst` and `≫ snd = snd ≫ s_{λμ}` (lemmas `baseChangeDiagram_map_fst/_snd`).
- "Y → Y_λ induced by id and p_λ": `(baseChangeCone D c p).π.app j = pullback.map _ _ _ _ (𝟙 Y) (c.π.app j.left)
  (𝟙 _)` (lemmas `baseChangeCone_π_app_fst/_snd`).
- Remarks "transition maps compose correctly, compatible with Y → Y_λ": the proved fields `map_id`, `map_comp`
  (functor) and `π.naturality` (cone). Remark "I_{λ0} directed and cofinal": not data, not stated in the source
  (Mathlib's `Over.forget i` is initial for cofiltered I, used in `isLimitBaseChangeCone`).

Universe: I must lie in the universe u of the schemes (`I : Type u`, `Category.{u} I`); this is the only
restriction relative to the node's "directed poset" (of any size); every citer's I (Stacks Tag 01YX setting,
the formalized route) is of this kind. The lead decides whether this is acceptable; otherwise a generalised
module would be a copy of the same construction with `I : Type w`.

Edge cases: empty I is impossible (λ0 ∈ I); `Over i` always contains `i` itself (Y_{λ0} ×_{S_{λ0}} S_{λ0}).
Y_{λ0} empty gives empty pullbacks; no restriction.

Searches: grep `baseChange\|basechanged\|limit.*pullback\|Iᵒᵖ ⥤ Scheme\|⥤ Scheme` in Mathlib/AlgebraicGeometry
and WeilConjectures/ — hit `baseChangeDiagram`/`baseChangeCone` (source, above); Mathlib's
`AffineTransitionLimit.lean` has only the analogous `opensDiagram`/`opensCone` (preimages of an open, not base
changes). `dag/lean_names_upstream.json`: 0 hits for `baseChangeDiagram`/`baseChangeCone` and no tag for this
node (lean_audit none). The node's own mathlib_searches (leanfinder, loogle, grep): no Mathlib match.

## Second reading by L

L read AffineTransitionLimit.lean:2175-2200: baseChangeDiagram and baseChangeCone are the node's construction (existing: true).
