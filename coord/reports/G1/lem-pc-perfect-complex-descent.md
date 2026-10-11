## Worker report

(Rewritten by reviewer R-pcd1348, FIX.)

`AlgebraicGeometry.perfect_complex_descends` in `Sheaf.AlgebraicGeometry.PerfectComplexDescent` states the
node as on sheaf-dag (the delivered statement correction is reverted, H7): directed `I : Type u`
(`Preorder`, `IsDirected`), `R : I ⥤ CommRingCat.{u}` with Noetherian stages, a colimit cocone
`c`/`hc`, `s : Xi ⟶ Spec (R.obj i)` locally of finite presentation, quasi-compact, quasi-separated;
`X := pullback s (Spec.map (c.ι.app i))` (the base change, no free iso or free map);
`E` perfect (`Scheme.IsPerfect`) on `X`. Conclusion: `∃ j ≥ i` and a perfect `Ej` on
`X_j := pullback s (Spec.map (R.map (homOfLE hij)))` with `Nonempty ((derivedPullback g).obj Ej ≅ E)`,
`g` the canonical `baseChangeMap s (Over.homMk (Spec.map (c.ι.app j)) _)` : X ⟶ X_j — the same
stage/pullback form as lem-pc-perfect-descend-morphisms (J1). Derived categories via
`[∀ Z, HasDerivedCategory …]` and `[∀ Z U, HasDerivedCategory (….over U)]` as J1.

## Second reading by G1

(Reviewer R-pcd1348 replaces the second reading.) The delivered version let the "derived base-change functor" `Fj` be an arbitrary existential functor
(take the constant functor at `E`: trivially true), left `X_j`, the maps `X_j ⟶ X_i`, `X ⟶ X_j`
and the iso `X ≅ X_i ×_{R_i} R` untied, carried an unused `A : CommRingCat`, and quantified the derived
categories of `X_j` existentially.
