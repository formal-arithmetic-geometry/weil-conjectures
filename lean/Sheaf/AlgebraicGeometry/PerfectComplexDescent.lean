module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Picard.TwistedDescent

/-! # Descent of a perfect complex

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.29.3 (Tag 09RF)
(blueprint: lem-pc-perfect-complex-descent).

`Xi` is finitely presented over `Spec (R.obj i)` via `s`; for `j ≥ i` the stage
`X_j` is `pullback s (Spec.map (R.map (homOfLE hij)))` and `X` is
`pullback s (Spec.map (c.ι.app i))`, as in lem-pc-perfect-descend-morphisms.
The base change from `X_j` to `X` is the derived pullback along the canonical
base-change map `X ⟶ X_j` (`baseChangeMap` along `Spec R ⟶ Spec R_j`).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A perfect object on the base change `X` of a finitely presented `R_i`-scheme `X_i`
to a filtered colimit `R` of Noetherian rings `R_i` descends, after increasing `i` to `j`,
to a perfect object `E_j` on `X_j = X_i ×_{R_i} R_j` with `L g^* E_j ≅ E`, where
`g : X ⟶ X_j` is the canonical map.
Source: Stacks Project, Derived Categories of Schemes, Lemma 36.29.3 (Tag 09RF)
(blueprint: lem-pc-perfect-complex-descent).

Proof, following the three steps of the node:
1. `X_i` is finitely presented over `R_i`, hence quasi-compact and quasi-separated.
   Choose a finite affine cover `V¹, …, Vⁿ` of `X_i`, put `Wᵏ = V¹ ∪ … ∪ Vᵏ`, and prove by
   induction on `k`: after increasing `i` there are a perfect `E_W` on the preimage of
   `Wᵏ` in `X_j` and an isomorphism `L f^* E_W ≅ E|_{f⁻¹ Wᵏ}`. The case `k = n` is the lemma.
2. Affine case: on `V = Spec A_j` with preimage `Spec A`, `A = colim A_j`, the restriction of
   `E` is `P̃` for a bounded complex `P` of finite projective `A`-modules
   (lem-pc-perfect-affine-bounded-projective); it descends to a bounded complex `P_j` of
   finite projective `A_j`-modules (lem-pc-affine-perfect-colimit-descent), and `P̃_j` is
   strictly perfect with `L f^* P̃_j ≅ E|_{f⁻¹V}` since its terms are flat.
3. Induction step: descend the overlap isomorphism `φ_V⁻¹ ∘ φ_W` to an isomorphism `c` on
   `W_j ∩ V_j` (lem-pc-perfect-descend-morphisms); take adjoints `a, b` into `R f_* E`
   (lem-pc-ringed-spaces-derived-adjoint), glue objects and maps on `W_j ∪ V_j`
   (lem-sc-derived-open-gluing); the glued object is perfect (perfectness is local), and the
   adjoint map `L f^* F ⟶ E|_{f⁻¹(W ∪ V)}` is an isomorphism because it is one on each
   member of an open cover. -/
theorem perfect_complex_descends
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ i : I, IsNoetherianRing (R.obj i)]
    (c : Cocone R) (hc : IsColimit c)
    (i : I) (Xi : Scheme.{u}) (s : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (E : schemeDerivedCategory (pullback s (Spec.map (c.ι.app i))))
    (hE : (pullback s (Spec.map (c.ι.app i))).IsPerfect E) :
    ∃ (j : I) (hij : i ≤ j)
      (Ej : schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE hij))))),
      (pullback s (Spec.map (R.map (homOfLE hij)))).IsPerfect Ej ∧
      Nonempty ((derivedPullback (baseChangeMap s
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (c.ι.app i)))
          (Over.homMk (Spec.map (c.ι.app j))
            (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])))).obj Ej ≅ E) := by
  sorry

end AlgebraicGeometry
