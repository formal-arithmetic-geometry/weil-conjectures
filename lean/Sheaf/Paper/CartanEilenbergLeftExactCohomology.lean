module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Exact

/-! # Left exact functors and cohomology

Source: literature/stacks-project/derived.tex, Lemma 015I (lemma-cartan-eilenberg), using the
split short exact sequences from injectivity
(blueprint: lem-sp-cart-eilenberg-left-exact-cohomology)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CategoryTheory

/-- If all cycles `Z^q(C)` and boundaries `B^q(C) = im(d^{q-1})` of a bounded-below complex are
injective, then for an additive left exact functor `G` the canonical comparison
`H^q(G(C)) → G(H^q(C))` induced by the maps on cycles and quotients is an isomorphism: there is
an isomorphism `φ` whose composite with the cycle map `G(Z^q(C)) → Z^q(G(C))` (lifting
`G(Z^q(C) ↪ C^q)`) and the projection `Z^q(G(C)) → H^q(G(C))` is `G` of the projection
`Z^q(C) → H^q(C)`; since the cycle map is an isomorphism and the projection is epi, this
equation determines `φ` as the canonical comparison.
Source: literature/stacks-project/derived.tex, Lemma 015I (lemma-cartan-eilenberg)
(blueprint: lem-sp-cart-eilenberg-left-exact-cohomology)

Proof: fix `q`. The short exact sequences `0 → B^q → Z^q → H^q → 0` and
`0 → Z^q → C^q → B^{q+1} → 0` split because their subobjects `B^q` and `Z^q` are injective.
Applying the additive left exact functor `G` preserves the splittings; left exactness identifies
`ker(G(C^q) → G(C^{q+1}))` with `G(Z^q)`, and the image of `G(C^{q-1}) → G(C^q)` is `G(B^q)`, so
`0 → G(B^q) → G(Z^q) → G(H^q) → 0` is split exact and the comparison induced by the maps on
cycles and quotients is an isomorphism `H^q(G(C)) ≅ G(H^q(C))`. -/
theorem cartanEilenberg_leftExact_cohomology
    {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B]
    (C : CochainComplex A ℤ)
    (hbounded : ∃ n : ℤ, ∀ q : ℤ, q < n → IsZero (C.X q))
    (hcycles : ∀ q : ℤ, Injective (C.cycles q))
    (hboundaries : ∀ q : ℤ, Injective (image (C.d (q - 1) q)))
    (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G] :
    ∀ q : ℤ, ∃ φ : ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj C).homology q ≅
        G.obj (C.homology q),
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj C).liftCycles
          (G.map (C.iCycles q)) (q + 1) (by simp)
          (by simp [← G.map_comp]) ≫
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj C).homologyπ q ≫ φ.hom =
      G.map (C.homologyπ q) := by
  obtain ⟨n, hn⟩ := hbounded
  intro q
  let i := (ComplexShape.up ℤ).prev q
  let k := (ComplexShape.up ℤ).next q
  let d := C.d i q
  let p := factorThruImage d
  let b : image d ⟶ C.cycles q := C.liftCycles (image.ι d) k rfl
    (image_ι_comp_eq_zero (C.d_comp_d i q k))
  have hb : b ≫ C.iCycles q = image.ι d := by
    dsimp [b]
    simp
  have : Mono b := mono_of_mono_fac hb
  have hpb : p ≫ b = C.toCycles i q := by
    rw [← cancel_mono (C.iCycles q), Category.assoc, hb, C.toCycles_i]
    exact image.fac d
  have hbπ : b ≫ C.homologyπ q = 0 := by
    rw [← cancel_epi p, ← Category.assoc, hpb, C.toCycles_comp_homologyπ, comp_zero]
  let T := ShortComplex.mk b (C.homologyπ q) hbπ
  have hT : T.ShortExact := by
    let S := ShortComplex.mk (C.toCycles i q) (C.homologyπ q)
      (C.toCycles_comp_homologyπ i q)
    have hS : S.Exact := S.exact_of_g_is_cokernel (C.homologyIsCokernel i q rfl)
    let φ : S ⟶ T :=
      { τ₁ := p
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by simpa [S, T] using hpb }
    exact ⟨(ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp hS⟩
  have : Injective T.X₁ := by
    have hprev : i = q - 1 :=
      (ComplexShape.up ℤ).prev_eq' (by simp [ComplexShape.up])
    change Injective (image (C.d i q))
    rw [hprev]
    exact hboundaries q
  let t := hT.splittingOfInjective (C := A)
  have wi : C.iCycles i ≫ d = 0 := C.iCycles_d _ _
  let U := ShortComplex.mk (C.iCycles i) d wi
  have hU : U.Exact := U.exact_of_f_is_kernel (C.cyclesIsKernel _ _ (by simp [i]))
  have wp : C.iCycles i ≫ p = 0 := comp_factorThruImage_eq_zero wi
  let V := ShortComplex.mk (C.iCycles i) p wp
  have hV : V.ShortExact :=
    ⟨V.exact_of_g_is_cokernel hU.isColimitImage⟩
  have : Injective V.X₁ := hcycles i
  let v := hV.splittingOfInjective
  have : Epi (G.map p) := (v.map G).epi_g
  let D := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj C
  have wiG : G.map (C.iCycles q) ≫ (D.sc q).g = 0 := by
    simp [D, ← G.map_comp]
  let hi : IsLimit (KernelFork.ofι (G.map (C.iCycles q)) wiG) :=
    isLimitForkMapOfIsLimit' G (C.iCycles_d q k)
      (C.cyclesIsKernel q _ rfl)
  have hf' : hi.lift (KernelFork.ofι (D.sc q).f (D.sc q).zero) =
      G.map (C.toCycles i q) := by
    apply Fork.IsLimit.hom_ext hi
    calc
      _ = (D.sc q).f := Fork.IsLimit.lift_ι hi
      _ = _ := by
        change G.map (C.d i q) = G.map (C.toCycles i q) ≫ G.map (C.iCycles q)
        rw [← G.map_comp, C.toCycles_i]
  have wπG : hi.lift (KernelFork.ofι (D.sc q).f (D.sc q).zero) ≫
      G.map (C.homologyπ q) = 0 := by
    rw [hf', ← G.map_comp, C.toCycles_comp_homologyπ, G.map_zero]
  have hπG : IsColimit (CokernelCofork.ofπ (G.map (C.homologyπ q)) wπG) := by
    have fac : hi.lift (KernelFork.ofι (D.sc q).f (D.sc q).zero) =
        G.map p ≫ G.map b := by
      rw [hf', ← G.map_comp, hpb]
    exact isCokernelEpiComp (t.map G).gIsCokernel (G.map p) fac
  let h : (D.sc q).LeftHomologyData :=
    { K := G.obj (C.cycles q)
      H := G.obj (C.homology q)
      i := G.map (C.iCycles q)
      π := G.map (C.homologyπ q)
      wi := wiG
      hi := hi
      wπ := wπG
      hπ := hπG }
  refine ⟨h.homologyIso, ?_⟩
  change (D.sc q).liftCycles (G.map (C.iCycles q)) _ ≫
    (D.sc q).homologyπ ≫ h.homologyIso.hom = G.map (C.homologyπ q)
  rw [h.homologyπ_comp_homologyIso_hom, ← Category.assoc]
  have hcan : (D.sc q).liftCycles (G.map (C.iCycles q)) wiG ≫ h.cyclesIso.hom = 𝟙 _ := by
    rw [← cancel_mono h.i, Category.assoc, h.cyclesIso_hom_comp_i]
    simp [h]
  rw [hcan, Category.id_comp]

end CategoryTheory
