/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
import Sheaf.AlgebraicGeometry.CompactFlatBarUnionAugmentation

/-! # Bar enlargement of a split compact-generator tower

Source: finite-piece and target-chain bar argument in
`lem-sc-flat-telescope-target-refinement`, following the generator resolution.
(blueprint: lem-sc-compact-flat-telescope-bar-enlargement).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
namespace AlgebraicGeometry


-- The finite recurrence of FilteredFreeTelescopeSplitting, used for sheaves as well.
private theorem sequential_sum_retraction {C : Type*} [Category C] [Preadditive C]
    (F : ℕ → C) (D : C) (j : ∀ n, F n ⟶ D)
    (hD : IsColimit (Cofan.mk D j)) (step : ∀ n, F n ⟶ F (n + 1))
    (d : D ⟶ D) (hd : ∀ n, j n ≫ d = j n - step n ≫ j (n + 1))
    (hsplit : ∀ n, ∃ r : F (n + 1) ⟶ F n, step n ≫ r = 𝟙 (F n)) :
    ∃ r : D ⟶ D, d ≫ r = 𝟙 D := by
  classical
  choose r hr using hsplit
  let t : ∀ n, F n ⟶ D := fun n ↦
    Nat.rec (motive := fun n ↦ F n ⟶ D) 0 (fun n t ↦ r n ≫ (t - j n)) n
  let b : D ⟶ D := Cofan.IsColimit.desc hD t
  refine ⟨b, Cofan.IsColimit.hom_ext hD _ _ (fun n ↦ ?_)⟩
  change j n ≫ (d ≫ b) = j n ≫ 𝟙 D
  rw [← Category.assoc, hd, Preadditive.sub_comp, Category.assoc]
  rw [show j n ≫ b = t n from Cofan.IsColimit.fac hD t n,
    show j (n + 1) ≫ b = t (n + 1) from Cofan.IsColimit.fac hD t (n + 1)]
  simp only [Category.comp_id]
  change t n - step n ≫ (r n ≫ (t n - j n)) = j n
  rw [← Category.assoc, hr, Category.id_comp]
  exact sub_sub_cancel _ _

private theorem split_telescope_cokernel (Y : Scheme.{u})
    (F : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (u : ∀ n : ℕ, F n ⟶ F (n + 1))
    (hsplit : ∀ (n : ℕ) (i : ℤ), IsSplitMono ((u n).f i)) :
    ∀ i : ℤ, Nonempty
      (((ShortComplex.mk (flatTelescopeDifferential F u)
        (cokernel.π (flatTelescopeDifferential F u))
        (cokernel.condition (flatTelescopeDifferential F u))).map
          (HomologicalComplex.eval _ (ComplexShape.up ℤ) i)).Splitting) := by
  intro i
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let ev := HomologicalComplex.eval A (ComplexShape.up ℤ) i
  let d := flatTelescopeDifferential F u
  let S := ShortComplex.mk d (cokernel.π d) (cokernel.condition d)
  let G : ℕ → A := fun n ↦ (F n).X i
  let D := (∐ F).X i
  let j : ∀ n, G n ⟶ D := fun n ↦ (Sigma.ι F n).f i
  have hD : IsColimit (Cofan.mk D j) :=
    (Cofan.isColimitMapCoconeEquiv ev F (Cofan.mk _ (Sigma.ι F)))
      (isColimitOfPreserves ev (coproductIsCoproduct F))
  have hd (n : ℕ) : j n ≫ d.f i = j n - (u n).f i ≫ j (n + 1) := by
    have h : Sigma.ι F n ≫ d = Sigma.ι F n - u n ≫ Sigma.ι F (n + 1) := by
      simp [d, flatTelescopeDifferential, Preadditive.comp_sub]
    exact congrArg (fun f ↦ f.f i) h
  have hr (n : ℕ) : ∃ r : G (n + 1) ⟶ G n, (u n).f i ≫ r = 𝟙 (G n) := by
    have := hsplit n i
    exact ⟨retraction ((u n).f i), IsSplitMono.id ((u n).f i)⟩
  obtain ⟨r, hdr⟩ := sequential_sum_retraction G D j hD
    (fun n ↦ (u n).f i) (d.f i) hd hr
  have hS : S.Exact := S.exact_of_g_is_cokernel (cokernelIsCokernel d)
  have hSev : (S.map ev).Exact := hS.map_of_epi_of_preservesCokernel ev
    (by dsimp [S]; infer_instance) (by infer_instance)
  have hg : Epi (S.map ev).g := by
    change Epi (ev.map (cokernel.π d))
    exact epi_of_isColimit_cofork
      (CokernelCofork.mapIsColimit _ (cokernelIsCokernel d) ev)
  exact ⟨ShortComplex.Splitting.ofExactOfRetraction (S.map ev) hSev r hdr hg⟩

/-- A split bounded-above compact-generator tower augmented into a flat telescope
admits a flat bar refinement and a split presentation of its enlarged bar total.
The input has the compact-generator structure needed for the finite-piece argument;
no resolution of a general input tower is asserted here.

Source: `lem-sc-flat-telescope-target-refinement`, proof from "Close finite sets"
through the final augmentation identity; the agent-written finite-piece bar argument
of `lem-sc-flat-telescope-arrow-bar-data`.

Proof. Fix generator decompositions in each term. Starting with finitely many
summands in finitely many degrees, close under the differential upwards: each
summand maps through finitely many next-degree summands by hgen. The upper bound
ends the procedure, producing finite subcomplexes. Keep stage-labelled copies of
these subcomplexes for stages at most n, with an arrow when the transition carries
one into the other. A finite subcomplex at an earlier stage maps into a finite
subcomplex at stage n: factor its finitely many generator terms through finite
subcoproducts, then close under the differential. Thus the stage-n subdiagram is
cofinal in this filtered diagram D_n, whose colimit is L_n. No compatibility of
generator decompositions across stages is required, and sums of images are never
assumed flat. Each diagram object retains its finite generator terms.
The unnormalized bar total
R_n of D_n is bounded above and flat; its augmentation c_n is a quasi-isomorphism
by exactness of filtered colimits of module sheaves. Simplicial degree p has
cochain degree -p; the common upper bound for the finite initial tower segment
makes the associated total-complex argument legitimate. Inclusions give s_n.

Write T as the supplied telescope and take finite cone blocks C_k, using domain
indices at most k and codomain indices at most k+1. They are bounded above and
flat, with split inclusions and union T. Each finite source subcomplex maps through
some C_k by finite support in each of its finitely many degrees. Monicity into T
makes that factor a chain map. Adjoin the target chain to the union of D_n, with
arrows from a source object to every block through which it factors. The least
factorization index is monotone and left adjoint to the target-chain inclusion.
Inserting the adjunction unit in bar strings, with alternating signs, gives a
homotopy equivalence from the enlarged bar total to the target-chain bar total.

Let F_n be the bar total on D_n and target indices at most n. Bar inclusions give
u and a, and satisfy the two transition identities strictly. The union bar total
has the degreewise split exact presentation by 1-shift on the sum of F_n: a
simplex's first stage splits the augmentation, and the finite-support recurrence
identifies its kernel. This gives exactly the displayed degreewise splittings; the cone calculation
is left to the caller. Compare the target-chain bar resolution of the augmented constant
right functor with its two-term representable resolution by 1-shift. Successive
projective lifts give maps and homotopies lifting the identity of that functor;
tensor with C_k. Every homotopy is finite on each input, so totalization is valid.
The finite-block telescope maps homotopy equivalently to T by the same split
exact-sequence cone calculation. Cancel the target-chain bar equivalence to see
that the enlarged bar augmentation into T is a homotopy equivalence.
Use that canonical bar augmentation as e, and the sum of stage inclusions
as b. The finite-support recurrence gives hzero and the splittings. Naturality
with a gives the displayed sum identity. Include the zero subcomplex to handle empty
source diagrams. Every construction is existential, not a choice in a definition.
(blueprint: lem-sc-compact-flat-telescope-bar-enlargement). -/
theorem exists_compact_flat_telescope_bar_enlargement (Y : Scheme.{u})
    (L : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (l : ∀ n : ℕ, L n ⟶ L (n + 1))
    (hb : ∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((L n).X i))
    (hsplit : ∀ (n : ℕ) (i : ℤ), IsSplitMono ((l n).f i))
    (hgen :
      ∀ (n : ℕ) (i : ℤ), ∃ (I : Type u)
        (G : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace)),
        Nonempty ((L n).X i ≅ ∐ G) ∧
        (∀ j : I, SheafOfModules.IsFlat (G j)) ∧
        ∀ (j : I) (K : Type u)
          (H : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
          (f : G j ⟶ ∐ H),
          ∃ (S : Finset K) (g : G j ⟶ ∐ (fun k : {k // k ∈ S} ↦ H k.1)),
            g ≫ Sigma.desc (fun k : {k // k ∈ S} ↦ Sigma.ι H k.1) = f)
    (T : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hT : isFlatTelescope Y T) (p : ∀ n : ℕ, L n ⟶ T)
    (hp : ∀ n : ℕ, l n ≫ p (n + 1) = p n) :
    let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
    let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
    ∃ (R F : ℕ → CochainComplex A ℤ)
      (s : ∀ n : ℕ, R n ⟶ R (n + 1))
      (u : ∀ n : ℕ, F n ⟶ F (n + 1))
      (c : ∀ n : ℕ, R n ⟶ L n) (a : ∀ n : ℕ, R n ⟶ F n),
      (∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((R n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((R n).X i)) ∧
      (∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((F n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((F n).X i)) ∧
      (∀ n : ℕ, QuasiIso (c n)) ∧
      (∀ n : ℕ, s n ≫ c (n + 1) = c n ≫ l n) ∧
      (∀ n : ℕ, s n ≫ a (n + 1) = a n ≫ u n) ∧
      ∃ (B : CochainComplex A ℤ) (b : (∐ F) ⟶ B) (e : B ⟶ T)
        (hzero : flatTelescopeDifferential F u ≫ b = 0),
        (∀ i : ℤ, Nonempty
          (((ShortComplex.mk (flatTelescopeDifferential F u) b hzero).map
            (HomologicalComplex.eval A (ComplexShape.up ℤ) i)).Splitting)) ∧
        IsIso (Q.map e) ∧
        Limits.Sigma.map a ≫ b ≫ e = Sigma.desc (fun n : ℕ ↦ c n ≫ p n) := by
  obtain ⟨D⟩ := exists_compact_flat_finite_subcomplex_diagrams Y L l hb hsplit hgen
  obtain ⟨R, F, s, u, c, a, hbR, hfR, hbF, hfF, hc, hs, ha, hu, q, hq, haq, he⟩ :=
    exists_compact_flat_bar_union_augmentation Y L l D T hT p hp
  let d := flatTelescopeDifferential F u
  have hzero : d ≫ Sigma.desc q = 0 := by
    apply Sigma.hom_ext
    intro n
    simp [d, flatTelescopeDifferential, Preadditive.comp_sub, Preadditive.sub_comp,
      Category.assoc, hq]
  let e := cokernel.desc d (Sigma.desc q) hzero
  refine ⟨R, F, s, u, c, a, hbR, hfR, hbF, hfF, hc, hs, ha,
    cokernel d, cokernel.π d, e, cokernel.condition d,
    split_telescope_cokernel Y F u hu, he hzero, ?_⟩
  dsimp [e]
  rw [cokernel.π_desc]
  apply Sigma.hom_ext
  intro n
  simp only [Sigma.ι_map_assoc, Sigma.ι_desc, haq]


end AlgebraicGeometry
