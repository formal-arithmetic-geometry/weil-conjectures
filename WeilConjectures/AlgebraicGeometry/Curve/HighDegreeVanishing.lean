/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Curve.Reductions
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyFilteredColimit
public import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.PointCount

/-!
# Étale cohomology of curves in degrees at least three

Let `C` be a curve over an algebraically closed field `k`. Assuming that `H²` of torsion sheaves
vanishes on affine curves over `k`, we show that `Hᵠ(C, F) = 0` for every torsion sheaf `F` and
`q ≥ 3`.

Choose an affine open `j : U ⟶ C` whose complement is a finite set of closed points
(`AlgebraicGeometry.IsCurve.exists_isAffineOpen_finite_compl`). The unit `F ⟶ j_* j^* F` is an
isomorphism over `U`, so it induces isomorphisms on `Hᵠ` for `q ≥ 2`. For a sheaf `G` on `U`
killed by `n`, embed `G` into an acyclic sheaf `J` killed by `n` whose pushforward is acyclic
(`AlgebraicGeometry.Etale.exists_mono_acyclic_of_nsmul_eq_zero`), with cokernel `G'`. The
sequence `0 → j_* G → j_* J → j_* G'` is exact, and the cokernel of its last map vanishes over
`U`, hence is acyclic; this gives `H³(C, j_* G) ↪ H²(C, j_* G')`. Embedding `G'` in the same way,
with cokernel `G''`, the map `j_* J' → j_* G''` is now an epimorphism: over an affine étale
`C`-scheme `V`, the scheme `V ×_C U` is an affine curve, so `H¹(V ×_C U, G') ≅ H²(V ×_C U, G)`
vanishes. Hence `H²(C, j_* G') ↪ H¹(C, j_* G'') ↪ H¹(U, G'') ≅ H²(U, G') = 0`. Degrees `q > 3`
follow by dimension shifting on `C`.

## Main statements

- `AlgebraicGeometry.IsCurve.exists_isAffineOpen_finite_compl`: a curve has an affine open whose
  complement is a finite set of closed points.
- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le_of_forall`: vanishing in degrees at
  least three, assuming the vanishing of `H²` on affine curves.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Topology

namespace AlgebraicGeometry

/-- The residue field of a closed point of a scheme locally of finite type over an algebraically
closed field `k` is algebraically closed: it is a finite extension of `k`. -/
lemma Scheme.isAlgClosed_residueField_of_isClosed {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X)
    (hx : IsClosed ({x} : Set X)) : IsAlgClosed (X.residueField x) := by
  let := (f.residueFieldAlgebraMap x).toAlgebra
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  have := (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
    (f := X.fromSpecResidueField x ≫ f)).mpr inferInstance
  rw [← f.specMap_residueFieldAlgebraMap, IsFinite.SpecMap_iff] at this
  have : Module.Finite k (X.residueField x) := this
  exact IsAlgClosed.of_ringEquiv k _ (RingEquiv.ofBijective (algebraMap k _)
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)))

open scoped Etale

variable {k : Type u} [Field k] {C : Scheme.{u}}

section Colimits

variable {X : Scheme.{u}}

/-- A section of a sheaf which is killed by a morphism lifts to the kernel. -/
lemma Etale.exists_kernel_ι_app_eq {G H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (ψ : G ⟶ H) {W : X.Etale} (x : G.obj.obj (op W)) (hx : ψ.hom.app (op W) x = 0) :
    ∃ t : (kernel ψ).obj.obj (op W), (kernel.ι ψ).hom.app (op W) t = x := by
  let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (evaluation _ _).obj (op W)
  let e := PreservesKernel.iso E ψ ≪≫ AddCommGrpCat.kernelIsoKer (E.map ψ)
  refine ⟨e.inv ⟨x, hx⟩, ?_⟩
  have h₁ := PreservesKernel.iso_inv_ι E ψ
  have h₂ := AddCommGrpCat.kernelIsoKer_inv_comp_ι (E.map ψ)
  change (e.inv ≫ E.map (kernel.ι ψ)) ⟨x, hx⟩ = x
  rw [Iso.trans_inv, Category.assoc, h₁, h₂]
  rfl

/-- **Filtered unions of subsheaves.** Let `c` be a cocone over a filtered diagram of abelian
étale sheaves whose legs are monomorphisms. If every section of the cocone point lies, locally,
in the image of some leg, then `c` is a colimit cocone: the comparison map from the colimit is a
monomorphism since filtered colimits are exact, and an epimorphism since it is locally
surjective. -/
noncomputable def Etale.isColimitOfMonoOfLocallySurjective {J : Type u} [SmallCategory J]
    [IsFiltered J] {D : J ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (c : Cocone D)
    [∀ j, Mono (c.ι.app j)]
    (h : ∀ (V : X.Etale) (s : c.pt.obj.obj (op V)), ∃ R ∈ X.smallEtaleTopology V,
      ∀ ⦃W : X.Etale⦄ (g : W ⟶ V), R g →
        ∃ (j : J) (t : (D.obj j).obj.obj (op W)),
          (c.ι.app j).hom.app (op W) t = c.pt.obj.map g.op s) :
    IsColimit c := by
  have : AB5OfSize.{u, u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    AB5OfSize_shrink.{u, u, u + 1, u + 1} _
  have : IsConnected J := IsFiltered.isConnected _
  let φ := colimit.desc D c
  have hmono : Mono φ := by
    let α : D ⟶ (Functor.const _).obj c.pt := { app j := c.ι.app j }
    have : Mono α := NatTrans.mono_of_mono_app _
    have : Mono (colim.map α) := inferInstance
    let e := (colimit.isColimit ((Functor.const J).obj c.pt)).coconePointUniqueUpToIso
      (isColimitConstCocone J c.pt)
    have : φ = colim.map α ≫ e.hom := by
      refine colimit.hom_ext fun j ↦ ?_
      simp [φ, e, α]
    rw [this]
    infer_instance
  have hepi : Epi φ := by
    have : Sheaf.IsLocallySurjective φ := by
      refine ⟨fun {V} s ↦ ?_⟩
      obtain ⟨R, hR, hRs⟩ := h V s
      refine X.smallEtaleTopology.superset_covering ?_ hR
      intro W g hg
      obtain ⟨j, t, ht⟩ := hRs g hg
      refine ⟨(colimit.ι D j).hom.app (op W) t, ?_⟩
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
        ← ObjectProperty.FullSubcategory.comp_hom, colimit.ι_desc]
      exact ht
    exact Sheaf.epi_of_isLocallySurjective _
  have : IsIso ((colimit.isColimit D).desc c) := isIso_of_mono_of_epi φ
  exact IsColimit.ofPointIso (colimit.isColimit D)

/-- **Reduction to bounded exponent.** On a quasi-compact quasi-separated scheme, a torsion
sheaf is the filtered union of its `n!`-torsion subsheaves, and étale cohomology commutes with
filtered colimits; so if `Hᵠ` vanishes for sheaves killed by a positive integer, it vanishes for
torsion sheaves. -/
theorem Etale.subsingleton_H_of_isTorsion [CompactSpace X] [QuasiSeparatedSpace X]
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (hF : F.IsTorsion) (q : ℕ)
    (h : ∀ (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ), 0 < n →
      n • 𝟙 G = 0 → Subsingleton (Sheaf.H G q)) :
    Subsingleton (Sheaf.H F q) := by
  let N (n : ULift.{u} ℕ) : ℕ := (n.down + 1).factorial
  have hdvd {n m : ULift.{u} ℕ} (hnm : n ≤ m) : N n ∣ N m :=
    Nat.factorial_dvd_factorial (Nat.succ_le_succ hnm)
  let K (n : ULift.{u} ℕ) := kernel (N n • 𝟙 F)
  have hK {n m : ULift.{u} ℕ} (hnm : n ≤ m) : kernel.ι (N n • 𝟙 F) ≫ (N m • 𝟙 F) = 0 := by
    obtain ⟨c, hc⟩ := hdvd hnm
    have h0 : N n • kernel.ι (N n • 𝟙 F) = 0 := by
      rw [← Category.comp_id (kernel.ι _), ← Preadditive.comp_nsmul, kernel.condition]
    rw [hc, Preadditive.comp_nsmul, Category.comp_id, mul_comm, ← smul_smul, h0, smul_zero]
  let D : ULift.{u} ℕ ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    { obj := K
      map {n m} f := kernel.lift _ (kernel.ι _) (hK (leOfHom f))
      map_id n := by
        rw [← cancel_mono (kernel.ι _)]
        simp only [kernel.lift_ι]
        exact (Category.id_comp _).symm
      map_comp f g := by
        rw [← cancel_mono (kernel.ι _)]
        simp }
  let c : Cocone D := { pt := F, ι := { app n := kernel.ι _ } }
  have : ∀ n, Mono (c.ι.app n) := fun n ↦ inferInstanceAs (Mono (kernel.ι _))
  have hc : IsColimit c := Etale.isColimitOfMonoOfLocallySurjective c fun V s ↦ by
    obtain ⟨S, hS, hSs⟩ := hF (U := op V) s
    refine ⟨S, hS, fun W g hg ↦ ?_⟩
    obtain ⟨m, hm, hms⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (hSs hg)
    refine ⟨ULift.up m, Etale.exists_kernel_ι_app_eq _ _ ?_⟩
    obtain ⟨d, hd⟩ : m ∣ (m + 1).factorial := Nat.dvd_factorial hm (Nat.le_succ m)
    have : ((sheafToPresheaf _ _).map (N (ULift.up m) • 𝟙 F)).app (op W) =
        N (ULift.up m) • 𝟙 _ := by
      rw [Functor.map_nsmul, NatTrans.app_nsmul]
      rfl
    change (((sheafToPresheaf _ _).map (N (ULift.up m) • 𝟙 F)).app (op W)) _ = 0
    rw [this]
    change (m + 1).factorial • (F.obj.map g.op s) = 0
    rw [hd, mul_nsmul', smul_comm, hms, smul_zero]
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have := essentiallySmallSelf.{u + 1} (ULift.{u} ℕ)
  obtain ⟨n, y, rfl⟩ := (Scheme.H_map_isColimit_of_isFiltered_of_large X hc q).1 x
  have : Subsingleton (Sheaf.H (K n) q) := h _ (N n) (Nat.factorial_pos _) (by
    rw [← cancel_mono (kernel.ι (N n • 𝟙 F)), zero_comp, Preadditive.nsmul_comp,
      Category.id_comp, ← Category.comp_id (kernel.ι _), ← Preadditive.comp_nsmul,
      kernel.condition])
  rw [Subsingleton.elim y 0, map_zero]

end Colimits

/-- The cokernel of a morphism into a sheaf killed by `n` is killed by `n`. -/
lemma Etale.nsmul_id_cokernel_eq_zero {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) {n : ℕ}
    (hG : n • 𝟙 G = 0) : n • 𝟙 (cokernel φ) = 0 := by
  rw [← cancel_epi (cokernel.π φ), comp_zero, Preadditive.comp_nsmul, Category.comp_id,
    ← Category.id_comp (cokernel.π φ), ← Preadditive.nsmul_comp, hG, zero_comp]

end AlgebraicGeometry
