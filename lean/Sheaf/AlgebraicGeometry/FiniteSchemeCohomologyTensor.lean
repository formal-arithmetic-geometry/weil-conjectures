/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups N1, J3
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.FiniteOverField
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.Cohomology.Clopen
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison

/-! # Cohomology and tensor invariance on a finite scheme

Source: Stacks Project, varieties.tex, Tag 0AYT, parts (3)--(5), rank one
(blueprint: lem-pc-finite-scheme-cohomology-tensor).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

private theorem finrankH_zero (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (M : X.Modules) :
    M.finrankH k 0 = @Module.finrank k Γ(M, ⊤) _ _
      (Module.compHom Γ(M, ⊤) (globalSectionsRingHom k (X := X))) := by
  let _ := Module.compHom Γ(M, ⊤) (globalSectionsRingHom k (X := X))
  let e : M.H 0 ≃ₗ[k] Γ(M, ⊤) :=
    { (H.zeroLinearEquiv M).toAddEquiv with
      map_smul' c x := (H.zeroLinearEquiv M).map_smul (globalSectionsRingHom k c) x }
  exact e.finrank_eq

private theorem tensor_iso_of_discrete {X : Scheme.{u}} [Finite X] [DiscreteTopology X]
    (G L : X.Modules) [L.IsInvertible] : Nonempty (G ⊗ₘ L ≅ G) := by
  classical
  let _ := Fintype.ofFinite X
  let e := Fintype.equivFin X
  let U (i : Fin (Fintype.card X)) : X.Opens := ⟨{e.symm i}, isOpen_discrete _⟩
  have hU : _root_.Pairwise (Function.onFun Disjoint U) := by
    intro i j hij
    change Disjoint (U i) (U j)
    rw [← TopologicalSpace.Opens.coe_disjoint]
    exact Set.disjoint_singleton.mpr (e.symm.injective.ne hij)
  have hcover : ⨆ i, U i = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨e x, by simp [U]⟩
  have : HasFiniteBiproducts X.Modules := Abelian.hasFiniteBiproducts
  let localIso (i : Fin (Fintype.card X)) :
      (restrictFunctor (U i).ι).obj (G ⊗ₘ L) ≅ (restrictFunctor (U i).ι).obj G := by
    have : Subsingleton (U i) := ⟨fun a b ↦ Subtype.ext (a.2.trans b.2.symm)⟩
    let t := (IsInvertible.nonempty_iso_unit
      (⟨e.symm i, rfl⟩ : U i) ((pullback (U i).ι).obj L)).some
    let s := (nonempty_pullback_tensorObj_iso (U i).ι G L).some
    exact (restrictFunctorIsoPullback (U i).ι).app _ ≪≫ s ≪≫
      (Iso.refl _ ⊗ᵢ t) ≪≫ ρ_ _ ≪≫ ((restrictFunctorIsoPullback (U i).ι).app G).symm
  let a : G ⊗ₘ L ≅ ⨁ fun i ↦
      (restrictFunctor (U i).ι ⋙ pushforward (U i).ι).obj (G ⊗ₘ L) :=
    @asIso _ _ _ _ (biproduct.lift fun i ↦
      (restrictAdjunction (U i).ι).unit.app (G ⊗ₘ L))
      (isIso_biproduct_lift_restrictAdjunction_unit U hU hcover (G ⊗ₘ L))
  let b : G ≅ ⨁ fun i ↦ (restrictFunctor (U i).ι ⋙ pushforward (U i).ι).obj G :=
    @asIso _ _ _ _ (biproduct.lift fun i ↦ (restrictAdjunction (U i).ι).unit.app G)
      (isIso_biproduct_lift_restrictAdjunction_unit U hU hcover G)
  exact ⟨a ≪≫ biproduct.mapIso (fun i ↦ (pushforward (U i).ι).mapIso (localIso i)) ≪≫ b.symm⟩

/-- On the spectrum of a finite-dimensional algebra, higher module cohomology vanishes,
global sections are finite dimensional, and tensoring with an invertible module preserves
their dimension and the Euler characteristic. Scalar restriction uses the given algebra
map, and the Euler characteristic uses its induced structure morphism.
Source: Stacks Project, varieties.tex, Tag 0AYT, parts (3)--(5), rank one
(blueprint: lem-pc-finite-scheme-cohomology-tensor).

Proof:
1. A finite basis makes A finite over k (`def-weil-finite-dimensional-subspace`). By
   `lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum`, Spec A is finite discrete.
   Chains of ideals terminate by dimension, so A is Noetherian and Spec A locally
   Noetherian (`pqf-def-locnoeth`).
2. Coherence gives quasi-coherence and finite type (`pqf-lem-coherent-ft-locnoeth`). By
   `lem-weil-pbc-quasi-coherent-finite-type-affine`, global sections are finite over A,
   hence finite over k by `lem-weil-pbc-finite-module-over-finite-algebra`.
3. Restrict to the disjoint singleton cover. Each restriction of L is trivial, so
   pullback compatibility with tensor and the right unitor identify the restrictions of
   G tensor L and G. The disjoint-cover biproduct decompositions assemble these into an
   isomorphism G tensor L ≅ G. This construction also works for the empty spectrum.
4. Evaluate the isomorphism on global sections and restrict scalars along k → A → Γ(T,O).
   Its inverse transfers finite dimensionality; the linear equivalence gives equal finranks.
5. Affine quasi-coherent vanishing (`lem-pc-affine-vanishing`) gives vanishing of the source
   Ext model H in positive degrees. The natural comparison
   (`lem-sc-module-cohomology-source-comparison`) transfers this to module-derived sections.
   The isomorphism from step 3 transfers vanishing to G tensor L.
6. All positive terms of the Euler sum vanish, so only degree zero remains. The linear
   equivalence H.zeroLinearEquiv identifies H⁰ with global sections. Naturality of ΓSpecIso
   identifies the scalar action from the structure morphism with the explicitly specified
   restricted action. Finally eulerChar_congr transfers the Euler characteristic along
   the isomorphism from step 3. No separate proper-cohomology finiteness theorem is needed. -/
theorem finiteSchemeCohomologyTensor
    {k A : Type u} [Field k] [CommRing A] [Algebra k A] [FiniteDimensional k A]
    (G L : (Spec (.of A)).Modules)
    (hG : RingedSpace.IsCoherent (Spec (.of A)).toRingedSpace G)
    (hL : L.IsInvertible) :
    (∀ q : ℕ, 0 < q →
      IsZero ((RingedSpace.moduleCohomology (Spec (.of A)).toRingedSpace q).obj G)) ∧
    (∀ q : ℕ, 0 < q →
      IsZero ((RingedSpace.moduleCohomology (Spec (.of A)).toRingedSpace q).obj (G ⊗ₘ L))) ∧
    @FiniteDimensional k Γ(G, ⊤) _ _
      (Module.compHom Γ(G, ⊤)
        ((Scheme.ΓSpecIso (.of A)).inv.hom.comp (algebraMap k A))) ∧
    @FiniteDimensional k Γ(G ⊗ₘ L, ⊤) _ _
      (Module.compHom Γ(G ⊗ₘ L, ⊤)
        ((Scheme.ΓSpecIso (.of A)).inv.hom.comp (algebraMap k A))) ∧
    @Module.finrank k Γ(G ⊗ₘ L, ⊤) _ _
      (Module.compHom Γ(G ⊗ₘ L, ⊤)
        ((Scheme.ΓSpecIso (.of A)).inv.hom.comp (algebraMap k A))) =
      @Module.finrank k Γ(G, ⊤) _ _
        (Module.compHom Γ(G, ⊤)
          ((Scheme.ΓSpecIso (.of A)).inv.hom.comp (algebraMap k A))) ∧
    @eulerChar k _ (Spec (.of A)) ⟨Spec.map (CommRingCat.ofHom (algebraMap k A))⟩ G =
      (@Module.finrank k Γ(G, ⊤) _ _
        (Module.compHom Γ(G, ⊤)
          ((Scheme.ΓSpecIso (.of A)).inv.hom.comp (algebraMap k A))) : ℤ) ∧
    @eulerChar k _ (Spec (.of A)) ⟨Spec.map (CommRingCat.ofHom (algebraMap k A))⟩ (G ⊗ₘ L) =
      @eulerChar k _ (Spec (.of A)) ⟨Spec.map (CommRingCat.ofHom (algebraMap k A))⟩ G := by
  classical
  let X := Spec (.of A)
  have : IsNoetherianRing A := IsNoetherianRing.of_finite k A
  have : IsLocallyNoetherian X := inferInstance
  have hqc := (isCoherent_iff_isQuasicoherent_and_isFiniteType X G).mp hG
  have : G.IsQuasicoherent := hqc.1
  have : G.IsFiniteType := hqc.2
  have : Module.Finite Γ(X, ⊤) Γ(G, ⊤) := finite_sections_of_finiteType G (isAffineOpen_top X)
  let _ : Module A Γ(G, ⊤) := Module.compHom Γ(G, ⊤) (Scheme.ΓSpecIso (.of A)).inv.hom
  have : Module.Finite A Γ(G, ⊤) := finite_sections_top_of_finite G
  let _ : Module k Γ(G, ⊤) := Module.compHom Γ(G, ⊤)
    ((Scheme.ΓSpecIso (.of A)).inv.hom.comp (algebraMap k A))
  have : IsScalarTower k A Γ(G, ⊤) := ⟨fun r a m ↦ by
    rw [Algebra.smul_def]
    change ((Scheme.ΓSpecIso (.of A)).inv.hom (algebraMap k A r * a)) • m = _
    rw [map_mul, mul_smul]
    rfl⟩
  have hfinite : FiniteDimensional k Γ(G, ⊤) := Module.Finite.trans A Γ(G, ⊤)
  let f := Spec.map (CommRingCat.ofHom (algebraMap k A))
  have : IsFinite f := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  obtain ⟨hfin, hdisc⟩ := finite_and_discreteTopology_of_isFinite f
  have : L.IsInvertible := hL
  obtain ⟨e⟩ := tensor_iso_of_discrete G L
  have vanish (q : ℕ) (hq : 0 < q) :
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace q).obj G) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
    have : Subsingleton (G.H (n + 1)) := subsingleton_H_succ_of_isAffine G n
    obtain ⟨c, _⟩ := exists_moduleCohomology_source_comparison X (n + 1)
    have : Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace (n + 1)).obj G) :=
      (c G).injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  let es : Γ(G ⊗ₘ L, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(G, ⊤) :=
    appLinearEquivOfIso e ⊤
  let _ : Module k Γ(G ⊗ₘ L, ⊤) := Module.compHom Γ(G ⊗ₘ L, ⊤)
    ((Scheme.ΓSpecIso (.of A)).inv.hom.comp (algebraMap k A))
  let esk : Γ(G ⊗ₘ L, ⊤) ≃ₗ[k] Γ(G, ⊤) :=
    { es.toAddEquiv with
      map_smul' r m := by
        exact es.map_smul
          (((Scheme.ΓSpecIso (.of A)).inv.hom.comp (algebraMap k A)) r) m }
  let _ : (Spec (.of A)).Over (Spec (.of k)) := ⟨f⟩
  have hscalar : globalSectionsRingHom k (X := X) =
      (Scheme.ΓSpecIso (.of A)).inv.hom.comp (algebraMap k A) := by
    change ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom = _
    simpa only [f, CommRingCat.hom_comp, CommRingCat.hom_ofHom] using
      congrArg CommRingCat.Hom.hom
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k A))).symm
  have hz := finrankH_zero k G
  rw [hscalar] at hz
  have heuler : eulerChar k G = (Module.finrank k Γ(G, ⊤) : ℤ) := by
    have hv (q : ℕ) (hq : 0 < q) : Subsingleton (G.H q) := by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
      exact subsingleton_H_succ_of_isAffine G n
    rw [eulerChar_eq_sum_range_of_subsingleton k G (D := 0) hv]
    simpa only [zero_add, Finset.sum_range_one, pow_zero, one_mul, finrankH]
      using congrArg (fun n : ℕ ↦ (n : ℤ)) hz
  refine ⟨vanish, ?_, hfinite, esk.symm.finiteDimensional, esk.finrank_eq, heuler, ?_⟩
  · intro q hq
    exact (vanish q hq).of_iso ((RingedSpace.moduleCohomology X.toRingedSpace q).mapIso e)
  · exact eulerChar_congr k e

end AlgebraicGeometry.Scheme.Modules
