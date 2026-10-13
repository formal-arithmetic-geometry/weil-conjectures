module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.Paper.ShiftedKoszulAugmentation
import Mathlib.LinearAlgebra.ExteriorPower.Basis

@[expose] public section

universe a b
open CategoryTheory
namespace AlgebraicGeometry

-- The finite-basis argument follows the proved helpers in
-- Sheaf.AlgebraicGeometry.AffineKoszulGeometricProperties.
private theorem koszul_term_free (A : Type a) [CommRing A] (r q : ℕ)
    (U : (Spec (.of A)).Opens) :
    ∃ m : ℕ, Nonempty
      ((SheafOfModules.overFunctor.{a} (moduleRings (Spec (.of A)).toRingedSpace) U).obj
        ((tilde.functor (.of A)).obj (ModuleCat.of A (⋀[A]^q (Fin r →₀ A)))) ≅
        SheafOfModules.free
          (R := (moduleRings (Spec (.of A)).toRingedSpace).over U) (ULift.{a} (Fin m))) := by
  classical
  let I := Set.powersetCard (Fin r) q
  let b := (Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower q
  let e : I ≃ ULift.{a} (Fin (Fintype.card I)) :=
    (Fintype.equivFin I).trans Equiv.ulift.symm
  let c := (b.reindex e).repr.toModuleIso
  let F := SheafOfModules.overFunctor.{a}
    (moduleRings (Spec (.of A)).toRingedSpace) U
  refine ⟨Fintype.card I, ⟨?_⟩⟩
  exact F.mapIso ((tilde.functor (.of A)).mapIso c ≪≫
      tildeFinsupp (ULift.{a} (Fin (Fintype.card I)))) ≪≫
    (SheafOfModules.mapFreeIso F (ULift.{a} (Fin (Fintype.card I))) (Iso.refl _)).symm

private theorem koszul_term_zero (A : Type a) [CommRing A] (r q : ℕ) (hq : r < q) :
    Limits.IsZero (ModuleCat.of A (⋀[A]^q (Fin r →₀ A))) := by
  classical
  let b := (Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower q
  have : IsEmpty (Set.powersetCard (Fin r) q) := ⟨fun s ↦ by
    have h := Finset.card_le_univ s.val
    have hs : s.val.card = q := s.property
    simp only [Fintype.card_fin, hs] at h
    omega⟩
  have : Subsingleton (⋀[A]^q (Fin r →₀ A)) :=
    b.repr.injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

private theorem shifted_koszul_strictly_perfect (A : Type a) [CommRing A] (r : ℕ)
    (f : Fin r → A) (U : (Spec (.of A)).Opens) :
    let K := ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{a} A)
      (SheafOfModules.{a} (moduleRings (Spec (.of A)).toRingedSpace))
      _ _ _ _ (tilde.functor (.of A))
      ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
      (shiftedKoszulComplex A r f))
    Scheme.IsStrictlyPerfect (Spec (.of A)) U
      (((SheafOfModules.overFunctor.{a}
        (moduleRings (Spec (.of A)).toRingedSpace) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) := by
  classical
  let L := shiftedKoszulChain A r f
  let T := tilde.functor (.of A)
  let : T.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let F := SheafOfModules.overFunctor.{a}
    (moduleRings (Spec (.of A)).toRingedSpace) U
  have hpos (n : ℤ) (hn : 0 < n) :
      Limits.IsZero (F.obj (T.obj ((L.extend ComplexShape.embeddingDownNat).X n))) := by
    apply F.map_isZero
    apply T.map_isZero
    apply L.isZero_extend_X
    intro q
    change -(q : ℤ) ≠ n
    omega
  have hneg (n : ℤ) (hn : n ≤ 0) : ∃ q : ℕ, -(q : ℤ) = n := by
    exact ⟨(-n).toNat, by omega⟩
  refine ⟨⟨-(r : ℤ), 0, ?_⟩, ?_⟩
  · intro n hn
    change Limits.IsZero (F.obj (T.obj ((L.extend ComplexShape.embeddingDownNat).X n)))
    by_cases hp : 0 < n
    · exact hpos n hp
    · obtain ⟨q, hq⟩ := hneg n (by omega)
      have hrq : r < q := by omega
      exact (F.map_isZero (T.map_isZero (koszul_term_zero A r (q + 1) (by omega)))).of_iso
        (F.mapIso (T.mapIso (L.extendXIso ComplexShape.embeddingDownNat hq)))
  · intro n
    change ∃ m : ℕ, ∃ (ι : F.obj (T.obj
        ((L.extend ComplexShape.embeddingDownNat).X n)) ⟶ _)
      (π : _ ⟶ F.obj (T.obj ((L.extend ComplexShape.embeddingDownNat).X n))),
        ι ≫ π = 𝟙 _
    by_cases hp : 0 < n
    · exact ⟨0, 0, 0, (hpos n hp).eq_of_src _ _⟩
    · obtain ⟨q, hq⟩ := hneg n (by omega)
      obtain ⟨m, ⟨e⟩⟩ := koszul_term_free A r (q + 1) U
      let e' := F.mapIso (T.mapIso (L.extendXIso ComplexShape.embeddingDownNat hq)) ≪≫ e
      exact ⟨m, e'.hom, e'.inv, e'.hom_inv_id⟩

/-- The shifted Koszul complex on powers of a finite sequence gives a perfect affine object.
Source: Stacks Project, Tag 08CX and Definition 08CM.
(blueprint: lem-sc-affine-perfect-koszul-principal-unit-perfect).

Proof: In degree `-n` the complex is the exterior power of degree `n + 1` of `A^r`.
The exterior powers have the wedge bases indexed by subsets of the standard basis,
so they are finite free and vanish when `n + 1 > r`. Extension gives zero in positive
cochain degrees, and negating the differential does not change any term. Applying
associated sheaves termwise therefore gives a bounded complex of finite free structure
sheaf modules. Restrict this complex to the whole scheme, or any neighbourhood of a
point. Restriction preserves finite free modules and zero terms, and its derived
comparison identifies this strictly perfect model with the restricted derived object.
This is the definition of perfectness. For `r = 0` all terms are zero; if `A` is the
zero ring, the spectrum is empty and the pointwise conclusion is vacuous. -/
theorem affine_perfect_koszul_principal_unit_perfect
    (A : Type a) [CommRing A] (r : ℕ) (f : Fin r → A) (e : ℕ) (he : 1 ≤ e)
    [HasDerivedCategory.{b}
      (SheafOfModules.{a} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ U : (Spec (.of A)).Opens,
      HasDerivedCategory.{b}
        (SheafOfModules.{a} ((moduleRings (Spec (.of A)).toRingedSpace).over U))] :
    Scheme.IsPerfect (Spec (.of A))
      (DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{a} A)
          (SheafOfModules.{a} (moduleRings (Spec (.of A)).toRingedSpace))
          _ _ _ _ (tilde.functor (.of A))
          ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
          (shiftedKoszulComplex A r (fun i ↦ f i ^ e)))) := by
  have _ := he
  classical
  let K := ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{a} A)
    (SheafOfModules.{a} (moduleRings (Spec (.of A)).toRingedSpace))
    _ _ _ _ (tilde.functor (.of A))
    ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
    (shiftedKoszulComplex A r (fun i ↦ f i ^ e)))
  change Scheme.IsPerfect (Spec (.of A)) (DerivedCategory.Q.obj K)
  intro x
  let F := SheafOfModules.overFunctor.{a}
    (moduleRings (Spec (.of A)).toRingedSpace) ⊤
  refine ⟨⊤, trivial, (F.mapHomologicalComplex (.up ℤ)).obj K,
    shifted_koszul_strictly_perfect A r (fun i ↦ f i ^ e) ⊤,
    ⟨F.mapDerivedCategoryFactors.app K⟩⟩

end AlgebraicGeometry
