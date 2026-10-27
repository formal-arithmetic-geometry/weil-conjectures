module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import WeilConjectures.PointCount
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic
import Sheaf.AlgebraicGeometry.LocalFibreDimensionOpen

/-!
# Lower bound for dimensions of fibres of an irreducible finite-type scheme

Source: Stacks Project, varieties.tex, Tag 0B2L
(blueprint: lem-zl-irreducible-fibre-dimension-lower-bound).
-/


@[expose] public section

set_option autoImplicit false

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The fibre inclusion is surjective on stalks, hence on residue fields. -/
private theorem fibre_residue_iso {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    IsIso ((f.fiberι (f x)).residueFieldMap (f.asFiber x)) := by
  let i := f.fiberι (f x)
  let z := f.asFiber x
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨RingHom.injective _, ?_⟩
  intro b
  obtain ⟨a, rfl⟩ := (f.fiber (f x)).residue_surjective z b
  obtain ⟨c, rfl⟩ := i.stalkMap_surjective z a
  exact ⟨X.residue (i z) c, rfl⟩

/-- The scalar map of a fibre agrees with the original residue-field map. -/
private theorem fibre_scalar {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    CommRingCat.ofHom
        ((f.fiberToSpecResidueField (f x)).residueFieldAlgebraMap (f.asFiber x)) =
      f.residueFieldMap x ≫ (X.residueFieldCongr (f.fiberι_asFiber x)).inv ≫
        (f.fiberι (f x)).residueFieldMap (f.asFiber x) := by
  apply Spec.map_injective
  rw [Scheme.Hom.specMap_residueFieldAlgebraMap]
  apply (cancel_mono (Y.fromSpecResidueField (f x))).mp
  simp only [Spec.map_comp, Category.assoc,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    Scheme.residueFieldCongr_inv, Scheme.residueFieldCongr_fromSpecResidueField_assoc]
  rw [← f.fiber_fac]
  simp only [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]

/-- Stacks Project, varieties.tex, Tag 0B2L, parts (2)(a) and (2)(b)
(blueprint: lem-zl-irreducible-fibre-dimension-lower-bound).
If `X` is irreducible and of finite type
over a field and `f : X ⟶ Y` is a morphism over that field, every local fibre dimension is
bounded below by the dimension difference, and this bound is attained on a dense open subset.
The difference is expressed by its natural-number representative, since
`WithBot ℕ∞` has no subtraction operation.

Proof (the eight steps of the node, following Tag 0B2L):
1. A field is Noetherian, and its spectrum is quasi-compact. Apply
   `lem-weil-pbc-finite-type-over-noetherian` to make `X` Noetherian. The minimal-closed-set
   theorem `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal` gives the descending-chain
   condition. Then `lem-sfb-noetherian-space-compact-subsets` makes every subset compact.
2. The composite of `f` with the structure map of `Y` is the structure map of `X`.
   Clause (f) of `lem-weil-pbc-proper-fp-permanence` makes `f` locally of finite type.
   Step 1 makes inverse images of affine opens compact, so `f` is finite type
   (`def-weil-finite-type-morphism`). Base change by `lem-sfb-finite-type-composition-base-change`
   makes every fibre finite type over its residue field. Its dimension is finite by
   `lem-kun-dimension-finite-type`.
3. Irreducibility includes nonemptiness. Choose the generic point `η` using
   `lem-weil-pbc-scheme-sober`, and put `ξ = f η`. The inverse image of the closure of `ξ`
   is closed and contains `η`, so it is all of `X`. As `ξ` belongs to the image,
   `Z = closure (range f)` is the closure of `ξ`, with generic point `ξ`.
   Every nonempty open of `X` contains `η`, since its closed complement cannot contain `η`.
4. Apply `lem-sc-closed-irreducible-dimension-trdeg` to the whole of `X` and to `Z` in `Y`.
   Their dimensions are the transcendence degrees of the generic residue fields over `k`.
   They are finite by `lem-kun-dimension-finite-type` and monotonicity for a closed subspace.
   The residue-field tower and `lem-kun-transcendence-degree-tower` therefore give a natural
   number `r = trdeg κ(ξ) κ(η)` and `dim X = dim Z + r`, without infinite subtraction.
5. The fibre homeomorphism in `def-pc-scheme-fibre` identifies `F = X_ξ` with the subspace
   of points mapping to `ξ`. It contains `η` as a generic point and is irreducible.
   By `lem-weil-pbc-fibre-product-point-residue-field`, its residue field at that point
   identifies with `κ(η)` compatibly with `κ(ξ)`: the point tensor ring is
   `κ(η) ⊗[κ(ξ)] κ(ξ)`, with isomorphism `a ⊗ b ↦ a * f♯(b)` and inverse `a ↦ a ⊗ 1`.
   This ring is a field, so the kernel prime is zero and the residue field is the same field.
6. Apply `lem-sc-closed-irreducible-dimension-trdeg` to the finite type irreducible fibre
   `F`. Step 5 gives `dim F = r`. By `lem-sc-dimension-locally-algebraic`, its local
   dimension at every point, including the point corresponding to `η`, is also `r`.
7. For any `x`, the minimum in `def-kun-topological-dimension-at-point` for its nonempty
   fibre is a finite nonnegative integer `n`: it is bounded by the finite global fibre
   dimension from step 2. By `lem-weil-pbc-local-fibre-dimension-open`, the locus of local
   fibre dimension at most `n` is open and contains `x`. It therefore contains `η` by
   step 3. Evaluating there gives `r ≤ n`, proving the pointwise lower bound.
8. Apply the same openness theorem at `r`. This open locus contains `η` by step 6, hence
   is dense. The lower bound from step 7 identifies it with the entire equality locus. -/
theorem irreducible_fibre_dimension_lower_bound
    (k : Type u) [Field k]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IrreducibleSpace X]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] :
    ∃ r : ℕ,
      topologicalKrullDim X =
        topologicalKrullDim (closure (Set.range f.base) : Set Y) +
          (r : WithBot ℕ∞) ∧
      (∀ x : X, (r : WithBot ℕ∞) ≤ topologicalKrullDimAt (f.asFiber x)) ∧
      Dense {x : X | topologicalKrullDimAt (f.asFiber x) = (r : WithBot ℕ∞)} ∧
      IsOpen {x : X | topologicalKrullDimAt (f.asFiber x) = (r : WithBot ℕ∞)} := by
  classical
  have hcomp : f ≫ (Y ↘ Spec (.of k)) = (X ↘ Spec (.of k)) :=
    comp_over f _
  have : LocallyOfFiniteType (f ≫ (Y ↘ Spec (.of k))) := hcomp ▸ inferInstance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (Y ↘ Spec (.of k))
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  let η := genericPoint X
  let ξ := f η
  let F := f.fiber ξ
  let z : F := f.asFiber η
  let p := f.fiberToSpecResidueField ξ
  let : F.Over (Spec (Y.residueField ξ)) := f.fiberOverSpecResidueField ξ
  have : LocallyOfFiniteType (F ↘ Spec (Y.residueField ξ)) :=
    show LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd f
      (Y.fromSpecResidueField ξ)) from inferInstance
  have : QuasiCompact (F ↘ Spec (Y.residueField ξ)) :=
    show QuasiCompact (CategoryTheory.Limits.pullback.snd f
      (Y.fromSpecResidueField ξ)) from inferInstance
  have hz : IsGenericPoint z (Set.univ : Set F) := by
    rw [isGenericPoint_iff_specializes]
    intro w
    simp only [Set.mem_univ, iff_true]
    apply (f.fiberι ξ).isEmbedding.isInducing.specializes_iff.mp
    change (f.fiberι (f η)) (f.asFiber η) ⤳ (f.fiberι ξ) w
    rw [f.fiberι_asFiber]
    exact genericPoint_specializes _
  have : IrreducibleSpace F := (irreducibleSpace_def F).mpr hz.isIrreducible
  have hξ : IsGenericPoint ξ (closure (Set.range f.base)) := by
    simpa only [Set.image_univ] using (genericPoint_spec X).image f.continuous
  obtain ⟨dX, hdX, htX⟩ := topologicalKrullDim_closed_irreducible_eq_trdeg
    (K := k) (Set.univ : Set X) isClosed_univ
    (IrreducibleSpace.isIrreducible_univ X) η (Set.mem_univ _) (genericPoint_closure X)
  have hdX' : topologicalKrullDim X = (dX : WithBot ℕ∞) := by
    simpa only [(Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq] using hdX
  obtain ⟨dZ, hdZ, htZ⟩ := topologicalKrullDim_closed_irreducible_eq_trdeg
    (K := k) (closure (Set.range f.base)) isClosed_closure hξ.isIrreducible ξ hξ.mem hξ
  obtain ⟨r, hdF, htF⟩ := topologicalKrullDim_closed_irreducible_eq_trdeg
    (K := Y.residueField ξ) (Set.univ : Set F) isClosed_univ hz.isIrreducible z
    (Set.mem_univ _) hz
  have hdF' : topologicalKrullDim F = (r : WithBot ℕ∞) := by
    simpa only [(Homeomorph.Set.univ F).isHomeomorph.topologicalKrullDim_eq] using hdF
  let : Algebra k (Y.residueField ξ) :=
    ((Y ↘ Spec (.of k)).residueFieldAlgebraMap ξ).toAlgebra
  let : Algebra k (X.residueField η) :=
    ((X ↘ Spec (.of k)).residueFieldAlgebraMap η).toAlgebra
  let : Algebra (Y.residueField ξ) (X.residueField η) :=
    (f.residueFieldMap η).hom.toAlgebra
  have : IsScalarTower k (Y.residueField ξ) (X.residueField η) :=
    IsScalarTower.of_algebraMap_eq' (by
      change _ = (f.residueFieldMap η).hom.comp
        ((Y ↘ Spec (.of k)).residueFieldAlgebraMap ξ)
      rw [← Scheme.Hom.residueFieldAlgebraMap_comp, hcomp]
      rfl)
  let : Algebra (Y.residueField ξ) (F.residueField z) :=
    (p.residueFieldAlgebraMap z).toAlgebra
  have : IsIso ((f.fiberι ξ).residueFieldMap z) := fibre_residue_iso f η
  let e : X.residueField η ≃ₐ[Y.residueField ξ] F.residueField z :=
    { ((X.residueFieldCongr (f.fiberι_asFiber η)).symm ≪≫
        asIso ((f.fiberι ξ).residueFieldMap z)).commRingCatIsoToRingEquiv with
      commutes' c := (ConcreteCategory.congr_hom (fibre_scalar f η) c).symm }
  have htr : Algebra.trdeg (Y.residueField ξ) (X.residueField η) = (r : Cardinal) :=
    e.trdeg_eq.trans htF
  have hsum : dZ + r = dX := by
    have h := trdeg_add_eq k (Y.residueField ξ) (A := X.residueField η)
    rw [htZ, htr, htX, ← Nat.cast_add] at h
    exact_mod_cast h
  have hzdim : topologicalKrullDimAt (f.asFiber η) = (r : WithBot ℕ∞) :=
    ((dimension_locally_algebraic (k := Y.residueField ξ) F).2 z).trans hdF'
  have hlower (x : X) : (r : WithBot ℕ∞) ≤ topologicalKrullDimAt (f.asFiber x) := by
    have hnonneg : 0 ≤ topologicalKrullDimAt (f.asFiber x) := by
      refine le_iInf₂ fun U hxU ↦ ?_
      apply Order.krullDim_nonneg_iff.mpr
      exact ⟨⟨closure {⟨f.asFiber x, hxU⟩}, isIrreducible_singleton.closure,
        isClosed_closure⟩⟩
    generalize hd : topologicalKrullDimAt (f.asFiber x) = d at hnonneg ⊢
    induction d using WithBot.recBotCoe with
    | bot => exact False.elim ((not_le_of_gt (by decide : (⊥ : WithBot ℕ∞) < 0)) hnonneg)
    | coe d =>
      induction d using ENat.recTopCoe with
      | top => exact le_top
      | coe n =>
        have hηmem := (genericPoint_spec X).mem_open_set_iff
          (isOpen_localFibreDimension_le f n)
        have hn : topologicalKrullDimAt (f.asFiber η) ≤ (n : WithBot ℕ∞) :=
          hηmem.mpr ⟨x, Set.mem_univ _, hd.le⟩
        exact hzdim ▸ hn
  have heq : {x : X | topologicalKrullDimAt (f.asFiber x) = (r : WithBot ℕ∞)} =
      {x : X | topologicalKrullDimAt (f.asFiber x) ≤ (r : WithBot ℕ∞)} := by
    ext x
    exact ⟨fun h ↦ h.le, fun h ↦ le_antisymm h (hlower x)⟩
  refine ⟨r, ?_, hlower, ?_, ?_⟩
  · rw [hdX', hdZ, ← Nat.cast_add, hsum]
  · apply Dense.mono (s₁ := {η}) (s₂ := _)
    · intro x hx
      exact (Set.mem_singleton_iff.mp hx) ▸ hzdim
    · exact dense_iff_closure_eq.mpr (genericPoint_closure X)
  · rw [heq]
    exact isOpen_localFibreDimension_le f r

end AlgebraicGeometry

end
