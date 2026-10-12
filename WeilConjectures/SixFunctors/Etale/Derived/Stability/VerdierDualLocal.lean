/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.GenericFiniteness
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.VerdierDual

/-!
# The Verdier dual of a complex of lisse sheaves on a smooth scheme

Let `O` be an irreducible scheme smooth of pure relative dimension `n` over a field `k`, and `K` a
complex on `O` represented by a bounded complex of flat finite locally constant sheaves in degrees
`[a, b]`. After shrinking `O` to a nonempty open, the Verdier dual `𝔻_O K = RHom(K, ω_O)` has Tor
amplitude in `[-b - 2n, -a - 2n]`.

The proof avoids the dualizability of lisse sheaves: after shrinking `O`, there is a finite étale
surjection `p : V ⟶ O` along which all the terms become constant
(`AlgebraicGeometry.Etale.exists_finite_etale_surjective_isConstant`), hence dualizable, being
constant sheaves of finite projective modules. Along the finite étale `p`, `p^* = Rp^!` commutes
with the internal hom, and `ω_O` is a shifted flat invertible sheaf by smooth duality, so
`p^* 𝔻_O K ≅ RHom(p^* K, p^* ω_O) ≅ (p^* K)^∨ ⊗ᴸ p^* ω_O`; the Tor amplitude then descends along
the surjection `p`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ]

/-! ### Trivialising finitely many locally constant sheaves -/

variable {Λ} in
/-- The pullback of a constant sheaf is constant. -/
lemma isConstant_upperStar {X Y : Scheme.{u}} (g : X ⟶ Y)
    {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hF : F.IsConstant Y.smallEtaleTopology) :
    ((g)^*[ModuleCat.{u + 1} Λ].obj F).IsConstant X.smallEtaleTopology := by
  obtain ⟨⟨M, ⟨e⟩⟩⟩ := hF
  exact Sheaf.isConstant_of_iso
    ((g)^*[ModuleCat.{u + 1} Λ].mapIso e.symm ≪≫ (upperStarConstantSheafIso _ g).app M)

variable {Λ} in
/-- Finitely many locally constant sheaves on an irreducible scheme become constant after
pullback along a single étale morphism from a nonempty scheme: intersect the images of étale
trivialisations of the individual sheaves, which are nonempty opens of an irreducible space, and
take the fibre product. -/
lemma exists_etale_isConstant_upperStar {O : Scheme.{u}} [IrreducibleSpace O] (n : ℕ)
    (F : Fin n → Sheaf O.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∀ i, IsLocallyConstantSheaf (F i)) :
    ∃ (W : Scheme.{u}) (_ : Nonempty W) (e : W ⟶ O) (_ : _root_.AlgebraicGeometry.Etale e),
      ∀ i, ((e)^*[ModuleCat.{u + 1} Λ].obj (F i)).IsConstant W.smallEtaleTopology := by
  induction n with
  | zero => exact ⟨O, inferInstance, 𝟙 O, inferInstance, Fin.elim0⟩
  | succ n ih =>
    obtain ⟨W, hW, e, he, hc⟩ := ih (fun i ↦ F i.castSucc) (fun i ↦ hF _)
    obtain ⟨⟨𝒰, h𝒰⟩⟩ := (hF (Fin.last n)).nonempty_locallyConstantDatum
    obtain ⟨x⟩ := (inferInstance : Nonempty O)
    let i := 𝒰.idx x
    have hi : _root_.AlgebraicGeometry.Etale (𝒰.f i) := 𝒰.map_prop i
    have hci : ((𝒰.f i)^*[ModuleCat.{u + 1} Λ].obj (F (Fin.last n))).IsConstant
        (𝒰.X i).smallEtaleTopology :=
      (isConstant_over_iff_upperStar _ _).1 (h𝒰 i)
    -- the images of `e` and of `𝒰.f i` meet
    obtain ⟨w⟩ := hW
    obtain ⟨y, hy⟩ := 𝒰.covers x
    obtain ⟨z, ⟨w', hw'⟩, ⟨y', hy'⟩⟩ := nonempty_preirreducible_inter e.isOpenMap.isOpen_range
      (𝒰.f i).isOpenMap.isOpen_range ⟨_, w, rfl⟩ ⟨_, y, rfl⟩
    obtain ⟨t, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := e) (g := 𝒰.f i) w' y'
      (hw'.trans hy'.symm)
    refine ⟨pullback e (𝒰.f i), ⟨t⟩, pullback.fst e (𝒰.f i) ≫ e, inferInstance, ?_⟩
    intro j
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · refine Sheaf.isConstant_congr _
        (((Etale.upperStarComp _ (pullback.snd e (𝒰.f i)) (𝒰.f i) _ pullback.condition).app
          (F (Fin.last n))).symm) (h := isConstant_upperStar _ hci)
    · refine Sheaf.isConstant_congr _
        (((Etale.upperStarComp _ (pullback.fst e (𝒰.f i)) e _ rfl).app (F j.castSucc)).symm)
        (h := isConstant_upperStar _ (hc j))

variable {Λ} in
/-- **Generic finite étale trivialisation.** Finitely many locally constant sheaves on an
irreducible locally noetherian scheme `O`, separated over a base, become constant after pullback
along a finite étale surjection onto a nonempty open of `O`: an étale trivialisation from an
affine scheme is finite over a nonempty open
(`AlgebraicGeometry.Scheme.Hom.exists_isFinite_preimage_of_etale`), and a finite étale morphism
onto an irreducible scheme whose image is nonempty is surjective, its image being open and
closed. -/
lemma exists_finite_etale_surjective_isConstant {O S : Scheme.{u}} [IrreducibleSpace O]
    [IsLocallyNoetherian O] (aO : O ⟶ S) [IsSeparated aO] [IsAffine S] (n : ℕ)
    (F : Fin n → Sheaf O.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∀ i, IsLocallyConstantSheaf (F i)) :
    ∃ (O' : O.Opens) (_ : (O' : Set O).Nonempty) (V : Scheme.{u}) (p : V ⟶ O')
      (_ : IsFinite p) (_ : _root_.AlgebraicGeometry.Etale p) (_ : Surjective p),
      ∀ i, ((p ≫ O'.ι)^*[ModuleCat.{u + 1} Λ].obj (F i)).IsConstant V.smallEtaleTopology := by
  obtain ⟨W, ⟨w⟩, e, he, hc⟩ := exists_etale_isConstant_upperStar n F hF
  have : IsLocallyNoetherian W := isLocallyNoetherian_of_isOpenImmersion' e
  -- restrict to a nonempty affine open of `W`
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hwW₀, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ w) isOpen_univ
  have : IsAffine W₀ := hW₀
  have : Nonempty W₀ := ⟨⟨w, hwW₀⟩⟩
  have : TopologicalSpace.NoetherianSpace W₀ := by
    have : IsLocallyNoetherian W₀ := isLocallyNoetherian_of_isOpenImmersion W₀.ι
    have : IsNoetherian W₀ := {}
    infer_instance
  let e₀ := W₀.ι ≫ e
  have : QuasiCompact e₀ := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : IsSeparated e₀ := by
    have : IsSeparated (e₀ ≫ aO) := inferInstance
    exact IsSeparated.of_comp e₀ aO
  obtain ⟨O', hO', hpre, hfin⟩ := e₀.exists_isFinite_preimage_of_etale
  let p := e₀ ∣_ O'
  have : _root_.AlgebraicGeometry.Etale p :=
    IsZariskiLocalAtTarget.restrict (P := @_root_.AlgebraicGeometry.Etale) inferInstance O'
  have : IrreducibleSpace O' := by
    obtain ⟨x, hx⟩ := hO'
    exact Subtype.irreducibleSpace (IsPreirreducible.open_subset O'.isOpen
      (IrreducibleSpace.isIrreducible_univ O).2 (Set.subset_univ _) |>.isIrreducible ⟨x, hx⟩)
  have hsurj : Surjective p := by
    refine ⟨?_⟩
    have hcl : IsClopen (Set.range p.base) :=
      ⟨p.isClosedMap.isClosed_range, p.isOpenMap.isOpen_range⟩
    obtain ⟨v, hv⟩ := hpre
    rw [← Set.range_eq_univ, hcl.eq_univ ⟨_, ⟨v, hv⟩, rfl⟩]
  refine ⟨O', hO', _, p, hfin, inferInstance, hsurj, fun i ↦ ?_⟩
  have hp : p ≫ O'.ι = (e₀ ⁻¹ᵁ O').ι ≫ W₀.ι ≫ e := morphismRestrict_ι e₀ O'
  refine Sheaf.isConstant_congr _ (((Etale.upperStarComp _ (e₀ ⁻¹ᵁ O').ι (W₀.ι ≫ e) _ hp).app
    (F i)).symm ≪≫ ((e₀ ⁻¹ᵁ O').ι)^*[ModuleCat.{u + 1} Λ].mapIso
      ((Etale.upperStarComp _ W₀.ι e _ rfl).app (F i)).symm) (h := ?_)
  exact isConstant_upperStar _ (isConstant_upperStar _ (hc i))

/-! ### Dualizability after a finite étale trivialisation -/

section Dualizable

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- A zero object of a preadditive monoidal category is dualizable, with itself as dual and zero
evaluation and coevaluation. -/
lemma isDualizable_of_isZero {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C]
    {Z : C} (hZ : IsZero Z) : IsDualizable Z :=
  ⟨{ rightDual := Z
     exact :=
      { coevaluation' := 0
        evaluation' := 0
        coevaluation_evaluation' := (hZ.of_iso (ρ_ Z).symm).eq_of_src _ _
        evaluation_coevaluation' := (hZ.of_iso (λ_ Z).symm).eq_of_src _ _ } }⟩

/-- The constant sheaf of a finite projective `Λ`-module is dualizable, the constant sheaf
functor being monoidal. -/
lemma isDualizable_constantSheaf {X : Scheme.{u}} (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    [Module.Projective Λ M] :
    IsDualizable ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
  IsDualizable.map _ (ModuleCat.isDualizable_of_projective M)

variable [Finite Λ]

/-- A flat finite sheaf on a nonempty scheme which is constant, with value `M`, has a finite
projective value: the stalk `M` is flat and finitely generated over the noetherian ring `Λ`. -/
lemma projective_and_finite_of_iso_constantSheaf {V : Scheme.{u}} [Nonempty V]
    {G : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hG : ObjectProperty.flat G)
    [IsFiniteSheaf G] {M : ModuleCat.{u + 1} Λ}
    (e : (constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M ≅ G) :
    Module.Projective Λ M ∧ Module.Finite Λ M := by
  obtain ⟨v⟩ := ‹Nonempty V›
  let s := V.algClosurePoint v
  let Φ := (pointSmallEtale s).ulift.{u + 1}
  let eM : Φ.sheafFiber.obj G ≅ M := Φ.sheafFiber.mapIso e.symm ≪≫ Φ.sheafFiberConstantSheafIso M
  have : Module.Flat Λ M :=
    (ModuleCat.flat_iff_flat M).1 (ObjectProperty.prop_of_iso _ eM (Φ.flat_sheafFiber_obj hG))
  have : Module.Finite Λ M := (ModuleCat.isFinitelyGenerated_iff M).1
    (((IsFiniteSheaf.isFinitelyGenerated_sheafFiber (F := G) _ s).of_iso
      (((pointSmallEtale s).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} Λ)).app G).symm).of_iso
        eM)
  have : IsNoetherianRing Λ := inferInstance
  have : Module.FinitePresentation Λ M := Module.finitePresentation_of_finite Λ M
  exact ⟨Module.Flat.projective_of_finitePresentation, inferInstance⟩

/-- **Dualizability after a finite étale trivialisation.** Let `O` be an irreducible locally
noetherian scheme, separated over an affine scheme, and `P` a bounded complex in degrees
`[a, b]` of flat finite locally constant sheaves of `Λ`-modules on `O`. After shrinking `O` to a
nonempty open `O'`, there is a finite étale surjection `p : V ⟶ O'` such that the pullback of
`P` to `V` is dualizable in `D(V_ét, Λ)`: its terms become constant sheaves of finite projective
modules. -/
lemma exists_finite_etale_isDualizable {O S : Scheme.{u}} [IrreducibleSpace O]
    [IsLocallyNoetherian O] (aO : O ⟶ S) [IsSeparated aO] [IsAffine S] {a b : ℤ}
    (P : CochainComplex (Sheaf O.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (hP : IsBoundedFlatComplex Λ a b P) (hPl : ∀ q, IsFiniteLocallyConstantSheaf (P.X q)) :
    ∃ (O' : O.Opens) (_ : (O' : Set O).Nonempty) (V : Scheme.{u}) (p : V ⟶ O')
      (_ : IsFinite p) (_ : _root_.AlgebraicGeometry.Etale p) (_ : Surjective p),
      IsDualizable (D((p ≫ O'.ι)^*[ModuleCat.{u + 1} Λ]).obj
        ((_root_.DerivedCategory.Q).obj P)) := by
  let n := (b + 1 - a).toNat
  obtain ⟨O', hO', V, p, hfin, het, hsurj, hc⟩ := exists_finite_etale_surjective_isConstant aO n
    (fun i ↦ P.X (a + (i : ℕ))) (fun i ↦ (hPl _).toIsLocallyConstantSheaf)
  refine ⟨O', hO', V, p, hfin, het, hsurj, ?_⟩
  let g := p ≫ O'.ι
  have : Nonempty V := by
    obtain ⟨x, hx⟩ := hO'
    obtain ⟨v, -⟩ := hsurj.surj ⟨x, hx⟩
    exact ⟨v⟩
  let P' := (((g)^*[ModuleCat.{u + 1} Λ]).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hP' (q : ℤ) : IsDualizable (P'.X q) := by
    by_cases hq : a ≤ q ∧ q ≤ b
    · have hi : a + ((⟨(q - a).toNat, by omega⟩ : Fin n) : ℕ) = q := by
        simp only
        omega
      have hci := hc ⟨(q - a).toNat, by omega⟩
      rw [hi] at hci
      obtain ⟨⟨M, ⟨e⟩⟩⟩ := hci
      have hflat : ObjectProperty.flat ((g)^*[ModuleCat.{u + 1} Λ].obj (P.X q)) :=
        Functor.PreservesFlat.flat_obj (F := (g)^*[ModuleCat.{u + 1} Λ]) (hP.2 q)
      have : IsFiniteSheaf ((g)^*[ModuleCat.{u + 1} Λ].obj (P.X q)) :=
        IsFiniteSheaf.upperStar _ _
      obtain ⟨_, _⟩ := projective_and_finite_of_iso_constantSheaf Λ hflat e
      exact IsDualizable.of_iso e (isDualizable_constantSheaf Λ M)
    · exact isDualizable_of_isZero (Functor.map_isZero _ (hP.1 q (by omega)))
  have : P'.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun q hq ↦ Functor.map_isZero _ (hP.1 q (.inl hq))
  have : P'.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun q hq ↦ Functor.map_isZero _ (hP.1 q (.inr hq))
  exact IsDualizable.of_iso (((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryFactors.app P)
    (_root_.DerivedCategory.isDualizable_Q_obj P' a b hP')

end Dualizable

/-! ### The Verdier dual of a complex of lisse sheaves -/

variable [Finite Λ]

/-- **The Verdier dual of a complex of lisse sheaves on a smooth scheme.** Let `O` be an
irreducible scheme, smooth of pure relative dimension `n`, separated and of finite type over a
field `k`, let `Λ` be a finite ring whose exponent is invertible in `k`, and let `P` be a bounded
complex in degrees `[a, b]` of flat finite locally constant sheaves of `Λ`-modules on `O`. Then
on a nonempty open `O' ⊆ O` the Verdier dual of `P` has Tor amplitude in `[-b - 2n, -a - 2n]`.

On a finite étale surjection `p : V ⟶ O'` trivialising the terms of `P`
(`AlgebraicGeometry.Etale.exists_finite_etale_isDualizable`), `p^* = Rp^!` gives
`p^* 𝔻 P ≅ RHom(p^* P, p^* ω)`, where `p^* P` is dualizable of Tor amplitude `[a, b]` and
`ω ≅ L[2n]` for a flat sheaf `L` (`thm-asd-smooth-tensor`), so that
`RHom(p^* P, p^* ω) ≅ (p^* P)^∨ ⊗ᴸ p^* ω` has Tor amplitude `[-b - 2n, -a - 2n]`; this descends
along the surjection `p`. -/
theorem exists_torAmplitudeIn_verdierDual_of_isFiniteLocallyConstantSheaf {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))] {O : Scheme.{u}} [IrreducibleSpace O]
    (aO : O ⟶ Spec (.of k)) [IsSeparated aO] [LocallyOfFiniteType aO] [QuasiCompact aO]
    (n : ℕ) [SmoothOfRelativeDimension n aO] {a b : ℤ}
    (P : CochainComplex (Sheaf O.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (hP : IsBoundedFlatComplex Λ a b P) (hPl : ∀ q, IsFiniteLocallyConstantSheaf (P.X q)) :
    ∃ O' : O.Opens, (O' : Set O).Nonempty ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) O' (-b - 2 * n) (-a - 2 * n)
        ((verdierDual (ModuleCat.{u + 1} Λ) (O'.ι ≫ aO)).obj
          (op (D((O'.ι)^*[ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.Q).obj P)))) := by
  have : IsLocallyNoetherian O := LocallyOfFiniteType.isLocallyNoetherian aO
  obtain ⟨O', hO', V, p, hfin, het, hsurj, hdual⟩ := exists_finite_etale_isDualizable Λ aO P hP hPl
  refine ⟨O', hO', ?_⟩
  have : TopologicalSpace.NoetherianSpace O := by
    have : CompactSpace O := QuasiCompact.compactSpace_of_compactSpace aO
    have : IsNoetherian O := {}
    infer_instance
  have : TopologicalSpace.NoetherianSpace O' := O'.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact O'.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : SmoothOfRelativeDimension n (O'.ι ≫ aO) := by
    have : SmoothOfRelativeDimension (0 + n) (O'.ι ≫ aO) := inferInstance
    simpa using this
  let N := D((O'.ι)^*[ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.Q).obj P)
  -- the dualizing complex of `O'` is a shifted flat sheaf
  obtain ⟨L, _, hLs, ⟨eω⟩, -⟩ := exists_dualizingComplex_iso_and_tensor Λ (O'.ι ≫ aO) n
  obtain ⟨-, hLf⟩ := isConstructibleSheaf_and_flat_of_sheafFiber_iso Λ L hLs
  -- the pullback of `N` along `p` is dualizable, of Tor amplitude `[a, b]`
  let eN : (L((p)^*[ModuleCat.{u + 1} Λ])).obj N ≅
      D((p ≫ O'.ι)^*[ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.Q).obj P) :=
    (leftDerivedUpperStarIsoMapDerivedCategory _ p).app N ≪≫
      ((Functor.mapDerivedCategoryCompIso _ _).app _).symm ≪≫
      (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp _ p O'.ι _ rfl).symm).app _
  have hNd : IsDualizable ((L((p)^*[ModuleCat.{u + 1} Λ])).obj N) := hdual.of_iso eN.symm
  have hQt : torAmplitudeIn (ModuleCat.{u + 1} Λ) O a b ((_root_.DerivedCategory.Q).obj P) :=
    _root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat _ a b hP.2
  have hNt : torAmplitudeIn (ModuleCat.{u + 1} Λ) V a b ((L((p)^*[ModuleCat.{u + 1} Λ])).obj N) :=
    torAmplitudeIn_leftDerivedUpperStar _ p a b ((torAmplitudeIn _ O' a b).prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ O'.ι).app _)
      (torAmplitudeIn_leftDerivedUpperStar _ O'.ι a b hQt))
  -- the pullback of the dualizing complex has Tor amplitude `[-2n, -2n]`
  let eω' : (R(p)^![ModuleCat.{u + 1} Λ]).obj (dualizingComplex _ (O'.ι ≫ aO)) ≅
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((p)^*[ModuleCat.{u + 1} Λ].obj L))⟦(2 * n : ℤ)⟧ :=
    (rightDerivedUpperShriekIsoOfIsFiniteOfEtale _ p).app _ ≪≫
      D((p)^*[ModuleCat.{u + 1} Λ]).mapIso eω ≪≫
      (D((p)^*[ModuleCat.{u + 1} Λ]).commShiftIso (2 * n : ℤ)).app _ ≪≫
      (shiftFunctor _ (2 * n : ℤ)).mapIso
        ((((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app L)
  have hωt : torAmplitudeIn (ModuleCat.{u + 1} Λ) V (-(2 * n)) (-(2 * n))
      ((R(p)^![ModuleCat.{u + 1} Λ]).obj (dualizingComplex _ (O'.ι ≫ aO))) := by
    have h := torAmplitudeIn_shift _ (torAmplitudeIn_singleFunctor_zero_of_flat _ _
      (Functor.PreservesFlat.flat_obj (F := (p)^*[ModuleCat.{u + 1} Λ]) hLf)) (2 * n : ℤ)
    exact (torAmplitudeIn _ V _ _).prop_of_iso eω'.symm (by simpa using h)
  -- `p^* 𝔻 N ≅ RHom(p^* N, Rp^! ω)`
  obtain ⟨eH⟩ := nonempty_iso_rightDerivedUpperShriek_derivedHom Λ p N
    (dualizingComplex _ (O'.ι ≫ aO))
  have h := torAmplitudeIn_derivedHom_of_isDualizable_aux _ hNt hNd hωt
  refine torAmplitudeIn_of_leftDerivedUpperStar_of_surjective Λ p hsurj.surj ?_
  refine (torAmplitudeIn _ V _ _).prop_of_iso
    (eH.symm ≪≫ ((rightDerivedUpperShriekIsoOfIsFiniteOfEtale _ p).app _ ≪≫
      ((leftDerivedUpperStarIsoMapDerivedCategory _ p).app _).symm)) ?_
  exact h.mono (by omega) (by omega)

end Etale

end AlgebraicGeometry
