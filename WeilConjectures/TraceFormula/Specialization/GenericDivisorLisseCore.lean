/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalSchemeDivisor
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorIntegral
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorLisse

/-!

# Generic vanishing for lisse generators: reduction to the codimension-one core

Let `X` be normal, `Z = V(h)` a principal divisor, `ζ` a generic point of `Z`, and `Rg_! Rj'_! M` a
lisse generator of `Dᵇc(X ∖ Z)` whose support has closure containing `ζ`. The local ring of `X` at
`ζ` is a discrete valuation ring, so the only proper generization of `ζ` is the generic point of
`X` (`AlgebraicGeometry.Scheme.specializes_eq_or_eq_genericPoint`); a set closed in `X ∖ Z` whose
closure contains `ζ` therefore contains the generic point of `X`
(`ProEtale.CondensedRing.genericPoint_mem_of_mem_closure`). Hence either `U₀ = ∅`, where everything
vanishes, or `U₀` covers `V ∖ Z` for an open neighbourhood `V` of `ζ`
(`ProEtale.CondensedRing.isEmpty_or_exists_opens_subset_range`). This proves the case of
generators whose support closure contains `ζ` from the codimension-one core
`ProEtale.CondensedRing.exists_isZero_upperStar_nearbyCycles_lowerShriek_of_subset_range`.

The core holds for every bounded constructible complex on `X ∖ Z`
(`ProEtale.CondensedRing.exists_isZero_upperStar_nearbyCycles_lowerShriek_padicAlgCl`): an
integral model and derived Nakayama reduce it to `𝔽_E`-coefficients.

## Unfinished

The core depends on the finite-coefficient statement
`ProEtale.CondensedRing.exists_isZero_upperStar_nearbyCycles_lowerShriek_residueField`, which is
`sorry`ed: it is the local acyclicity along a divisor of extensions by zero of constructible
`𝔽_E`-complexes on the complement (the nearby cycles of the deformation `x = t u` at the zero
section).

-/

@[expose] public section

universe u

open CategoryTheory Limits Topology TopologicalSpace IsLocalRing Pretriangulated ZeroObject

open scoped CategoryTheory.Functor CategoryTheory.Obj

/-- In a noetherian quasi-sober space, if `x` lies in the closure of a set `R` which is closed in
an open set `O ⊇ R`, then some generization of `x` lies in `R`. -/
lemma exists_mem_specializes_of_mem_closure {α : Type*} [TopologicalSpace α] [NoetherianSpace α]
    [QuasiSober α] {O R : Set α} (hO : IsOpen O) (hRO : R ⊆ O) (hR : closure R ∩ O ⊆ R)
    {x : α} (hx : x ∈ closure R) : ∃ c ∈ R, c ⤳ x := by
  classical
  obtain ⟨S, hS, hSeq⟩ := NoetherianSpace.exists_finset_irreducible ⟨closure R, isClosed_closure⟩
  have hcl : closure R = ⋃ K ∈ S, (K : Set α) := by
    have := congrArg ((↑) : Closeds α → Set α) hSeq
    simpa [Closeds.coe_finset_sup] using this
  have hT : closure R ⊆
      ⋃ K ∈ S.filter fun K : Closeds α ↦ ((K : Set α) ∩ O).Nonempty, (K : Set α) := by
    refine closure_minimal (fun r hr ↦ ?_) (isClosed_biUnion_finset fun K _ ↦ K.isClosed)
    obtain ⟨K, hK, hrK⟩ := Set.mem_iUnion₂.1 (hcl ▸ subset_closure hr)
    exact Set.mem_iUnion₂.2 ⟨K, Finset.mem_filter.2 ⟨hK, r, hrK, hRO hr⟩, hrK⟩
  obtain ⟨K, hK, hxK⟩ := Set.mem_iUnion₂.1 (hT hx)
  obtain ⟨hKS, y, hyK, hyO⟩ := Finset.mem_filter.1 hK
  have hirr : IsIrreducible (K : Set α) := hS ⟨K, hKS⟩
  have hgen := hirr.isGenericPoint_genericPoint K.isClosed
  refine ⟨hirr.genericPoint, hR ⟨?_, (hgen.specializes hyK).mem_open hO hyO⟩,
    hgen.specializes hxK⟩
  rw [hcl]
  exact Set.mem_iUnion₂.2 ⟨K, hKS, hgen.mem⟩

/-- The image `f '' s` of a closed set under an embedding is closed in the range of `f`. -/
lemma Topology.IsEmbedding.closure_image_inter_range_subset {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : α → β} (hf : IsEmbedding f) {s : Set α} (hs : IsClosed s) :
    closure (f '' s) ∩ Set.range f ⊆ f '' s := by
  rintro _ ⟨hy, z, rfl⟩
  refine ⟨z, ?_, rfl⟩
  rw [← hs.closure_eq, hf.closure_eq_preimage_closure_image]
  exact hy

namespace AlgebraicGeometry.Scheme

/-- **Generizations of a generic point of a principal divisor**: on a locally noetherian normal
(integral) scheme, let `x` be a point of the zero locus of a nonzero global function `h` with no
proper generization in the zero locus. Then every generization of `x` is `x` itself or the generic
point of `X`: the local ring at `x` is a discrete valuation ring. -/
lemma specializes_eq_or_eq_genericPoint {X : Scheme.{u}} (hX : IsNormalScheme X)
    [IsLocallyNoetherian X] {h : Γ(X, ⊤)} (hh : h ≠ 0) {x : X}
    (hx : x ∈ X.zeroLocus (U := ⊤) {h})
    (hgen : ∀ y ∈ X.zeroLocus (U := ⊤) {h}, y ⤳ x → y = x) {y : X} (hy : y ⤳ x) :
    haveI := hX.1
    y = x ∨ y = genericPoint X := by
  have := hX.1
  have := (hX.2 x).1
  have := (hX.2 x).2
  have : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    IsDiscreteValuationRing.of_maximalIdeal_mem_minimalPrimes_span_singleton
      ((map_ne_zero_iff _ (germ_injective_of_isIntegral X (U := ⊤) x trivial)).2 hh)
      (maximalIdeal_stalk_mem_minimalPrimes hx hgen)
  have hp (p : Spec (X.presheaf.stalk x)) : p = closedPoint _ ∨ p.asIdeal = ⊥ := by
    by_cases hb : p.asIdeal = ⊥
    · exact Or.inr hb
    · refine Or.inl (PrimeSpectrum.ext ?_)
      exact IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hb p.isPrime)
  have hη : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
    rw [range_fromSpecStalk]
    exact genericPoint_specializes x
  have hy' : y ∈ Set.range (X.fromSpecStalk x) := by
    rw [range_fromSpecStalk]
    exact hy
  obtain ⟨q, hq⟩ := hη
  obtain ⟨p, rfl⟩ := hy'
  rcases hp p with rfl | hpb
  · exact Or.inl fromSpecStalk_closedPoint
  · refine Or.inr ?_
    rcases hp q with rfl | hqb
    · exfalso
      have hxf : x ∉ X.basicOpen h := (X.mem_zeroLocus_iff _ x).1 hx h rfl
      rw [fromSpecStalk_closedPoint] at hq
      refine hxf (hq ▸ ((genericPoint_spec X).mem_open_set_iff (X.basicOpen h).isOpen).2 ?_)
      rw [Set.univ_inter, Set.nonempty_iff_ne_empty, Ne, ← Opens.coe_bot, SetLike.coe_set_eq,
        basicOpen_eq_bot_iff]
      exact hh
    · rw [← hq]
      congr 1
      exact PrimeSpectrum.ext (hpb.trans hqb.symm)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] {X : Over (Spec (.of k))}

/-- A point of the centre `V(h)` lies in the zero locus of `h`. -/
lemma subschemeι_mem_zeroLocus {h : Γ(X.left, ⊤)} {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h})) (ζ : (centre X I).left) :
    I.subschemeι ζ ∈ X.left.zeroLocus (U := ⊤) {h} := by
  subst hI
  rw [← IdealSheafData.range_subschemeι_ofIdealTop_span]
  exact ⟨ζ, rfl⟩

/-- A generic point of an irreducible component of the centre `V(h)` has no proper generization
in the zero locus of `h`. -/
lemma eq_of_specializes_subschemeι {h : Γ(X.left, ⊤)} {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h})) (ζ : (centre X I).left)
    (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left) (y : X.left)
    (hy : y ∈ X.left.zeroLocus (U := ⊤) {h}) (hyζ : y ⤳ I.subschemeι ζ) :
    y = I.subschemeι ζ := by
  subst hI
  rw [← IdealSheafData.range_subschemeι_ofIdealTop_span] at hy
  obtain ⟨y', rfl⟩ := hy
  have hspec : y' ⤳ ζ := (Scheme.Hom.isClosedEmbedding _).isInducing.specializes_iff.1 hyζ
  have hle := hζ.2 isIrreducible_singleton.closure (specializes_iff_closure_subset.1 hspec)
  obtain rfl := (hspec.antisymm (specializes_iff_closure_subset.2 hle)).eq
  rfl

variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]

/-- **A set closed in `X ∖ V(h)` whose closure contains a generic point of `V(h)` contains the
generic point of `X`** (`X` normal): it contains a generization of `ζ` outside `V(h)`, which is
the generic point since `𝒪_{X,ζ}` is a discrete valuation ring. -/
theorem genericPoint_mem_of_mem_closure (hX : IsNormalScheme X.left) {h : Γ(X.left, ⊤)}
    (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h})) (ζ : (centre X I).left)
    (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left) {R : Set X.left}
    (hRO : R ⊆ (I.support.compl : Set X.left))
    (hR : closure R ∩ (I.support.compl : Set X.left) ⊆ R) (hζR : I.subschemeι ζ ∈ closure R) :
    haveI := hX.1
    genericPoint X.left ∈ R := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsNoetherian X.left := ⟨⟩
  obtain ⟨c, hcR, hc⟩ := exists_mem_specializes_of_mem_closure I.support.compl.isOpen hRO hR hζR
  rcases Scheme.specializes_eq_or_eq_genericPoint hX hh (subschemeι_mem_zeroLocus hI ζ)
    (eq_of_specializes_subschemeι hI ζ hζ) hc with rfl | rfl
  · have hζI : I.subschemeι ζ ∈ (I.support : Set X.left) := by
      rw [← IdealSheafData.range_subschemeι]
      exact ⟨ζ, rfl⟩
    exact absurd hζI (hRO hcR)
  · exact hcR

/-- **The support of a lisse generator near a generic point of `V(h)`**: let `g : Z₀ ⟶ X ∖ V(h)`
be a closed immersion and `j' : U₀ ⟶ Z₀` an open immersion, and suppose that the closure in `X`
of the image of `Z₀` contains a generic point `ζ` of `V(h)`. Then either `U₀` is empty, or there
is an open neighbourhood `V` of `ζ` in `X` with `V ∖ V(h)` contained in the image of `U₀`. -/
theorem isEmpty_or_exists_opens_subset_range (hX : IsNormalScheme X.left) {h : Γ(X.left, ⊤)}
    (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h})) {Z₀ : Over (Spec (.of k))}
    (g : Z₀ ⟶ overRestrict X I.support.compl) [IsClosedImmersion g.left]
    {U₀ : Over (Spec (.of k))} (j' : U₀ ⟶ Z₀) [IsOpenImmersion j'.left]
    (ζ : (centre X I).left) (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left)
    (hζZ₀ : I.subschemeι ζ ∈ closure (Set.range (g ≫ overRestrictι X I.support.compl).left.base)) :
    IsEmpty U₀.left ∨ ∃ V : X.left.Opens, I.subschemeι ζ ∈ V ∧
      (V : Set X.left) ∩ (I.support.compl : Set X.left) ⊆
        Set.range (j' ≫ g ≫ overRestrictι X I.support.compl).left.base := by
  have := hX.1
  set ι := (overRestrictι X I.support.compl).left
  have hι : IsOpenEmbedding ι.base := ι.isOpenEmbedding
  have hιr : Set.range ι.base = (I.support.compl : Set X.left) := range_overRestrictι X _
  -- the image of `Z₀` contains the generic point of `X`
  have hη : genericPoint X.left ∈ Set.range (g ≫ overRestrictι X I.support.compl).left.base := by
    refine genericPoint_mem_of_mem_closure hX hh hI ζ hζ ?_ ?_ hζZ₀
    · rintro _ ⟨z, rfl⟩
      rw [← hιr]
      exact ⟨_, rfl⟩
    · have he : Set.range (g ≫ overRestrictι X I.support.compl).left.base =
          ι.base '' Set.range g.left.base := by
        rw [← Set.range_comp]
        rfl
      rw [he, ← hιr]
      exact hι.isEmbedding.closure_image_inter_range_subset g.left.isClosedEmbedding.isClosed_range
  -- hence `g` is surjective
  obtain ⟨z₀, hz₀⟩ := hη
  have hsurj : Function.Surjective g.left.base := by
    intro z
    have hsp : g.left.base z₀ ⤳ z := by
      rw [← hι.isInducing.specializes_iff]
      exact hz₀ ▸ genericPoint_specializes (ι.base z)
    exact hsp.mem_closed g.left.isClosedEmbedding.isClosed_range ⟨z₀, rfl⟩
  -- the image `P` of `U₀` is open
  set P := Set.range (j' ≫ g ≫ overRestrictι X I.support.compl).left.base
  have hPe : P = ι.base '' (g.left.base '' Set.range j'.left.base) := by
    rw [Set.image_image, ← Set.range_comp]
    rfl
  have hgopen : IsOpenMap g.left.base := by
    intro W hW
    rw [← compl_compl W, Set.image_compl_eq ⟨g.left.isClosedEmbedding.injective, hsurj⟩]
    exact (g.left.isClosedEmbedding.isClosedMap _ hW.isClosed_compl).isOpen_compl
  have hP : IsOpen P := hPe ▸ hι.isOpenMap _ (hgopen _ j'.left.isOpenEmbedding.isOpen_range)
  by_cases hU : IsEmpty U₀.left
  · exact Or.inl hU
  right
  obtain ⟨u⟩ := not_isEmpty_iff.1 hU
  have hηP : genericPoint X.left ∈ P :=
    ((genericPoint_spec X.left).mem_open_set_iff hP).2 ⟨_, trivial, u, rfl⟩
  set D := (I.support.compl : Set X.left) \ P
  refine ⟨⟨(closure D)ᶜ, isClosed_closure.isOpen_compl⟩, fun hζD ↦ ?_, ?_⟩
  · refine (genericPoint_mem_of_mem_closure hX hh hI ζ hζ (R := D) Set.sdiff_subset ?_ hζD).2 hηP
    rintro y ⟨hyD, hyO⟩
    refine ⟨hyO, fun hyP ↦ ?_⟩
    obtain ⟨w, ⟨hwP, hwD⟩⟩ := mem_closure_iff.1 hyD P hP hyP
    exact hwD.2 hwP
  · rintro y ⟨hyD, hyO⟩
    by_contra hyP
    exact hyD (subset_closure ⟨hyO, hyP⟩)

/-! ### Sheaf-theoretic part of route (a) -/

variable {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (k' : Type u) [Field k'] [Algebra k k'] [IsSeparated X.hom]

/-- **Empty support**: if the open `U₀` carrying the lisse sheaf `M` is empty, the lisse generator
`Rg_! Rj'_! M` vanishes, and so does the restricted specialization of its extension by zero. -/
theorem exists_isZero_upperStar_nearbyCycles_lowerShriek_of_isEmpty
    {I : X.left.IdealSheafData}
    {Z₀ : Over (Spec (.of k))} [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    [IsSeparated Z₀.hom] (g : Z₀ ⟶ overRestrict X I.support.compl) [IsClosedImmersion g.left]
    {U₀ : Over (Spec (.of k))} [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [IsSeparated U₀.hom] (j' : U₀ ⟶ Z₀) [IsOpenImmersion j'.left] [IsEmpty U₀.left]
    (M : Dᵇc(U₀.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N : Dᵇc((overRestrict X I.support.compl).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (e : N ≅ (boundedConstructibleLowerShriek ℓ g).obj
      ((boundedConstructibleLowerShriek ℓ j').obj M))
    (ζ : (centre X I).left) :
    ∃ U : (centre X I).left.Opens, ζ ∈ U ∧
      IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦
        Profinite.padicAlgClRingObj ℓ⟧)).obj
        (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          (((deformationModel X I k').nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
            ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
              (overRestrictι X I.support.compl)).obj N).obj))) := by
  have hM : IsZero M := IsZero.of_full_of_faithful_of_isZero (boundedConstructible _).ι M
    (isZero_derivedCategory_of_isEmpty ℓ M.obj)
  have hN : IsZero N := ((boundedConstructibleLowerShriek ℓ g).map_isZero
    ((boundedConstructibleLowerShriek ℓ j').map_isZero hM)).of_iso e
  refine ⟨⊤, trivial, Functor.map_isZero _ (Functor.map_isZero _
    (NearbyCyclesModel.isZero_nearbyCycles_obj _ _ ?_))⟩
  exact (boundedConstructible _).ι.map_isZero
    ((boundedConstructibleOpenImmersionLowerShriek _ ℓ _).map_isZero hN)

set_option linter.unusedVariables false in
-- The lisse generator data are part of the interface of the reduction.
/-- **The codimension-one core** (route (a), after the geometric reduction
`isEmpty_or_exists_opens_subset_range`): the hypotheses of
`exists_isZero_upperStar_nearbyCycles_lowerShriek_lisseGenerator_of_mem_closure`, with the
closure condition replaced by its consequence that, on an open neighbourhood `V` of `ζ`, the
lisse generator `Rg_! Rj'_! M` is lisse on all of `V ∖ Z`.

This is the genuine local acyclicity statement: near `ζ` the complex `j_! N` is the extension by
zero of a lisse complex on the complement of the divisor (up to the universal homeomorphism
`U₀ ∩ V ⟶ V ∖ Z`), and `Le^* Ψ_X(j_! N)` vanishes near `ζ`. It holds for every bounded
constructible `N` (`exists_isZero_upperStar_nearbyCycles_lowerShriek_padicAlgCl`), by reduction to
`𝔽_E`-coefficients through an integral model of `N` and derived Nakayama. -/
theorem exists_isZero_upperStar_nearbyCycles_lowerShriek_of_subset_range
    [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
    (hX : IsNormalScheme X.left) {h : Γ(X.left, ⊤)} (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    {Z₀ : Over (Spec (.of k))} [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    [IsSeparated Z₀.hom] (g : Z₀ ⟶ overRestrict X I.support.compl) [IsClosedImmersion g.left]
    {U₀ : Over (Spec (.of k))} [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [IsSeparated U₀.hom] [IsAffine U₀.left] (j' : U₀ ⟶ Z₀) [IsOpenImmersion j'.left]
    (M : Dᵇc(U₀.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (hM : IsDualizable M)
    (N : Dᵇc((overRestrict X I.support.compl).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (e : N ≅ (boundedConstructibleLowerShriek ℓ g).obj
      ((boundedConstructibleLowerShriek ℓ j').obj M))
    (ζ : (centre X I).left) (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left)
    (V : X.left.Opens) (hζV : I.subschemeι ζ ∈ V)
    (hV : (V : Set X.left) ∩ (I.support.compl : Set X.left) ⊆
      Set.range (j' ≫ g ≫ overRestrictι X I.support.compl).left.base) :
    ∃ U : (centre X I).left.Opens, ζ ∈ U ∧
      IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦
        Profinite.padicAlgClRingObj ℓ⟧)).obj
        (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          (((deformationModel X I k').nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
            ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
              (overRestrictι X I.support.compl)).obj N).obj))) :=
  exists_isZero_upperStar_nearbyCycles_lowerShriek_padicAlgCl k' hX hh hI ζ hζ N

/-- **The target modulo the codimension-one core**: route (a) reduces
`exists_isZero_upperStar_nearbyCycles_lowerShriek_lisseGenerator_of_mem_closure` to
`exists_isZero_upperStar_nearbyCycles_lowerShriek_of_subset_range`, by the geometric reduction
`isEmpty_or_exists_opens_subset_range` and the empty case
`exists_isZero_upperStar_nearbyCycles_lowerShriek_of_isEmpty`. -/
theorem exists_isZero_upperStar_nearbyCycles_lowerShriek_lisseGenerator_of_mem_closure
    [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
    (hX : IsNormalScheme X.left) {h : Γ(X.left, ⊤)} (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    {Z₀ : Over (Spec (.of k))} [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    [IsSeparated Z₀.hom] (g : Z₀ ⟶ overRestrict X I.support.compl) [IsClosedImmersion g.left]
    {U₀ : Over (Spec (.of k))} [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [IsSeparated U₀.hom] [IsAffine U₀.left] (j' : U₀ ⟶ Z₀) [IsOpenImmersion j'.left]
    (M : Dᵇc(U₀.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (hM : IsDualizable M)
    (N : Dᵇc((overRestrict X I.support.compl).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (e : N ≅ (boundedConstructibleLowerShriek ℓ g).obj
      ((boundedConstructibleLowerShriek ℓ j').obj M))
    (ζ : (centre X I).left) (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left)
    (hζZ₀ : I.subschemeι ζ ∈ closure (Set.range (g ≫ overRestrictι X I.support.compl).left.base)) :
    ∃ U : (centre X I).left.Opens, ζ ∈ U ∧
      IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦
        Profinite.padicAlgClRingObj ℓ⟧)).obj
        (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          (((deformationModel X I k').nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
            ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
              (overRestrictι X I.support.compl)).obj N).obj))) := by
  rcases isEmpty_or_exists_opens_subset_range hX hh hI g j' ζ hζ hζZ₀ with hU | ⟨V, hζV, hV⟩
  · exact exists_isZero_upperStar_nearbyCycles_lowerShriek_of_isEmpty k' g j' M N e ζ
  · exact exists_isZero_upperStar_nearbyCycles_lowerShriek_of_subset_range k' hX hh hI g j' M hM
      N e ζ hζ V hζV hV

/-- **The local computation at a generic point of a principal divisor for lisse generators**
(the local nearby-cycles computation of the proof of blueprint `det-sp-generic-divisor`, for
extensions by zero of lisse generators): let `X` be normal, `Z = V(h)` for a nonzero global
function `h`, `j : X ∖ Z ⟶ X` the complement, `N` a lisse generator of `Dᵇc(X ∖ Z)⟦ℚ̲̄_ℓ⟧` and `ζ`
a generic point of an irreducible component of `Z`. Then the restriction `Le^* Ψ_X(j_! N)` to the
zero section vanishes over a neighbourhood of `ζ`: the extension by zero is locally acyclic along
the divisor near `ζ`. Unfinished. -/
theorem exists_isZero_upperStar_nearbyCycles_lowerShriek_lisseGenerator [IsSepClosed k']
    [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] (hX : IsNormalScheme X.left)
    {h : Γ(X.left, ⊤)} (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    (N : Dᵇc((overRestrict X I.support.compl).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hN : lisseGenerator ℓ (overRestrict X I.support.compl) N)
    (ζ : (centre X I).left) (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left) :
    ∃ U : (centre X I).left.Opens, ζ ∈ U ∧
      IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦
        Profinite.padicAlgClRingObj ℓ⟧)).obj
        (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          (((deformationModel X I k').nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
            ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
              (overRestrictι X I.support.compl)).obj N).obj))) := by
  obtain ⟨Z₀, _, _, _, g, _, U₀, _, _, _, _, j', _, M, hM, hNM⟩ := hN
  by_cases hζZ₀ : I.subschemeι ζ ∈
      closure (Set.range (g ≫ overRestrictι X I.support.compl).left.base)
  · exact exists_isZero_upperStar_nearbyCycles_lowerShriek_lisseGenerator_of_mem_closure k' hX
      hh hI g j' M hM N hNM.some ζ hζ hζZ₀
  · exact exists_isZero_upperStar_nearbyCycles_lowerShriek_of_notMem_closure k' g _ N hNM.some ζ
      hζZ₀

/-- **Reduction of the local computation to the lisse generators**: for `L` with `Li^* L = 0`,
the restricted specialization `Le^* Ψ_X(L)` vanishes near `ζ` as soon as it does for the
extensions by zero `j_! N` of the lisse generators `N` of `Dᵇc(X ∖ Z)⟦ℚ̲̄_ℓ⟧`. Indeed the
open–closed triangle `j_! Lj^* L ⟶ L ⟶ Ri_* Li^* L ⟶` shows `L ≅ j_! Lj^* L`. -/
theorem exists_isZero_upperStar_nearbyCycles_of_lowerShriek {I : X.left.IdealSheafData}
    (ζ : (centre X I).left)
    (h : ∀ N : Dᵇc((overRestrict X I.support.compl).left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      lisseGenerator ℓ (overRestrict X I.support.compl) N →
      nearbyCyclesVanishNear X I k' (Profinite.padicAlgClRingObj ℓ) ζ
        ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
          (overRestrictι X I.support.compl)).obj N).obj)
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hL : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (centreι X I)).obj L)) :
    nearbyCyclesVanishNear X I k' (Profinite.padicAlgClRingObj ℓ) ζ L.obj := by
  obtain ⟨δ, hδ⟩ := exists_distTriang_openImmersionLowerShriek_openClosed
    (overRestrictι X I.support.compl) (centreι X I) (isCompl_range_overRestrictι_centreι I) L
  have h₃ : IsZero ((boundedConstructible _).ι.obj ((boundedConstructibleLowerStar ℓ
      (centreι X I)).obj ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (centreι X I)).obj L))) :=
    (boundedConstructible _).ι.map_isZero ((boundedConstructibleLowerStar ℓ _).map_isZero hL)
  have : IsIso ((boundedConstructible _).ι.map
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
        (overRestrictι X I.support.compl)).counit.app L)) :=
    (Triangle.isZero₃_iff_isIso₁ _ hδ).1 h₃
  exact (nearbyCyclesVanishNear X I k' _ ζ).prop_of_iso (asIso ((boundedConstructible _).ι.map
    ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
      (overRestrictι X I.support.compl)).counit.app L)))
    (nearbyCyclesVanishNear_lowerShriek_of_lisseGenerator k' ζ h _)

end AlgebraicGeometry.ProEtale.CondensedRing
