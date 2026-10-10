/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Sites.DivisorMap
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-!
# Local structure of divisors on étale neighbourhoods

Let `X` be an integral regular locally noetherian scheme with generic point
`i : Spec k(X) ⟶ X`, and `V` an étale `X`-scheme. The local rings of `V` are regular, hence
unique factorisation domains, and the local generic ring of `V` at a point `y` is the fraction
field of `𝒪_{V,y}` (`AlgebraicGeometry.Scheme.Etale.isFractionRing_localGenericRing`). This file
collects the local facts about the divisors of functions on the generic fibre of `V` which enter
the proof of the exactness of the divisor sequence.

## Main statements

- `AlgebraicGeometry.Scheme.exists_opens_isPreirreducible`: a point whose local ring is a domain
  has an irreducible open neighbourhood.
- `AlgebraicGeometry.Scheme.Etale.injective_toLocalGenericRing`: on an integral quasi-separated
  étale `X`-scheme, a function on the generic fibre is determined by its image in the local
  generic ring at any point.
- `AlgebraicGeometry.Scheme.Etale.exists_specializes_comap_eq_span`: the prime elements of the
  local ring `𝒪_{V,y}` correspond to the points of codimension one generalising `y`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Order TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- A point whose local ring is a domain has an irreducible open neighbourhood: the
generalisations of `y` are the images of the primes of `𝒪_{V,y}`, which all contain the zero
ideal, so `y` lies in a single irreducible component of a noetherian open neighbourhood. -/
lemma exists_opens_isPreirreducible {V : Scheme.{u}} [IsLocallyNoetherian V] (y : V)
    [IsDomain (V.presheaf.stalk y)] :
    ∃ W : V.Opens, y ∈ W ∧ IsPreirreducible (W : Set V) := by
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hyU₀, -⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have : NoetherianSpace U₀ := @noetherianSpace_of_isAffineOpen _ U₀ hU₀
    (IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩)
  have : QuasiSober U₀ := inferInstanceAs (QuasiSober (Scheme.Opens.toScheme (X := V) U₀))
  -- the generic point of `Spec 𝒪_{V,y}` generalises every generalisation of `y`
  let c : V := V.fromSpecStalk y ⟨⊥, Ideal.isPrime_bot⟩
  have hc : ∀ a : V, a ⤳ y → c ⤳ a := by
    intro a ha
    have ha' : a ∈ Set.range (V.fromSpecStalk y) := by rw [Scheme.range_fromSpecStalk]; exact ha
    obtain ⟨p, rfl⟩ := ha'
    exact ((PrimeSpectrum.le_iff_specializes _ _).1 bot_le).map (V.fromSpecStalk y).continuous
  have hcU₀ : c ∈ U₀ := (hc y specializes_rfl).mem_open U₀.2 hyU₀
  -- hence `y` lies in a unique irreducible component of `U₀`
  obtain ⟨W₀, hW₀, hyW₀, hirr⟩ := NoetherianSpace.exists_isOpen_isPreirreducible
    (α := U₀) ⟨y, hyU₀⟩ fun Z₁ hZ₁ Z₂ hZ₂ h₁ h₂ ↦ by
      have key (Z : Set U₀) (hZ : Z ∈ irreducibleComponents U₀) (h : ⟨y, hyU₀⟩ ∈ Z) :
          Z = closure {⟨c, hcU₀⟩} := by
        obtain ⟨g, hg⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents _ hZ)
        have hcg : (⟨c, hcU₀⟩ : U₀) ⤳ g :=
          (Topology.IsInducing.subtypeVal.specializes_iff).1
            (hc g.1 ((hg.specializes h).map continuous_subtype_val))
        have hsub : Z ⊆ closure {⟨c, hcU₀⟩} := by
          rw [← hg.def]
          exact specializes_iff_closure_subset.1 hcg
        exact ((hZ.2 isIrreducible_singleton.closure hsub).antisymm hsub).symm
      rw [key Z₁ hZ₁ h₁, key Z₂ hZ₂ h₂]
  refine ⟨⟨Subtype.val '' W₀, U₀.2.isOpenMap_subtype_val W₀ hW₀⟩, ⟨_, hyW₀, rfl⟩,
    hirr.image _ continuous_subtype_val.continuousOn⟩

/-- A germ at `y` is the germ of a section over an affine open neighbourhood of `y` inside any
given open neighbourhood. -/
lemma exists_isAffineOpen_germ_eq {V : Scheme.{u}} {y : V} {N : V.Opens} (hyN : y ∈ N)
    (t : V.presheaf.stalk y) :
    ∃ (U : V.Opens) (_ : IsAffineOpen U) (hyU : y ∈ U) (_ : U ≤ N) (s : Γ(V, U)),
      V.presheaf.germ U y hyU s = t := by
  obtain ⟨U₁, hyU₁, s₁, hs₁⟩ := V.presheaf.exists_germ_eq t
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUle⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ U₁ ⊓ N from ⟨hyU₁, hyN⟩)
      (U₁ ⊓ N).isOpen
  refine ⟨U, hU, hyU, fun z hz ↦ (hUle hz).2, V.presheaf.map (homOfLE fun z hz ↦ (hUle hz).1).op s₁,
    ?_⟩
  rw [V.presheaf.germ_res_apply]
  exact hs₁

/-- A unit of the local ring at `y` is the germ of a unit over an affine open neighbourhood of `y`
inside any given open neighbourhood. -/
lemma exists_isAffineOpen_isUnit_germ_eq {V : Scheme.{u}} {y : V} {N : V.Opens} (hyN : y ∈ N)
    (r : (V.presheaf.stalk y)ˣ) :
    ∃ (U : V.Opens) (_ : IsAffineOpen U) (hyU : y ∈ U) (_ : U ≤ N) (s : Γ(V, U)),
      IsUnit s ∧ V.presheaf.germ U y hyU s = r := by
  obtain ⟨U₁, hU₁, hyU₁, hU₁N, s₁, hs₁⟩ := exists_isAffineOpen_germ_eq hyN r.val
  have hyD : y ∈ V.basicOpen s₁ := (V.mem_basicOpen s₁ y hyU₁).2 (hs₁ ▸ r.isUnit)
  refine ⟨V.basicOpen s₁, hU₁.basicOpen s₁, hyD, (V.basicOpen_le s₁).trans hU₁N,
    V.presheaf.map (homOfLE (V.basicOpen_le s₁)).op s₁, V.toRingedSpace.isUnit_res_basicOpen s₁,
    ?_⟩
  rw [V.presheaf.germ_res_apply]
  exact hs₁

/-- An open subscheme of a scheme with reduced local rings, contained in a preirreducible set and
containing a point, is integral. -/
lemma isIntegral_of_isPreirreducible {V : Scheme.{u}} [IsReduced V] {U : V.Opens} {y : V}
    (hyU : y ∈ U) {W : Set V} (hW : IsPreirreducible W) (hUW : (U : Set V) ⊆ W) :
    IsIntegral U.toScheme := by
  have : Nonempty U := ⟨⟨y, hyU⟩⟩
  have : IrreducibleSpace U := Subtype.irreducibleSpace
    ⟨⟨y, hyU⟩, hW.open_subset U.2 hUW⟩
  have : IsReduced U.toScheme := isReduced_of_isOpenImmersion U.ι
  exact isIntegral_of_irreducibleSpace_of_isReduced _

namespace Etale

variable {X : Scheme.{u}} [IsIntegral X]

/-- **Functions on the generic fibre are determined locally.** Let `X` be an integral scheme and
`V` an étale `X`-scheme which is integral and quasi-separated. Then a function on the generic
fibre `V ×_X Spec k(X)` is determined by its image in the local generic ring at any point `y`:
`Spec 𝒪_{V,y} ⟶ V` is scheme-theoretically dominant, and stays so after the flat base change to
the generic fibre. -/
lemma injective_toLocalGenericRing (V : X.Etale) [IsIntegral V.left]
    [QuasiSeparatedSpace V.left] (y : V.left) :
    Function.Injective (toLocalGenericRing V y) := by
  have : IsDominant (V.left.fromSpecStalk y) := by
    rw [isDominant_iff, DenseRange, range_fromSpecStalk]
    refine dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset ?_)
    rw [← (genericPoint_spec V.left).def]
    exact closure_mono (Set.singleton_subset_iff.2 ((genericPoint_spec V.left).specializes trivial))
  have : IsSchemeTheoreticallyDominant (V.left.fromSpecStalk y) := .of_isDominant _
  have : QuasiCompact (V.left.fromSpecStalk y) := quasiCompact_of_compactSpace _
  let m := pullback.map (V.left.fromSpecStalk y ≫ V.hom) X.fromSpecFunctionField V.hom
    X.fromSpecFunctionField (V.left.fromSpecStalk y) (𝟙 _) (𝟙 _) (by simp) (by simp)
  have H : IsPullback (pullback.fst _ _) m (V.left.fromSpecStalk y)
      (pullback.fst V.hom X.fromSpecFunctionField) := by
    refine IsPullback.of_bot ?_ (by simp [m]) (IsPullback.of_hasPullback V.hom _)
    have : m ≫ pullback.snd V.hom X.fromSpecFunctionField =
        pullback.snd (V.left.fromSpecStalk y ≫ V.hom) X.fromSpecFunctionField := by
      simp [m]
    rw [this]
    exact IsPullback.of_hasPullback _ _
  have : Flat X.fromSpecFunctionField := Scheme.flat_fromSpecStalk _ _
  have : IsSchemeTheoreticallyDominant m := IsSchemeTheoreticallyDominant.of_isPullback H
  have : QuasiCompact m := MorphismProperty.of_isPullback H inferInstance
  exact m.app_injective ⊤

/-- The germ at a point of an open subscheme `U` of a section over `U`, transported to `U`. -/
lemma germ_topIso_inv {V : Scheme.{u}} (U : V.Opens) (a : Γ(V, U)) (z : U) :
    U.toScheme.presheaf.germ ⊤ z trivial (U.topIso.inv a) =
      (U.stalkIso z).inv (V.presheaf.germ U z z.2 a) := by
  rw [← Scheme.Opens.germ_stalkIso_inv U ⊤ z trivial, Scheme.Opens.topIso_inv,
    CommRingCat.comp_apply]
  congr 1
  exact V.presheaf.germ_res_apply _ _ _ _

/-- The map `Γ(Spec 𝒪_{V,y} ×_X Spec k(X), 𝒪) ⟶ Γ(Spec 𝒪_{V,w} ×_X Spec k(X), 𝒪)` of local generic
rings induced by a generalisation `w ⤳ y`. -/
noncomputable def localGenericRingSpecializes (V : X.Etale) {w y : V.left} (h : w ⤳ y) :
    localGenericRing V y ⟶ localGenericRing V w :=
  (pullback.map _ _ _ _ (Spec.map (V.left.presheaf.stalkSpecializes h)) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, SpecMap_stalkSpecializes_fromSpecStalk_assoc]) (by simp)).appTop

lemma toLocalGenericRing_comp_localGenericRingSpecializes (V : X.Etale) {w y : V.left}
    (h : w ⤳ y) :
    toLocalGenericRing V y ≫ localGenericRingSpecializes V h = toLocalGenericRing V w := by
  rw [toLocalGenericRing, toLocalGenericRing, localGenericRingSpecializes,
    ← Scheme.Hom.comp_appTop, pullback.map_comp]
  congr 2
  exact SpecMap_stalkSpecializes_fromSpecStalk h

lemma stalkToLocalGenericRing_comp_localGenericRingSpecializes (V : X.Etale) {w y : V.left}
    (h : w ⤳ y) :
    stalkToLocalGenericRing V y ≫ localGenericRingSpecializes V h =
      V.left.presheaf.stalkSpecializes h ≫ stalkToLocalGenericRing V w := by
  rw [stalkToLocalGenericRing, stalkToLocalGenericRing, localGenericRingSpecializes,
    Category.assoc, ← Scheme.Hom.comp_appTop, pullback.lift_fst, Scheme.Hom.comp_appTop,
    ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

/-- In an algebra, `φ * b = a` with `b` a unit means that `φ` is the image of `a b⁻¹`. -/
lemma _root_.eq_algebraMap_mul_inv_of_mul_eq {A L : Type*} [CommRing A] [CommRing L]
    [Algebra A L] {φ : L} {a b : A} (hb : IsUnit b) (h : φ * algebraMap A L b = algebraMap A L a) :
    φ = algebraMap A L (a * ↑hb.unit⁻¹) := by
  rw [map_mul, ← h, mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]

variable [IsRegular X]

/-- The image in the local generic ring at a point `z` of an open `U` of a function on `V`,
restricted to the generic fibre of `U`. -/
lemma toLocalGenericRing_map_ofOpensι (V : X.Etale) (U : V.left.Opens) (z : U)
    (f : Γ(pullback V.hom X.fromSpecFunctionField, ⊤)) :
    toLocalGenericRing (ofOpens V U) z
        (((MorphismProperty.Over.pullback @Etale ⊤ X.fromSpecFunctionField).map
          (ofOpensι V U)).left.appTop f) =
      localGenericRingMap (ofOpensι V U) z (toLocalGenericRing V z.1 f) :=
  (congrArg (fun g ↦ g.hom f) (toLocalGenericRing_comp_localGenericRingMap (ofOpensι V U) z)).symm

/-- The image in the local generic ring at a point `z` of an open `U` of a section of `𝒪_V` over
`U`, pulled back to the generic fibre of `U`. -/
lemma toLocalGenericRing_fst_topIso_inv (V : X.Etale) (U : V.left.Opens) (a : Γ(V.left, U))
    (z : U) :
    toLocalGenericRing (ofOpens V U) z
        ((pullback.fst (ofOpens V U).hom X.fromSpecFunctionField).appTop (U.topIso.inv a)) =
      localGenericRingMap (ofOpensι V U) z
        (stalkToLocalGenericRing V z.1 (V.left.presheaf.germ U z z.2 a)) := by
  refine (toLocalGenericRing_fst_appTop (ofOpens V U) z (U.topIso.inv a)).trans ?_
  refine (congrArg _ ((germ_topIso_inv U a z).trans
    (congrArg (fun g ↦ g.hom (V.left.presheaf.germ U z z.2 a))
      (Scheme.Opens.stalkIso_inv U z)))).trans ?_
  exact (congrArg (fun g ↦ g.hom (V.left.presheaf.germ U z z.2 a))
    (stalkToLocalGenericRing_comp_localGenericRingMap (ofOpensι V U) z)).symm

/-- A function on the generic fibre which is a quotient `a / b` of functions on `V` invertible
at `z` has order `0` at `z`. -/
lemma ord_eq_zero_of_mul_eq (W : X.Etale) (z : W.left)
    (g : Γ(pullback W.hom X.fromSpecFunctionField, ⊤)ˣ) (a b : Γ(W.left, ⊤))
    (h : g.val * (pullback.fst W.hom X.fromSpecFunctionField).appTop b =
      (pullback.fst W.hom X.fromSpecFunctionField).appTop a)
    (ha : z ∈ W.left.basicOpen a) (hb : z ∈ W.left.basicOpen b) : ord W z g = 0 := by
  by_cases hcoh : coheight (W.hom z) = 1
  · rw [ord, if_pos hcoh]
    have := isDiscreteValuationRing_stalk W hcoh
    let := (stalkToLocalGenericRing W z).hom.toAlgebra
    have := isFractionRing_localGenericRing W z
    have ha' := (W.left.mem_basicOpen_top a z).1 ha
    have hb' := (W.left.mem_basicOpen_top b z).1 hb
    have h' := congrArg (toLocalGenericRing W z).hom h
    rw [map_mul, toLocalGenericRing_fst_appTop, toLocalGenericRing_fst_appTop] at h'
    rw [eq_algebraMap_mul_inv_of_mul_eq hb' h']
    exact Ring.ordOf_algebraMap_of_isUnit (ha'.mul hb'.unit⁻¹.isUnit)
  · exact ord_of_coheight_ne_one W hcoh _

/-- A point with a generalisation other than itself and the generic point does not have
codimension one. -/
lemma _root_.AlgebraicGeometry.Scheme.coheight_ne_one_of_specializes {S : Scheme.{u}}
    [IrreducibleSpace S] {z c : S} (hcz : c ⤳ z) (hne : c ≠ z) (hc : c ≠ genericPoint S) :
    coheight z ≠ 1 := by
  have h₁ : z < c := lt_of_le_not_ge (le_iff_specializes.2 hcz)
    fun h ↦ hne (hcz.antisymm (le_iff_specializes.1 h)).eq
  have h₂ : c < genericPoint S := lt_of_le_not_ge
    (le_iff_specializes.2 ((genericPoint_spec S).specializes trivial))
    fun h ↦ hc (((genericPoint_spec S).specializes trivial).antisymm
      (le_iff_specializes.1 h)).eq.symm
  have h₃ := coheight_add_one_le h₁
  have h₄ := coheight_add_one_le h₂
  intro h
  rw [h] at h₃
  have h₅ : (2 : ℕ∞) ≤ coheight (genericPoint S) + 1 + 1 := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ coheight (genericPoint S) + 1 + 1 := by gcongr; exact bot_le
  have h₆ : coheight (genericPoint S) + 1 + 1 ≤ coheight c + 1 := by gcongr
  exact absurd (h₅.trans (h₆.trans h₃)) (by decide)


/-- **Prime elements of a local ring define points of codimension one.** Let `X` be an integral
regular scheme and `V` an étale `X`-scheme. For a prime element `p` of the local ring `𝒪_{V,y}`,
the point of `V` defined by the prime ideal `(p)` lies over a point of `X` of codimension one: its
local ring is the localization of `𝒪_{V,y}` at `(p)`
(`AlgebraicGeometry.Scheme.isLocalization_stalkSpecializes`), of dimension the height of `(p)`,
which is one by Krull's principal ideal theorem. -/
lemma coheight_hom_fromSpecStalk_span (V : X.Etale) (y : V.left) {p : V.left.presheaf.stalk y}
    (hp : Prime p) :
    coheight (V.hom (V.left.fromSpecStalk y
      ⟨Ideal.span {p}, (Ideal.span_singleton_prime hp.ne_zero).2 hp⟩)) = 1 := by
  set q : PrimeSpectrum (V.left.presheaf.stalk y) :=
    ⟨Ideal.span {p}, (Ideal.span_singleton_prime hp.ne_zero).2 hp⟩
  have : (Ideal.span {p}).IsPrime := q.2
  rw [coheight_hom_apply]
  have h := ringKrullDim_stalk_eq_coheight (V.left.fromSpecStalk y q)
  let := (V.left.presheaf.stalkSpecializes (fromSpecStalk_specializes q)).hom.toAlgebra
  have : IsLocalization.AtPrime (V.left.presheaf.stalk (V.left.fromSpecStalk y q))
    (Ideal.span {p}) := isLocalization_stalkSpecializes_fromSpecStalk q
  have hd := IsLocalization.AtPrime.ringKrullDim_eq_height (Ideal.span {p})
    (V.left.presheaf.stalk (V.left.fromSpecStalk y q))
  have hh := Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hp.ne_zero) hp.not_isUnit
  rw [hd, hh] at h
  exact_mod_cast h.symm

variable [IsLocallyNoetherian X]

/-- **Units of the local ring spread out.** Let `X` be an integral regular locally noetherian
scheme and `V` an étale `X`-scheme. If a function `f` on the generic fibre of `V` maps to a unit
`r` of `𝒪_{V,y}` in the local generic ring at `y`, then near `y` it is a unit of `𝒪_V`: `r` is the
germ of a unit on an affine irreducible neighbourhood `U` of `y`, which agrees with `f` on the
generic fibre of `U` by `AlgebraicGeometry.Scheme.Etale.injective_toLocalGenericRing`. -/
lemma exists_eq_of_toLocalGenericRing_eq (V : X.Etale) (y : V.left)
    (f : Γ(pullback V.hom X.fromSpecFunctionField, ⊤)) (r : (V.left.presheaf.stalk y)ˣ)
    (hr : toLocalGenericRing V y f = stalkToLocalGenericRing V y r) :
    ∃ (U : V.left.Opens) (_ : y ∈ U) (u : Γ(Etale.ofOpens V U |>.left, ⊤)ˣ),
      (pullback.fst (Etale.ofOpens V U).hom X.fromSpecFunctionField).appTop u.val =
        ((MorphismProperty.Over.pullback @Etale ⊤ X.fromSpecFunctionField).map
          (Etale.ofOpensι V U)).left.appTop f := by
  have : IsLocallyNoetherian ((Functor.fromPUnit X).obj V.right) := ‹IsLocallyNoetherian X›
  have : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian V.hom
  have : IsReduced V.left := isReduced_of_isReduced_stalk _
  obtain ⟨W₀, hyW₀, hW₀⟩ := exists_opens_isPreirreducible y
  obtain ⟨U, hU, hyU, hUW₀, s, hs, hsr⟩ := exists_isAffineOpen_isUnit_germ_eq hyW₀ r
  have : IsIntegral (ofOpens V U).left := isIntegral_of_isPreirreducible hyU hW₀ hUW₀
  have : IsAffine (ofOpens V U).left := hU
  refine ⟨U, hyU, (hs.map U.topIso.inv.hom).unit, ?_⟩
  refine injective_toLocalGenericRing (ofOpens V U) ⟨y, hyU⟩ ?_
  have h₁ := congrArg (fun g ↦ g.hom f)
    (toLocalGenericRing_comp_localGenericRingMap (ofOpensι V U) ⟨y, hyU⟩)
  have h₂ := congrArg (fun g ↦ g.hom r.val)
    (stalkToLocalGenericRing_comp_localGenericRingMap (ofOpensι V U) ⟨y, hyU⟩)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h₁ h₂
  have h₃ : (ofOpens V U).left.presheaf.germ ⊤ ⟨y, hyU⟩ trivial (U.topIso.inv s) =
      (ofOpensι V U).left.stalkMap ⟨y, hyU⟩ r.val := by
    exact (germ_topIso_inv U s ⟨y, hyU⟩).trans ((congrArg (U.stalkIso ⟨y, hyU⟩).inv.hom hsr).trans
      (congrArg (fun g ↦ g.hom r.val) (Scheme.Opens.stalkIso_inv U ⟨y, hyU⟩)))
  refine ((toLocalGenericRing_fst_appTop (ofOpens V U) ⟨y, hyU⟩ (U.topIso.inv s)).trans ?_).trans h₁
  exact (congrArg _ h₃).trans (h₂.symm.trans (congrArg _ hr.symm))

/-- **Local algebraic Hartogs at a point.** Let `X` be an integral regular locally noetherian
scheme, `V` an étale `X`-scheme and `f` a unit on the generic fibre of `V` whose order vanishes
at every generalisation of `y`. Then `f` maps to a unit of `𝒪_{V,y}` in the local generic ring
at `y`. Write the image of `f` as a reduced fraction `a / b` in the fraction field of the unique
factorisation domain `𝒪_{V,y}`; a prime factor `p` of `a` or `b` defines a generalisation `w` of
`y` of codimension one at which `f` has order zero, so `a` and `b` have the same image in the
residue field of `𝒪_{V,w}`, and `p` divides both. -/
lemma exists_toLocalGenericRing_eq_of_ord_eq_zero (V : X.Etale) (y : V.left)
    (f : Γ(pullback V.hom X.fromSpecFunctionField, ⊤)ˣ) (hf : ∀ w, w ⤳ y → ord V w f = 0) :
    ∃ r : (V.left.presheaf.stalk y)ˣ,
      toLocalGenericRing V y f = stalkToLocalGenericRing V y r := by
  have : IsRegular V.left := ⟨fun z ↦ inferInstance⟩
  have : UniqueFactorizationMonoid (V.left.presheaf.stalk y) :=
    IsRegular.uniqueFactorizationMonoid_stalk y
  let A := V.left.presheaf.stalk y
  let L := localGenericRing V y
  let : Algebra A L := (stalkToLocalGenericRing V y).hom.toAlgebra
  have : IsFractionRing A L := isFractionRing_localGenericRing V y
  let : Field L := IsFractionRing.toField A
  obtain ⟨a, b, hab, he⟩ := IsFractionRing.exists_reduced_fraction A (toLocalGenericRing V y f.val)
  have h₁ : stalkToLocalGenericRing V y a =
      toLocalGenericRing V y f * stalkToLocalGenericRing V y b :=
    (IsLocalization.mk'_eq_iff_eq_mul).1 he
  -- a prime divides `a` if and only if it divides `b`
  have key (p : A) (hp : Prime p) : p ∣ a ↔ p ∣ (b : A) := by
    let q : PrimeSpectrum A := ⟨Ideal.span {p}, (Ideal.span_singleton_prime hp.ne_zero).2 hp⟩
    have hw : V.left.fromSpecStalk y q ⤳ y := fromSpecStalk_specializes q
    have hcoh := coheight_hom_fromSpecStalk_span V y hp
    have hq := comap_stalkSpecializes_fromSpecStalk q
    have := isDiscreteValuationRing_stalk V hcoh
    let := (stalkToLocalGenericRing V (V.left.fromSpecStalk y q)).hom.toAlgebra
    have := isFractionRing_localGenericRing V (V.left.fromSpecStalk y q)
    have hord := hf _ hw
    rw [ord, if_pos hcoh] at hord
    obtain ⟨r, hr⟩ := Ring.exists_eq_algebraMap_of_ordOf_eq_zero
      (Units.map (toLocalGenericRing V (V.left.fromSpecStalk y q)).hom.toMonoidHom f) hord
    let σ := (V.left.presheaf.stalkSpecializes hw).hom
    have h₂ := congrArg (localGenericRingSpecializes V hw).hom h₁
    have hc₁ := congrArg (fun g ↦ g.hom f.val)
      (toLocalGenericRing_comp_localGenericRingSpecializes V hw)
    have hc₂ (x : A) := congrArg (fun g ↦ g.hom x)
      (stalkToLocalGenericRing_comp_localGenericRingSpecializes V hw)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hc₁ hc₂
    rw [map_mul, hc₂, hc₂, hc₁] at h₂
    have h₃ : σ a = r * σ b := by
      refine IsFractionRing.injective _
        (localGenericRing V (V.left.fromSpecStalk y q)) ?_
      rw [map_mul]
      exact h₂.trans (congrArg (· * _) hr.symm)
    have mem (x : A) : p ∣ x ↔ σ x ∈ IsLocalRing.maximalIdeal _ := by
      rw [← Ideal.mem_span_singleton]
      exact (Set.ext_iff.1 (congrArg SetLike.coe hq) x).symm
    rw [mem, mem, h₃]
    exact Ideal.unit_mul_mem_iff_mem _ r.isUnit
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [IsLocalization.mk'_zero] at he
    exact (f.isUnit.map (toLocalGenericRing V y).hom).ne_zero he.symm
  have hunit (x : A) (hx0 : x ≠ 0) (hx : ∀ p : A, Prime p → p ∣ x → False) : IsUnit x := by
    by_contra hxu
    obtain ⟨p, hp, hpx⟩ := WfDvdMonoid.exists_irreducible_factor hxu hx0
    exact hx p (UniqueFactorizationMonoid.irreducible_iff_prime.1 hp) hpx
  have ha : IsUnit a := hunit a ha0 fun p hp hpa ↦
    hp.not_isUnit (hab hpa ((key p hp).1 hpa))
  have hb : IsUnit (b : A) := hunit b (nonZeroDivisors.ne_zero b.2) fun p hp hpb ↦
    hp.not_isUnit (hab ((key p hp).2 hpb) hpb)
  refine ⟨ha.unit * hb.unit⁻¹, ?_⟩
  change _ = stalkToLocalGenericRing V y (a * ↑hb.unit⁻¹)
  rw [map_mul, h₁, mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]

end Etale

end AlgebraicGeometry.Scheme
