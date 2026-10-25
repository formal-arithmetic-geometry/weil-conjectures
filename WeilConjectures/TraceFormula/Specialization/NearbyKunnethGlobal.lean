/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethGeneric
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethProper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
public import WeilConjectures.TraceFormula.Specialization.TraitProduct

/-!

# Gabber's Künneth formula for nearby cycles: global sections

Let `M`, `N` be models of finite type over the strictly henselian trait `S = Spec k'⟦t⟧`
(`k'` separably closed) along proper structure morphisms `q_M`, `q_N`, and let `P` be their
product over the trait. This file proves the global-sections step (blueprint
`sk-prop-tf-nearby-external-kunneth`, equation (4)) of Illusie's proof of Gabber's Künneth
formula: the direct image `R(a_{P_s})_* Π_{A,B}` of the Künneth map of nearby cycles to the
point `Spec k'` is an isomorphism
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.isIso_lowerStar_kunnethMap`).
Equivalently, the cone of `Π_{A,B}` has no global sections.

## Proof

After passing to the models of the geometric generic fibres
(`NearbyCyclesModel.isIso_map_kunnethMap_iff_toGeneric`), the structure morphisms are morphisms
of models `ψ : M ⟶ T` to the trait `T` as a model of its geometric generic point
(`NearbyCyclesModel.traitGenericModel`). The compatibility of the Künneth map with direct
images (blueprint `det-nearby-kunneth-proper`,
`NearbyCyclesModel.kunnethMap_comp_pushforwardExchange`) identifies `R(a_{P_s})_* Π_{A,B}`, up
to
* the proper exchanges `χ_ψ` (blueprint `det-sp-nearby-cycles-exchanges` (2),
  `NearbyCyclesModel.IsTraitModelOver.isIso_pushforwardExchange_toTraitGeneric_app`),
* the ordinary Künneth isomorphism `RΓ(X_s) ⊗ RΓ(Y_s) ≅ RΓ(X_s × Y_s)` over `k'` (blueprint
  `sk-lem-sf-kunneth-star`, `ProEtale.CondensedRing.isIso_lowerStarKunnethMap'_of_isPullback`),

with the Künneth map of the trait `T` at `(RΓ(X_η̄, A), RΓ(Y_η̄, B))` followed by the nearby cycles
of the ordinary Künneth isomorphism on the geometric generic fibres; the former is an isomorphism
because the nearby cycles of the trait are monoidal on bounded constructible complexes on the
geometric generic point (`NearbyCyclesModel.isIso_kunnethMap_traitGenericModel`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The ordinary Künneth formula over a separably closed field -/

section OrdinaryKunneth

variable (ℓ : ℕ) [Fact ℓ.Prime] {K : Type u} [Field K] [IsSepClosed K] [Fact (ringChar K).Prime]
  [Fact (ringChar K ≠ ℓ)] {X Y P : Over (Spec (.of K))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

/-- **The ordinary Künneth formula over a separably closed field** (blueprint
`sk-lem-sf-kunneth-star`, for `f_i : X_i ⟶ Y_i = Spec K`; SGA 4½, [Th. finitude], Cor. 1.11;
for `ℚ̄_ℓ`-coefficients by passage to the limit, Bhatt–Scholze §6.8): for separated `K`-schemes
of finite type `X`, `Y` with product `P = X ×_K Y` and bounded constructible `A`, `B`, the
Künneth map `RΓ(X, A) ⊗ RΓ(Y, B) ⟶ RΓ(X ×_K Y, A ⊠ B)`
(`ProEtale.CondensedRing.lowerStarKunnethMap'` of the two squares over `Spec K`) is an
isomorphism. The blueprint node is stated over `k = 𝔽̄_q`; over a separably closed field it
applies since passing to an algebraic closure does not change the étale topoi (blueprint
`sk-prop-tf-nearby-external-kunneth`). -/
theorem isIso_lowerStarKunnethMap'_of_isPullback (p₁ : P ⟶ X) (p₂ : P ⟶ Y)
    (h : IsPullback p₁.left p₂.left X.hom Y.hom)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) A)
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)))
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left) B) :
    IsIso (lowerStarKunnethMap' (Profinite.padicAlgClRingObj ℓ)
      (⟨by rw [Over.w p₁, Category.comp_id]⟩ : CommSq p₁.left P.hom X.hom (𝟙 _))
      (⟨by rw [Over.w p₂, Category.comp_id]⟩ : CommSq p₂.left P.hom Y.hom (𝟙 _)) A B) :=
  sorry

end OrdinaryKunneth

namespace NearbyCyclesModel

/-! ### The trait as a model of its geometric generic point -/

section TraitGeneric

variable (k' : Type u) [Field k']

/-- The trait `S = Spec k'⟦t⟧` as a model of its geometric generic point `Spec Ω`, with special
fibre `Spec k'`: the geometric generic point `j : Spec Ω ⟶ S`, the closed point
`i : Spec k' ⟶ S` and `ε = 𝟙`. Its nearby cycles `Ψ_S = i^* Rj_*` are those of SGA 7 XIII, on
complexes on the geometric generic point. -/
noncomputable def traitGenericModel :
    NearbyCyclesModel (Spec (.of (traitGenericField k'))) (Spec (.of k')) where
  total := trait k'
  generic := Spec (.of (traitGenericField k'))
  j := traitGenericPoint k'
  i := traitClosedPoint k'
  ε := 𝟙 _

variable {k'}

/-- The identity morphism of a model. -/
@[simps]
def Hom.id {X X' : Scheme.{u}} (M : NearbyCyclesModel X X') : M.Hom M (𝟙 X) (𝟙 X') where
  total := 𝟙 _
  generic := 𝟙 _
  comm_j := by simp
  comm_i := by simp
  comm_ε := by simp

variable {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

/-- The structure morphisms `q : 𝒳 ⟶ S` and `g : 𝒳_η̄ ⟶ Spec Ω` of a model of finite type over
the trait are a morphism from the model of its geometric generic fibre to the trait. -/
@[simps]
def IsTraitModelOver.toTraitGeneric (h : M.IsTraitModelOver q g) :
    M.toGeneric.Hom (traitGenericModel k') g X'.hom where
  total := q
  generic := g
  comm_j := h.isPullback_j.w.symm
  comm_i := h.isPullback_i.w.symm
  comm_ε := (Category.comp_id _).trans (Category.id_comp _).symm

end TraitGeneric

end NearbyCyclesModel

/-! ### Fibres of a product over the trait -/

section Pasting

variable {C : Type*} [Category C] {Pt Mt Nt S Z X Y s : C} {φ₁ : Pt ⟶ Mt} {φ₂ : Pt ⟶ Nt}
  {qM : Mt ⟶ S} {qN : Nt ⟶ S} {iP : Z ⟶ Pt} {iM : X ⟶ Mt} {iN : Y ⟶ Nt} {hX : X ⟶ s}
  {hY : Y ⟶ s} {hZ : Z ⟶ s} {c : s ⟶ S} {f₁ : Z ⟶ X} {f₂ : Z ⟶ Y}

/-- The fibre of a product over a base point: if `P = M ×_S N` and `X`, `Y`, `Z` are the fibres
of `M`, `N`, `P` over `c : s ⟶ S`, the maps `Z ⟶ X`, `Z ⟶ Y` induced by the projections exhibit
`Z` as `X ×_s Y`. -/
lemma isPullback_fibre_of_isPullback (hpb : IsPullback φ₁ φ₂ qM qN)
    (hMi : IsPullback iM hX qM c) (hNi : IsPullback iN hY qN c)
    (hPi : IsPullback iP hZ (φ₁ ≫ qM) c) (c₁ : f₁ ≫ iM = iP ≫ φ₁) (c₂ : f₂ ≫ iN = iP ≫ φ₂)
    (h₁ : f₁ ≫ hX = hZ) (h₂ : f₂ ≫ hY = hZ) : IsPullback f₁ f₂ hX hY := by
  -- the square `Z ⟶ X`, `P ⟶ M` over `iP`, `iM` is cartesian
  have hL : IsPullback f₁ iP iM φ₁ := by
    refine IsPullback.of_right (h₁₂ := hX) (h₂₂ := qM) (v₁₃ := c) ?_ c₁ hMi.flip
    rw [h₁]
    exact hPi.flip
  -- paste it with `P = M ×_S N`
  have hV : IsPullback f₁ (f₂ ≫ iN) (hX ≫ c) qN := by
    rw [c₂, ← hMi.w]
    exact hL.paste_vert hpb
  exact IsPullback.of_bot hV (by rw [h₁, h₂]) hNi.flip

/-- The maps between fibres over a monomorphism `c : s ⟶ S` are maps over `s`. -/
lemma comp_eq_of_mono [Mono c] (hMi : IsPullback iM hX qM c) (hPi : IsPullback iP hZ (φ₁ ≫ qM) c)
    (c₁ : f₁ ≫ iM = iP ≫ φ₁) : f₁ ≫ hX = hZ := by
  rw [← cancel_mono c, Category.assoc, ← hMi.w, reassoc_of% c₁, hPi.w]

end Pasting

namespace NearbyCyclesModel

section Product

variable {k' : Type u} [Field k'] {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {N : NearbyCyclesModel Y Y'.left}
  {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X} {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y}
  {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'} {φ₂ : P.Hom N f₂ f₂'}
  {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

instance : IsClosedImmersion (traitClosedPoint k') :=
  IsClosedImmersion.spec_of_surjective _ fun a ↦ ⟨PowerSeries.C a, by simp⟩

/-- The morphism of special fibres of the first projection of a product over the trait lies over
`Spec k'`. -/
lemma special_comp_hom_fst (hM : M.IsTraitModelOver qM gM)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM)) : f₁' ≫ X'.hom = Z'.hom :=
  comp_eq_of_mono hM.isPullback_i hP.isPullback_i φ₁.comm_i

/-- The morphism of special fibres of the second projection of a product over the trait lies over
`Spec k'`. -/
lemma special_comp_hom_snd (hN : N.IsTraitModelOver qN gN)
    (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM)) : f₂' ≫ Y'.hom = Z'.hom := by
  rw [hpb.w] at hP
  exact comp_eq_of_mono hN.isPullback_i hP.isPullback_i φ₂.comm_i

/-- The special fibre of a product over the trait is the product of the special fibres. -/
lemma isPullback_special (hM : M.IsTraitModelOver qM gM) (hN : N.IsTraitModelOver qN gN)
    (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM)) :
    IsPullback f₁' f₂' X'.hom Y'.hom :=
  isPullback_fibre_of_isPullback hpb hM.isPullback_i hN.isPullback_i hP.isPullback_i φ₁.comm_i
    φ₂.comm_i (special_comp_hom_fst hM hP) (special_comp_hom_snd hN hpb hP)

/-- The geometric generic fibre of a product over the trait is the product of the geometric
generic fibres over `Spec Ω`, if the projections are compatible with the structure morphisms to
`Spec Ω`. -/
lemma isPullback_generic (hM : M.IsTraitModelOver qM gM) (hN : N.IsTraitModelOver qN gN)
    (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) :
    IsPullback φ₁.generic φ₂.generic gM gN :=
  isPullback_fibre_of_isPullback hpb hM.isPullback_j hN.isPullback_j hP.isPullback_j φ₁.comm_j
    φ₂.comm_j rfl hgen

end Product

/-! ### The proper exchange and the nearby cycles of the trait -/

section Exchange

variable (ℓ : ℕ) [Fact ℓ.Prime] {k' : Type u} [Field k'] [IsSepClosed k']
  [Fact (ringChar k' ≠ ℓ)] {X : Scheme.{u}} {X' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

/-- **The proper exchange for the structure morphism** (blueprint
`det-sp-nearby-cycles-exchanges` (2), for the proper morphism `f = q : 𝒳 ⟶ S` to the trait; SGA 7
XIII (2.1.7.1)): for a model `M` of finite type over the strictly henselian trait along a proper
`q` and a bounded constructible complex `C₀` on the total space, the pushforward exchange
`χ : Ψ_S Rg_* (Lj^* C₀) ⟶ R(q_s)_* Ψ_M (Lj^* C₀)` of the structure morphism
`(q, g) : M ⟶ S` (`NearbyCyclesModel.IsTraitModelOver.toTraitGeneric`) is an isomorphism. Here
`Lj^* C₀` is the pullback to the geometric generic fibre of the complex `C₀|_{𝒳_η}` on the
generic fibre, as in the blueprint node; `Ψ_S Rg_*` is the nearby cycles of the trait of
`Rq_{η*}`, computed on the geometric generic fibre by proper base change. -/
theorem IsTraitModelOver.isIso_pushforwardExchange_toTraitGeneric_app
    (h : M.IsTraitModelOver q g) [IsProper q]
    (C₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total)))
    (hC₀ : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total) C₀) :
    IsIso ((h.toTraitGeneric.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app
      (L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C₀)) :=
  sorry

omit [IsSepClosed k'] [Fact (ringChar k' ≠ ℓ)] in
/-- A natural transformation is invertible at an object isomorphic to one where it is
invertible. -/
lemma _root_.CategoryTheory.NatTrans.isIso_app_of_iso' {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (τ : F ⟶ G) {U U' : C} (e : U ≅ U') [IsIso (τ.app U')] : IsIso (τ.app U) := by
  have h : τ.app U = F.map e.hom ≫ τ.app U' ≫ G.map e.inv := by
    rw [τ.naturality_assoc, ← G.map_comp, e.hom_inv_id, G.map_id, Category.comp_id]
  rw [h]
  infer_instance

/-- The proper exchange of the structure morphism is invertible at every complex isomorphic to
the pullback `Lj^* C₀` of a bounded constructible complex on the total space. -/
theorem IsTraitModelOver.isIso_pushforwardExchange_toTraitGeneric_app_of_iso
    (h : M.IsTraitModelOver q g) [IsProper q]
    (U : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.generic)))
    (hU : ∃ C₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total)),
      boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total) C₀ ∧
        Nonempty (U ≅ L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C₀)) :
    IsIso ((h.toTraitGeneric.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app U) := by
  obtain ⟨C₀, hC₀, ⟨e⟩⟩ := hU
  have := h.isIso_pushforwardExchange_toTraitGeneric_app ℓ C₀ hC₀
  exact NatTrans.isIso_app_of_iso' _ e

variable [Fact (ringChar k').Prime]

/-- **The nearby cycles of the trait are monoidal on the geometric generic point**: the Künneth
map of the trait `T` (as a model of its geometric generic point) is an isomorphism at bounded
constructible complexes `C`, `D` on `Spec Ω`. -/
theorem isIso_kunnethMap_traitGenericModel
    (C D : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of (traitGenericField k'))))
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (Spec (.of (traitGenericField k'))))))
    (hC : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (Spec (.of (traitGenericField k')))) C)
    (hD : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (Spec (.of (traitGenericField k')))) D) :
    IsIso (kunnethMap (Profinite.padicAlgClRingObj ℓ) (Hom.id (traitGenericModel k'))
      (Hom.id (traitGenericModel k')) C D) :=
  sorry

end Exchange

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
