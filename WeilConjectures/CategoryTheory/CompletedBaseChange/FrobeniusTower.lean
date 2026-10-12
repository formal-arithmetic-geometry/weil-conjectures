/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.CompletedBaseChange.Completed
public import WeilConjectures.CategoryTheory.CompletedBaseChange.Frobenius

/-!
# Frobenius structures on the towers of the completed base change

Let `ρ : Reduction 𝔇 𝔗` be the reduction of a base change square `𝔇` into the square `𝔗` of
derived categories of towers, and let `𝔉 : FrobeniusDatum 𝔗` be a Frobenius datum on the
towers (the levelwise Frobenius pullbacks `Φ_Z = L Fr_Z^*`). A Weil structure
`ϑ : Φ_X K_• ≅ K_•` on the reduction tower of `K` (the compatible family `ϑ_n` of
`def-weil-pbc-frobenius-tower-datum`) induces Weil structures on the four corners
(`def-weil-pbc-frobenius-corner-structures`):

* `Θ_B` and `Θ_D` through the Frobenius faces (`FrobeniusDatum.weilB`, `weilD`);
* `Θ_A = h⁻¹ Θ_B Φ(h)` and `Θ_C = h'⁻¹ Θ_D Φ(h')` by transport along the projection-formula
  isomorphisms `h`, `h'`.

All four edges are then Weil morphisms (`lemma-weil-pbc-frobenius-level-rectangle`), and the
rectangle is a rectangle of Weil objects.

The levels of a tower are reached through a *Frobenius compatibility* of the derived limit
formalism (`CategoryTheory.TowerLimitFormalism.FrobeniusCompat`): the underlying tower of
`Φ M_•` is `(Φ M_n)_n`, and the derived limit commutes with `Φ` compatibly with the projections
(the canonical comparison of the product-cone model, an isomorphism since `Φ` is an exact
equivalence). Evaluation at `n` and the derived limit then lift to functors of Weil objects
(`levelWeil`, `rlimWeil`); the transitions and the projections are Weil morphisms
(`lemma-weil-pbc-frobenius-tower-compatibility`, `lemma-weil-pbc-frobenius-product-cone-limit`).

Finally the completed objects `S = Lg^*_comp Rf_* K = A_∞` and `T = Rf'_* Lg'^*_comp K ≅ D_∞`
carry the completed Weil structures `Θ_S`, `Θ_T` (`def-weil-pbc-completed-frobenius-structures`),
and the completed base change map is a Weil morphism
(`lemma-weil-pbc-completed-frobenius-equivariance`).
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

namespace CategoryTheory

namespace Endofunctor.IsoAlgebra

variable {C : Type u₁} [Category.{v₁} C] {F : C ⥤ C}

/-- A morphism of Weil objects from a morphism of the underlying objects commuting with the
structure isomorphisms. -/
def homMk {K K' : IsoAlgebra F} (f : K.carrier ⟶ K'.carrier)
    (h : F.map f ≫ K'.str.hom = K.str.hom ≫ f) : K ⟶ K' :=
  ObjectProperty.homMk { f := f, h := by simpa [str_hom] using h }

@[simp]
lemma homMk_hom_f {K K' : IsoAlgebra F} (f : K.carrier ⟶ K'.carrier)
    (h : F.map f ≫ K'.str.hom = K.str.hom ≫ f) : (homMk f h).hom.f = f := rfl

/-- A morphism of Weil objects commutes with the structure isomorphisms. -/
@[reassoc]
lemma hom_comm {K K' : IsoAlgebra F} (φ : K ⟶ K') :
    F.map φ.hom.f ≫ K'.str.hom = K.str.hom ≫ φ.hom.f := by
  simpa [str_hom] using φ.hom.h

lemma hom_ext' {K K' : IsoAlgebra F} {φ ψ : K ⟶ K'} (h : φ.hom.f = ψ.hom.f) : φ = ψ :=
  ObjectProperty.hom_ext _ (Algebra.Hom.ext h)

end Endofunctor.IsoAlgebra

open Endofunctor

namespace TowerLimitFormalism

variable {𝒯 : Type u₁} [Category.{v₁} 𝒯] {T : Type u₂} [Category.{v₂} T]
  [HasZeroObject T] [HasShift T ℤ] [Preadditive T] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T] (𝔏 : TowerLimitFormalism 𝒯 T)

/-- A *Frobenius compatibility* of a derived limit formalism with endofunctors `Φ` of the
derived towers and `Φ_T` of the base: the underlying tower of `Φ M_•` is `Φ_T` applied
levelwise, and the derived limit commutes with the Frobenius pullbacks compatibly with the
projections. For an exact autoequivalence `Φ_T` acting levelwise on towers, this is the
canonical comparison `Φ_T (R lim M_•) ≅ R lim (Φ_T M_n)` of
`lemma-weil-pbc-frobenius-product-cone-limit`. -/
structure FrobeniusCompat (Φ : 𝒯 ⥤ 𝒯) (ΦT : T ⥤ T) where
  /-- The underlying tower of `Φ M_•` is `(Φ_T M_n)_n`. -/
  towerIso : 𝔏.tower ⋙ (whiskeringRight ℕᵒᵖ T T).obj ΦT ≅ Φ ⋙ 𝔏.tower
  /-- The comparison `Φ_T (R lim M_•) ≅ R lim (Φ M_•)`. -/
  rlimIso : 𝔏.rlim ⋙ ΦT ≅ Φ ⋙ 𝔏.rlim
  /-- The comparison is compatible with the projections. -/
  proj_comm (n : ℕ) (M : 𝒯) :
    ΦT.map ((𝔏.proj n).app M) ≫ (towerIso.hom.app M).app (op n) =
      rlimIso.hom.app M ≫ (𝔏.proj n).app (Φ.obj M)

namespace FrobeniusCompat

variable {𝔏} {Φ : 𝒯 ⥤ 𝒯} {ΦT : T ⥤ T} (𝔠 : 𝔏.FrobeniusCompat Φ ΦT)

/-- The level `n` comparison `Φ_T (ev_n M) ≅ ev_n (Φ M)`. -/
def evIso (n : ℕ) : 𝔏.ev n ⋙ ΦT ≅ Φ ⋙ 𝔏.ev n :=
  Functor.isoWhiskerRight 𝔠.towerIso ((evaluation ℕᵒᵖ T).obj (op n))

@[simp]
lemma evIso_hom_app (n : ℕ) (M : 𝒯) :
    (𝔠.evIso n).hom.app M = (𝔠.towerIso.hom.app M).app (op n) := rfl

/-- Evaluation at level `n` as a functor of Weil objects: a Weil tower `(M_•, Θ)` gives the
level structures `Θ_n : Φ_T M_n ≅ ev_n (Φ M_•) ≅ M_n`. -/
noncomputable def levelWeil (n : ℕ) : IsoAlgebra Φ ⥤ IsoAlgebra ΦT :=
  IsoAlgebra.mapOfNatIso (𝔠.evIso n)

/-- The derived limit as a functor of Weil objects: the Weil structure
`Θ_∞ : Φ_T (R lim M_•) ≅ R lim (Φ M_•) ⟶ R lim M_•` of
`lemma-weil-pbc-frobenius-product-cone-limit`. -/
noncomputable def rlimWeil : IsoAlgebra Φ ⥤ IsoAlgebra ΦT :=
  IsoAlgebra.mapOfNatIso 𝔠.rlimIso

lemma levelWeil_obj_str_hom (n : ℕ) (M : IsoAlgebra Φ) :
    ((𝔠.levelWeil n).obj M).str.hom =
      (𝔠.towerIso.hom.app M.carrier).app (op n) ≫ (𝔏.ev n).map M.str.hom := by
  simp [levelWeil]

lemma rlimWeil_obj_str_hom (M : IsoAlgebra Φ) :
    (𝔠.rlimWeil.obj M).str.hom = 𝔠.rlimIso.hom.app M.carrier ≫ 𝔏.rlim.map M.str.hom := by
  simp [rlimWeil]

/-- The transitions of a Weil tower are Weil morphisms, as a natural transformation
`levelWeil (n + 1) ⟶ levelWeil n`. -/
noncomputable def transitionWeil (n : ℕ) : 𝔠.levelWeil (n + 1) ⟶ 𝔠.levelWeil n :=
  IsoAlgebra.mapOfNatIsoHom (𝔏.transition n) (by
    ext M
    simpa using ((𝔠.towerIso.hom.app M).naturality (homOfLE n.le_succ).op))

@[simp]
lemma transitionWeil_app_hom_f (n : ℕ) (M : IsoAlgebra Φ) :
    ((𝔠.transitionWeil n).app M).hom.f = (𝔏.transition n).app M.carrier := rfl

/-- The projections of a Weil tower are Weil morphisms, as a natural transformation
`rlimWeil ⟶ levelWeil n`. -/
noncomputable def projWeil (n : ℕ) : 𝔠.rlimWeil ⟶ 𝔠.levelWeil n :=
  IsoAlgebra.mapOfNatIsoHom (𝔏.proj n) (by
    ext M
    simpa using 𝔠.proj_comm n M)

@[simp]
lemma projWeil_app_hom_f (n : ℕ) (M : IsoAlgebra Φ) :
    ((𝔠.projWeil n).app M).hom.f = (𝔏.proj n).app M.carrier := rfl

/-- **Frobenius tower compatibility** (Blueprint `lemma-weil-pbc-frobenius-tower-compatibility`,
abstract form): for a Weil tower `(M_•, Θ)`, the level structures `Θ_n` commute with the
transitions, `t_{n+1,n} ∘ Θ_{n+1} = Θ_n ∘ Φ_T(t_{n+1,n})`. -/
@[reassoc]
lemma transition_comm (n : ℕ) (M : IsoAlgebra Φ) :
    ΦT.map ((𝔏.transition n).app M.carrier) ≫ ((𝔠.levelWeil n).obj M).str.hom =
      ((𝔠.levelWeil (n + 1)).obj M).str.hom ≫ (𝔏.transition n).app M.carrier :=
  IsoAlgebra.hom_comm ((𝔠.transitionWeil n).app M)

/-- A morphism of Weil towers is a Weil morphism at every level. -/
@[reassoc]
lemma level_comm (n : ℕ) {M N : IsoAlgebra Φ} (φ : M ⟶ N) :
    ΦT.map ((𝔏.ev n).map φ.hom.f) ≫ ((𝔠.levelWeil n).obj N).str.hom =
      ((𝔠.levelWeil n).obj M).str.hom ≫ (𝔏.ev n).map φ.hom.f :=
  IsoAlgebra.hom_comm ((𝔠.levelWeil n).map φ)

/-- The derived limit of a morphism of Weil towers is a Weil morphism. -/
@[reassoc]
lemma rlim_comm {M N : IsoAlgebra Φ} (φ : M ⟶ N) :
    ΦT.map (𝔏.rlim.map φ.hom.f) ≫ (𝔠.rlimWeil.obj N).str.hom =
      (𝔠.rlimWeil.obj M).str.hom ≫ 𝔏.rlim.map φ.hom.f :=
  IsoAlgebra.hom_comm (𝔠.rlimWeil.map φ)

/-- The projections `R lim M_• ⟶ M_n` of a Weil tower commute with `Θ_∞` and `Θ_n`. -/
@[reassoc]
lemma proj_comm_str (n : ℕ) (M : IsoAlgebra Φ) :
    ΦT.map ((𝔏.proj n).app M.carrier) ≫ ((𝔠.levelWeil n).obj M).str.hom =
      (𝔠.rlimWeil.obj M).str.hom ≫ (𝔏.proj n).app M.carrier :=
  IsoAlgebra.hom_comm ((𝔠.projWeil n).app M)

end FrobeniusCompat

end TowerLimitFormalism

namespace BaseChangeSquare

variable {𝒳 : Type u₁} {𝒴 : Type u₂} {𝒳' : Type u₃} {𝒴' : Type u₄}
  [Category.{v₁} 𝒳] [Category.{v₂} 𝒴] [Category.{v₃} 𝒳'] [Category.{v₄} 𝒴']
  {𝒯 : Type u₅} {𝒰 : Type u₆} {𝒯' : Type u₇} {𝒰' : Type u₈}
  [Category.{v₅} 𝒯] [Category.{v₆} 𝒰] [Category.{v₇} 𝒯'] [Category.{v₈} 𝒰']

namespace Reduction

variable {𝔇 : BaseChangeSquare 𝒳 𝒴 𝒳' 𝒴'} {𝔗 : BaseChangeSquare 𝒯 𝒰 𝒯' 𝒰'}
  (ρ : Reduction 𝔇 𝔗) (𝔉 : FrobeniusDatum 𝔗) (K : 𝒳)
  (ϑ : 𝔉.ΦX.obj (ρ.redX.obj K) ≅ ρ.redX.obj K)

/-- The reduction tower `K_•` of `K` with the Weil structure `ϑ`. -/
noncomputable def weilTower : IsoAlgebra 𝔉.ΦX := IsoAlgebra.mk (ρ.redX.obj K) ϑ

/-- The corner `B` with its Weil structure `Θ_B = g^*(f_* ϑ ∘ β_f) ∘ κ_g` (Blueprint
`def-weil-pbc-frobenius-corner-structures`). -/
noncomputable def weilCornerB : IsoAlgebra 𝔉.ΦY' := 𝔉.weilB.obj (ρ.weilTower 𝔉 K ϑ)

/-- The corner `D` with its Weil structure `Θ_D = f'_*(g'^* ϑ ∘ κ_{g'}) ∘ β_{f'}` (Blueprint
`def-weil-pbc-frobenius-corner-structures`). -/
noncomputable def weilCornerD : IsoAlgebra 𝔉.ΦY' := 𝔉.weilD.obj (ρ.weilTower 𝔉 K ϑ)

lemma weilCornerB_carrier : (ρ.weilCornerB 𝔉 K ϑ).carrier = ρ.cornerB.obj K := rfl

lemma weilCornerD_carrier : (ρ.weilCornerD 𝔉 K ϑ).carrier = ρ.cornerD.obj K := rfl

variable [IsIso (ρ.arrowH.app K)] [IsIso (ρ.arrowH'.app K)]

/-- The corner `A` with the transported Weil structure `Θ_A = h⁻¹ Θ_B Φ(h)` (Blueprint
`def-weil-pbc-frobenius-corner-structures`). -/
noncomputable def weilCornerA : IsoAlgebra 𝔉.ΦY' :=
  (ρ.weilCornerB 𝔉 K ϑ).transport (asIso (ρ.arrowH.app K))

/-- The corner `C` with the transported Weil structure `Θ_C = h'⁻¹ Θ_D Φ(h')` (Blueprint
`def-weil-pbc-frobenius-corner-structures`). -/
noncomputable def weilCornerC : IsoAlgebra 𝔉.ΦY' :=
  (ρ.weilCornerD 𝔉 K ϑ).transport (asIso (ρ.arrowH'.app K))

/-- The edge `h` as a Weil morphism (by definition of `Θ_A`). -/
noncomputable def weilArrowH : ρ.weilCornerA 𝔉 K ϑ ⟶ ρ.weilCornerB 𝔉 K ϑ :=
  ((ρ.weilCornerB 𝔉 K ϑ).transportIso (asIso (ρ.arrowH.app K))).hom

/-- The edge `h'` as a Weil morphism (by definition of `Θ_C`). -/
noncomputable def weilArrowH' : ρ.weilCornerC 𝔉 K ϑ ⟶ ρ.weilCornerD 𝔉 K ϑ :=
  ((ρ.weilCornerD 𝔉 K ϑ).transportIso (asIso (ρ.arrowH'.app K))).hom

/-- The edge `v' = ξ_{K_•}` as a Weil morphism: the pasting coherence of exchange maps in the
Frobenius cube (`FrobeniusDatum.weilExchange`). -/
noncomputable def weilArrowV' : ρ.weilCornerB 𝔉 K ϑ ⟶ ρ.weilCornerD 𝔉 K ϑ :=
  𝔉.weilExchange.app (ρ.weilTower 𝔉 K ϑ)

@[simp] lemma weilArrowH_hom_f : (ρ.weilArrowH 𝔉 K ϑ).hom.f = ρ.arrowH.app K := rfl

@[simp] lemma weilArrowH'_hom_f : (ρ.weilArrowH' 𝔉 K ϑ).hom.f = ρ.arrowH'.app K := rfl

@[simp] lemma weilArrowV'_hom_f : (ρ.weilArrowV' 𝔉 K ϑ).hom.f = ρ.arrowV'.app K := rfl

/-- The edge `v` commutes with the transported structures `Θ_A`, `Θ_C`: cancel `h'` in the
rectangle, the other three edges being Weil morphisms. -/
lemma arrowV_comm :
    𝔉.ΦY'.map (ρ.arrowV.app K) ≫ (ρ.weilCornerC 𝔉 K ϑ).str.hom =
      (ρ.weilCornerA 𝔉 K ϑ).str.hom ≫ ρ.arrowV.app K :=
  IsoAlgebra.comm_of_rectangle (ρ.rectangle_app K)
    (IsoAlgebra.hom_comm (ρ.weilArrowH 𝔉 K ϑ)) (IsoAlgebra.hom_comm (ρ.weilArrowV' 𝔉 K ϑ))
    (IsoAlgebra.hom_comm (ρ.weilArrowH' 𝔉 K ϑ))

/-- The edge `v` as a Weil morphism. -/
noncomputable def weilArrowV : ρ.weilCornerA 𝔉 K ϑ ⟶ ρ.weilCornerC 𝔉 K ϑ :=
  IsoAlgebra.homMk (ρ.arrowV.app K) (ρ.arrowV_comm 𝔉 K ϑ)

@[simp] lemma weilArrowV_hom_f : (ρ.weilArrowV 𝔉 K ϑ).hom.f = ρ.arrowV.app K := rfl

/-- **The Frobenius rectangle** (Blueprint `lemma-weil-pbc-frobenius-level-rectangle`,
abstract form on the towers): the four edges `h, v, h', v'` are Weil morphisms
(`weilArrowH`, `weilArrowV`, `weilArrowH'`, `weilArrowV'`), and the exchange rectangle is a
commutative rectangle of Weil objects. -/
theorem weil_rectangle :
    ρ.weilArrowH 𝔉 K ϑ ≫ ρ.weilArrowV' 𝔉 K ϑ = ρ.weilArrowV 𝔉 K ϑ ≫ ρ.weilArrowH' 𝔉 K ϑ :=
  IsoAlgebra.hom_ext' (by simpa using ρ.rectangle_app K)

/-- The two typed composites `𝒫 = (v' h) ∘ Θ_A` and `𝒬 = Θ_D ∘ Φ(v' h)` of
`lemma-weil-pbc-frobenius-level-rectangle` agree, and the same holds for `h' v`. -/
lemma weil_rectangle_comm :
    𝔉.ΦY'.map (ρ.arrowH.app K ≫ ρ.arrowV'.app K) ≫ (ρ.weilCornerD 𝔉 K ϑ).str.hom =
      (ρ.weilCornerA 𝔉 K ϑ).str.hom ≫ ρ.arrowH.app K ≫ ρ.arrowV'.app K ∧
    𝔉.ΦY'.map (ρ.arrowV.app K ≫ ρ.arrowH'.app K) ≫ (ρ.weilCornerD 𝔉 K ϑ).str.hom =
      (ρ.weilCornerA 𝔉 K ϑ).str.hom ≫ ρ.arrowV.app K ≫ ρ.arrowH'.app K :=
  ⟨by simpa using IsoAlgebra.hom_comm (ρ.weilArrowH 𝔉 K ϑ ≫ ρ.weilArrowV' 𝔉 K ϑ),
    by simpa using IsoAlgebra.hom_comm (ρ.weilArrowV 𝔉 K ϑ ≫ ρ.weilArrowH' 𝔉 K ϑ)⟩

end Reduction

variable [HasZeroObject 𝒳'] [HasShift 𝒳' ℤ] [Preadditive 𝒳']
  [∀ n : ℤ, (shiftFunctor 𝒳' n).Additive] [Pretriangulated 𝒳']
  [HasZeroObject 𝒴'] [HasShift 𝒴' ℤ] [Preadditive 𝒴']
  [∀ n : ℤ, (shiftFunctor 𝒴' n).Additive] [Pretriangulated 𝒴']

namespace CompletionDatum

variable {𝔇 : BaseChangeSquare 𝒳 𝒴 𝒳' 𝒴'} {𝔗 : BaseChangeSquare 𝒯 𝒰 𝒯' 𝒰'}
  (𝔠 : CompletionDatum 𝔇 𝔗) (𝔉 : FrobeniusDatum 𝔗) {ΦY'b : 𝒴' ⥤ 𝒴'}
  (𝔣 : 𝔠.limY'.FrobeniusCompat 𝔉.ΦY' ΦY'b) (K : 𝒳)
  (ϑ : 𝔉.ΦX.obj (𝔠.ρ.redX.obj K) ≅ 𝔠.ρ.redX.obj K)

/-- The Weil structure `Θ_{Z,n}` on the level `n` of a corner `Z` (Blueprint
`def-weil-pbc-frobenius-corner-structures`, level `n`). -/
noncomputable abbrev levelWeil (n : ℕ) (Z : IsoAlgebra 𝔉.ΦY') : IsoAlgebra ΦY'b :=
  (𝔣.levelWeil n).obj Z

variable [IsIso (𝔠.ρ.arrowH.app K)] [IsIso (𝔠.ρ.arrowH'.app K)]

/-- **The finite-level Frobenius rectangle** (Blueprint
`lemma-weil-pbc-frobenius-level-rectangle`): at every level `n`, the four edges
`h_n, v_n, h'_n, v'_n` commute with the level structures `Θ_{Z,n}`. -/
lemma level_weil_edges (n : ℕ) :
    ΦY'b.map ((𝔠.limY'.ev n).map (𝔠.ρ.arrowH.app K)) ≫
        ((𝔣.levelWeil n).obj (𝔠.ρ.weilCornerB 𝔉 K ϑ)).str.hom =
      ((𝔣.levelWeil n).obj (𝔠.ρ.weilCornerA 𝔉 K ϑ)).str.hom ≫
        (𝔠.limY'.ev n).map (𝔠.ρ.arrowH.app K) ∧
    ΦY'b.map ((𝔠.limY'.ev n).map (𝔠.ρ.arrowV.app K)) ≫
        ((𝔣.levelWeil n).obj (𝔠.ρ.weilCornerC 𝔉 K ϑ)).str.hom =
      ((𝔣.levelWeil n).obj (𝔠.ρ.weilCornerA 𝔉 K ϑ)).str.hom ≫
        (𝔠.limY'.ev n).map (𝔠.ρ.arrowV.app K) ∧
    ΦY'b.map ((𝔠.limY'.ev n).map (𝔠.ρ.arrowH'.app K)) ≫
        ((𝔣.levelWeil n).obj (𝔠.ρ.weilCornerD 𝔉 K ϑ)).str.hom =
      ((𝔣.levelWeil n).obj (𝔠.ρ.weilCornerC 𝔉 K ϑ)).str.hom ≫
        (𝔠.limY'.ev n).map (𝔠.ρ.arrowH'.app K) ∧
    ΦY'b.map ((𝔠.limY'.ev n).map (𝔠.ρ.arrowV'.app K)) ≫
        ((𝔣.levelWeil n).obj (𝔠.ρ.weilCornerD 𝔉 K ϑ)).str.hom =
      ((𝔣.levelWeil n).obj (𝔠.ρ.weilCornerB 𝔉 K ϑ)).str.hom ≫
        (𝔠.limY'.ev n).map (𝔠.ρ.arrowV'.app K) :=
  ⟨𝔣.level_comm n (𝔠.ρ.weilArrowH 𝔉 K ϑ), 𝔣.level_comm n (𝔠.ρ.weilArrowV 𝔉 K ϑ),
    𝔣.level_comm n (𝔠.ρ.weilArrowH' 𝔉 K ϑ), 𝔣.level_comm n (𝔠.ρ.weilArrowV' 𝔉 K ϑ)⟩

/-- The completed object `S = Lg^*_comp Rf_* K = R lim A_•` with its Weil structure
`Θ_S = Θ_{A,∞}` (Blueprint `def-weil-pbc-completed-frobenius-structures`; here `s = 𝟙`, since
`S` is by definition the derived limit of `A_•`). -/
noncomputable def weilS : IsoAlgebra ΦY'b := 𝔣.rlimWeil.obj (𝔠.ρ.weilCornerA 𝔉 K ϑ)

/-- The completed object `T = Rf'_* Lg'^*_comp K` with its Weil structure
`Θ_T = t Θ_{D,∞} Φ(t⁻¹)`, where `t : D_∞ ≅ T` is the inverse of the direct-image/limit
commutation (Blueprint `def-weil-pbc-completed-frobenius-structures`). -/
noncomputable def weilT : IsoAlgebra ΦY'b :=
  (𝔣.rlimWeil.obj (𝔠.ρ.weilCornerD 𝔉 K ϑ)).transport
    (𝔠.lowerLim.app (𝔗.upperG'.obj (𝔠.ρ.redX.obj K)))

/-- The common limit map `W = V' H = H' V : A_∞ ⟶ D_∞` as a Weil morphism (Blueprint
`lemma-weil-pbc-frobenius-product-cone-limit`). -/
noncomputable def weilLimitExchange :
    𝔣.rlimWeil.obj (𝔠.ρ.weilCornerA 𝔉 K ϑ) ⟶ 𝔣.rlimWeil.obj (𝔠.ρ.weilCornerD 𝔉 K ϑ) :=
  𝔣.rlimWeil.map (𝔠.ρ.weilArrowH 𝔉 K ϑ ≫ 𝔠.ρ.weilArrowV' 𝔉 K ϑ)

/-- **Frobenius product-cone limit** (Blueprint `lemma-weil-pbc-frobenius-product-cone-limit`,
abstract form): the limits `H, V, H', V'` of the four edges are Weil morphisms for the
structures `Θ_{Z,∞}`, and so is `W = V' H = H' V`; both factorisations give the same Weil
morphism. -/
lemma limit_weil_edges :
    ΦY'b.map (𝔠.limY'.rlim.map (𝔠.ρ.arrowH.app K)) ≫
        (𝔣.rlimWeil.obj (𝔠.ρ.weilCornerB 𝔉 K ϑ)).str.hom =
      (𝔣.rlimWeil.obj (𝔠.ρ.weilCornerA 𝔉 K ϑ)).str.hom ≫
        𝔠.limY'.rlim.map (𝔠.ρ.arrowH.app K) ∧
    ΦY'b.map (𝔠.limY'.rlim.map (𝔠.ρ.arrowV.app K)) ≫
        (𝔣.rlimWeil.obj (𝔠.ρ.weilCornerC 𝔉 K ϑ)).str.hom =
      (𝔣.rlimWeil.obj (𝔠.ρ.weilCornerA 𝔉 K ϑ)).str.hom ≫
        𝔠.limY'.rlim.map (𝔠.ρ.arrowV.app K) ∧
    ΦY'b.map (𝔠.limY'.rlim.map (𝔠.ρ.arrowH'.app K)) ≫
        (𝔣.rlimWeil.obj (𝔠.ρ.weilCornerD 𝔉 K ϑ)).str.hom =
      (𝔣.rlimWeil.obj (𝔠.ρ.weilCornerC 𝔉 K ϑ)).str.hom ≫
        𝔠.limY'.rlim.map (𝔠.ρ.arrowH'.app K) ∧
    ΦY'b.map (𝔠.limY'.rlim.map (𝔠.ρ.arrowV'.app K)) ≫
        (𝔣.rlimWeil.obj (𝔠.ρ.weilCornerD 𝔉 K ϑ)).str.hom =
      (𝔣.rlimWeil.obj (𝔠.ρ.weilCornerB 𝔉 K ϑ)).str.hom ≫
        𝔠.limY'.rlim.map (𝔠.ρ.arrowV'.app K) ∧
    𝔣.rlimWeil.map (𝔠.ρ.weilArrowH 𝔉 K ϑ ≫ 𝔠.ρ.weilArrowV' 𝔉 K ϑ) =
      𝔣.rlimWeil.map (𝔠.ρ.weilArrowV 𝔉 K ϑ ≫ 𝔠.ρ.weilArrowH' 𝔉 K ϑ) :=
  ⟨𝔣.rlim_comm (𝔠.ρ.weilArrowH 𝔉 K ϑ), 𝔣.rlim_comm (𝔠.ρ.weilArrowV 𝔉 K ϑ),
    𝔣.rlim_comm (𝔠.ρ.weilArrowH' 𝔉 K ϑ), 𝔣.rlim_comm (𝔠.ρ.weilArrowV' 𝔉 K ϑ),
    by rw [𝔠.ρ.weil_rectangle]⟩

/-- The completed base change map as a Weil morphism `(S, Θ_S) ⟶ (T, Θ_T)`:
`Ex^comp = t W s` with `s = 𝟙`. -/
noncomputable def weilCompletedExchange : 𝔠.weilS 𝔉 𝔣 K ϑ ⟶ 𝔠.weilT 𝔉 𝔣 K ϑ :=
  𝔠.weilLimitExchange 𝔉 𝔣 K ϑ ≫ ((𝔣.rlimWeil.obj (𝔠.ρ.weilCornerD 𝔉 K ϑ)).transportIso
    (𝔠.lowerLim.app (𝔗.upperG'.obj (𝔠.ρ.redX.obj K)))).inv

lemma weilCompletedExchange_hom_f :
    (𝔠.weilCompletedExchange 𝔉 𝔣 K ϑ).hom.f = 𝔠.completedExchange.app K := by
  rw [completedExchange_app']
  rfl

/-- **Completed proper base change is Frobenius-equivariant** (Blueprint
`lemma-weil-pbc-completed-frobenius-equivariance`, abstract form):
`Ex^comp ∘ Θ_S = Θ_T ∘ Φ_{Y'}(Ex^comp) : Φ_{Y'} S ⟶ T`. -/
theorem completedExchange_frobenius_comm :
    ΦY'b.map (𝔠.completedExchange.app K) ≫ (𝔠.weilT 𝔉 𝔣 K ϑ).str.hom =
      (𝔠.weilS 𝔉 𝔣 K ϑ).str.hom ≫ 𝔠.completedExchange.app K := by
  rw [← 𝔠.weilCompletedExchange_hom_f 𝔉 𝔣 K ϑ]
  exact IsoAlgebra.hom_comm _

end CompletionDatum

end BaseChangeSquare

end CategoryTheory
