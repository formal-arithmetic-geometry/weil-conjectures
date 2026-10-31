/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.LineProjAffineChartAtlas
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
import WeilConjectures.AlgebraicGeometry.AffineTensorGeneratorLocus
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import WeilConjectures.AlgebraicGeometry.BoundaryPullbackTensorUnit
import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections

/-! # Pullback of generation opens and specified relative-Proj fraction maps

Source: Stacks Project, Divisors on Spaces, Tag 0D2Z, opening assertion and (3);
Constructions, Tags 01O9 and 01NK (blueprint: lem-trf-line-proj-chart-pullback).

The square is only commutative. The primed algebra is identified degreewise with
its actual tensor pullback, compatibly with the coefficientwise Proj comparison.
The pulled-back homogeneous map is constructed from normalized composition and
power comparisons. All fraction equations are cross-multiplied on generator opens.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

/-- The component of normalized pullback composition, pinned by equality to the
canonical comparison. The equality witness keeps type checking from expanding the
adjunction construction. Source: Stacks, Tag 0097
(blueprint: def-trf-line-proj-comparison-components). -/
noncomputable def lineProjCompHom {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) (h : Y ⟶ Z) (M : Z.Modules) :
    (tensorPullback (g ≫ h)).obj M ⟶ (tensorPullback g).obj ((tensorPullback h).obj M) :=
  Classical.choose (show ∃ c : (tensorPullback (g ≫ h)).obj M ⟶
      (tensorPullback g).obj ((tensorPullback h).obj M),
    c = (tensorPullbackSectionComp g h).hom.app M from ⟨_, rfl⟩)

private theorem lineProjCompHom_eq {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) (h : Y ⟶ Z) (M : Z.Modules) :
    lineProjCompHom g h M = (tensorPullbackSectionComp g h).hom.app M :=
  Classical.choose_spec (show ∃ c : (tensorPullback (g ≫ h)).obj M ⟶
      (tensorPullback g).obj ((tensorPullback h).obj M),
    c = (tensorPullbackSectionComp g h).hom.app M from ⟨_, rfl⟩)

/-- The inverse component of normalized pullback composition, pinned to the canonical
comparison. Source: Stacks, Tag 0097
(blueprint: def-trf-line-proj-comparison-components). -/
noncomputable def lineProjCompInv {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) (h : Y ⟶ Z) (M : Z.Modules) :
    (tensorPullback g).obj ((tensorPullback h).obj M) ⟶ (tensorPullback (g ≫ h)).obj M :=
  Classical.choose (show ∃ c : (tensorPullback g).obj ((tensorPullback h).obj M) ⟶
      (tensorPullback (g ≫ h)).obj M,
    c = (tensorPullbackSectionComp g h).inv.app M from ⟨_, rfl⟩)

private theorem lineProjCompInv_eq {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) (h : Y ⟶ Z) (M : Z.Modules) :
    lineProjCompInv g h M = (tensorPullbackSectionComp g h).inv.app M :=
  Classical.choose_spec (show ∃ c : (tensorPullback g).obj ((tensorPullback h).obj M) ⟶
      (tensorPullback (g ≫ h)).obj M,
    c = (tensorPullbackSectionComp g h).inv.app M from ⟨_, rfl⟩)

/-- The power comparison component, pinned to the canonical tensor-pullback comparison.
Source: Stacks, Tag 0095 (blueprint: def-trf-line-proj-comparison-components). -/
noncomputable def lineProjPowHom {X Y : Scheme.{u}} (h : X ⟶ Y)
    (L : Y.Modules) (n : ℕ) :
    (tensorPullback h).obj (L.tensorPow n) ⟶ ((tensorPullback h).obj L).tensorPow n :=
  Classical.choose (show ∃ c : (tensorPullback h).obj (L.tensorPow n) ⟶
      ((tensorPullback h).obj L).tensorPow n,
    c = (boundaryPullbackPowIso h L n).hom from ⟨_, rfl⟩)

private theorem lineProjPowHom_eq {X Y : Scheme.{u}} (h : X ⟶ Y)
    (L : Y.Modules) (n : ℕ) : lineProjPowHom h L n = (boundaryPullbackPowIso h L n).hom :=
  Classical.choose_spec (show ∃ c : (tensorPullback h).obj (L.tensorPow n) ⟶
      ((tensorPullback h).obj L).tensorPow n,
    c = (boundaryPullbackPowIso h L n).hom from ⟨_, rfl⟩)

/-- Transport along equality of scheme morphisms, pinned to the usual equality map.
Source: Stacks, Tag 0095 (blueprint: def-trf-line-proj-comparison-components). -/
noncomputable def lineProjSquareCast {X Y : Scheme.{u}} {j k : X ⟶ Y}
    (e : j = k) (M : Y.Modules) : (tensorPullback j).obj M ⟶ (tensorPullback k).obj M :=
  Classical.choose (show ∃ c : (tensorPullback j).obj M ⟶ (tensorPullback k).obj M,
    c = (eqToIso (congrArg (fun l ↦ (tensorPullback l).obj M) e)).hom from ⟨_, rfl⟩)

private theorem lineProjSquareCast_eq {X Y : Scheme.{u}} {j k : X ⟶ Y}
    (e : j = k) (M : Y.Modules) : lineProjSquareCast e M =
      (eqToIso (congrArg (fun l ↦ (tensorPullback l).obj M) e)).hom :=
  Classical.choose_spec (show ∃ c : (tensorPullback j).obj M ⟶ (tensorPullback k).obj M,
    c = (eqToIso (congrArg (fun l ↦ (tensorPullback l).obj M) e)).hom from ⟨_, rfl⟩)

attribute [local irreducible] tensorPullbackObj tensorPullbackMap

/-- The section corresponding to a pure tensor a tensor c in the pulled-back degree-n
sheaf. The isomorphism beta identifies the chosen primed sheaf with the actual pullback.
Source: Stacks, Tag 0D2Z(3) (blueprint: lem-trf-line-proj-chart-pullback). -/
noncomputable def lineProjBaseSection {T T' : Scheme.{u}} (g : T' ⟶ T)
    (A : RelativeProjAlgebra T) (A' : RelativeProjAlgebra T')
    (β : ∀ n : ℕ, A'.piece n ≅ (tensorPullback g).obj (A.piece n))
    (V : T.affineOpens) (V' : T'.affineOpens) (hV : V'.1 ≤ g ⁻¹ᵁ V.1)
    (n : ℕ) (a : Γ(A.piece n, V.1)) (c : Γ(T', V'.1)) : Γ(A'.piece n, V'.1) :=
  c • (β n).inv.app V'.1
    (((tensorPullback g).obj (A.piece n)).presheaf.map (homOfLE hV).op
      (tensorPullbackSection g (A.piece n) V.1 a))

/-- The pulled-back homogeneous map, using the commutativity of the square, normalized
composition of tensor pullbacks, and the canonical comparison for powers of a line module.
Source: Stacks, Tag 0D2Z(3) (blueprint: lem-trf-line-proj-chart-pullback). -/
noncomputable def lineProjPullbackMap {W W' T T' : Scheme.{u}}
    {f : W ⟶ T} {f' : W' ⟶ T'} {h : W' ⟶ W} {g : T' ⟶ T}
    (hsq : h ≫ f = f' ≫ g) (A : RelativeProjAlgebra T) (A' : RelativeProjAlgebra T')
    (L : W.Modules) (β : ∀ n : ℕ, A'.piece n ≅ (tensorPullback g).obj (A.piece n))
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n) (n : ℕ) :
    (tensorPullback f').obj (A'.piece n) ⟶ ((tensorPullback h).obj L).tensorPow n :=
  (tensorPullback f').map (β n).hom ≫
    (lineProjCompInv f' g (A.piece n)) ≫
    lineProjSquareCast hsq.symm (A.piece n) ≫
    (lineProjCompHom h f (A.piece n)) ≫
    (tensorPullback h).map (ψ n) ≫ lineProjPowHom h L n

private theorem comp_four_congr {X : Scheme.{u}}
    {M₀ M₁ M₂ M₃ M₄ M₅ M₆ : X.Modules}
    (c₁ : M₀ ⟶ M₁) (c₅ : M₄ ⟶ M₅)
    {c₂ d₂ : M₁ ⟶ M₂} {c₃ d₃ : M₂ ⟶ M₃}
    {c₄ d₄ : M₃ ⟶ M₄} {c₆ d₆ : M₅ ⟶ M₆}
    (h₂ : c₂ = d₂) (h₃ : c₃ = d₃) (h₄ : c₄ = d₄) (h₆ : c₆ = d₆) :
    c₁ ≫ c₂ ≫ c₃ ≫ c₄ ≫ c₅ ≫ c₆ = c₁ ≫ d₂ ≫ d₃ ≫ d₄ ≫ c₅ ≫ d₆ := by
  subst d₂ d₃ d₄ d₆
  rfl

/-- The comparison components give exactly the original canonical pullback composite.
Source: Stacks, Tag 0D2Z(3) (blueprint: lem-trf-line-proj-chart-pullback).
Proof: replace each equality-pinned component by its defining canonical map. -/
theorem lineProjPullbackMap_canonical {W W' T T' : Scheme.{u}}
    {f : W ⟶ T} {f' : W' ⟶ T'} {h : W' ⟶ W} {g : T' ⟶ T}
    (hsq : h ≫ f = f' ≫ g) (A : RelativeProjAlgebra T) (A' : RelativeProjAlgebra T')
    (L : W.Modules) (β : ∀ n : ℕ, A'.piece n ≅ (tensorPullback g).obj (A.piece n))
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n) (n : ℕ) :
    lineProjPullbackMap hsq A A' L β ψ n =
      (tensorPullback f').map (β n).hom ≫
        (tensorPullbackSectionComp f' g).inv.app (A.piece n) ≫
        (eqToIso (congrArg (fun k ↦ (tensorPullback k).obj (A.piece n)) hsq.symm)).hom ≫
        (tensorPullbackSectionComp h f).hom.app (A.piece n) ≫
        (tensorPullback h).map (ψ n) ≫ (boundaryPullbackPowIso h L n).hom := by
  exact comp_four_congr ((tensorPullback f').map (β n).hom)
    ((tensorPullback h).map (ψ n))
    (lineProjCompInv_eq f' g (A.piece n)) (lineProjSquareCast_eq hsq.symm (A.piece n))
    (lineProjCompHom_eq h f (A.piece n)) (lineProjPowHom_eq h L n)

/-- A map to relative Proj is specified by homogeneous fractions on every generator open.
The chart factorizations are actual maps, and the scalar equation uses the given psi.
Source: Stacks, Tags 01NK and 01O9 (blueprint: lem-trf-line-proj-chart-pullback). -/
def LineProjSpecifiedMap {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (G : W.Opens) (q : G.toScheme ⟶ A.affineData.relProj) : Prop :=
  ∀ (V : T.affineOpens) (d : ℕ) (hd : 0 < d) (a : Γ(A.piece d, V.1)),
    ∃ (j : (lineProjGeneratorOpen f A L ψ V d a).toScheme ⟶ G.toScheme)
      (r : LineProjChart f A L ψ V d a),
      j ≫ G.ι = (lineProjGeneratorOpen f A L ψ V d a).ι ∧
      LineProjFractionFormula f A L ψ V d a (lineProjGeneratorOpen f A L ψ V d a)
        inf_le_left r ∧
      j ≫ q = lineProjChartToRelative f A L ψ V d hd a r

/-- The pulled-back frame on a chart B' mapping into B, namely the restriction of 1 tensor e.
Source: Stacks, Tag 0D2Z(3) (blueprint: lem-trf-line-proj-chart-pullback). -/
noncomputable def lineProjPulledFrame {W W' : Scheme.{u}} (h : W' ⟶ W) (L : W.Modules)
    (B : W.affineOpens) (B' : W'.affineOpens) (hB : B'.1 ≤ h ⁻¹ᵁ B.1)
    (e : Γ(L, B.1)) : Γ((tensorPullback h).obj L, B'.1) :=
  ((tensorPullback h).obj L).presheaf.map (homOfLE hB).op
    (tensorPullbackSection h L B.1 e)

/-- The part of a pulled-back generator chart lying in B'. This is the basic open of the
image of alpha, without requiring the ambient inverse-image chart to be affine.
Source: Stacks, Tag 0D2Z(3) (blueprint: lem-trf-line-proj-chart-pullback). -/
def lineProjPulledBasicOpen {W W' : Scheme.{u}} (h : W' ⟶ W)
    (B : W.affineOpens) (B' : W'.affineOpens) (α : Γ(W, B.1)) : W'.Opens :=
  B'.1 ⊓ h ⁻¹ᵁ W.basicOpen α

/-- On all affine trivializing charts the pure-tensor coefficient is h-sharp(alpha)
times f'-sharp(c), and the inverse images of the unprimed basic opens cover G'.
Source: Stacks, Tag 0D2Z(3) (blueprint: lem-trf-line-proj-chart-pullback). -/
def LineProjPullbackCoefficients {W W' T T' : Scheme.{u}}
    (f : W ⟶ T) (f' : W' ⟶ T') (h : W' ⟶ W) (g : T' ⟶ T)
    (A : RelativeProjAlgebra T) (A' : RelativeProjAlgebra T') (L : W.Modules)
    (β : ∀ n : ℕ, A'.piece n ≅ (tensorPullback g).obj (A.piece n))
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (ψ' : ∀ n : ℕ, (tensorPullback f').obj (A'.piece n) ⟶
      ((tensorPullback h).obj L).tensorPow n) (G' : W'.Opens) : Prop :=
  ∀ (V : T.affineOpens) (V' : T'.affineOpens) (hV : V'.1 ≤ g ⁻¹ᵁ V.1)
    (B : W.affineOpens) (B' : W'.affineOpens) (hB : B.1 ≤ f ⁻¹ᵁ V.1)
    (hB' : B'.1 ≤ f' ⁻¹ᵁ V'.1) (hBB : B'.1 ≤ h ⁻¹ᵁ B.1)
    (e : Γ(L, B.1)), IsFreeGenerator e →
    IsFreeGenerator (lineProjPulledFrame h L B B' hBB e) ∧
    (∀ (n : ℕ) (a : Γ(A.piece n, V.1)) (α : Γ(W, B.1)),
      (L.tensorPow n).presheaf.map (homOfLE hB).op (lineProjImage f A L ψ V.1 n a) =
        α • lineProjFramePower L B.1 e n →
      ∀ c : Γ(T', V'.1),
        (((tensorPullback h).obj L).tensorPow n).presheaf.map (homOfLE hB').op
            (lineProjImage f' A' ((tensorPullback h).obj L) ψ' V'.1 n
              (lineProjBaseSection g A A' β V V' hV n a c)) =
          ((h.appLE B.1 B'.1 hBB α) * (f'.appLE V'.1 B'.1 hB' c)) •
            lineProjFramePower ((tensorPullback h).obj L) B'.1
              (lineProjPulledFrame h L B B' hBB e) n) ∧
    G' ⊓ B'.1 = ⨆ (d : ℕ) (_hd : 0 < d) (a : Γ(A.piece d, V.1)) (α : Γ(W, B.1))
      (_hα : (L.tensorPow d).presheaf.map (homOfLE hB).op
          (lineProjImage f A L ψ V.1 d a) = α • lineProjFramePower L B.1 e d),
      lineProjPulledBasicOpen h B B' α

/-- Both composites on a pulled-back basic open factor through the same homogeneous
localization chart; its scalar map sends b/a^m to h-sharp(alpha_b)/h-sharp(alpha_a)^m.
The cross-multiplied equation is valid also on the empty scheme.
Source: Stacks, Tags 0D2Z(3), 01O9 and 01NK
(blueprint: lem-trf-line-proj-chart-pullback). -/
def LineProjCommonFractions {W W' T : Scheme.{u}} (f : W ⟶ T) (h : W' ⟶ W)
    (A : RelativeProjAlgebra T) (L : W.Modules)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (G : W.Opens) (G' : W'.Opens) (P' : Scheme.{u})
    (q : G.toScheme ⟶ A.affineData.relProj) (q' : G'.toScheme ⟶ P')
    (c : P' ⟶ A.affineData.relProj) : Prop :=
  ∀ (V : T.affineOpens) (B : W.affineOpens) (B' : W'.affineOpens)
    (hB : B.1 ≤ f ⁻¹ᵁ V.1) (hBB : B'.1 ≤ h ⁻¹ᵁ B.1)
    (e : Γ(L, B.1)), IsFreeGenerator e →
    ∀ (d : ℕ) (hd : 0 < d) (a : Γ(A.piece d, V.1)) (αa : Γ(W, B.1)),
      (L.tensorPow d).presheaf.map (homOfLE hB).op (lineProjImage f A L ψ V.1 d a) =
        αa • lineProjFramePower L B.1 e d →
      ∃ (j' : (lineProjPulledBasicOpen h B B' αa).toScheme ⟶ G'.toScheme)
        (j : (lineProjPulledBasicOpen h B B' αa).toScheme ⟶ G.toScheme)
        (r : (lineProjPulledBasicOpen h B B' αa).toScheme ⟶
          Spec (.of (HomogeneousLocalization.Away (A.grade V)
            (lineProjElement A V d a).val))),
        j' ≫ G'.ι = (lineProjPulledBasicOpen h B B' αa).ι ∧
        j ≫ G.ι = (lineProjPulledBasicOpen h B B' αa).ι ≫ h ∧
        r ≫ Proj.awayι (A.grade V) (lineProjElement A V d a).val
            (lineProjElement A V d a).property hd ≫ A.affineData.relProjι V =
          j' ≫ q' ≫ c ∧
        r ≫ Proj.awayι (A.grade V) (lineProjElement A V d a).val
            (lineProjElement A V d a).property hd ≫ A.affineData.relProjι V = j ≫ q ∧
        ∀ (m : ℕ) (b : Γ(A.piece (m • d), V.1)) (αb : Γ(W, B.1)),
          (L.tensorPow (m • d)).presheaf.map (homOfLE hB).op
              (lineProjImage f A L ψ V.1 (m • d) b) =
            αb • lineProjFramePower L B.1 e (m • d) →
          lineProjScalar (lineProjPulledBasicOpen h B B' αa) r
              (HomogeneousLocalization.Away.mk (A.grade V)
                (lineProjElement A V d a).property m
                (lineProjElement A V (m • d) b).val
                (lineProjElement A V (m • d) b).property) *
            (@id Γ(W', lineProjPulledBasicOpen h B B' αa)
              (W'.presheaf.map (homOfLE (inf_le_left :
                lineProjPulledBasicOpen h B B' αa ≤ B'.1)).op
                  (h.appLE B.1 B'.1 hBB αa))) ^ m =
            @id Γ(W', lineProjPulledBasicOpen h B B' αa)
              (W'.presheaf.map (homOfLE (inf_le_left :
                lineProjPulledBasicOpen h B B' αa ≤ B'.1)).op
                  (h.appLE B.1 B'.1 hBB αb))

private theorem tensor_section_eq_unit {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) :
    tensorPullbackSection g M U s =
      ((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app M).app U s := by
  exact (Classical.choose_spec (exists_tensorPullbackAdjunction g) M (op U) s).symm

attribute [local irreducible] tensorPullbackSection

private theorem pushforward_smul {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : X.Modules) (U : Y.Opens) (r : Γ(Y, U)) (s : Γ((pushforward g).obj M, U)) :
    (r • s : Γ((pushforward g).obj M, U)) = g.app U r • (show Γ(M, g ⁻¹ᵁ U) from s) := rfl

private theorem tensor_section_add {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (a b : Γ(M, U)) :
    tensorPullbackSection g M U (a + b) =
      tensorPullbackSection g M U a + tensorPullbackSection g M U b := by
  simp only [tensor_section_eq_unit, map_add]

private theorem tensor_section_zero {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) : tensorPullbackSection g M U 0 = 0 := by
  simp only [tensor_section_eq_unit, map_zero]

private theorem tensor_section_smul {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (r : Γ(Y, U)) (s : Γ(M, U)) :
    tensorPullbackSection g M U (r • s) =
      g.app U r • tensorPullbackSection g M U s := by
  rw [tensor_section_eq_unit, tensor_section_eq_unit]
  exact (Hom.app_smul
    ((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app M) r s).trans
      (pushforward_smul g _ U r _)

private theorem tensor_section_natural {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M N : Y.Modules} (φ : M ⟶ N) (U : Y.Opens) (s : Γ(M, U)) :
    ((tensorPullback g).map φ).app (g ⁻¹ᵁ U) (tensorPullbackSection g M U s) =
      tensorPullbackSection g N U (φ.app U s) := by
  simp only [tensor_section_eq_unit]
  exact congrArg (fun z ↦ z.app U s)
    ((Classical.choose (exists_tensorPullbackAdjunction g)).unit_naturality φ)

private theorem tensor_section_map {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Y.Modules) {U V : Y.Opens} (h : V ≤ U) (s : Γ(M, U)) :
    tensorPullbackSection g M V (M.presheaf.map (homOfLE h).op s) =
      ((tensorPullback g).obj M).presheaf.map (homOfLE (g.preimage_mono h)).op
        (tensorPullbackSection g M U s) := by
  simp only [tensor_section_eq_unit]
  exact Hom.app_presheaf_map ((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app M)
    (homOfLE h) s

private theorem tensor_section_comp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (s : Γ(M, U)) :
    ((tensorPullbackSectionComp g h).hom.app M).app ((g ≫ h) ⁻¹ᵁ U)
        (tensorPullbackSection (g ≫ h) M U s) =
      tensorPullbackSection g ((tensorPullback h).obj M) (h ⁻¹ᵁ U)
        (tensorPullbackSection h M U s) := by
  have hunit {A B : Scheme.{u}} (j : A ⟶ B) (N : B.Modules)
      (V : B.Opens) (t : Γ(N, V)) :
      ((tensorPullbackSectionAdjunction j).unit.app N).app V t =
        tensorPullbackSection j N V t :=
    (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction j)).1 N V t
  have hc := (tensorPullbackSectionAdjunction (g ≫ h)).unit_leftAdjointUniq_hom_app
    (((tensorPullbackSectionAdjunction h).comp (tensorPullbackSectionAdjunction g)).ofNatIsoRight
      (pushforwardComp g h)) M
  have hs := congrArg (fun z ↦ z.app U s) hc
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Hom.comp_app, pushforward_map_app, pushforwardComp_hom_app_app,
    Adjunction.comp_unit_app] at hs
  change ((tensorPullbackSectionComp g h).hom.app M).app ((g ≫ h) ⁻¹ᵁ U)
    (((tensorPullbackSectionAdjunction (g ≫ h)).unit.app M).app U s) =
    ((tensorPullbackSectionAdjunction g).unit.app ((tensorPullback h).obj M)).app (h ⁻¹ᵁ U)
      (((tensorPullbackSectionAdjunction h).unit.app M).app U s) at hs
  simpa only [hunit] using hs


attribute [local irreducible] tensorPullbackSectionComp

private theorem section_restrict_restrict {X : Scheme.{u}} (M : X.Modules)
    {U V B : X.Opens} (hV : V ≤ U) (hB : B ≤ V) (s : Γ(M, U)) :
    M.presheaf.map (homOfLE hB).op (M.presheaf.map (homOfLE hV).op s) =
      M.presheaf.map (homOfLE (hB.trans hV)).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private theorem tensor_section_congr {X Y : Scheme.{u}} {j k : X ⟶ Y}
    (e : j = k) (M : Y.Modules) (U : Y.Opens) (B : X.Opens)
    (hj : B ≤ j ⁻¹ᵁ U) (hk : B ≤ k ⁻¹ᵁ U) (s : Γ(M, U)) :
    ((eqToIso (congrArg (fun z ↦ (tensorPullback z).obj M) e)).hom).app B
      (((tensorPullback j).obj M).presheaf.map (homOfLE hj).op
        (tensorPullbackSection j M U s)) =
      ((tensorPullback k).obj M).presheaf.map (homOfLE hk).op
        (tensorPullbackSection k M U s) := by
  subst k
  rfl

private theorem tensor_section_comp_inv_restrict {X Y Z : Scheme.{u}}
    (j : X ⟶ Y) (k : Y ⟶ Z) (M : Z.Modules) (U : Z.Opens) (V : Y.Opens)
    (B : X.Opens) (hV : V ≤ k ⁻¹ᵁ U) (hB : B ≤ j ⁻¹ᵁ V) (s : Γ(M, U)) :
    ((lineProjCompInv j k M)).app B
      (((tensorPullback j).obj ((tensorPullback k).obj M)).presheaf.map (homOfLE hB).op
        (tensorPullbackSection j ((tensorPullback k).obj M) V
          (((tensorPullback k).obj M).presheaf.map (homOfLE hV).op
            (tensorPullbackSection k M U s)))) =
      ((tensorPullback (j ≫ k)).obj M).presheaf.map
        (homOfLE ((hB.trans (j.preimage_mono hV)).trans
          (Scheme.Hom.comp_preimage j k U).ge)).op
        (tensorPullbackSection (j ≫ k) M U s) := by
  rw [lineProjCompInv_eq]
  rw [tensor_section_map, section_restrict_restrict,
    ← tensor_section_comp]
  erw [Hom.app_presheaf_map]
  have hc := congrArg (fun z ↦ z.app ((j ≫ k) ⁻¹ᵁ U)
    (tensorPullbackSection (j ≫ k) M U s))
    ((tensorPullbackSectionComp j k).app M).hom_inv_id
  change ((tensorPullbackSectionComp j k).inv.app M).app ((j ≫ k) ⁻¹ᵁ U)
    (((tensorPullbackSectionComp j k).hom.app M).app ((j ≫ k) ⁻¹ᵁ U)
      (tensorPullbackSection (j ≫ k) M U s)) = _ at hc
  change ((tensorPullback (j ≫ k)).obj M).presheaf.map
    (homOfLE ((hB.trans (j.preimage_mono hV)).trans
          (Scheme.Hom.comp_preimage j k U).ge)).op
    (((tensorPullbackSectionComp j k).inv.app M).app ((j ≫ k) ⁻¹ᵁ U)
      (((tensorPullbackSectionComp j k).hom.app M).app ((j ≫ k) ⁻¹ᵁ U)
        (tensorPullbackSection (j ≫ k) M U s))) = _
  rw [hc]
  rfl

private theorem tensor_section_comp_restrict {X Y Z : Scheme.{u}}
    (j : X ⟶ Y) (k : Y ⟶ Z) (M : Z.Modules) (U : Z.Opens) (V : Y.Opens)
    (B : X.Opens) (hV : V ≤ k ⁻¹ᵁ U) (hB : B ≤ j ⁻¹ᵁ V) (s : Γ(M, U)) :
    ((lineProjCompHom j k M)).app B
      (((tensorPullback (j ≫ k)).obj M).presheaf.map
        (homOfLE ((hB.trans (j.preimage_mono hV)).trans
          (Scheme.Hom.comp_preimage j k U).ge)).op
        (tensorPullbackSection (j ≫ k) M U s)) =
      ((tensorPullback j).obj ((tensorPullback k).obj M)).presheaf.map (homOfLE hB).op
        (tensorPullbackSection j ((tensorPullback k).obj M) V
          (((tensorPullback k).obj M).presheaf.map (homOfLE hV).op
            (tensorPullbackSection k M U s))) := by
  rw [lineProjCompHom_eq]
  rw [tensor_section_map, section_restrict_restrict]
  erw [Hom.app_presheaf_map]
  exact congrArg
    (fun z ↦ ((tensorPullback j).obj ((tensorPullback k).obj M)).presheaf.map
      (homOfLE ((hB.trans (j.preimage_mono hV)).trans
          (Scheme.Hom.comp_preimage j k U).ge)).op z)
    (tensor_section_comp j k M U s)

private theorem tensor_square_section {W W' T T' : Scheme.{u}}
    (f : W ⟶ T) (f' : W' ⟶ T') (h : W' ⟶ W) (g : T' ⟶ T)
    (hsq : h ≫ f = f' ≫ g) (M : T.Modules)
    (V : T.Opens) (V' : T'.Opens) (B : W.Opens) (B' : W'.Opens)
    (hV : V' ≤ g ⁻¹ᵁ V) (hB : B ≤ f ⁻¹ᵁ V) (hB' : B' ≤ f' ⁻¹ᵁ V')
    (hBB : B' ≤ h ⁻¹ᵁ B) (a : Γ(M, V)) :
    ((lineProjCompHom h f M)).app B'
      ((lineProjSquareCast hsq.symm M).app B'
        (((lineProjCompInv f' g M)).app B'
          ((((tensorPullback f').obj ((tensorPullback g).obj M)).presheaf.map
            (homOfLE hB').op) (tensorPullbackSection f' ((tensorPullback g).obj M) V'
              (((tensorPullback g).obj M).presheaf.map (homOfLE hV).op
                (tensorPullbackSection g M V a)))))) =
      ((tensorPullback h).obj ((tensorPullback f).obj M)).presheaf.map
        (homOfLE hBB).op
        (tensorPullbackSection h ((tensorPullback f).obj M) B
          (((tensorPullback f).obj M).presheaf.map (homOfLE hB).op
            (tensorPullbackSection f M V a))) := by
  rw [lineProjSquareCast_eq]
  rw [tensor_section_comp_inv_restrict]
  erw [tensor_section_congr hsq.symm M V B'
    ((hB'.trans (f'.preimage_mono hV)).trans (Scheme.Hom.comp_preimage f' g V).ge)
    ((hBB.trans (h.preimage_mono hB)).trans (Scheme.Hom.comp_preimage h f V).ge) a]
  exact tensor_section_comp_restrict h f M V B B' hB hBB a


private theorem frame_power_restrict {W : Scheme.{u}} (L : W.Modules)
    {U V : W.Opens} (h : V ≤ U) (e : Γ(L, U)) (n : ℕ) :
    (L.tensorPow n).presheaf.map (homOfLE h).op (lineProjFramePower L U e n) =
      lineProjFramePower L V (L.presheaf.map (homOfLE h).op e) n := by
  induction n with
  | zero =>
    change W.presheaf.map (homOfLE h).op 1 = 1
    exact map_one _
  | succ n ih =>
    change (L ⊗ L.tensorPow n).presheaf.map (homOfLE h).op
      (tmulSection e (lineProjFramePower L U e n)) =
      tmulSection (L.presheaf.map (homOfLE h).op e)
        (lineProjFramePower L V (L.presheaf.map (homOfLE h).op e) n)
    rw [tmulSection_map, ih]

private theorem pullback_frame_power {W W' : Scheme.{u}} (h : W' ⟶ W)
    (L : W.Modules) (U : W.Opens) (e : Γ(L, U)) (n : ℕ) :
    (boundaryPullbackPowIso h L n).hom.app (h ⁻¹ᵁ U)
        (tensorPullbackSection h (L.tensorPow n) U (lineProjFramePower L U e n)) =
      lineProjFramePower ((tensorPullback h).obj L) (h ⁻¹ᵁ U)
        (tensorPullbackSection h L U e) n := by
  induction n with
  | zero =>
    change (pullbackObjUnitIso h).hom.app (h ⁻¹ᵁ U)
      (((boundaryPullbackComparison h).hom.app (𝟙_ W.Modules)).app (h ⁻¹ᵁ U)
        (tensorPullbackSection h (𝟙_ W.Modules) U (unitSectionsEquiv U 1))) = _
    rw [tensor_section_eq_unit]
    have hu := (Classical.choose (exists_tensorPullbackAdjunction h)).unit_leftAdjointUniq_hom_app
      (pullbackPushforwardAdjunction h) (𝟙_ W.Modules)
    have hs := congrArg (fun z ↦ z.app U (unitSectionsEquiv U 1)) hu
    change ((boundaryPullbackComparison h).hom.app (𝟙_ W.Modules)).app (h ⁻¹ᵁ U)
      (((Classical.choose (exists_tensorPullbackAdjunction h)).unit.app
        (𝟙_ W.Modules)).app U (unitSectionsEquiv U 1)) = _ at hs
    rw [hs]
    change (pullbackObjUnitIso h).hom.app (h ⁻¹ᵁ U) (pullbackSection h (1 : Γ(W, U))) =
      (1 : Γ(W', h ⁻¹ᵁ U))
    simpa only [map_one] using
      pullbackObjUnitIso_hom_app_pullbackSection h (1 : Γ(W, U))
  | succ n ih =>
    change (Iso.refl ((tensorPullback h).obj L) ⊗ᵢ boundaryPullbackPowIso h L n).hom.app
      (h ⁻¹ᵁ U) ((boundaryPullbackTensorIso h L (L.tensorPow n)).hom.app (h ⁻¹ᵁ U)
        (tensorPullbackSection h (L ⊗ L.tensorPow n) U
          (tmulSection e (lineProjFramePower L U e n)))) =
      tmulSection (tensorPullbackSection h L U e)
        (lineProjFramePower ((tensorPullback h).obj L) (h ⁻¹ᵁ U)
          (tensorPullbackSection h L U e) n)
    rw [tensor_section_eq_unit, boundaryPullbackTensorIso_unit_tmul, tensorIso_hom]
    exact (tensorHom_app_tmulSection (𝟙 ((tensorPullback h).obj L))
      (boundaryPullbackPowIso h L n).hom _ _).trans (by
        simpa only [Hom.id_app, ConcreteCategory.id_apply, ← tensor_section_eq_unit] using
          congrArg (tmulSection (tensorPullbackSection h L U e)) ih)


private theorem pullback_section_comparison {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) :
    ((boundaryPullbackComparison g).hom.app M).app (g ⁻¹ᵁ U)
        (tensorPullbackSection g M U s) = pullbackSection g s := by
  let a := Classical.choose (exists_tensorPullbackAdjunction g)
  have hu := a.unit_leftAdjointUniq_hom_app (pullbackPushforwardAdjunction g) M
  have hs := congrArg (fun z ↦ z.val.app (op U) s) hu
  change _ = ((pullbackPushforwardAdjunction g).unit.app M).app U s
  have ht : (a.unit.app M).app U s = tensorPullbackSection g M U s :=
    (tensor_section_eq_unit g M U s).symm
  change ((boundaryPullbackComparison g).hom.app M).app (g ⁻¹ᵁ U)
    ((a.unit.app M).app U s) = _ at hs
  rw [ht] at hs
  exact hs

private theorem pulled_frame_isFreeGenerator {W W' : Scheme.{u}} (h : W' ⟶ W)
    (L : W.Modules) (B : W.affineOpens) (B' : W'.affineOpens)
    (hBB : B'.1 ≤ h ⁻¹ᵁ B.1) (e : Γ(L, B.1)) (he : IsFreeGenerator e) :
    IsFreeGenerator (lineProjPulledFrame h L B B' hBB e) := by
  let q := (boundaryPullbackComparison h).app L
  have hf := ((he.pullback_unit_app h).map hBB).app_hom q.symm
  change IsFreeGenerator (q.inv.app B'.1
    (((pullback h).obj L).presheaf.map (homOfLE hBB).op (pullbackSection h e))) at hf
  rw [← pullback_section_comparison h L B.1 e, ← Hom.app_presheaf_map] at hf
  change IsFreeGenerator (q.inv.app B'.1 (q.hom.app B'.1
    (((tensorPullback h).obj L).presheaf.map (homOfLE hBB).op
      (tensorPullbackSection h L B.1 e)))) at hf
  have hc (s : Γ((tensorPullback h).obj L, B'.1)) :
      q.inv.app B'.1 (q.hom.app B'.1 s) = s := by
    exact congrArg (fun z ↦ z.app B'.1 s) q.hom_inv_id
  rw [hc] at hf
  exact hf

attribute [local irreducible] boundaryPullbackPowIso

private theorem module_comp_app {X : Scheme.{u}} {M N P : X.Modules}
    (φ : M ⟶ N) (ψ : N ⟶ P) (U : X.Opens) (s : Γ(M, U)) :
    (φ ≫ ψ).app U s = ψ.app U (φ.app U s) := rfl

private theorem module_chain_apply {X : Scheme.{u}}
    {M₀ M₁ M₂ M₃ M₄ M₅ M₆ : X.Modules}
    (a₁ : M₀ ⟶ M₁) (a₂ : M₁ ⟶ M₂) (a₃ : M₂ ⟶ M₃)
    (a₄ : M₃ ⟶ M₄) (a₅ : M₄ ⟶ M₅) (a₆ : M₅ ⟶ M₆)
    (U V : X.Opens) (hUV : V ≤ U) (s : Γ(M₀, U))
    (t : Γ(M₁, U)) (u : Γ(M₄, V)) (v : Γ(M₆, V))
    (h₁ : a₁.app U s = t)
    (h₂ : a₄.app V (a₃.app V (a₂.app V
      (M₁.presheaf.map (homOfLE hUV).op t))) = u)
    (h₃ : a₆.app V (a₅.app V u) = v) :
    M₆.presheaf.map (homOfLE hUV).op
      ((a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅ ≫ a₆).app U s) = v := by
  rw [module_comp_app, h₁, ← Hom.app_presheaf_map]
  simp only [module_comp_app]
  rw [h₂, h₃]

private theorem tensor_section_iso_cancel {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (e : M ≅ N) (U : Y.Opens) (s : Γ(N, U)) :
    ((tensorPullback f).map e.hom).app (f ⁻¹ᵁ U)
      (tensorPullbackSection f M U (e.inv.app U s)) = tensorPullbackSection f N U s := by
  rw [tensor_section_natural, iso_hom_app_inv_app]

private theorem tensor_section_map_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (φ : M ⟶ N) (U : Y.Opens) (V : X.Opens)
    (hV : V ≤ f ⁻¹ᵁ U) (s : Γ(M, U)) :
    ((tensorPullback f).map φ).app V
      (((tensorPullback f).obj M).presheaf.map (homOfLE hV).op
        (tensorPullbackSection f M U s)) =
      ((tensorPullback f).obj N).presheaf.map (homOfLE hV).op
        (tensorPullbackSection f N U (φ.app U s)) := by
  rw [Hom.app_presheaf_map, tensor_section_natural]

private theorem tensor_section_nested_image {W W' T : Scheme.{u}}
    (f : W ⟶ T) (h : W' ⟶ W) (M : T.Modules) (N : W.Modules)
    (φ : (tensorPullback f).obj M ⟶ N) (V : T.Opens) (B : W.Opens) (B' : W'.Opens)
    (hB : B ≤ f ⁻¹ᵁ V) (hBB : B' ≤ h ⁻¹ᵁ B) (a : Γ(M, V)) :
    ((tensorPullback h).map φ).app B'
      (((tensorPullback h).obj ((tensorPullback f).obj M)).presheaf.map
        (homOfLE hBB).op (tensorPullbackSection h ((tensorPullback f).obj M) B
          (((tensorPullback f).obj M).presheaf.map (homOfLE hB).op
            (tensorPullbackSection f M V a)))) =
      ((tensorPullback h).obj N).presheaf.map (homOfLE hBB).op
        (tensorPullbackSection h N B (N.presheaf.map (homOfLE hB).op
          (φ.app (f ⁻¹ᵁ V) (tensorPullbackSection f M V a)))) := by
  have hn := tensor_section_map_restrict h φ B B' hBB
    (((tensorPullback f).obj M).presheaf.map (homOfLE hB).op
      (tensorPullbackSection f M V a))
  have hm := Hom.app_presheaf_map φ (homOfLE hB) (tensorPullbackSection f M V a)
  exact hn.trans (congrArg (fun z ↦ ((tensorPullback h).obj N).presheaf.map
    (homOfLE hBB).op (tensorPullbackSection h N B z)) hm)

private theorem module_chain_pure
    {W W' T T' : Scheme.{u}} (f : W ⟶ T) (f' : W' ⟶ T')
    (h : W' ⟶ W) (g : T' ⟶ T) (M : T.Modules) (M' : T'.Modules)
    (N : W.Modules) (N' : W'.Modules) (β : M' ≅ (tensorPullback g).obj M)
    (φ : (tensorPullback f).obj M ⟶ N) (ρ : (tensorPullback h).obj N ⟶ N')
    (M₂ M₃ : W'.Modules)
    (c₁ : (tensorPullback f').obj ((tensorPullback g).obj M) ⟶ M₂)
    (c₂ : M₂ ⟶ M₃)
    (c₃ : M₃ ⟶ (tensorPullback h).obj ((tensorPullback f).obj M))
    (V : T.Opens) (V' : T'.Opens) (B : W.Opens) (B' : W'.Opens)
    (hV : V' ≤ g ⁻¹ᵁ V) (hB : B ≤ f ⁻¹ᵁ V) (hB' : B' ≤ f' ⁻¹ᵁ V')
    (hBB : B' ≤ h ⁻¹ᵁ B) (a : Γ(M, V))
    (hs : c₃.app B' (c₂.app B' (c₁.app B'
      (((tensorPullback f').obj ((tensorPullback g).obj M)).presheaf.map
        (homOfLE hB').op (tensorPullbackSection f' ((tensorPullback g).obj M) V'
          (((tensorPullback g).obj M).presheaf.map (homOfLE hV).op
            (tensorPullbackSection g M V a)))))) =
      ((tensorPullback h).obj ((tensorPullback f).obj M)).presheaf.map
        (homOfLE hBB).op (tensorPullbackSection h ((tensorPullback f).obj M) B
          (((tensorPullback f).obj M).presheaf.map (homOfLE hB).op
            (tensorPullbackSection f M V a)))) :
    N'.presheaf.map (homOfLE hB').op
      (((tensorPullback f').map β.hom ≫ c₁ ≫ c₂ ≫ c₃ ≫
        (tensorPullback h).map φ ≫ ρ).app (f' ⁻¹ᵁ V')
        (tensorPullbackSection f' M' V'
          (β.inv.app V' (((tensorPullback g).obj M).presheaf.map (homOfLE hV).op
            (tensorPullbackSection g M V a))))) =
      ρ.app B' (((tensorPullback h).obj N).presheaf.map (homOfLE hBB).op
        (tensorPullbackSection h N B (N.presheaf.map (homOfLE hB).op
          (φ.app (f ⁻¹ᵁ V) (tensorPullbackSection f M V a))))) := by
  exact module_chain_apply ((tensorPullback f').map β.hom) c₁ c₂ c₃
    ((tensorPullback h).map φ) ρ _ _ _ _ _ _ _
    (tensor_section_iso_cancel f' β V' _) hs
    (congrArg (fun z ↦ ρ.app B' z)
      (tensor_section_nested_image f h M N φ V B B' hB hBB a))

private theorem tensor_square_image {W W' T T' : Scheme.{u}}
    (f : W ⟶ T) (f' : W' ⟶ T') (h : W' ⟶ W) (g : T' ⟶ T)
    (hsq : h ≫ f = f' ≫ g) (M : T.Modules) (M' : T'.Modules)
    (N : W.Modules) (N' : W'.Modules) (β : M' ≅ (tensorPullback g).obj M)
    (φ : (tensorPullback f).obj M ⟶ N) (ρ : (tensorPullback h).obj N ⟶ N')
    (V : T.Opens) (V' : T'.Opens) (B : W.Opens) (B' : W'.Opens)
    (hV : V' ≤ g ⁻¹ᵁ V) (hB : B ≤ f ⁻¹ᵁ V) (hB' : B' ≤ f' ⁻¹ᵁ V')
    (hBB : B' ≤ h ⁻¹ᵁ B) (a : Γ(M, V)) :
    N'.presheaf.map (homOfLE hB').op
      (((tensorPullback f').map β.hom ≫
        (lineProjCompInv f' g M) ≫
        lineProjSquareCast hsq.symm M ≫
        (lineProjCompHom h f M) ≫
        (tensorPullback h).map φ ≫ ρ).app (f' ⁻¹ᵁ V')
        (tensorPullbackSection f' M' V'
          (β.inv.app V' (((tensorPullback g).obj M).presheaf.map (homOfLE hV).op
            (tensorPullbackSection g M V a))))) =
      ρ.app B' (((tensorPullback h).obj N).presheaf.map (homOfLE hBB).op
        (tensorPullbackSection h N B
          (N.presheaf.map (homOfLE hB).op
            (φ.app (f ⁻¹ᵁ V) (tensorPullbackSection f M V a))))) := by
  exact module_chain_pure f f' h g M M' N N' β φ ρ
    ((tensorPullback (f' ≫ g)).obj M) ((tensorPullback (h ≫ f)).obj M)
    ((lineProjCompInv f' g M))
    (lineProjSquareCast hsq.symm M)
    ((lineProjCompHom h f M))
    V V' B B' hV hB hB' hBB a
    (tensor_square_section f f' h g hsq M V V' B B' hV hB hB' hBB a)


private theorem tensor_frame_scalar {X Y : Scheme.{u}} (h : X ⟶ Y)
    (N : Y.Modules) (N' : X.Modules) (ρ : (tensorPullback h).obj N ⟶ N')
    (B : Y.Opens) (B' : X.Opens) (hBB : B' ≤ h ⁻¹ᵁ B)
    (e : Γ(N, B)) (e' : Γ(N', B')) (s : Γ(N, B)) (α : Γ(Y, B))
    (hs : s = α • e)
    (he : ρ.app B' (((tensorPullback h).obj N).presheaf.map (homOfLE hBB).op
      (tensorPullbackSection h N B e)) = e') :
    ρ.app B' (((tensorPullback h).obj N).presheaf.map (homOfLE hBB).op
      (tensorPullbackSection h N B s)) = h.appLE B B' hBB α • e' := by
  rw [hs, tensor_section_smul, map_smul, Hom.app_smul, he]
  rfl

private theorem tensor_square_coefficient {W W' T T' : Scheme.{u}}
    (f : W ⟶ T) (f' : W' ⟶ T') (h : W' ⟶ W) (g : T' ⟶ T)
    (hsq : h ≫ f = f' ≫ g) (M : T.Modules) (M' : T'.Modules)
    (N : W.Modules) (N' : W'.Modules) (β : M' ≅ (tensorPullback g).obj M)
    (φ : (tensorPullback f).obj M ⟶ N) (ρ : (tensorPullback h).obj N ⟶ N')
    (V : T.Opens) (V' : T'.Opens) (B : W.Opens) (B' : W'.Opens)
    (hV : V' ≤ g ⁻¹ᵁ V) (hB : B ≤ f ⁻¹ᵁ V) (hB' : B' ≤ f' ⁻¹ᵁ V')
    (hBB : B' ≤ h ⁻¹ᵁ B) (a : Γ(M, V))
    (e : Γ(N, B)) (e' : Γ(N', B')) (α : Γ(W, B)) (c : Γ(T', V'))
    (ha : N.presheaf.map (homOfLE hB).op
      (φ.app (f ⁻¹ᵁ V) (tensorPullbackSection f M V a)) = α • e)
    (he : ρ.app B' (((tensorPullback h).obj N).presheaf.map (homOfLE hBB).op
      (tensorPullbackSection h N B e)) = e') :
    N'.presheaf.map (homOfLE hB').op
      (((tensorPullback f').map β.hom ≫ lineProjCompInv f' g M ≫
        lineProjSquareCast hsq.symm M ≫
        lineProjCompHom h f M ≫ (tensorPullback h).map φ ≫ ρ).app (f' ⁻¹ᵁ V')
        (tensorPullbackSection f' M' V'
          (c • β.inv.app V' (((tensorPullback g).obj M).presheaf.map (homOfLE hV).op
            (tensorPullbackSection g M V a))))) =
      (h.appLE B B' hBB α * f'.appLE V' B' hB' c) • e' := by
  rw [tensor_section_smul, Hom.app_smul, map_smul]
  change f'.appLE V' B' hB' c • _ = _
  rw [tensor_square_image f f' h g hsq M M' N N' β φ ρ V V' B B' hV hB hB' hBB a,
    tensor_frame_scalar h N N' ρ B B' hBB e e' _ α ha he, smul_smul, mul_comm]

private theorem lineProj_base_coefficient {W W' T T' : Scheme.{u}}
    (f : W ⟶ T) (f' : W' ⟶ T') (h : W' ⟶ W) (g : T' ⟶ T)
    (hsq : h ≫ f = f' ≫ g) (A : RelativeProjAlgebra T) (A' : RelativeProjAlgebra T')
    (L : W.Modules) (β : ∀ n : ℕ, A'.piece n ≅ (tensorPullback g).obj (A.piece n))
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (V : T.affineOpens) (V' : T'.affineOpens) (hV : V'.1 ≤ g ⁻¹ᵁ V.1)
    (B : W.affineOpens) (B' : W'.affineOpens) (hB : B.1 ≤ f ⁻¹ᵁ V.1)
    (hB' : B'.1 ≤ f' ⁻¹ᵁ V'.1) (hBB : B'.1 ≤ h ⁻¹ᵁ B.1)
    (e : Γ(L, B.1)) (n : ℕ) (a : Γ(A.piece n, V.1)) (α : Γ(W, B.1))
    (hα : (L.tensorPow n).presheaf.map (homOfLE hB).op
      (lineProjImage f A L ψ V.1 n a) = α • lineProjFramePower L B.1 e n)
    (c : Γ(T', V'.1)) :
    (((tensorPullback h).obj L).tensorPow n).presheaf.map (homOfLE hB').op
      (lineProjImage f' A' ((tensorPullback h).obj L)
        (lineProjPullbackMap hsq A A' L β ψ) V'.1 n
        (lineProjBaseSection g A A' β V V' hV n a c)) =
      ((h.appLE B.1 B'.1 hBB α) * (f'.appLE V'.1 B'.1 hB' c)) •
        lineProjFramePower ((tensorPullback h).obj L) B'.1
          (lineProjPulledFrame h L B B' hBB e) n := by
  apply tensor_square_coefficient f f' h g hsq (A.piece n) (A'.piece n)
    (L.tensorPow n) (((tensorPullback h).obj L).tensorPow n) (β n) (ψ n)
    (lineProjPowHom h L n) V.1 V'.1 B.1 B'.1 hV hB hB' hBB a
    (lineProjFramePower L B.1 e n)
    (lineProjFramePower ((tensorPullback h).obj L) B'.1
      (lineProjPulledFrame h L B B' hBB e) n) α c hα
  rw [lineProjPowHom_eq, Hom.app_presheaf_map, pullback_frame_power, frame_power_restrict]
  rfl

private theorem affine_tensor_section_induction {T T' : Scheme.{u}} (g : T' ⟶ T)
    (M : T.Modules) [M.IsQuasicoherent] (M' : T'.Modules)
    (β : M' ≅ (tensorPullback g).obj M)
    (V : T.affineOpens) (V' : T'.affineOpens) (hV : V'.1 ≤ g ⁻¹ᵁ V.1)
    (P : Γ(M', V'.1) → Prop) (hzero : P 0)
    (hadd : ∀ s t, P s → P t → P (s + t))
    (hsmul : ∀ (c : Γ(T', V'.1)) s, P s → P (c • s))
    (hpure : ∀ a : Γ(M, V.1), P (β.inv.app V'.1
      (((tensorPullback g).obj M).presheaf.map (homOfLE hV).op
        (tensorPullbackSection g M V.1 a)))) : ∀ s, P s := by
  let : Algebra Γ(T, V.1) Γ(T', V'.1) := (g.appLE V.1 V'.1 hV).hom.toAlgebra
  let : ∀ G : T.Modules, Module Γ(T, V.1) Γ((tensorPullback g).obj G, V'.1) :=
    fun G ↦ Module.compHom _ (g.appLE V.1 V'.1 hV).hom
  obtain ⟨c, hc, _, ht, _⟩ := exists_tensorPullback_affine_sections g V V' hV
  intro s
  obtain ⟨t, he⟩ := (hc M inferInstance).surjective (β.hom.app V'.1 s)
  have hi : β.inv.app V'.1 (c M inferInstance t) = s := by
    rw [he]
    exact iso_hom_app_inv_app β.symm V'.1 s
  rw [← hi]
  clear he hi
  induction t using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using hzero
  | tmul a b =>
    rw [ht, Hom.app_smul]
    have hn (a : Γ(M, V.1)) :
        ((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app M).val.app
          (op V.1) a = tensorPullbackSection g M V.1 a :=
      (tensor_section_eq_unit g M V.1 a).symm
    rw [hn]
    exact hsmul b _ (hpure a)
  | add t u ht hu =>
    simp only [map_add]
    exact hadd _ _ ht hu

private theorem tensor_coefficient_unit {W W' T T' : Scheme.{u}}
    (f : W ⟶ T) (f' : W' ⟶ T') (h : W' ⟶ W) (g : T' ⟶ T)
    (M : T.Modules) [M.IsQuasicoherent] (M' : T'.Modules) [M'.IsQuasicoherent]
    (N : W.Modules) (N' : W'.Modules)
    (β : M' ≅ (tensorPullback g).obj M)
    (φ : (tensorPullback f).obj M ⟶ N)
    (φ' : (tensorPullback f').obj M' ⟶ N')
    (V : T.affineOpens) (V' : T'.affineOpens) (hV : V'.1 ≤ g ⁻¹ᵁ V.1)
    (B : W.affineOpens) (B' : W'.affineOpens) (hB : B.1 ≤ f ⁻¹ᵁ V.1)
    (hB' : B'.1 ≤ f' ⁻¹ᵁ V'.1) (hBB : B'.1 ≤ h ⁻¹ᵁ B.1)
    (e : Γ(N, B.1)) (he : IsFreeGenerator e)
    (e' : Γ(N', B'.1)) (he' : IsFreeGenerator e')
    (hpure : ∀ (a : Γ(M, V.1)) (α : Γ(W, B.1)),
      φ.app B.1 (((tensorPullback f).obj M).presheaf.map (homOfLE hB).op
        (tensorPullbackSection f M V.1 a)) = α • e →
      φ'.app B'.1 (((tensorPullback f').obj M').presheaf.map (homOfLE hB').op
        (tensorPullbackSection f' M' V'.1 (β.inv.app V'.1
          (((tensorPullback g).obj M).presheaf.map (homOfLE hV).op
            (tensorPullbackSection g M V.1 a))))) = (h.appLE B.1 B'.1 hBB α) • e')
    (x : W') (hx : x ∈ B'.1) :
    Function.Surjective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ'.mapPresheaf) ↔
      ∃ (a : Γ(M, V.1)) (α : Γ(W, B.1)),
        φ.app B.1 (((tensorPullback f).obj M).presheaf.map (homOfLE hB).op
          (tensorPullbackSection f M V.1 a)) = α • e ∧
        x ∈ W'.basicOpen (h.appLE B.1 B'.1 hBB α) := by
  classical
  let image (s : Γ(M', V'.1)) := φ'.app B'.1
    (((tensorPullback f').obj M').presheaf.map (homOfLE hB').op
      (tensorPullbackSection f' M' V'.1 s))
  let coeff (s : Γ(M', V'.1)) := he'.coeff (image s)
  let q (s : Γ(M', V'.1)) := W'.presheaf.germ B'.1 x hx (coeff s)
  have hqadd (s t : Γ(M', V'.1)) : q (s + t) = q s + q t := by
    simp only [q, coeff, image, tensor_section_add, map_add, IsFreeGenerator.coeff_add]
  have hqzero : q 0 = 0 := by
    simp only [q, coeff, image, tensor_section_zero, map_zero, IsFreeGenerator.coeff_zero]
  have hqsmul (c : Γ(T', V'.1)) (s : Γ(M', V'.1)) :
      q (c • s) = W'.presheaf.germ B'.1 x hx (f'.appLE V'.1 B'.1 hB' c) * q s := by
    simp only [q, coeff, image, tensor_section_smul, map_smul, Hom.app_smul,
      IsFreeGenerator.coeff_smul_left, map_mul]
    rfl
  constructor
  · intro hs
    obtain ⟨s, α', hs', hx'⟩ :=
      (affine_tensor_generator_locus f' M' N' φ' V' B' hB' e' he' x hx).mp hs
    have hunit : IsUnit (q s) := by
      have hc : coeff s = α' := (he'.coeff_eq_iff _ _).mpr hs'.symm
      change IsUnit (W'.presheaf.germ B'.1 x hx (coeff s))
      rw [hc]
      exact (W'.mem_basicOpen α' x hx).mp hx'
    by_contra hn
    have hm : ∀ s, q s ∈ IsLocalRing.maximalIdeal (W'.presheaf.stalk x) := by
      apply affine_tensor_section_induction g M M' β V V' hV
      · rw [hqzero]; exact Ideal.zero_mem _
      · intro s t hs ht
        rw [hqadd]; exact Ideal.add_mem _ hs ht
      · intro c s hs
        rw [hqsmul]; exact Ideal.mul_mem_left _ _ hs
      · intro a
        obtain ⟨α, hα⟩ := he.exists_smul_eq
          (φ.app B.1 (((tensorPullback f).obj M).presheaf.map (homOfLE hB).op
            (tensorPullbackSection f M V.1 a)))
        have hc := hpure a α hα.symm
        change image _ = (h.appLE B.1 B'.1 hBB α) • e' at hc
        have hq : q (β.inv.app V'.1
            (((tensorPullback g).obj M).presheaf.map (homOfLE hV).op
              (tensorPullbackSection g M V.1 a))) =
            W'.presheaf.germ B'.1 x hx (h.appLE B.1 B'.1 hBB α) := by
          simp only [q, coeff, hc, IsFreeGenerator.coeff_smul_self]
        rw [hq, IsLocalRing.mem_maximalIdeal]
        intro hu
        exact hn ⟨a, α, hα.symm, (W'.mem_basicOpen _ x hx).mpr hu⟩
    have hnot := hm s
    rw [IsLocalRing.mem_maximalIdeal] at hnot
    exact hnot hunit
  · rintro ⟨a, α, ha, hxα⟩
    apply (affine_tensor_generator_locus f' M' N' φ' V' B' hB' e' he' x hx).mpr
    exact ⟨β.inv.app V'.1 (((tensorPullback g).obj M).presheaf.map (homOfLE hV).op
      (tensorPullbackSection g M V.1 a)), h.appLE B.1 B'.1 hBB α, hpure a α ha, hxα⟩

private theorem piece_quasicoherent {T : Scheme.{u}} (A : RelativeProjAlgebra T)
    (n : ℕ) : (A.piece n).IsQuasicoherent := by
  let E := A.algebra.obj.toModule
  have : E.IsQuasicoherent := A.algebra.property
  let R : Retract (A.piece n) E :=
    { i := Sigma.ι A.piece n ≫ A.decomposition.hom
      r := A.decomposition.inv ≫ Sigma.π A.piece n
      retract := by simp }
  let δ : E ⟶ E := 𝟙 E - R.r ≫ R.i
  have hc : R.i ≫ δ = 0 := by simp [δ]
  have hl : IsLimit (KernelFork.ofι R.i hc) :=
    KernelFork.IsLimit.ofι _ _ (fun k _ ↦ k ≫ R.r)
      (fun k hk ↦ by
        rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at hk
        rw [Category.assoc, ← hk])
      (fun k _ m hm ↦ by rw [← hm, Category.assoc, R.retract, Category.comp_id])
  let e : kernel δ ≅ A.piece n := (kernelIsKernel δ).conePointUniqueUpToIso hl
  have := isQuasicoherent_kernel δ
  exact (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso e inferInstance

private theorem frame_power_free {W : Scheme.{u}} (L : W.Modules)
    (B : W.Opens) (e : Γ(L, B)) (he : IsFreeGenerator e) (n : ℕ) :
    IsFreeGenerator (lineProjFramePower L B e n) := by
  induction n with
  | zero => exact isFreeGenerator_one B
  | succ n ih => exact he.tmulSection ih

private theorem lineProj_generation_cover {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (G : W.Opens)
    (hG : (G : Set W) = {x | ∃ d : ℕ, 0 < d ∧ Function.Surjective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (ψ d).mapPresheaf)})
    (V : T.affineOpens) (B : W.affineOpens) (hB : B.1 ≤ f ⁻¹ᵁ V.1)
    (e : Γ(L, B.1)) (he : IsFreeGenerator e) :
    G ⊓ B.1 = ⨆ (d : ℕ) (_hd : 0 < d) (a : Γ(A.piece d, V.1)) (α : Γ(W, B.1))
      (_hα : (L.tensorPow d).presheaf.map (homOfLE hB).op
          (lineProjImage f A L ψ V.1 d a) = α • lineProjFramePower L B.1 e d),
      W.basicOpen α := by
  have (d : ℕ) : (A.piece d).IsQuasicoherent := piece_quasicoherent A d
  ext x
  constructor
  · rintro ⟨hxG, hxB⟩
    have hxG' : x ∈ (G : Set W) := hxG
    rw [hG] at hxG'
    obtain ⟨d, hd, hs⟩ := hxG'
    obtain ⟨a, α, ha, hα⟩ :=
      (affine_tensor_generator_locus f (A.piece d) (L.tensorPow d) (ψ d)
        V B hB (lineProjFramePower L B.1 e d) (frame_power_free L B.1 e he d) x hxB).mp hs
    have ha' : (L.tensorPow d).presheaf.map (homOfLE hB).op
        (lineProjImage f A L ψ V.1 d a) = α • lineProjFramePower L B.1 e d := by
      rw [lineProjImage, ← Hom.app_presheaf_map]
      exact ha
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨d,
      TopologicalSpace.Opens.mem_iSup.mpr ⟨hd,
      TopologicalSpace.Opens.mem_iSup.mpr ⟨a,
      TopologicalSpace.Opens.mem_iSup.mpr ⟨α,
      TopologicalSpace.Opens.mem_iSup.mpr ⟨ha', hα⟩⟩⟩⟩⟩
  · intro hx
    obtain ⟨d, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨hd, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨a, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨α, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨ha, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have hxB := W.basicOpen_le α hx
    refine ⟨?_, hxB⟩
    have hs : Function.Surjective
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (ψ d).mapPresheaf) := by
      apply (affine_tensor_generator_locus f (A.piece d) (L.tensorPow d) (ψ d)
        V B hB (lineProjFramePower L B.1 e d) (frame_power_free L B.1 e he d) x hxB).mpr
      refine ⟨a, α, ?_, hx⟩
      rw [Hom.app_presheaf_map]
      exact ha
    change x ∈ (G : Set W)
    rw [hG]
    exact ⟨d, hd, hs⟩

private theorem lineProj_pullback_cover {W W' T T' : Scheme.{u}}
    (f : W ⟶ T) (f' : W' ⟶ T') (h : W' ⟶ W) (g : T' ⟶ T)
    (_hsq : h ≫ f = f' ≫ g) (A : RelativeProjAlgebra T) (A' : RelativeProjAlgebra T')
    (L : W.Modules) (β : ∀ n : ℕ, A'.piece n ≅ (tensorPullback g).obj (A.piece n))
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (ψ' : ∀ n : ℕ, (tensorPullback f').obj (A'.piece n) ⟶
      ((tensorPullback h).obj L).tensorPow n)
    (hpure : ∀ (V : T.affineOpens) (V' : T'.affineOpens) (hV : V'.1 ≤ g ⁻¹ᵁ V.1)
      (B : W.affineOpens) (B' : W'.affineOpens) (hB : B.1 ≤ f ⁻¹ᵁ V.1)
      (hB' : B'.1 ≤ f' ⁻¹ᵁ V'.1) (hBB : B'.1 ≤ h ⁻¹ᵁ B.1)
      (e : Γ(L, B.1)) (n : ℕ) (a : Γ(A.piece n, V.1)) (α : Γ(W, B.1)),
      (L.tensorPow n).presheaf.map (homOfLE hB).op
        (lineProjImage f A L ψ V.1 n a) = α • lineProjFramePower L B.1 e n →
      (((tensorPullback h).obj L).tensorPow n).presheaf.map (homOfLE hB').op
        (lineProjImage f' A' ((tensorPullback h).obj L) ψ' V'.1 n
          (lineProjBaseSection g A A' β V V' hV n a 1)) =
        (h.appLE B.1 B'.1 hBB α) • lineProjFramePower ((tensorPullback h).obj L) B'.1
          (lineProjPulledFrame h L B B' hBB e) n)
    (G' : W'.Opens)
    (hG' : (G' : Set W') = {x | ∃ d : ℕ, 0 < d ∧ Function.Surjective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (ψ' d).mapPresheaf)})
    (V : T.affineOpens) (V' : T'.affineOpens) (hV : V'.1 ≤ g ⁻¹ᵁ V.1)
    (B : W.affineOpens) (B' : W'.affineOpens) (hB : B.1 ≤ f ⁻¹ᵁ V.1)
    (hB' : B'.1 ≤ f' ⁻¹ᵁ V'.1) (hBB : B'.1 ≤ h ⁻¹ᵁ B.1)
    (e : Γ(L, B.1)) (he : IsFreeGenerator e) :
    G' ⊓ B'.1 = ⨆ (d : ℕ) (_hd : 0 < d) (a : Γ(A.piece d, V.1)) (α : Γ(W, B.1))
      (_hα : (L.tensorPow d).presheaf.map (homOfLE hB).op
          (lineProjImage f A L ψ V.1 d a) = α • lineProjFramePower L B.1 e d),
      lineProjPulledBasicOpen h B B' α := by
  have (n : ℕ) : (A.piece n).IsQuasicoherent := piece_quasicoherent A n
  have (n : ℕ) : (A'.piece n).IsQuasicoherent := piece_quasicoherent A' n
  have hc (n : ℕ) (x : W') (hx : x ∈ B'.1) :
      Function.Surjective
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (ψ' n).mapPresheaf) ↔
        ∃ (a : Γ(A.piece n, V.1)) (α : Γ(W, B.1)),
          (L.tensorPow n).presheaf.map (homOfLE hB).op
            (lineProjImage f A L ψ V.1 n a) = α • lineProjFramePower L B.1 e n ∧
          x ∈ lineProjPulledBasicOpen h B B' α := by
    have ht := tensor_coefficient_unit f f' h g (A.piece n) (A'.piece n)
      (L.tensorPow n) (((tensorPullback h).obj L).tensorPow n) (β n) (ψ n)
      (ψ' n) V V' hV B B' hB hB' hBB
      (lineProjFramePower L B.1 e n) (frame_power_free L B.1 e he n)
      (lineProjFramePower ((tensorPullback h).obj L) B'.1
        (lineProjPulledFrame h L B B' hBB e) n)
      (frame_power_free _ _ _ (pulled_frame_isFreeGenerator h L B B' hBB e he) n)
      (by
        intro a α ha
        have ha' : (L.tensorPow n).presheaf.map (homOfLE hB).op
            (lineProjImage f A L ψ V.1 n a) = α • lineProjFramePower L B.1 e n := by
          rw [lineProjImage, ← Hom.app_presheaf_map]
          exact ha
        have hp := hpure V V' hV B B' hB hB' hBB e n a α ha'
        simpa only [lineProjBaseSection, one_smul, map_one, mul_one, lineProjImage,
          ← Hom.app_presheaf_map] using hp) x hx
    simpa only [Hom.app_presheaf_map, lineProjImage,
      Scheme.basicOpen_appLE, lineProjPulledBasicOpen] using ht
  ext x
  constructor
  · rintro ⟨hxG, hxB⟩
    have hxG : x ∈ (G' : Set W') := hxG
    rw [hG'] at hxG
    obtain ⟨d, hd, hs⟩ := hxG
    obtain ⟨a, α, ha, hxα⟩ := (hc d x hxB).mp hs
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨d,
      TopologicalSpace.Opens.mem_iSup.mpr ⟨hd,
      TopologicalSpace.Opens.mem_iSup.mpr ⟨a,
      TopologicalSpace.Opens.mem_iSup.mpr ⟨α,
      TopologicalSpace.Opens.mem_iSup.mpr ⟨ha, hxα⟩⟩⟩⟩⟩
  · intro hx
    obtain ⟨d, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨hd, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨a, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨α, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨ha, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have hxB := hx.1
    refine ⟨?_, hxB⟩
    change x ∈ (G' : Set W')
    rw [hG']
    exact ⟨d, hd, (hc d x hxB).mpr ⟨a, α, ha, hx⟩⟩

private theorem lineProj_generation_preimage {W W' T T' : Scheme.{u}}
    (f : W ⟶ T) (f' : W' ⟶ T') (h : W' ⟶ W) (g : T' ⟶ T)
    (hsq : h ≫ f = f' ≫ g) (A : RelativeProjAlgebra T) (A' : RelativeProjAlgebra T')
    (L : W.Modules) [L.IsInvertible]
    (β : ∀ n : ℕ, A'.piece n ≅ (tensorPullback g).obj (A.piece n))
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (ψ' : ∀ n : ℕ, (tensorPullback f').obj (A'.piece n) ⟶
      ((tensorPullback h).obj L).tensorPow n)
    (G : W.Opens) (G' : W'.Opens)
    (hG : (G : Set W) = {x | ∃ d : ℕ, 0 < d ∧ Function.Surjective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (ψ d).mapPresheaf)})
    (hc : LineProjPullbackCoefficients f f' h g A A' L β ψ ψ' G') : G' = h ⁻¹ᵁ G := by
  have : SheafOfModules.IsInvertible L := IsInvertible.sheafOfModules_isInvertible L
  ext x
  obtain ⟨V, hV, hxV, _⟩ :=
    exists_isAffineOpen_mem_and_subset (x := f (h x)) (U := ⊤) (by trivial)
  let V₀ : T.affineOpens := ⟨V, hV⟩
  have hxg : f' x ∈ g ⁻¹ᵁ V := by
    change (f' ≫ g) x ∈ V
    rw [← hsq]
    exact hxV
  obtain ⟨V', hV', hxV', hVg⟩ := exists_isAffineOpen_mem_and_subset hxg
  let V₁ : T'.affineOpens := ⟨V', hV'⟩
  change V' ≤ g ⁻¹ᵁ V at hVg
  obtain ⟨B, hxB, hBV, e, he⟩ :=
    exists_isFreeGenerator L (x := h x) (W := f ⁻¹ᵁ V) hxV
  obtain ⟨B', hB', hxB', hBB'⟩ :=
    exists_isAffineOpen_mem_and_subset (x := x)
      (U := (f' ⁻¹ᵁ V') ⊓ (h ⁻¹ᵁ B.1)) ⟨hxV', hxB⟩
  let B₁ : W'.affineOpens := ⟨B', hB'⟩
  have hBV' : B' ≤ f' ⁻¹ᵁ V' := fun y hy ↦ (hBB' hy).1
  have hBB : B' ≤ h ⁻¹ᵁ B.1 := fun y hy ↦ (hBB' hy).2
  have ho := lineProj_generation_cover f A L ψ G hG V₀ B hBV e he
  have hn := (hc V₀ V₁ hVg B B₁ hBV hBV' hBB e he).2.2
  constructor
  · intro hx
    have hx : x ∈ G' ⊓ B' := ⟨hx, hxB'⟩
    rw [hn] at hx
    obtain ⟨d, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨hd, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨a, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨α, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨ha, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have hm : h x ∈ G ⊓ B.1 := by
      rw [ho]
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨d,
        TopologicalSpace.Opens.mem_iSup.mpr ⟨hd,
        TopologicalSpace.Opens.mem_iSup.mpr ⟨a,
        TopologicalSpace.Opens.mem_iSup.mpr ⟨α,
        TopologicalSpace.Opens.mem_iSup.mpr ⟨ha, hx.2⟩⟩⟩⟩⟩
    exact hm.1
  · intro hx
    have hx : h x ∈ G ⊓ B.1 := ⟨hx, hxB⟩
    rw [ho] at hx
    obtain ⟨d, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨hd, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨a, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨α, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨ha, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have hm : x ∈ G' ⊓ B' := by
      rw [hn]
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨d,
        TopologicalSpace.Opens.mem_iSup.mpr ⟨hd,
        TopologicalSpace.Opens.mem_iSup.mpr ⟨a,
        TopologicalSpace.Opens.mem_iSup.mpr ⟨α,
        TopologicalSpace.Opens.mem_iSup.mpr ⟨ha, hxB', hx⟩⟩⟩⟩⟩
    exact hm.1

private theorem lineProjScalar_resLE {X Y : Scheme.{u}} (h : X ⟶ Y)
    (U : X.Opens) (V : Y.Opens) (hUV : U ≤ h ⁻¹ᵁ V) {R : CommRingCat.{u}}
    (q : V.toScheme ⟶ Spec R) :
    lineProjScalar U (h.resLE V U hUV ≫ q) =
      lineProjScalar V q ≫ h.appLE V U hUV := by
  simp only [lineProjScalar, Scheme.Hom.comp_appTop, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem lineProjScalar_homOfLE {X : Scheme.{u}} (U V : X.Opens) (hUV : U ≤ V)
    {R : CommRingCat.{u}} (q : V.toScheme ⟶ Spec R) :
    lineProjScalar U (X.homOfLE hUV ≫ q) =
      lineProjScalar V q ≫ X.presheaf.map (homOfLE hUV).op := by
  ext s
  let t := q.appTop ((Scheme.ΓSpecIso R).inv s)
  have ht : V.topIso.inv (V.topIso.hom t) = t := V.topIso.hom_inv_id_apply t
  change U.topIso.hom ((X.homOfLE hUV).appTop t) =
    X.presheaf.map (homOfLE hUV).op (V.topIso.hom t)
  conv_lhs => rw [← ht]
  rw [Scheme.homOfLE_appTop_topIso_inv]
  exact U.topIso.inv_hom_id_apply _


private theorem appLE_restrict_square {X Y : Scheme.{u}} (h : X ⟶ Y)
    (B D : Y.Opens) (hDB : D ≤ B) (B' U : X.Opens)
    (hUB' : U ≤ B') (hB'B : B' ≤ h ⁻¹ᵁ B) (hUD : U ≤ h ⁻¹ᵁ D)
    (α : Γ(Y, B)) :
    h.appLE D U hUD (Y.presheaf.map (homOfLE hDB).op α) =
      X.presheaf.map (homOfLE hUB').op (h.appLE B B' hB'B α) := by
  change (Y.presheaf.map (homOfLE hDB).op ≫ h.appLE D U hUD) α =
    (h.appLE B B' hB'B ≫ X.presheaf.map (homOfLE hUB').op) α
  rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

private theorem lineProj_unprimed_chart_on_basic {W T : Scheme.{u}}
    (f : W ⟶ T) (A : RelativeProjAlgebra T) (L : W.Modules) [L.IsInvertible]
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (hunit : ∀ (V : T.Opens) (r : Γ(T, V)),
      lineProjImage f A L ψ V 0 (A.graded.unit.val.app (op V) (unitSectionsEquiv V r)) =
        unitSectionsEquiv (f ⁻¹ᵁ V) (f.app V r))
    (hmul : ∀ (V : T.Opens) (m n : ℕ) (a : Γ(A.piece m, V)) (b : Γ(A.piece n, V)),
      lineProjImage f A L ψ V (m + n) (A.graded.mul m n V a b) =
        (L.tensorPowAddIso m n).inv.app (f ⁻¹ᵁ V)
          (tmulSection (lineProjImage f A L ψ V m a) (lineProjImage f A L ψ V n b)))
    (G : W.Opens) (q : G.toScheme ⟶ A.affineData.relProj)
    (hq : LineProjSpecifiedMap f A L ψ G q)
    (V : T.affineOpens) (B : W.affineOpens) (hB : B.1 ≤ f ⁻¹ᵁ V.1)
    (e : Γ(L, B.1)) (he : IsFreeGenerator e)
    (d : ℕ) (hd : 0 < d) (a : Γ(A.piece d, V.1)) (αa : Γ(W, B.1))
    (ha : (L.tensorPow d).presheaf.map (homOfLE hB).op
      (lineProjImage f A L ψ V.1 d a) = αa • lineProjFramePower L B.1 e d) :
    ∃ (j : (W.basicOpen αa).toScheme ⟶ G.toScheme)
      (r : (W.basicOpen αa).toScheme ⟶ Spec (.of
        (HomogeneousLocalization.Away (A.grade V) (lineProjElement A V d a).val))),
      j ≫ G.ι = (W.basicOpen αa).ι ∧
      r ≫ Proj.awayι (A.grade V) (lineProjElement A V d a).val
        (lineProjElement A V d a).property hd ≫ A.affineData.relProjι V = j ≫ q ∧
      ∀ (m : ℕ) (b : Γ(A.piece (m • d), V.1)) (αb : Γ(W, B.1)),
        (L.tensorPow (m • d)).presheaf.map (homOfLE hB).op
          (lineProjImage f A L ψ V.1 (m • d) b) =
            αb • lineProjFramePower L B.1 e (m • d) →
        lineProjScalar (W.basicOpen αa) r
          (HomogeneousLocalization.Away.mk (A.grade V) (lineProjElement A V d a).property
            m (lineProjElement A V (m • d) b).val
            (lineProjElement A V (m • d) b).property) *
          (W.presheaf.map (homOfLE (W.basicOpen_le αa)).op αa) ^ m =
            W.presheaf.map (homOfLE (W.basicOpen_le αa)).op αb := by
  obtain ⟨charts, _, _, huniq, _, htriv, _⟩ :=
    exists_lineProj_affine_chart_atlas f A L ψ hunit hmul
  obtain ⟨j₀, r₀, hj₀, hr₀, hq₀⟩ := hq V d hd a
  have hr : r₀ = charts V d hd a :=
    by simpa only [Scheme.homOfLE_rfl, Category.id_comp] using
      (huniq V d hd a (lineProjGeneratorOpen f A L ψ V d a) le_rfl r₀).mp hr₀
  obtain ⟨hopen, hfrac⟩ := htriv V d hd a B hB e he αa ha
  have hle : W.basicOpen αa ≤ lineProjGeneratorOpen f A L ψ V d a := by
    rw [← hopen]
    exact inf_le_left
  let i := W.homOfLE hle
  refine ⟨i ≫ j₀, i ≫ r₀, ?_, ?_, ?_⟩
  · simp only [i, Category.assoc, hj₀, Scheme.homOfLE_ι]
  · simpa only [lineProjChartToRelative, lineProjChartToLocal, Category.assoc] using
      congrArg (fun z ↦ i ≫ z) hq₀.symm
  · intro m b αb hb
    have hf := hfrac m b αb hb
    have hh : ∀ (C : W.Opens), C = lineProjGeneratorOpen f A L ψ V d a ⊓ B.1 →
        ∀ (hC : C ≤ lineProjGeneratorOpen f A L ψ V d a)
        (hCB : C ≤ B.1),
        W.presheaf.map (homOfLE hC).op
            (lineProjScalar (lineProjGeneratorOpen f A L ψ V d a) (charts V d hd a)
              (HomogeneousLocalization.Away.mk (A.grade V)
                (lineProjElement A V d a).property m
                (lineProjElement A V (m • d) b).val
                (lineProjElement A V (m • d) b).property)) *
          (W.presheaf.map (homOfLE hCB).op αa) ^ m =
            W.presheaf.map (homOfLE hCB).op αb := by
      intro C hC hCG hCB
      subst C
      exact hf
    rw [lineProjScalar_homOfLE, hr]
    exact hh _ hopen.symm hle (W.basicOpen_le αa)

private theorem restriction_generator_basic {X : Scheme.{u}} (F : X.Opens)
    (N : X.Modules) (s : Γ(N, F)) (B : X.Opens) (hB : B ≤ F)
    (e : Γ(N, B)) (he : IsFreeGenerator e) (α : Γ(X, B))
    (ha : N.presheaf.map (homOfLE hB).op s = α • e) :
    F ⊓ F.ι ''ᵁ generatingLocus
      ((N.restrictAppIso F.ι ⊤).inv
        (N.presheaf.map (eqToHom F.ι_image_top).op s)) ⊓ B = X.basicOpen α := by
  let σ : Γ(N.restrict F.ι, ⊤) := (N.restrictAppIso F.ι ⊤).inv
    (N.presheaf.map (eqToHom F.ι_image_top).op s)
  let C := F.ι ⁻¹ᵁ B
  have hCB : F.ι ''ᵁ C = B := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hB
  let eC : Γ(N.restrict F.ι, C) := (N.restrictAppIso F.ι C).inv
    (N.presheaf.map (eqToHom hCB).op e)
  let αC : Γ(F.toScheme, C) := (F.ι.appIso C).hom
    (X.presheaf.map (eqToHom hCB).op α)
  have heC : IsFreeGenerator eC := by
    apply (isFreeGenerator_restrict_iff F.ι N _).mpr
    exact he.map (le_of_eq hCB)
  have hσ : (N.restrict F.ι).presheaf.map (homOfLE le_top).op σ = αC • eC := by
    have hr : N.presheaf.map
        (homOfLE (F.ι.image_mono (show C ≤ ⊤ from le_top))).op
        (N.presheaf.map (eqToHom F.ι_image_top).op s) =
        N.presheaf.map (eqToHom hCB).op (N.presheaf.map (homOfLE hB).op s) := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    change (N.restrict F.ι).presheaf.map (homOfLE le_top).op
      ((N.restrictAppIso F.ι ⊤).inv _) = _
    rw [← ConcreteCategory.comp_apply, restrictAppIso_inv_map,
      ConcreteCategory.comp_apply, hr, ha, map_smul]
    exact congrArg (fun z ↦ z (N.presheaf.map (eqToHom hCB).op e))
      (smul_restrictAppIso_inv F.ι N C (X.presheaf.map (eqToHom hCB).op α))
  have hbasic : F.ι ''ᵁ F.toScheme.basicOpen αC = X.basicOpen α := by
    rw [Scheme.image_basicOpen, Iso.hom_inv_id_apply, Scheme.basicOpen_res_eq]
  ext x
  constructor
  · rintro ⟨⟨hxF, hxgen⟩, hxB⟩
    obtain ⟨y, hy, hxy⟩ := hxgen
    have hyC : y ∈ C := by
      change F.ι y ∈ B
      change F.ι y = x at hxy
      rw [hxy]
      exact hxB
    have hyα := (generatesAt_iff_mem_basicOpen heC hσ hyC).mp hy
    exact hbasic ▸ (show x ∈ F.ι ''ᵁ F.toScheme.basicOpen αC from ⟨y, hyα, hxy⟩)
  · intro hx
    obtain ⟨y, hy, hxy⟩ := (show x ∈ F.ι ''ᵁ F.toScheme.basicOpen αC from hbasic.symm ▸ hx)
    have hyC : y ∈ C := F.toScheme.basicOpen_le αC hy
    have hygen := (generatesAt_iff_mem_basicOpen heC hσ hyC).mpr hy
    exact ⟨⟨hB (X.basicOpen_le α hx), y, hygen, hxy⟩, X.basicOpen_le α hx⟩

private theorem lineProj_generator_basic {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (V : T.affineOpens) (d : ℕ) (a : Γ(A.piece d, V.1))
    (B : W.affineOpens) (hB : B.1 ≤ f ⁻¹ᵁ V.1)
    (e : Γ(L, B.1)) (he : IsFreeGenerator e) (α : Γ(W, B.1))
    (ha : (L.tensorPow d).presheaf.map (homOfLE hB).op
      (lineProjImage f A L ψ V.1 d a) = α • lineProjFramePower L B.1 e d) :
    lineProjGeneratorOpen f A L ψ V d a ⊓ B.1 = W.basicOpen α := by
  exact restriction_generator_basic (f ⁻¹ᵁ V.1) (L.tensorPow d)
    (lineProjImage f A L ψ V.1 d a) B.1 hB
    (lineProjFramePower L B.1 e d) (frame_power_free L B.1 e he d) α ha

private theorem frame_power_cast {X : Scheme.{u}} (L : X.Modules) (U : X.Opens)
    (e : Γ(L, U)) {i j : ℕ} (hij : i = j) :
    (eqToHom (congrArg L.tensorPow hij)).app U (lineProjFramePower L U e i) =
      lineProjFramePower L U e j := by
  subst j
  rfl

private theorem frame_power_add {X : Scheme.{u}} (L : X.Modules) (U : X.Opens)
    (e : Γ(L, U)) (m n : ℕ) :
    (L.tensorPowAddIso m n).inv.app U
      (tmulSection (lineProjFramePower L U e m) (lineProjFramePower L U e n)) =
      lineProjFramePower L U e (m + n) := by
  induction m with
  | zero =>
    rw [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv, Hom.comp_app,
      ConcreteCategory.comp_apply]
    exact (congrArg _ ((leftUnitor_hom_app_tmulSection _ _).trans (one_smul _ _))).trans
      (frame_power_cast L U e (Nat.zero_add n).symm)
  | succ m ih =>
    rw [tensorPowAddIso, Iso.trans_inv, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      Hom.comp_app, Hom.comp_app, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      lineProjFramePower]
    have h2 : (Iso.refl L ⊗ᵢ L.tensorPowAddIso m n).inv.app U
        (tmulSection e (tmulSection (lineProjFramePower L U e m)
          (lineProjFramePower L U e n))) =
        tmulSection e (lineProjFramePower L U e (m + n)) := by
      rw [tensorIso_inv, Iso.refl_inv, tensorHom_app_tmulSection, ih, Hom.id_app]
      rfl
    exact (congrArg _ ((congrArg _ (associator_hom_app_tmulSection _ _ _)).trans h2)).trans
      (frame_power_cast L U e (Nat.succ_add m n).symm)

private theorem frame_power_mul {X : Scheme.{u}} (L : X.Modules) (U : X.Opens)
    (e : Γ(L, U)) (d m : ℕ) :
    (L.tensorPowMulIso d m).inv.app U
      (lineProjFramePower (L.tensorPow d) U (lineProjFramePower L U e d) m) =
      lineProjFramePower L U e (d * m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [tensorPowMulIso, Iso.trans_inv, Iso.trans_inv, eqToIso.inv,
      Hom.comp_app, Hom.comp_app, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      lineProjFramePower]
    have h2 : (Iso.refl (L.tensorPow d) ⊗ᵢ L.tensorPowMulIso d m).inv.app U
        (tmulSection (lineProjFramePower L U e d)
          (lineProjFramePower (L.tensorPow d) U (lineProjFramePower L U e d) m)) =
        tmulSection (lineProjFramePower L U e d) (lineProjFramePower L U e (d * m)) := by
      rw [tensorIso_inv, Iso.refl_inv, tensorHom_app_tmulSection, ih, Hom.id_app]
      rfl
    exact (congrArg _ ((congrArg _ h2).trans (frame_power_add L U e d (d * m)))).trans
      (frame_power_cast L U e (by ring))

private theorem frame_power_smul {X : Scheme.{u}} (L : X.Modules) (U : X.Opens)
    (e : Γ(L, U)) (c : Γ(X, U)) (n : ℕ) :
    lineProjFramePower L U (c • e) n = c ^ n • lineProjFramePower L U e n := by
  induction n with
  | zero => simp only [lineProjFramePower, pow_zero, one_smul]
  | succ n ih =>
    simp only [lineProjFramePower, ih, smul_tmulSection, tmulSection_smul,
      smul_smul, pow_succ']
    rw [mul_comm]

private theorem lineProjPower_frame {X : Scheme.{u}} (L : X.Modules) (U : X.Opens)
    (e : Γ(L, U)) (c : Γ(X, U)) (d m : ℕ) :
    lineProjPower L U d (c • lineProjFramePower L U e d) m =
      c ^ m • lineProjFramePower L U e (m • d) := by
  simp only [lineProjPower, frame_power_smul, Hom.app_smul, frame_power_mul]
  exact congrArg (fun z ↦ c ^ m • z) (frame_power_cast L U e (Nat.mul_comm d m))

private theorem lineProj_fraction_coefficient {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (V : T.affineOpens) (d : ℕ) (a : Γ(A.piece d, V.1))
    (C : W.Opens) (hC : C ≤ f ⁻¹ᵁ V.1)
    (r : C.toScheme ⟶ Spec (.of (HomogeneousLocalization.Away (A.grade V)
      (lineProjElement A V d a).val)))
    (hr : LineProjFractionFormula f A L ψ V d a C hC r)
    (B : W.affineOpens) (hB : B.1 ≤ f ⁻¹ᵁ V.1) (hCB : C ≤ B.1)
    (e : Γ(L, B.1)) (he : IsFreeGenerator e) (αa : Γ(W, B.1))
    (ha : (L.tensorPow d).presheaf.map (homOfLE hB).op
      (lineProjImage f A L ψ V.1 d a) = αa • lineProjFramePower L B.1 e d)
    (m : ℕ) (b : Γ(A.piece (m • d), V.1)) (αb : Γ(W, B.1))
    (hb : (L.tensorPow (m • d)).presheaf.map (homOfLE hB).op
      (lineProjImage f A L ψ V.1 (m • d) b) =
        αb • lineProjFramePower L B.1 e (m • d)) :
    lineProjScalar C r (HomogeneousLocalization.Away.mk (A.grade V)
      (lineProjElement A V d a).property m
      (lineProjElement A V (m • d) b).val (lineProjElement A V (m • d) b).property) *
        (W.presheaf.map (homOfLE hCB).op αa) ^ m =
      W.presheaf.map (homOfLE hCB).op αb := by
  have haC := congrArg ((L.tensorPow d).presheaf.map (homOfLE hCB).op) ha
  have hbC := congrArg ((L.tensorPow (m • d)).presheaf.map (homOfLE hCB).op) hb
  rw [section_restrict_restrict, map_smul, frame_power_restrict] at haC hbC
  have hf := hr m b
  rw [haC, lineProjPower_frame, hbC, smul_smul] at hf
  exact (frame_power_free L C (L.presheaf.map (homOfLE hCB).op e) (he.map hCB)
    (m • d)).smul_left_injective hf

private theorem lineProjScalar_specMap {X : Scheme.{u}} (U : X.Opens)
    {R S : CommRingCat.{u}} (q : U.toScheme ⟶ Spec S) (ρ : R ⟶ S) :
    lineProjScalar U (q ≫ Spec.map ρ) = ρ ≫ lineProjScalar U q := by
  simp only [lineProjScalar, Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality]

private theorem lineProjScalar_ext {X : Scheme.{u}} (U : X.Opens) {R : Type u}
    [CommRing R] (p q : U.toScheme ⟶ Spec (.of R))
    (h : lineProjScalar U p = lineProjScalar U q) : p = q := by
  apply AlgebraicGeometry.ext_to_Spec
  apply (cancel_mono U.topIso.hom).mp
  exact h

private theorem lineProjPower_restrict {X : Scheme.{u}} (L : X.Modules)
    {U V : X.Opens} (h : V ≤ U) (d : ℕ) (s : Γ(L.tensorPow d, U)) (m : ℕ) :
    (L.tensorPow (m • d)).presheaf.map (homOfLE h).op (lineProjPower L U d s m) =
      lineProjPower L V d ((L.tensorPow d).presheaf.map (homOfLE h).op s) m := by
  unfold lineProjPower
  erw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map, frame_power_restrict]
  rfl

private theorem lineProjFraction_restrict {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (V : T.affineOpens) (d : ℕ) (a : Γ(A.piece d, V.1))
    (C E : W.Opens) (hC : C ≤ f ⁻¹ᵁ V.1) (hEC : E ≤ C)
    (r : C.toScheme ⟶ Spec (.of (HomogeneousLocalization.Away (A.grade V)
      (lineProjElement A V d a).val)))
    (hr : LineProjFractionFormula f A L ψ V d a C hC r) :
    LineProjFractionFormula f A L ψ V d a E (hEC.trans hC)
      (W.homOfLE hEC ≫ r) := by
  intro m b
  have hh := congrArg ((L.tensorPow (m • d)).presheaf.map (homOfLE hEC).op) (hr m b)
  rw [map_smul, lineProjPower_restrict, section_restrict_restrict,
    section_restrict_restrict] at hh
  rw [lineProjScalar_homOfLE]
  exact hh

private theorem away_comparison {R S : Type u} [CommRing R] [CommRing S]
    {σ τ : Type u} [SetLike σ R] [AddSubgroupClass σ R]
    [SetLike τ S] [AddSubgroupClass τ S]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ)
    [GradedRing 𝒜] [GradedRing ℬ] (δ : 𝒜 →+*ᵍ ℬ)
    (hirr : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map δ)
    (d : ℕ) (hd : 0 < d) (a : R) (ha : a ∈ 𝒜 d)
    (a' : S) (ha' : a' ∈ ℬ d) (haa : a' = δ a)
    (P : Scheme.{u}) (p : Proj 𝒜 ⟶ P) :
    ∃ κ : Spec (.of (HomogeneousLocalization.Away ℬ a')) ⟶
        Spec (.of (HomogeneousLocalization.Away 𝒜 a)),
      κ ≫ Proj.awayι 𝒜 a ha hd ≫ p =
        Proj.awayι ℬ a' ha' hd ≫ Proj.map δ hirr ≫ p ∧
      ∀ {X : Scheme.{u}} (U : X.Opens)
        (r : U.toScheme ⟶ Spec (.of (HomogeneousLocalization.Away ℬ a')))
        (m : ℕ) (b : R) (hb : b ∈ 𝒜 (m • d)),
        lineProjScalar U (r ≫ κ) (HomogeneousLocalization.Away.mk 𝒜 ha m b hb) =
          lineProjScalar U r
            (HomogeneousLocalization.Away.mk ℬ ha' m (δ b) (δ.map_mem hb)) := by
  subst a'
  refine ⟨Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map δ a)), ?_, ?_⟩
  · exact congrArg (fun z ↦ z ≫ p) (Proj.awayι_comp_map δ hirr hd a ha).symm
  · intro X U r m b hb
    rw [lineProjScalar_specMap]
    change lineProjScalar U r (HomogeneousLocalization.Away.map δ a _) = _
    rw [HomogeneousLocalization.Away.map_mk]

private theorem isUnit_restrict_basic {X : Scheme.{u}} (B C : X.Opens)
    (hCB : C ≤ B) (r : Γ(X, B)) (hCr : C ≤ X.basicOpen r) :
    IsUnit (X.presheaf.map (homOfLE hCB).op r) := by
  have hh := (X.toRingedSpace.isUnit_res_basicOpen r).map
    (X.presheaf.map (homOfLE hCr).op).hom
  change IsUnit (X.presheaf.map (homOfLE hCr).op
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op r)) at hh
  rw [← CommRingCat.comp_apply, ← Functor.map_comp] at hh
  exact hh

private theorem fraction_map_unique {X : Scheme.{u}} (U : X.Opens)
    {R : Type u} [CommRing R] {σ : Type*} [SetLike σ R] [AddSubgroupClass σ R]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (d : ℕ) (a : R) (ha : a ∈ 𝒜 d)
    (p q : U.toScheme ⟶ Spec (.of (HomogeneousLocalization.Away 𝒜 a)))
    (α : Γ(X, U)) (hα : IsUnit α)
    (h : ∀ (m : ℕ) (b : R) (hb : b ∈ 𝒜 (m • d)),
      lineProjScalar U p (HomogeneousLocalization.Away.mk 𝒜 ha m b hb) * α ^ m =
        lineProjScalar U q (HomogeneousLocalization.Away.mk 𝒜 ha m b hb) * α ^ m) :
    p = q := by
  apply lineProjScalar_ext U
  ext x
  obtain ⟨m, b, hb, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 ha x
  exact (hα.pow m).mul_right_cancel (h m b hb)

private theorem away_mk_congr {R : Type u} [CommRing R]
    {σ : Type u} [SetLike σ R] [AddSubgroupClass σ R]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (a : R) (ha : a ∈ 𝒜 d)
    (m : ℕ) (b c : R) (hb : b ∈ 𝒜 (m • d)) (hc : c ∈ 𝒜 (m • d))
    (hbc : b = c) : HomogeneousLocalization.Away.mk 𝒜 ha m b hb =
      HomogeneousLocalization.Away.mk 𝒜 ha m c hc := by
  subst c
  rfl

private theorem lineProj_local_naturality {W W' T T' : Scheme.{u}}
    (f : W ⟶ T) (f' : W' ⟶ T') (h : W' ⟶ W) (g : T' ⟶ T)
    (A : RelativeProjAlgebra T) (A' : RelativeProjAlgebra T')
    (L : W.Modules) [L.IsInvertible]
    (β : ∀ n : ℕ, A'.piece n ≅ (tensorPullback g).obj (A.piece n))
    (D : GradedAlgebraData.PullbackData g A.affineData A'.affineData)
    (hD : ∀ (V : T.affineOpens) (V' : T'.affineOpens) (hV : V'.1 ≤ g ⁻¹ᵁ V.1)
      (n : ℕ) (a : Γ(A.piece n, V.1)),
      (lineProjElement A' V' n (lineProjBaseSection g A A' β V V' hV n a 1)).val =
        D.map hV (lineProjElement A V n a).val)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (hunit : ∀ (V : T.Opens) (r : Γ(T, V)),
      lineProjImage f A L ψ V 0 (A.graded.unit.val.app (op V) (unitSectionsEquiv V r)) =
        unitSectionsEquiv (f ⁻¹ᵁ V) (f.app V r))
    (hmul : ∀ (V : T.Opens) (m n : ℕ) (a : Γ(A.piece m, V)) (b : Γ(A.piece n, V)),
      lineProjImage f A L ψ V (m + n) (A.graded.mul m n V a b) =
        (L.tensorPowAddIso m n).inv.app (f ⁻¹ᵁ V)
          (tmulSection (lineProjImage f A L ψ V m a) (lineProjImage f A L ψ V n b)))
    (ψ' : ∀ n : ℕ, (tensorPullback f').obj (A'.piece n) ⟶
      ((tensorPullback h).obj L).tensorPow n)
    (G : W.Opens) (G' : W'.Opens)
    (hc : LineProjPullbackCoefficients f f' h g A A' L β ψ ψ' G')
    (q : G.toScheme ⟶ A.affineData.relProj)
    (q' : G'.toScheme ⟶ A'.affineData.relProj)
    (hq : LineProjSpecifiedMap f A L ψ G q)
    (hq' : LineProjSpecifiedMap f' A' ((tensorPullback h).obj L) ψ' G' q')
    (V : T.affineOpens) (V' : T'.affineOpens) (hV : V'.1 ≤ g ⁻¹ᵁ V.1)
    (B : W.affineOpens) (B' : W'.affineOpens) (hB : B.1 ≤ f ⁻¹ᵁ V.1)
    (hB' : B'.1 ≤ f' ⁻¹ᵁ V'.1) (hBB : B'.1 ≤ h ⁻¹ᵁ B.1)
    (e : Γ(L, B.1)) (he : IsFreeGenerator e)
    (d : ℕ) (hd : 0 < d) (a : Γ(A.piece d, V.1)) (αa : Γ(W, B.1))
    (ha : (L.tensorPow d).presheaf.map (homOfLE hB).op
      (lineProjImage f A L ψ V.1 d a) = αa • lineProjFramePower L B.1 e d) :
    ∃ (j' : (lineProjPulledBasicOpen h B B' αa).toScheme ⟶ G'.toScheme)
      (j : (lineProjPulledBasicOpen h B B' αa).toScheme ⟶ G.toScheme),
      j' ≫ G'.ι = (lineProjPulledBasicOpen h B B' αa).ι ∧
      j ≫ G.ι = (lineProjPulledBasicOpen h B B' αa).ι ≫ h ∧
      j' ≫ q' ≫ D.relProjComparison = j ≫ q := by
  let : GradedRing (A.grade V) := A.gradeRing V
  let : GradedRing (A'.grade V') := A'.gradeRing V'
  let L' := (tensorPullback h).obj L
  let a' := lineProjBaseSection g A A' β V V' hV d a 1
  let e' := lineProjPulledFrame h L B B' hBB e
  let α' := h.appLE B.1 B'.1 hBB αa
  let U := lineProjPulledBasicOpen h B B' αa
  have he' : IsFreeGenerator e' := (hc V V' hV B B' hB hB' hBB e he).1
  have hpure (n : ℕ) (b : Γ(A.piece n, V.1)) (αb : Γ(W, B.1))
      (hb : (L.tensorPow n).presheaf.map (homOfLE hB).op
        (lineProjImage f A L ψ V.1 n b) = αb • lineProjFramePower L B.1 e n) :
      (L'.tensorPow n).presheaf.map (homOfLE hB').op
        (lineProjImage f' A' L' ψ' V'.1 n
          (lineProjBaseSection g A A' β V V' hV n b 1)) =
        h.appLE B.1 B'.1 hBB αb • lineProjFramePower L' B'.1 e' n := by
    simpa only [map_one, mul_one] using
      (hc V V' hV B B' hB hB' hBB e he).2.1 n b αb hb 1
  have ha' := hpure d a αa ha
  have hbasic : W'.basicOpen α' = U := Scheme.basicOpen_appLE h B'.1 B.1 hBB αa
  have hopen : lineProjGeneratorOpen f' A' L' ψ' V' d a' ⊓ B'.1 = U :=
    (lineProj_generator_basic f' A' L' ψ' V' d a' B' hB' e' he' α' ha').trans hbasic
  have hUgen : U ≤ lineProjGeneratorOpen f' A' L' ψ' V' d a' := by
    rw [← hopen]
    exact inf_le_left
  obtain ⟨j₀, r₀, hj₀, hr₀, hf₀⟩ := lineProj_unprimed_chart_on_basic
    f A L ψ hunit hmul G q hq V B hB e he d hd a αa ha
  obtain ⟨j₁, r₁, hj₁, hf₁, hq₁⟩ := hq' V' d hd a'
  let i := W'.homOfLE hUgen
  let r' := i ≫ r₁
  let l := h.resLE (W.basicOpen αa) U (show U ≤ h ⁻¹ᵁ W.basicOpen αa from inf_le_right)
  obtain ⟨κ, hκ, hfκ⟩ := away_comparison (A.grade V) (A'.grade V') (D.map hV)
    (D.irrelevant_le_map hV) d hd (lineProjElement A V d a).val
    (lineProjElement A V d a).property (lineProjElement A' V' d a').val
    (lineProjElement A' V' d a').property (hD V V' hV d a)
    A.affineData.relProj (A.affineData.relProjι V)
  have hfrac' : LineProjFractionFormula f' A' L' ψ' V' d a' U
      (hUgen.trans inf_le_left) r' :=
    lineProjFraction_restrict f' A' L' ψ' V' d a'
      (lineProjGeneratorOpen f' A' L' ψ' V' d a') U inf_le_left hUgen r₁ hf₁
  have hr : r' ≫ κ = l ≫ r₀ := by
    apply fraction_map_unique U (A.grade V) d (lineProjElement A V d a).val
      (lineProjElement A V d a).property _ _
      (W'.presheaf.map (homOfLE (inf_le_left : U ≤ B'.1)).op α')
      (isUnit_restrict_basic B'.1 U inf_le_left α' (by rw [hbasic]))
    intro m b hb
    obtain ⟨b₀, hb₀⟩ := hb
    subst b
    obtain ⟨αb, hαb⟩ := (frame_power_free L B.1 e he (m • d)).exists_smul_eq
      ((L.tensorPow (m • d)).presheaf.map (homOfLE hB).op
        (lineProjImage f A L ψ V.1 (m • d) b₀))
    have hb' := hpure (m • d) b₀ αb hαb.symm
    have hn := lineProj_fraction_coefficient f' A' L' ψ' V' d a' U
      (hUgen.trans inf_le_left) r' hfrac' B' hB' inf_le_left e' he' α' ha'
      m (lineProjBaseSection g A A' β V V' hV (m • d) b₀ 1)
      (h.appLE B.1 B'.1 hBB αb) hb'
    have hu := congrArg (fun z ↦ h.appLE (W.basicOpen αa) U inf_le_right z)
      (hf₀ m b₀ αb hαb.symm)
    rw [map_mul, map_pow] at hu
    rw [lineProjScalar_resLE]
    rw [appLE_restrict_square h B.1 (W.basicOpen αa) (W.basicOpen_le αa)
      B'.1 U inf_le_left hBB inf_le_right αa,
      appLE_restrict_square h B.1 (W.basicOpen αa) (W.basicOpen_le αa)
      B'.1 U inf_le_left hBB inf_le_right αb] at hu
    rw [hfκ]
    have hm := hD V V' hV (m • d) b₀
    have hmk := away_mk_congr (A'.grade V') d
      (lineProjElement A' V' d a').val (lineProjElement A' V' d a').property
      m _ _ (lineProjElement A' V' (m • d)
        (lineProjBaseSection g A A' β V V' hV (m • d) b₀ 1)).property
      ((D.map hV).map_mem (lineProjElement A V (m • d) b₀).property) hm
    let αU : Γ(W', U) := W'.presheaf.map (homOfLE (inf_le_left : U ≤ B'.1)).op α'
    have hsc := congrArg (fun z ↦ lineProjScalar U r' z * αU ^ m) hmk
    convert hsc.symm.trans (hn.trans hu.symm) using 1 <;> rfl
  refine ⟨i ≫ j₁, l ≫ j₀, ?_, ?_, ?_⟩
  · rw [Category.assoc, hj₁]
    exact Scheme.homOfLE_ι W' hUgen
  · rw [Category.assoc, hj₀]
    exact Scheme.Hom.resLE_comp_ι h inf_le_right
  · have hp := congrArg (fun z ↦ i ≫ z ≫ D.relProjComparison) hq₁
    have hcmp := D.relProjι_relProjComparison hV
    calc
      (i ≫ j₁) ≫ q' ≫ D.relProjComparison =
          r' ≫ Proj.awayι (A'.grade V') (lineProjElement A' V' d a').val
            (lineProjElement A' V' d a').property hd ≫
            A'.affineData.relProjι V' ≫ D.relProjComparison := by
        simpa only [lineProjChartToRelative, lineProjChartToLocal, r',
          Category.assoc] using hp
      _ = r' ≫ Proj.awayι (A'.grade V') (lineProjElement A' V' d a').val
            (lineProjElement A' V' d a').property hd ≫
            D.localComparison hV := by
        rw [hcmp]
      _ = r' ≫ κ ≫ Proj.awayι (A.grade V) (lineProjElement A V d a).val
            (lineProjElement A V d a).property hd ≫ A.affineData.relProjι V := by
        simpa only [GradedAlgebraData.PullbackData.localComparison, Category.assoc]
          using congrArg (fun z ↦ r' ≫ z) hκ.symm
      _ = (l ≫ r₀) ≫ Proj.awayι (A.grade V) (lineProjElement A V d a).val
            (lineProjElement A V d a).property hd ≫ A.affineData.relProjι V := by
        rw [← Category.assoc r' κ, hr]
      _ = (l ≫ j₀) ≫ q := by
        simpa only [Category.assoc] using congrArg (fun z ↦ l ≫ z) hr₀

private theorem lineProj_common_of_equality {W W' T : Scheme.{u}}
    (f : W ⟶ T) (h : W' ⟶ W) (A : RelativeProjAlgebra T)
    (L : W.Modules) [L.IsInvertible]
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (hunit : ∀ (V : T.Opens) (r : Γ(T, V)),
      lineProjImage f A L ψ V 0 (A.graded.unit.val.app (op V) (unitSectionsEquiv V r)) =
        unitSectionsEquiv (f ⁻¹ᵁ V) (f.app V r))
    (hmul : ∀ (V : T.Opens) (m n : ℕ) (a : Γ(A.piece m, V)) (b : Γ(A.piece n, V)),
      lineProjImage f A L ψ V (m + n) (A.graded.mul m n V a b) =
        (L.tensorPowAddIso m n).inv.app (f ⁻¹ᵁ V)
          (tmulSection (lineProjImage f A L ψ V m a) (lineProjImage f A L ψ V n b)))
    (G : W.Opens) (G' : W'.Opens) (P' : Scheme.{u})
    (q : G.toScheme ⟶ A.affineData.relProj) (q' : G'.toScheme ⟶ P')
    (c : P' ⟶ A.affineData.relProj) (hq : LineProjSpecifiedMap f A L ψ G q)
    (k : G'.toScheme ⟶ G.toScheme)
    (hk : k ≫ G.ι = G'.ι ≫ h) (heq : q' ≫ c = k ≫ q)
    (hG' : G' = h ⁻¹ᵁ G) :
    LineProjCommonFractions f h A L ψ G G' P' q q' c := by
  intro V B B' hB hBB e he d hd a αa ha
  obtain ⟨j₀, r₀, hj₀, hr₀, hf₀⟩ := lineProj_unprimed_chart_on_basic
    f A L ψ hunit hmul G q hq V B hB e he d hd a αa ha
  let D := W.basicOpen αa
  let U := lineProjPulledBasicOpen h B B' αa
  have hDG : D ≤ G := by
    intro x hx
    have hx' := congrArg (fun z ↦ z ⟨x, hx⟩) hj₀
    have hxG : (j₀ ≫ G.ι) ⟨x, hx⟩ ∈ G := (j₀ ⟨x, hx⟩).property
    rw [hx'] at hxG
    exact hxG
  have hUG : U ≤ h ⁻¹ᵁ G := fun x hx ↦ hDG hx.2
  have hUG' : U ≤ G' := hG'.symm ▸ hUG
  let j' := W'.homOfLE hUG'
  let j := h.resLE G U hUG
  let l := h.resLE D U (show U ≤ h ⁻¹ᵁ D from inf_le_right)
  have hj : j ≫ G.ι = U.ι ≫ h := Scheme.Hom.resLE_comp_ι h hUG
  have hlj : l ≫ j₀ = j := by
    apply (cancel_mono G.ι).mp
    rw [Category.assoc, hj₀]
    exact (Scheme.Hom.resLE_comp_ι h (show U ≤ h ⁻¹ᵁ D from inf_le_right)).trans hj.symm
  have hj'k : j' ≫ k = j := by
    apply (cancel_mono G.ι).mp
    rw [Category.assoc, hk, ← Category.assoc, Scheme.homOfLE_ι]
    exact hj.symm
  refine ⟨j', j, l ≫ r₀, Scheme.homOfLE_ι W' hUG', hj, ?_, ?_, ?_⟩
  · have hh := congrArg (fun z ↦ l ≫ z) hr₀
    have hjj : l ≫ j₀ = j' ≫ k := hlj.trans hj'k.symm
    simpa only [Category.assoc, heq, ← Category.assoc l j₀ q, hjj, Category.assoc] using hh
  · have hh := congrArg (fun z ↦ l ≫ z) hr₀
    simpa only [Category.assoc, ← hlj] using hh
  · intro m b αb hb
    have hf := congrArg (fun z ↦ h.appLE D U (show U ≤ h ⁻¹ᵁ D from inf_le_right) z)
      (hf₀ m b αb hb)
    rw [map_mul, map_pow] at hf
    rw [lineProjScalar_resLE]
    change h.appLE D U _ (lineProjScalar D r₀ _) * _ = _
    rw [appLE_restrict_square h B.1 D (W.basicOpen_le αa) B'.1 U
      inf_le_left hBB inf_le_right αa,
      appLE_restrict_square h B.1 D (W.basicOpen_le αa) B'.1 U
        inf_le_left hBB inf_le_right αb] at hf
    exact hf

private theorem open_cover_hom_ext {X Y : Scheme.{u}} {G : X.Opens}
    {ι : Type*} (U : ι → X.Opens) (hU : ∀ i, U i ≤ G)
    (hcov : G = ⨆ i, U i) (p q : G.toScheme ⟶ Y)
    (heq : ∀ i, X.homOfLE (hU i) ≫ p = X.homOfLE (hU i) ≫ q) : p = q := by
  let V : ι → G.toScheme.Opens := fun i ↦ G.ι ⁻¹ᵁ U i
  have hV : TopologicalSpace.IsOpenCover V := by
    apply eq_top_iff.mpr
    intro x hx
    apply TopologicalSpace.Opens.mem_iSup.mpr
    have hx : G.ι x ∈ ⨆ i, U i := hcov ▸ x.property
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨i, hi⟩
  apply (G.toScheme.openCoverOfIsOpenCover V hV).hom_ext
  intro i
  let e : (U i).toScheme ≅ (V i).toScheme :=
    (X.homOfLE (hU i)).isoOpensRange ≪≫
      G.toScheme.isoOfEq (X.opensRange_homOfLE (hU i))
  have he : e.hom ≫ (V i).ι = X.homOfLE (hU i) := by
    simp only [e, Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom,
      Scheme.homOfLE_ι, Scheme.Hom.isoOpensRange_hom_ι]
  change (V i).ι ≫ p = (V i).ι ≫ q
  apply (cancel_epi e.hom).mp
  simpa only [← Category.assoc, he] using heq i

private theorem lineProj_global_naturality {W W' T T' : Scheme.{u}}
    (f : W ⟶ T) (f' : W' ⟶ T') (h : W' ⟶ W) (g : T' ⟶ T)
    (hsq : h ≫ f = f' ≫ g) (A : RelativeProjAlgebra T) (A' : RelativeProjAlgebra T')
    (L : W.Modules) [L.IsInvertible]
    (β : ∀ n : ℕ, A'.piece n ≅ (tensorPullback g).obj (A.piece n))
    (D : GradedAlgebraData.PullbackData g A.affineData A'.affineData)
    (hD : ∀ (V : T.affineOpens) (V' : T'.affineOpens) (hV : V'.1 ≤ g ⁻¹ᵁ V.1)
      (n : ℕ) (a : Γ(A.piece n, V.1)),
      (lineProjElement A' V' n (lineProjBaseSection g A A' β V V' hV n a 1)).val =
        D.map hV (lineProjElement A V n a).val)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (hunit : ∀ (V : T.Opens) (r : Γ(T, V)),
      lineProjImage f A L ψ V 0 (A.graded.unit.val.app (op V) (unitSectionsEquiv V r)) =
        unitSectionsEquiv (f ⁻¹ᵁ V) (f.app V r))
    (hmul : ∀ (V : T.Opens) (m n : ℕ) (a : Γ(A.piece m, V)) (b : Γ(A.piece n, V)),
      lineProjImage f A L ψ V (m + n) (A.graded.mul m n V a b) =
        (L.tensorPowAddIso m n).inv.app (f ⁻¹ᵁ V)
          (tmulSection (lineProjImage f A L ψ V m a) (lineProjImage f A L ψ V n b)))
    (ψ' : ∀ n : ℕ, (tensorPullback f').obj (A'.piece n) ⟶
      ((tensorPullback h).obj L).tensorPow n)
    (G : W.Opens) (G' : W'.Opens)
    (hc : LineProjPullbackCoefficients f f' h g A A' L β ψ ψ' G')
    (hpre : G' = h ⁻¹ᵁ G)
    (q : G.toScheme ⟶ A.affineData.relProj)
    (q' : G'.toScheme ⟶ A'.affineData.relProj)
    (hq : LineProjSpecifiedMap f A L ψ G q)
    (hq' : LineProjSpecifiedMap f' A' ((tensorPullback h).obj L) ψ' G' q') :
    ∃ k : G'.toScheme ⟶ G.toScheme,
      k ≫ G.ι = G'.ι ≫ h ∧ q' ≫ D.relProjComparison = k ≫ q := by
  let k := h.resLE G G' hpre.le
  have hk : k ≫ G.ι = G'.ι ≫ h := Scheme.Hom.resLE_comp_ι h hpre.le
  refine ⟨k, hk, ?_⟩
  have : SheafOfModules.IsInvertible L := IsInvertible.sheafOfModules_isInvertible L
  have hlocal (x : G'.toScheme) : ∃ (U : W'.Opens) (hUG : U ≤ G'),
      x.val ∈ U ∧ W'.homOfLE hUG ≫ q' ≫ D.relProjComparison =
        W'.homOfLE hUG ≫ k ≫ q := by
    obtain ⟨V, hV, hxV, _⟩ :=
      exists_isAffineOpen_mem_and_subset (x := f (h x.val)) (U := ⊤) (by trivial)
    let V₀ : T.affineOpens := ⟨V, hV⟩
    have hxg : f' x.val ∈ g ⁻¹ᵁ V := by
      change (f' ≫ g) x.val ∈ V
      rw [← hsq]
      exact hxV
    obtain ⟨V', hV', hxV', hVg⟩ := exists_isAffineOpen_mem_and_subset hxg
    let V₁ : T'.affineOpens := ⟨V', hV'⟩
    change V' ≤ g ⁻¹ᵁ V at hVg
    obtain ⟨B, hxB, hBV, e, he⟩ :=
      exists_isFreeGenerator L (x := h x.val) (W := f ⁻¹ᵁ V) hxV
    obtain ⟨B', hB', hxB', hBB'⟩ :=
      exists_isAffineOpen_mem_and_subset (x := x.val)
        (U := (f' ⁻¹ᵁ V') ⊓ (h ⁻¹ᵁ B.1)) ⟨hxV', hxB⟩
    let B₁ : W'.affineOpens := ⟨B', hB'⟩
    have hBV' : B' ≤ f' ⁻¹ᵁ V' := fun y hy ↦ (hBB' hy).1
    have hBB : B' ≤ h ⁻¹ᵁ B.1 := fun y hy ↦ (hBB' hy).2
    have hx : x.val ∈ G' ⊓ B' := ⟨x.property, hxB'⟩
    rw [(hc V₀ V₁ hVg B B₁ hBV hBV' hBB e he).2.2] at hx
    obtain ⟨d, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨hd, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨a, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨α, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨ha, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨j', j, hj', hj, heq⟩ := lineProj_local_naturality f f' h g A A' L β D hD
      ψ hunit hmul ψ' G G' hc q q' hq hq' V₀ V₁ hVg B B₁ hBV hBV' hBB e he
      d hd a α ha
    let U := lineProjPulledBasicOpen h B B₁ α
    have hUG : U ≤ G' := by
      intro y hy
      have hh := congrArg (fun z ↦ z ⟨y, hy⟩) hj'
      have ht : (j' ≫ G'.ι) ⟨y, hy⟩ ∈ G' := (j' ⟨y, hy⟩).property
      rw [hh] at ht
      exact ht
    have hji : W'.homOfLE hUG = j' := by
      apply (cancel_mono G'.ι).mp
      exact (Scheme.homOfLE_ι W' hUG).trans hj'.symm
    have hjk : W'.homOfLE hUG ≫ k = j := by
      apply (cancel_mono G.ι).mp
      rw [Category.assoc, hk, ← Category.assoc, Scheme.homOfLE_ι]
      exact hj.symm
    refine ⟨U, hUG, hx, ?_⟩
    rw [hji, heq, ← hji, ← Category.assoc, hjk]
  choose U hUG hxU hU using hlocal
  apply open_cover_hom_ext U hUG ?_ (q' ≫ D.relProjComparison) (k ≫ q)
    (fun x ↦ by simpa only [Category.assoc] using hU x)
  ext x
  constructor
  · intro hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  · intro hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact hUG i hi

/-- Arbitrary pullback preserves the positive-degree generation open, the frame
coefficient formula and its basic-open cover, and every specified homogeneous-fraction
map to relative Proj. No cartesian, flatness or finite-generation hypothesis is used.

Source: Stacks Project, Divisors on Spaces, Tag 0D2Z, opening assertion and (3);
Constructions, Tags 01O9 and 01NK (blueprint: lem-trf-line-proj-chart-pullback).

Proof:
1. The affine-chart atlas (lem-trf-line-proj-affine-chart-atlas) identifies the union
of positive-degree stalkwise surjectivity loci with the generator opens D(alpha_a).
2. Degreewise affine tensor pullback (lem-weil-pbc-module-pullback-affine-sections)
identifies primed sections with sums of a tensor c. Pull back a frame and its inverse;
the normalized power comparison (def-sc-tensor-pullback-power-comparison) sends
1 tensor e^d to (1 tensor e)^d. Thus the coefficient is h-sharp(alpha_a) f'-sharp(c).
The pullback algebra is quasi-coherent (lem-weil-pbc-module-pullback-quasi-coherent).
3. If a sum of multiples of h-sharp(alpha_a) is a unit in a local ring, at least one
h-sharp(alpha_a) is outside the maximal ideal. Conversely that term alone generates.
This proves the cover and G' = h inverse G, even for nonflat morphisms.
4. The coefficientwise relative-Proj comparison
(lemma-nagata-relative-proj-base-change-arbitrary), on affine charts
(lem-nagata-affine-proj-scalar-extension), sends b/a^m to
(b tensor 1)/(a tensor 1)^m. The specified primed map then sends it to
h-sharp(alpha_b)/h-sharp(alpha_a)^m. The unprimed map followed by h gives the same
value, since a ring map preserves the inverse of a unit. No denominator regularity is used.
5. All elements of degree-zero homogeneous localization have these representatives
(def-nagata-homogeneous-localization-degree-zero), so the ring maps agree. The affine
spectrum correspondence (def-weil-affine-spectrum) and scheme morphism gluing
(lem-weil-pbc-scheme-morphism-gluing) give equality on G'. Refine arbitrary intersections
by affine opens; do not assume affine intersections. The same computation gives the
asserted common fraction formula, including m=0, nilpotent generators and empty opens. -/
theorem lineProj_chart_pullback {W W' T T' : Scheme.{u}}
    (f : W ⟶ T) (f' : W' ⟶ T') (h : W' ⟶ W) (g : T' ⟶ T)
    (hsq : h ≫ f = f' ≫ g) (A : RelativeProjAlgebra T) (A' : RelativeProjAlgebra T')
    (L : W.Modules) [L.IsInvertible]
    (β : ∀ n : ℕ, A'.piece n ≅ (tensorPullback g).obj (A.piece n))
    (D : GradedAlgebraData.PullbackData g A.affineData A'.affineData)
    (hD : ∀ (V : T.affineOpens) (V' : T'.affineOpens) (hV : V'.1 ≤ g ⁻¹ᵁ V.1)
      (n : ℕ) (a : Γ(A.piece n, V.1)),
      (lineProjElement A' V' n (lineProjBaseSection g A A' β V V' hV n a 1)).val =
        D.map hV (lineProjElement A V n a).val)
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (hunit : ∀ (V : T.Opens) (r : Γ(T, V)),
      lineProjImage f A L ψ V 0 (A.graded.unit.val.app (op V) (unitSectionsEquiv V r)) =
        unitSectionsEquiv (f ⁻¹ᵁ V) (f.app V r))
    (hmul : ∀ (V : T.Opens) (m n : ℕ) (a : Γ(A.piece m, V)) (b : Γ(A.piece n, V)),
      lineProjImage f A L ψ V (m + n) (A.graded.mul m n V a b) =
        (L.tensorPowAddIso m n).inv.app (f ⁻¹ᵁ V)
          (tmulSection (lineProjImage f A L ψ V m a) (lineProjImage f A L ψ V n b)))
    (ψ' : ∀ n : ℕ, (tensorPullback f').obj (A'.piece n) ⟶
      ((tensorPullback h).obj L).tensorPow n)
    (hψ' : ψ' = lineProjPullbackMap hsq A A' L β ψ)
    (G : W.Opens) (G' : W'.Opens)
    (hG : (G : Set W) = {x | ∃ d : ℕ, 0 < d ∧ Function.Surjective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (ψ d).mapPresheaf)})
    (hG' : (G' : Set W') = {x | ∃ d : ℕ, 0 < d ∧ Function.Surjective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (ψ' d).mapPresheaf)}) :
    G' = h ⁻¹ᵁ G ∧
    LineProjPullbackCoefficients f f' h g A A' L β ψ ψ' G' ∧
    ∀ (q : G.toScheme ⟶ A.affineData.relProj)
      (q' : G'.toScheme ⟶ A'.affineData.relProj),
      LineProjSpecifiedMap f A L ψ G q →
      LineProjSpecifiedMap f' A' ((tensorPullback h).obj L) ψ' G' q' →
      (∃ k : G'.toScheme ⟶ G.toScheme,
        k ≫ G.ι = G'.ι ≫ h ∧ q' ≫ D.relProjComparison = k ≫ q) ∧
      LineProjCommonFractions f h A L ψ G G' A'.affineData.relProj q q'
        D.relProjComparison := by
  have hpure : ∀ (V : T.affineOpens) (V' : T'.affineOpens) (hV : V'.1 ≤ g ⁻¹ᵁ V.1)
      (B : W.affineOpens) (B' : W'.affineOpens) (hB : B.1 ≤ f ⁻¹ᵁ V.1)
      (hB' : B'.1 ≤ f' ⁻¹ᵁ V'.1) (hBB : B'.1 ≤ h ⁻¹ᵁ B.1)
      (e : Γ(L, B.1)) (n : ℕ) (a : Γ(A.piece n, V.1)) (α : Γ(W, B.1)),
      (L.tensorPow n).presheaf.map (homOfLE hB).op
        (lineProjImage f A L ψ V.1 n a) = α • lineProjFramePower L B.1 e n →
      (((tensorPullback h).obj L).tensorPow n).presheaf.map (homOfLE hB').op
        (lineProjImage f' A' ((tensorPullback h).obj L) ψ' V'.1 n
          (lineProjBaseSection g A A' β V V' hV n a 1)) =
        (h.appLE B.1 B'.1 hBB α) • lineProjFramePower ((tensorPullback h).obj L) B'.1
          (lineProjPulledFrame h L B B' hBB e) n := by
    intro V V' hV B B' hB hB' hBB e n a α ha
    rw [hψ']
    simpa only [map_one, mul_one] using
      lineProj_base_coefficient f f' h g hsq A A' L β ψ V V' hV B B' hB hB' hBB
        e n a α ha 1
  have hc : LineProjPullbackCoefficients f f' h g A A' L β ψ ψ' G' := by
    intro V V' hV B B' hB hB' hBB e he
    refine ⟨pulled_frame_isFreeGenerator h L B B' hBB e he, ?_, ?_⟩
    · intro n a α ha c
      rw [hψ']
      exact lineProj_base_coefficient f f' h g hsq A A' L β ψ V V' hV B B' hB hB' hBB
        e n a α ha c
    · exact lineProj_pullback_cover f f' h g hsq A A' L β ψ ψ' hpure G' hG'
        V V' hV B B' hB hB' hBB e he
  have hpre := lineProj_generation_preimage f f' h g hsq A A' L β ψ ψ' G G' hG hc
  refine ⟨hpre, hc, ?_⟩
  intro q q' hq hq'
  obtain ⟨k, hk, hcomm⟩ := lineProj_global_naturality f f' h g hsq A A' L β D hD
    ψ hunit hmul ψ' G G' hc hpre q q' hq hq'
  refine ⟨⟨k, hk, hcomm⟩, ?_⟩
  exact lineProj_common_of_equality f h A L ψ hunit hmul G G' A'.affineData.relProj
    q q' D.relProjComparison hq k hk hcomm hpre


end AlgebraicGeometry.Scheme.Modules
