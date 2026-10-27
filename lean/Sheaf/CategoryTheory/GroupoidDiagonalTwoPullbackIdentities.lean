module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.ModuliChartNormalization
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack

/-! # Diagonals and 2-fibre products of fibred groupoids

Source: Stacks Project, categories.tex, Tags 04YR and 04Z1
(blueprint: lem-sfb-groupoid-diagonal-two-pullback-identities).

The comparison maps use the existing comma model and retain all automorphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃ v₄ w₄

open AlgebraicGeometry

namespace CategoryTheory

/-- The structural isomorphism in the existing 2-fibre product, over base identities.
Source: Stacks 0040 (blueprint: lem-sfb-groupoid-diagonal-two-pullback-identities). -/
def moduliTwoFiberStructuralIso {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {H : BasedCategory.{v₃, w₃} (Over S)} (f : BasedFunctor F H) (g : BasedFunctor G H) :
    (moduliTwoFiberFst f g).comp f ≅ (moduliTwoFiberSnd f g).comp g :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents (fun x ↦ @asIso _ _ _ _ x.obj.hom x.property.1)
      (fun a ↦ a.hom.w))
    (fun x ↦ x.property.2)

/-- Left whiskering of an over-base isomorphism, allowing independent category sizes.
Source: Stacks 003T (blueprint: lem-sfb-groupoid-diagonal-two-pullback-identities). -/
def moduliWhiskerLeftIso {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {H : BasedCategory.{v₃, w₃} (Over S)} (f : BasedFunctor F G)
    {g h : BasedFunctor G H} (e : g ≅ h) : f.comp g ≅ f.comp h :=
  BasedNatIso.mkNatIso
    (Functor.isoWhiskerLeft f.toFunctor ((BasedNatTrans.forgetful G H).mapIso e))
    (fun x ↦ by
      change H.p.IsHomLift (𝟙 (F.p.obj x)) (e.hom.toNatTrans.app (f.obj x))
      rw [← f.w_obj x]
      exact e.hom.isHomLift' (f.obj x))

/-- Right whiskering of an over-base isomorphism, allowing independent category sizes.
Source: Stacks 003T (blueprint: lem-sfb-groupoid-diagonal-two-pullback-identities). -/
def moduliWhiskerRightIso {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {H : BasedCategory.{v₃, w₃} (Over S)} {f g : BasedFunctor F G}
    (e : f ≅ g) (h : BasedFunctor G H) : f.comp h ≅ g.comp h :=
  BasedNatIso.mkNatIso
    (Functor.isoWhiskerRight ((BasedNatTrans.forgetful F G).mapIso e) h.toFunctor)
    (fun x ↦ by
      change H.p.IsHomLift (𝟙 (F.p.obj x)) (h.map (e.hom.toNatTrans.app x))
      have := e.hom.isHomLift' x
      infer_instance)

/-- The right vertical map in base change of a diagonal. Its comparison at
`(z₁,z₂,θ)` is `φ₁ ≫ b(θ) ≫ φ₂⁻¹` in Lean's left-to-right convention.
Source: Stacks 04YR (blueprint: lem-sfb-groupoid-diagonal-two-pullback-identities). -/
def moduliDiagonalBaseChangeRight {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    {Y' : BasedCategory.{v₃, w₃} (Over S)}
    (a : BasedFunctor X Y) (b : BasedFunctor Y' Y) :
    BasedFunctor
      (moduliTwoFiberProduct (moduliTwoFiberSnd a b) (moduliTwoFiberSnd a b))
      (moduliTwoFiberProduct a a) :=
  moduliTwoFiberLift
    ((moduliTwoFiberFst (moduliTwoFiberSnd a b) (moduliTwoFiberSnd a b)).comp
      (moduliTwoFiberFst a b))
    ((moduliTwoFiberSnd (moduliTwoFiberSnd a b) (moduliTwoFiberSnd a b)).comp
      (moduliTwoFiberFst a b))
    (moduliWhiskerLeftIso
        (moduliTwoFiberFst (moduliTwoFiberSnd a b) (moduliTwoFiberSnd a b))
        (moduliTwoFiberStructuralIso a b) ≪≫
      moduliWhiskerRightIso
        (moduliTwoFiberStructuralIso (moduliTwoFiberSnd a b) (moduliTwoFiberSnd a b)) b ≪≫
      (moduliWhiskerLeftIso
        (moduliTwoFiberSnd (moduliTwoFiberSnd a b) (moduliTwoFiberSnd a b))
        (moduliTwoFiberStructuralIso a b)).symm)

/-- The identity-component 2-cell for base change of a relative diagonal.
Source: Stacks 04YR (blueprint: lem-sfb-groupoid-diagonal-two-pullback-identities). -/
def moduliDiagonalBaseChangeIso {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    {Y' : BasedCategory.{v₃, w₃} (Over S)}
    (a : BasedFunctor X Y) (b : BasedFunctor Y' Y) :
    (moduliTwoFiberFst a b).comp (moduliRelativeDiagonal a) ≅
      (moduliRelativeDiagonal (moduliTwoFiberSnd a b)).comp
        (moduliDiagonalBaseChangeRight a b) :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents
      (F := ((moduliTwoFiberFst a b).comp (moduliRelativeDiagonal a)).toFunctor)
      (G := ((moduliRelativeDiagonal (moduliTwoFiberSnd a b)).comp
        (moduliDiagonalBaseChangeRight a b)).toFunctor)
      (fun z ↦ ObjectProperty.isoMk _ (Comma.isoMk (Iso.refl _) (Iso.refl _) (by
        have := z.property.1
        dsimp [moduliDiagonalBaseChangeRight, moduliTwoFiberLift,
          moduliWhiskerLeftIso, moduliWhiskerRightIso, moduliTwoFiberStructuralIso,
          moduliRelativeDiagonal, BasedNatIso.mkNatIso, BasedFunctor.comp,
          BasedNatTrans.forgetful, moduliTwoFiberFst, moduliTwoFiberSnd]
        change a.map (𝟙 z.obj.left) ≫
          (z.obj.hom ≫ b.map (𝟙 z.obj.right) ≫ inv z.obj.hom) =
          𝟙 _ ≫ a.map (𝟙 z.obj.left)
        simp)))
      (fun s ↦ by
        apply ObjectProperty.hom_ext
        apply Comma.hom_ext <;>
          change s.hom.left ≫ 𝟙 _ = 𝟙 _ ≫ s.hom.left
        all_goals simp))
    (fun z ↦ by
      apply (BasedFunctor.isHomLift_iff (moduliTwoFiberFst a a) _ _).mp
      change X.p.IsHomLift (𝟙 (X.p.obj z.obj.left)) (𝟙 z.obj.left)
      infer_instance)

/-- The canonical comparison for base change of a diagonal, with components
`z ↦ (x, (z,z,id), (id,id))`.
Source: Stacks 04YR (blueprint: lem-sfb-groupoid-diagonal-two-pullback-identities). -/
def moduliDiagonalBaseChangeComparison {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    {Y' : BasedCategory.{v₃, w₃} (Over S)}
    (a : BasedFunctor X Y) (b : BasedFunctor Y' Y) :
    BasedFunctor (moduliTwoFiberProduct a b)
      (moduliTwoFiberProduct (moduliRelativeDiagonal a)
        (moduliDiagonalBaseChangeRight a b)) :=
  moduliTwoFiberLift (moduliTwoFiberFst a b)
    (moduliRelativeDiagonal (moduliTwoFiberSnd a b)) (moduliDiagonalBaseChangeIso a b)

/-- Applying `h` to the structural isomorphism: the upper map in Tag 04Z1.
Source: Stacks 04Z1 (blueprint: lem-sfb-groupoid-diagonal-two-pullback-identities). -/
def moduliTwoFiberPostcompose {S : Scheme.{u}}
    {A : BasedCategory.{v₁, w₁} (Over S)} {B : BasedCategory.{v₂, w₂} (Over S)}
    {C : BasedCategory.{v₃, w₃} (Over S)} {D : BasedCategory.{v₄, w₄} (Over S)}
    (f : BasedFunctor A C) (g : BasedFunctor B C) (h : BasedFunctor C D) :
    BasedFunctor (moduliTwoFiberProduct f g) (moduliTwoFiberProduct (f.comp h) (g.comp h)) :=
  moduliTwoFiberLift (moduliTwoFiberFst f g) (moduliTwoFiberSnd f g)
    (moduliWhiskerRightIso (moduliTwoFiberStructuralIso f g) h)

/-- The map `(f,g)` from the fibre product over `D` to `C ×_D C`.
Source: Stacks 04Z1 (blueprint: lem-sfb-groupoid-diagonal-two-pullback-identities). -/
def moduliTwoFiberAfterMapRight {S : Scheme.{u}}
    {A : BasedCategory.{v₁, w₁} (Over S)} {B : BasedCategory.{v₂, w₂} (Over S)}
    {C : BasedCategory.{v₃, w₃} (Over S)} {D : BasedCategory.{v₄, w₄} (Over S)}
    (f : BasedFunctor A C) (g : BasedFunctor B C) (h : BasedFunctor C D) :
    BasedFunctor (moduliTwoFiberProduct (f.comp h) (g.comp h)) (moduliTwoFiberProduct h h) :=
  moduliTwoFiberLift ((moduliTwoFiberFst (f.comp h) (g.comp h)).comp f)
    ((moduliTwoFiberSnd (f.comp h) (g.comp h)).comp g)
    (moduliTwoFiberStructuralIso (f.comp h) (g.comp h))

/-- The canonical 2-cell has components `(id,φ)` at `(a,b,φ)`.
Source: Stacks 04Z1 (blueprint: lem-sfb-groupoid-diagonal-two-pullback-identities). -/
def moduliTwoFiberAfterMapIso {S : Scheme.{u}}
    {A : BasedCategory.{v₁, w₁} (Over S)} {B : BasedCategory.{v₂, w₂} (Over S)}
    {C : BasedCategory.{v₃, w₃} (Over S)} {D : BasedCategory.{v₄, w₄} (Over S)}
    (f : BasedFunctor A C) (g : BasedFunctor B C) (h : BasedFunctor C D) :
    ((moduliTwoFiberFst f g).comp f).comp (moduliRelativeDiagonal h) ≅
      (moduliTwoFiberPostcompose f g h).comp (moduliTwoFiberAfterMapRight f g h) :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents
      (F := (((moduliTwoFiberFst f g).comp f).comp (moduliRelativeDiagonal h)).toFunctor)
      (G := ((moduliTwoFiberPostcompose f g h).comp
        (moduliTwoFiberAfterMapRight f g h)).toFunctor)
      (fun z ↦ ObjectProperty.isoMk _
        (Comma.isoMk (Iso.refl _) (@asIso _ _ _ _ z.obj.hom z.property.1) (by
          dsimp [moduliTwoFiberAfterMapRight, moduliTwoFiberPostcompose,
            moduliTwoFiberLift, moduliWhiskerRightIso, moduliTwoFiberStructuralIso,
            moduliRelativeDiagonal, BasedNatIso.mkNatIso, BasedFunctor.comp,
            BasedNatTrans.forgetful, moduliTwoFiberFst, moduliTwoFiberSnd]
          simp)))
      (fun s ↦ by
        apply ObjectProperty.hom_ext
        apply Comma.hom_ext
        · change f.map s.hom.left ≫ 𝟙 _ = 𝟙 _ ≫ f.map s.hom.left
          simp
        · change f.map s.hom.left ≫ _ = _ ≫ g.map s.hom.right
          exact s.hom.w))
    (fun z ↦ by
      apply (BasedFunctor.isHomLift_iff (moduliTwoFiberFst h h) _ _).mp
      change C.p.IsHomLift (𝟙 (A.p.obj z.obj.left)) (𝟙 (f.obj z.obj.left))
      infer_instance)

/-- The canonical comparison for Tag 04Z1, with components
`(a,b,φ) ↦ (f(a), (a,b,h(φ)), (id,φ))`.
Source: Stacks 04Z1 (blueprint: lem-sfb-groupoid-diagonal-two-pullback-identities). -/
def moduliTwoFiberAfterMapComparison {S : Scheme.{u}}
    {A : BasedCategory.{v₁, w₁} (Over S)} {B : BasedCategory.{v₂, w₂} (Over S)}
    {C : BasedCategory.{v₃, w₃} (Over S)} {D : BasedCategory.{v₄, w₄} (Over S)}
    (f : BasedFunctor A C) (g : BasedFunctor B C) (h : BasedFunctor C D) :
    BasedFunctor (moduliTwoFiberProduct f g)
      (moduliTwoFiberProduct (moduliRelativeDiagonal h) (moduliTwoFiberAfterMapRight f g h)) :=
  moduliTwoFiberLift ((moduliTwoFiberFst f g).comp f) (moduliTwoFiberPostcompose f g h)
    (moduliTwoFiberAfterMapIso f g h)

/-- Base change of a relative diagonal is 2-cartesian, with its canonical comparison
an equivalence over the base (including unit and counit over base identities).
Source: Stacks 04YR (blueprint: lem-sfb-groupoid-diagonal-two-pullback-identities).

Proof: Write z=(x,y,φ), and λ=φ₂⁻¹ b(θ) φ₁ in right-to-left composition.
The right vertical functor sends (z₁,z₂,θ) to (x₁,x₂,λ), respects arrows by their
comma equations, and sends the diagonal to the diagonal with identity components.
In a fibre, a pullback object is (x,z₁,z₂,θ,r₁,r₂), with
 a(r₂)=λ a(r₁). Choose z=(x,y₁,φ₁ a(r₁)). The arrows (r₁,id) and (r₂,θ)
give an isomorphism from its canonical image to the given object: the second comma
equation follows after multiplying the displayed relation by φ₂. This proves
essential surjectivity. A morphism between canonical images has components s,
(p₁,t₁),(p₂,t₂); its equations force t₁=t₂ and p₁=p₂=s. The remaining equation
is exactly the arrow equation for z to w, giving full faithfulness, including
all automorphisms. Componentwise cartesian lifting makes the triple models fibred
in groupoids. Every arrow is cartesian, so the comparison is cartesian.
Apply lem-sfb-fibred-groupoid-equivalence-criterion fibrewise to obtain the
quasi-inverse and both isomorphisms over identities. -/
theorem moduli_diagonal_baseChange_twoCartesian {S : Scheme.{u}}
    (X : BasedCategory.{v₁, w₁} (Over S)) (Y : BasedCategory.{v₂, w₂} (Over S))
    (Y' : BasedCategory.{v₃, w₃} (Over S))
    (hX : IsFibredInGroupoids X) (hY : IsFibredInGroupoids Y)
    (hY' : IsFibredInGroupoids Y') (a : BasedFunctor X Y) (b : BasedFunctor Y' Y) :
    ∃ inverse : BasedFunctor
        (moduliTwoFiberProduct (moduliRelativeDiagonal a) (moduliDiagonalBaseChangeRight a b))
        (moduliTwoFiberProduct a b),
      Nonempty (ModuliTwoIso ((moduliDiagonalBaseChangeComparison a b).comp inverse)
        (BasedFunctor.id (moduliTwoFiberProduct a b))) ∧
      Nonempty (ModuliTwoIso (inverse.comp (moduliDiagonalBaseChangeComparison a b))
        (BasedFunctor.id (moduliTwoFiberProduct (moduliRelativeDiagonal a)
          (moduliDiagonalBaseChangeRight a b)))) := by
  sorry

/-- The change from a fibre product over C to one over D is the 2-pullback of Δ_h.
The comparison is the specified `(id,φ)` comparison, and its inverse and both
isomorphisms lie over the base.
Source: Stacks 04Z1 (blueprint: lem-sfb-groupoid-diagonal-two-pullback-identities).

Proof: Applying h to the structural isomorphism gives the upper functor.
The square's 2-cell at (a,b,φ) is (id,φ); its naturality is the comma arrow equation.
An object of the proposed pullback in a fibre is (c,a,b,η,α,β), where
η h(α)=h(β). Set φ=β α⁻¹ (right-to-left composition). Then h(φ)=η, and
(α⁻¹,id) gives an isomorphism from the canonical image of (a,b,φ) to the object.
This proves essential surjectivity even when h is not faithful. A morphism between
canonical images consists of t and (r,s); the first comparison forces t=f(r),
and the second says g(s)φ=φ'f(r). That is exactly the arrow equation over C;
applying h also gives the equation over D. Thus the comparison is fully faithful.
All functors are over the base. The triple models are fibred in groupoids by
componentwise lifting and unique factorization; every arrow is cartesian.
Apply lem-sfb-fibred-groupoid-equivalence-criterion to obtain the quasi-inverse
and both natural isomorphisms over base identities. -/
theorem moduli_fibreProduct_afterMap_twoCartesian {S : Scheme.{u}}
    (A : BasedCategory.{v₁, w₁} (Over S)) (B : BasedCategory.{v₂, w₂} (Over S))
    (C : BasedCategory.{v₃, w₃} (Over S)) (D : BasedCategory.{v₄, w₄} (Over S))
    (hA : IsFibredInGroupoids A) (hB : IsFibredInGroupoids B)
    (hC : IsFibredInGroupoids C) (hD : IsFibredInGroupoids D)
    (f : BasedFunctor A C) (g : BasedFunctor B C) (h : BasedFunctor C D) :
    ∃ inverse : BasedFunctor
        (moduliTwoFiberProduct (moduliRelativeDiagonal h) (moduliTwoFiberAfterMapRight f g h))
        (moduliTwoFiberProduct f g),
      Nonempty (ModuliTwoIso ((moduliTwoFiberAfterMapComparison f g h).comp inverse)
        (BasedFunctor.id (moduliTwoFiberProduct f g))) ∧
      Nonempty (ModuliTwoIso (inverse.comp (moduliTwoFiberAfterMapComparison f g h))
        (BasedFunctor.id (moduliTwoFiberProduct (moduliRelativeDiagonal h)
          (moduliTwoFiberAfterMapRight f g h)))) := by
  sorry

end CategoryTheory
