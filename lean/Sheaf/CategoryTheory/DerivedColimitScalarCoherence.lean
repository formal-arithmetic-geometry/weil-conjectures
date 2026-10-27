/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.CategoryTheory.DerivedColimitBar
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-!
# Semilinear coherence of the normalized derived-colimit exchange

Source: Stacks Project, Cohomology on Sites, Tags 08PH and 08Q8 (with the typed order
of the latter corrected), and the explicit composite-unit argument in the DAG
(blueprint: lem-trf-derived-colimit-scalar-coherence).

The coefficient-category presentation of change of rings uses ordinary presheaves.
All restriction comparisons below descend the actual identity on underlying elements.
Mathlib writes scalar tensors as `s tensor x`, the symmetric convention to the source.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe w₁ w₂ w₃ w₄ u v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory

/-- Transpose an input followed by the second unit, across the specified right-adjoint
square. This is the canonical semilinear map, not a separately chosen arrow.
Source: Stacks 08PH and 08Q8, composite-unit expansion
(blueprint: lem-trf-derived-colimit-scalar-coherence). -/
def scalarAdjointMap
    {A₁ : Type u₁} {A₂ : Type u₂} {B₁ : Type u₃} {B₂ : Type u₄}
    [Category.{v₁} A₁] [Category.{v₂} A₂] [Category.{v₃} B₁] [Category.{v₄} B₂]
    {L₁ : A₁ ⥤ B₁} {R₁ : B₁ ⥤ A₁} {L₂ : A₂ ⥤ B₂} {R₂ : B₂ ⥤ A₂}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {P : A₂ ⥤ A₁} {Q : B₂ ⥤ B₁} (δ : R₂ ⋙ P ≅ Q ⋙ R₁)
    {M : A₁} {N : A₂} (t : M ⟶ P.obj N) : L₁.obj M ⟶ Q.obj (L₂.obj N) :=
  (adj₁.homEquiv _ _).symm
    (t ≫ P.map (adj₂.unit.app N) ≫ δ.hom.app (L₂.obj N))

/-- Precomposition and restriction on ordinary module presheaves.
Source: Stacks 08PH (blueprint: lem-trf-derived-colimit-scalar-coherence). -/
abbrev categoryScalarPrecomp {E D : Type u} [SmallCategory E] [SmallCategory D]
    {R S : Type u} [CommRing R] [CommRing S] (u : E ⥤ D) (a : R →+* S) :
    (Dᵒᵖ ⥤ ModuleCat.{u} S) ⥤ (Eᵒᵖ ⥤ ModuleCat.{u} R) :=
  (Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{u} S)).obj u.op ⋙
    (Functor.whiskeringRight Eᵒᵖ (ModuleCat.{u} S) (ModuleCat.{u} R)).obj
      (ModuleCat.restrictScalars a)

/-- The identity on underlying point modules for a commuting coefficient square.
Source: Stacks 08Q8 (blueprint: lem-trf-derived-colimit-scalar-coherence). -/
def categoryScalarPointSquare {R S R' S' : Type u}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (φ : R →+* S) (ψ : R' →+* S') (a : R →+* R') (b : S →+* S')
    (hab : b.comp φ = ψ.comp a) :
    ModuleCat.restrictScalars ψ ⋙ ModuleCat.restrictScalars a ≅
      ModuleCat.restrictScalars b ⋙ ModuleCat.restrictScalars φ :=
  (ModuleCat.restrictScalarsComp a ψ).symm ≪≫
    ModuleCat.restrictScalarsCongr hab.symm ≪≫ ModuleCat.restrictScalarsComp φ b

/-- Constants commute with semilinear precomposition by the identity on each section.
Source: Stacks 08PH and 08Q8
(blueprint: lem-trf-derived-colimit-scalar-coherence). -/
def categoryScalarConstantSquare {E D : Type u} [SmallCategory E] [SmallCategory D]
    {R S : Type u} [CommRing R] [CommRing S] (u : E ⥤ D) (a : R →+* S) :
    (Functor.const Dᵒᵖ : ModuleCat.{u} S ⥤ _) ⋙ categoryScalarPrecomp u a ≅
      ModuleCat.restrictScalars a ⋙ (Functor.const Eᵒᵖ : ModuleCat.{u} R ⥤ _) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- The coefficient square on presheaves, with precomposition; its components are the
identity on the abelian groups. Source: Stacks 08PH and 08Q8
(blueprint: lem-trf-derived-colimit-scalar-coherence). -/
def categoryScalarPresheafSquare {E D : Type u} [SmallCategory E] [SmallCategory D]
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (φ : R →+* S) (ψ : R' →+* S') (a : R →+* R') (b : S →+* S')
    (hab : b.comp φ = ψ.comp a) (u : E ⥤ D) :
    ((Functor.whiskeringRight Dᵒᵖ (ModuleCat.{u} S') (ModuleCat.{u} R')).obj
      (ModuleCat.restrictScalars ψ)) ⋙ categoryScalarPrecomp u a ≅
      categoryScalarPrecomp u b ⋙
      ((Functor.whiskeringRight Eᵒᵖ (ModuleCat.{u} S) (ModuleCat.{u} R)).obj
        (ModuleCat.restrictScalars φ)) :=
  NatIso.ofComponents
    (fun F ↦ NatIso.ofComponents
      (fun U ↦ (categoryScalarPointSquare φ ψ a b hab).app (F.obj (u.op.obj U)))
      (by intros; ext x; rfl))
    (by intros; ext U x; rfl)

/-- Descend an actual commuting square of exact functors, retaining the canonical
composition identifications. Source: Stacks 08PH and 08Q8
(blueprint: lem-trf-derived-colimit-scalar-coherence). -/
def categoryScalarDerivedSquare
    {A₁ : Type u₁} {A₂ : Type u₂} {B₁ : Type u₃} {B₂ : Type u₄}
    [Category.{v₁} A₁] [Category.{v₂} A₂] [Category.{v₃} B₁] [Category.{v₄} B₂]
    [Abelian A₁] [Abelian A₂] [Abelian B₁] [Abelian B₂]
    [HasDerivedCategory.{w₁} A₁] [HasDerivedCategory.{w₂} A₂]
    [HasDerivedCategory.{w₃} B₁] [HasDerivedCategory.{w₄} B₂]
    {R₁ : B₁ ⥤ A₁} {R₂ : B₂ ⥤ A₂} {P : A₂ ⥤ A₁} {Q : B₂ ⥤ B₁}
    [R₁.Additive] [R₂.Additive] [P.Additive] [Q.Additive]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (δ : R₂ ⋙ P ≅ Q ⋙ R₁) :
    R₂.mapDerivedCategory ⋙ P.mapDerivedCategory ≅
      Q.mapDerivedCategory ⋙ R₁.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso R₂ P).symm ≪≫
    Functor.mapDerivedCategoryNatIso δ ≪≫ Functor.mapDerivedCategoryCompIso Q R₁

/-- The unique unit-normalized exchange of the two composite left adjoints.
Source: Stacks 08Q8 and the conjugate-isomorphism unit equation
(blueprint: lem-trf-derived-colimit-scalar-coherence). -/
def categoryScalarExchange (B : CategoryColimitBarSystem.{u})
    (E : Type u) [SmallCategory E] {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S)
    (T : DerivedCategory (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤
      DerivedCategory (Eᵒᵖ ⥤ ModuleCat.{u} S))
    (adjT : T ⊣ ((Functor.whiskeringRight Eᵒᵖ (ModuleCat.{u} S) (ModuleCat.{u} R)).obj
      (ModuleCat.restrictScalars φ)).mapDerivedCategory)
    (T₀ : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (adjT₀ : T₀ ⊣ (ModuleCat.restrictScalars φ).mapDerivedCategory) :
    T ⋙ (B.models E S).derived ≅ (B.models E R).derived ⋙ T₀ :=
  (conjugateIsoEquiv ((B.models E R).adjunction.comp adjT₀)
    (adjT.comp (B.models E S).adjunction)).symm
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (NatIso.ofComponents
            (F := ModuleCat.restrictScalars φ ⋙
              (Functor.const Eᵒᵖ : ModuleCat.{u} R ⥤ _))
            (G := (Functor.const Eᵒᵖ : ModuleCat.{u} S ⥤ _) ⋙
              (Functor.whiskeringRight Eᵒᵖ (ModuleCat.{u} S) (ModuleCat.{u} R)).obj
                (ModuleCat.restrictScalars φ))
            (fun _ ↦ Iso.refl _) (by intros; rfl)) ≪≫
          Functor.mapDerivedCategoryCompIso _ _)

/-- The semilinear derived-colimit exchange square, for arbitrary unbounded derived
objects and arbitrary derived input arrows. Source: Stacks 08PH and 08Q8, explicit
composite-unit argument (blueprint: lem-trf-derived-colimit-scalar-coherence).

Proof: put P = Res_a u⁻¹ and Q = Res_b u⁻¹. The composite adjunction for
L_S T has unit r_E(lambda_S) tau_E; that for T₀ L_R has unit C_R(tau₀) lambda_R.
The definition of categoryScalarExchange is exactly the isomorphism carrying these
units to one another. Transpose the left route under T_E followed by L_{E,S}.
The definitions of a_S and t_S and the right-adjoint commuting squares identify its
transpose with P(eta_{B,D}) t, using the unit equation for chi_D. Transpose the right
route: first the unit equation for chi_E, then the defining transposes of b_R and a_R,
give P(C_D(tau₀') lambda_{D,R'}) t = P(eta_{B,D}) t again. The composite Hom
bijection is injective, so the two routes agree. No chain representative for t,
flatness of any ring map, or boundedness is used. -/
theorem categoryColimitScalarCoherence
    (B : CategoryColimitBarSystem.{u}) {E D : Type u} [SmallCategory E] [SmallCategory D]
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (φ : R →+* S) (ψ : R' →+* S') (a : R →+* R') (b : S →+* S')
    (hab : b.comp φ = ψ.comp a) (u : E ⥤ D)
    (T : DerivedCategory (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤
      DerivedCategory (Eᵒᵖ ⥤ ModuleCat.{u} S))
    (adjT : T ⊣ ((Functor.whiskeringRight Eᵒᵖ (ModuleCat.{u} S) (ModuleCat.{u} R)).obj
      (ModuleCat.restrictScalars φ)).mapDerivedCategory)
    (T' : DerivedCategory (Dᵒᵖ ⥤ ModuleCat.{u} R') ⥤
      DerivedCategory (Dᵒᵖ ⥤ ModuleCat.{u} S'))
    (adjT' : T' ⊣ ((Functor.whiskeringRight Dᵒᵖ (ModuleCat.{u} S') (ModuleCat.{u} R')).obj
      (ModuleCat.restrictScalars ψ)).mapDerivedCategory)
    (T₀ : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (adjT₀ : T₀ ⊣ (ModuleCat.restrictScalars φ).mapDerivedCategory)
    (T₀' : DerivedCategory (ModuleCat.{u} R') ⥤ DerivedCategory (ModuleCat.{u} S'))
    (adjT₀' : T₀' ⊣ (ModuleCat.restrictScalars ψ).mapDerivedCategory)
    (M : DerivedCategory (Eᵒᵖ ⥤ ModuleCat.{u} R))
    (M' : DerivedCategory (Dᵒᵖ ⥤ ModuleCat.{u} R'))
    (t : M ⟶ (categoryScalarPrecomp u a).mapDerivedCategory.obj M') :
    scalarAdjointMap (B.models E S).adjunction (B.models D S').adjunction
        (categoryScalarDerivedSquare (categoryScalarConstantSquare u b))
        (scalarAdjointMap adjT adjT'
          (categoryScalarDerivedSquare (categoryScalarPresheafSquare φ ψ a b hab u)) t) ≫
      (ModuleCat.restrictScalars b).mapDerivedCategory.map
        ((categoryScalarExchange B D ψ T' adjT' T₀' adjT₀').hom.app M') =
    (categoryScalarExchange B E φ T adjT T₀ adjT₀).hom.app M ≫
      scalarAdjointMap adjT₀ adjT₀'
        (categoryScalarDerivedSquare (categoryScalarPointSquare φ ψ a b hab))
        (scalarAdjointMap (B.models E R).adjunction (B.models D R').adjunction
          (categoryScalarDerivedSquare (categoryScalarConstantSquare u a)) t) := by
  sorry

/-- Vertical pasting of right-adjoint squares, with all associators inserted.
Source: Stacks 08PH and the mates pasting law
(blueprint: lem-trf-derived-colimit-scalar-coherence). -/
def scalarAdjointSquareVComp
    {A₁ : Type u₁} {A₂ : Type u₂} {A₃ : Type u₃}
    {B₁ : Type u₄} {B₂ : Type u₅} {B₃ : Type u₆}
    [Category.{v₁} A₁] [Category.{v₂} A₂] [Category.{v₃} A₃]
    [Category.{v₄} B₁] [Category.{v₅} B₂] [Category.{v₆} B₃]
    {R₁ : B₁ ⥤ A₁} {R₂ : B₂ ⥤ A₂} {R₃ : B₃ ⥤ A₃}
    {P : A₂ ⥤ A₁} {P' : A₃ ⥤ A₂} {Q : B₂ ⥤ B₁} {Q' : B₃ ⥤ B₂}
    (δ : R₂ ⋙ P ≅ Q ⋙ R₁) (δ' : R₃ ⋙ P' ≅ Q' ⋙ R₂) :
    R₃ ⋙ (P' ⋙ P) ≅ (Q' ⋙ Q) ⋙ R₁ :=
  (Functor.associator R₃ P' P).symm ≪≫ Functor.isoWhiskerRight δ' P ≪≫
    Functor.associator Q' R₂ P ≪≫ Functor.isoWhiskerLeft Q' δ ≪≫
      (Functor.associator Q' Q R₁).symm

/-- Horizontal pasting of right-adjoint squares for composite adjunctions.
Source: Stacks 08Q8 and the mates pasting law
(blueprint: lem-trf-derived-colimit-scalar-coherence). -/
def scalarAdjointSquareHComp
    {A₁ : Type u₁} {A₂ : Type u₂} {B₁ : Type u₃}
    {B₂ : Type u₄} {C₁ : Type u₅} {C₂ : Type u₆}
    [Category.{v₁} A₁] [Category.{v₂} A₂] [Category.{v₃} B₁]
    [Category.{v₄} B₂] [Category.{v₅} C₁] [Category.{v₆} C₂]
    {R₁ : B₁ ⥤ A₁} {R₂ : B₂ ⥤ A₂} {S₁ : C₁ ⥤ B₁} {S₂ : C₂ ⥤ B₂}
    {P : A₂ ⥤ A₁} {Q : B₂ ⥤ B₁} {H : C₂ ⥤ C₁}
    (δ : R₂ ⋙ P ≅ Q ⋙ R₁) (ε : S₂ ⋙ Q ≅ H ⋙ S₁) :
    (S₂ ⋙ R₂) ⋙ P ≅ H ⋙ (S₁ ⋙ R₁) :=
  Functor.associator S₂ R₂ P ≪≫ Functor.isoWhiskerLeft S₂ δ ≪≫
    (Functor.associator S₂ Q R₁).symm ≪≫ Functor.isoWhiskerRight ε R₁ ≪≫
      Functor.associator H S₁ R₁

/-- Identity compatibility for each of the three canonical transposes in the square.
This is the adjunction form, so it applies to colimit and coefficient adjunctions alike.
Source: Stacks 08PH and 08Q8, identity clause of the composite-unit calculation
(blueprint: lem-trf-derived-colimit-scalar-coherence).

Proof: the defining transpose is the unit (the unitors have identity components).
The inverse Hom bijection sends the unit to the identity. -/
theorem scalarAdjointMap_identity
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) (M : A) :
    scalarAdjointMap adj adj (R.rightUnitor ≪≫ R.leftUnitor.symm) (𝟙 M) =
      𝟙 (L.obj M) := by
  sorry

/-- Composition in the indexing/restriction direction for the canonical transposes.
The iterated restriction is displayed, so an actual composed indexing functor is
identified with it by its canonical derived composition comparison.
Source: Stacks 08PH and 08Q8, vertical pasting of mates
(blueprint: lem-trf-derived-colimit-scalar-coherence).

Proof: transpose the composite of the two adjuncts. Naturality of the intervening
unit and the defining unit equations give the input t followed by P(t'), then the
last unit and the pasted right-adjoint square. This is the defining transpose of
the left side; injectivity of the Hom bijection gives the equality. -/
theorem scalarAdjointMap_composition
    {A₁ : Type u₁} {A₂ : Type u₂} {A₃ : Type u₃}
    {B₁ : Type u₄} {B₂ : Type u₅} {B₃ : Type u₆}
    [Category.{v₁} A₁] [Category.{v₂} A₂] [Category.{v₃} A₃]
    [Category.{v₄} B₁] [Category.{v₅} B₂] [Category.{v₆} B₃]
    {L₁ : A₁ ⥤ B₁} {R₁ : B₁ ⥤ A₁} {L₂ : A₂ ⥤ B₂} {R₂ : B₂ ⥤ A₂}
    {L₃ : A₃ ⥤ B₃} {R₃ : B₃ ⥤ A₃}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    {P : A₂ ⥤ A₁} {P' : A₃ ⥤ A₂} {Q : B₂ ⥤ B₁} {Q' : B₃ ⥤ B₂}
    (δ : R₂ ⋙ P ≅ Q ⋙ R₁) (δ' : R₃ ⋙ P' ≅ Q' ⋙ R₂)
    {M : A₁} {N : A₂} {O : A₃} (t : M ⟶ P.obj N) (t' : N ⟶ P'.obj O) :
    scalarAdjointMap adj₁ adj₃ (scalarAdjointSquareVComp δ δ') (t ≫ P.map t') =
      scalarAdjointMap adj₁ adj₂ δ t ≫ Q.map (scalarAdjointMap adj₂ adj₃ δ' t') := by
  sorry

/-- Pasting in the coefficient-adjunction direction. Combined with vertical composition
and uniqueness of conjugate isomorphisms, this gives pasting of the normalized exchange
squares, with the canonical composite-adjunction identifications.
Source: Stacks 08Q8, horizontal pasting of mates
(blueprint: lem-trf-derived-colimit-scalar-coherence).

Proof: expand the Hom bijection of each composite adjunction as the composite of
its two Hom bijections. The two successive inverse bijections give the right side.
The composite unit is the first unit followed by the first right adjoint applied
to the second unit. Substitution in the defining transpose gives exactly the
pasted right square on the left. Apply the inverse composite bijection. -/
theorem scalarAdjointMap_coefficient_pasting
    {A₁ : Type u₁} {A₂ : Type u₂} {B₁ : Type u₃}
    {B₂ : Type u₄} {C₁ : Type u₅} {C₂ : Type u₆}
    [Category.{v₁} A₁] [Category.{v₂} A₂] [Category.{v₃} B₁]
    [Category.{v₄} B₂] [Category.{v₅} C₁] [Category.{v₆} C₂]
    {L₁ : A₁ ⥤ B₁} {R₁ : B₁ ⥤ A₁} {L₂ : A₂ ⥤ B₂} {R₂ : B₂ ⥤ A₂}
    {K₁ : B₁ ⥤ C₁} {S₁ : C₁ ⥤ B₁} {K₂ : B₂ ⥤ C₂} {S₂ : C₂ ⥤ B₂}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₁' : K₁ ⊣ S₁) (adj₂' : K₂ ⊣ S₂)
    {P : A₂ ⥤ A₁} {Q : B₂ ⥤ B₁} {H : C₂ ⥤ C₁}
    (δ : R₂ ⋙ P ≅ Q ⋙ R₁) (ε : S₂ ⋙ Q ≅ H ⋙ S₁)
    {M : A₁} {N : A₂} (t : M ⟶ P.obj N) :
    scalarAdjointMap (adj₁.comp adj₁') (adj₂.comp adj₂')
        (scalarAdjointSquareHComp δ ε) t =
      scalarAdjointMap adj₁' adj₂' ε (scalarAdjointMap adj₁ adj₂ δ t) := by
  sorry

/-- The chain-level scalar exchange, with no flatness assumption on F or the ring map.
Source: Stacks 08PG and 08Q8, tensor/coprod expansion
(blueprint: lem-trf-derived-colimit-scalar-coherence).

Proof: tensor commutes with each chain-indexed direct sum. Send (sigma,s tensor x)
to s tensor (sigma,x); the inverse distributes tensor over the finite support of
a direct-sum element. Balancing and the universal properties show that the two
maps are inverse. Every bar face commutes with them: all but the last face keep
the coefficient, and the last face restricts x on both sides. Hence they commute
with the signed differential. In positive degrees both complexes vanish. -/
theorem categoryColimitScalarCoherence_barIso
    (B : CategoryColimitBarSystem.{u}) {E : Type u} [SmallCategory E]
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (F : Eᵒᵖ ⥤ ModuleCat.{u} R) :
    ∃ Φ : (B.models E S).bar.obj ((F ⋙ ModuleCat.extendScalars φ)) ≅
        ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj
          ((B.models E R).bar.obj F),
      ∀ (n : ℕ) (c : ComposableArrows E n) (x : F.obj (op c.right)) (s : S),
        Φ.hom.f (-(n : ℤ))
            ((B.models E S).generator ((F ⋙ ModuleCat.extendScalars φ)) n c (s ⊗ₜ[R,φ] x)) =
          s ⊗ₜ[R,φ] ((B.models E R).generator F n c x) := by
  sorry

/-- The scalar-exchange chain square, including both semilinear tensor maps and their
pure-tensor formulas. The formula hypotheses specify the unique isomorphisms from the
previous clause. There is no flatness assumption.
Source: Stacks 08PH and 08Q8, the balanced generator calculation
(blueprint: lem-trf-derived-colimit-scalar-coherence).

Proof: transposing t followed by the ordinary coefficient unit gives the sectionwise
map s tensor x to b(s) tensor t(x). It is balanced since b(phi(r)) = psi(a(r)).
The same construction applied degreewise to the canonical bar map gives kS. It
commutes with the differential by additivity and the chain-map property of B.map.
On generators the two routes both give b(s) tensor (u sigma,t(x)), by the two
specified exchange formulas and B.formula. Such generators span every nonpositive
degree; positive degrees vanish. Equality on them proves equality of chain maps. -/
theorem categoryColimitScalarCoherence_bar_square
    (B : CategoryColimitBarSystem.{u}) {E D : Type u} [SmallCategory E] [SmallCategory D]
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (φ : R →+* S) (ψ : R' →+* S') (a : R →+* R') (b : S →+* S')
    (hab : b.comp φ = ψ.comp a) (u : E ⥤ D)
    (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (G : Dᵒᵖ ⥤ ModuleCat.{u} R')
    (t : F ⟶ u.op ⋙ G ⋙ ModuleCat.restrictScalars a)
    (Φ : (B.models E S).bar.obj ((F ⋙ ModuleCat.extendScalars φ)) ≅
      ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj
        ((B.models E R).bar.obj F))
    (Ψ : (B.models D S').bar.obj ((G ⋙ ModuleCat.extendScalars ψ)) ≅
      ((ModuleCat.extendScalars ψ).mapHomologicalComplex (.up ℤ)).obj
        ((B.models D R').bar.obj G))
    (hΦ : ∀ (n : ℕ) (c : ComposableArrows E n) (x : F.obj (op c.right)) (s : S),
      Φ.hom.f (-(n : ℤ))
          ((B.models E S).generator ((F ⋙ ModuleCat.extendScalars φ)) n c (s ⊗ₜ[R,φ] x)) =
        s ⊗ₜ[R,φ] ((B.models E R).generator F n c x))
    (hΨ : ∀ (n : ℕ) (c : ComposableArrows D n) (x : G.obj (op c.right)) (s : S'),
      Ψ.hom.f (-(n : ℤ))
          ((B.models D S').generator ((G ⋙ ModuleCat.extendScalars ψ)) n c (s ⊗ₜ[R',ψ] x)) =
        s ⊗ₜ[R',ψ] ((B.models D R').generator G n c x)) :
    ∃ (tS : (F ⋙ ModuleCat.extendScalars φ) ⟶
        u.op ⋙ (G ⋙ ModuleCat.extendScalars ψ) ⋙ ModuleCat.restrictScalars b)
      (kS : ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj
          ((B.models E R).bar.obj F) ⟶
        ((ModuleCat.restrictScalars b).mapHomologicalComplex (.up ℤ)).obj
          (((ModuleCat.extendScalars ψ).mapHomologicalComplex (.up ℤ)).obj
            ((B.models D R').bar.obj G))),
      (∀ (U : Eᵒᵖ) (x : F.obj U) (s : S),
        tS.app U (s ⊗ₜ[R,φ] x) =
          b s ⊗ₜ[R',ψ] (@id (G.obj (u.op.obj U)) (t.app U x))) ∧
      (∀ (q : ℤ) (x : ((B.models E R).bar.obj F).X q) (s : S),
        kS.f q (s ⊗ₜ[R,φ] x) =
          b s ⊗ₜ[R',ψ] (@id (((B.models D R').bar.obj G).X q)
            (((B.map u a t).f q) x))) ∧
      B.map u b tS ≫
          ((ModuleCat.restrictScalars b).mapHomologicalComplex (.up ℤ)).map Ψ.hom =
        Φ.hom ≫ kS := by
  sorry

/-- The existing closed tensor structure on ordinary module presheaves. This supplies
colimit preservation for the standard total tensor of unbounded presheaf complexes.
Source: Stacks 06YN, sectionwise tensor on the identity-cover site
(blueprint: lem-trf-derived-colimit-scalar-coherence). -/
instance categoryScalarPresheafClosed (E : Type u) [SmallCategory E]
    (R : Type u) [CommRing R] : MonoidalClosed (Eᵒᵖ ⥤ ModuleCat.{u} R) :=
  Functor.functorCategoryMonoidalClosed Eᵒᵖ (ModuleCat.{u} R)

/-- The canonical comparison with termwise ordinary extension: transpose the localized
ordinary unit using the exact-restriction factorization. On K-flat representatives it
is the usual derived-extension comparison. Its definition fixes the representative
normalization even if a different presentation of the derived left adjoint is used.
Source: Stacks 07A6, 08Q8, normalized coefficient adjunction
(blueprint: lem-trf-derived-colimit-scalar-coherence). -/
def scalarAdjointCochainComparison
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    {e : A ⥤ B} {r : B ⥤ A} [e.Additive] [r.Additive]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r] (adj : e ⊣ r)
    {L : DerivedCategory A ⥤ DerivedCategory B} (d : L ⊣ r.mapDerivedCategory)
    (P : CochainComplex A ℤ) :
    L.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((e.mapHomologicalComplex (.up ℤ)).obj P) :=
  (d.homEquiv _ _).symm
    (DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      r.mapDerivedCategoryFactors.inv.app ((e.mapHomologicalComplex (.up ℤ)).obj P))

/-- The canonical comparisons carry each derived transpose of this item to the
corresponding chain-level adjunct: if the cochain map `g` is degreewise the ordinary
transpose of `f` followed by the second ordinary unit and the right-adjoint square,
then the derived transpose of the localized `f` is represented by `g`. Applied to
`B.map u a t` and `kS` it identifies `b_R` with `kS`; applied to the single complexes
of `t` and `tS` it identifies `t_S` with `tS`. Together with the bar dependency for
`a_R` and `a_S`, and `categoryColimitScalarCoherence_bar_represents` for the two
exchanges, this is the assertion that the chain square represents the derived square.
Source: Stacks 08PH and 08Q8, adjunct formula of the normalized coefficient adjunction
(blueprint: lem-trf-derived-colimit-scalar-coherence).

Proof: transpose both sides under `d₁`. The left side gives, by naturality of the
derived square and the defining transpose of the second comparison, the localization
of `f`, then `P` of the localized ordinary unit, then the descended square. The right
side gives, by the defining transpose of the first comparison and naturality of the
factorization of `r₁`, the localization of the ordinary unit followed by `r₁ g`,
which is `f` followed by `P` of the unit and `δ` by the hypothesis on `g`. The two
agree by the compatibility of the composition isomorphisms with the factorizations. -/
theorem scalarAdjointCochainComparison_scalarAdjointMap
    {A₁ : Type u₁} {A₂ : Type u₂} {B₁ : Type u₃} {B₂ : Type u₄}
    [Category.{v₁} A₁] [Category.{v₂} A₂] [Category.{v₃} B₁] [Category.{v₄} B₂]
    [Abelian A₁] [Abelian A₂] [Abelian B₁] [Abelian B₂]
    [HasDerivedCategory.{w₁} A₁] [HasDerivedCategory.{w₂} A₂]
    [HasDerivedCategory.{w₃} B₁] [HasDerivedCategory.{w₄} B₂]
    {e₁ : A₁ ⥤ B₁} {r₁ : B₁ ⥤ A₁} {e₂ : A₂ ⥤ B₂} {r₂ : B₂ ⥤ A₂}
    {P : A₂ ⥤ A₁} {Q : B₂ ⥤ B₁}
    [e₁.Additive] [e₂.Additive] [r₁.Additive] [r₂.Additive] [P.Additive] [Q.Additive]
    [PreservesFiniteLimits r₁] [PreservesFiniteColimits r₁]
    [PreservesFiniteLimits r₂] [PreservesFiniteColimits r₂]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (adj₁ : e₁ ⊣ r₁) (adj₂ : e₂ ⊣ r₂)
    {L₁ : DerivedCategory A₁ ⥤ DerivedCategory B₁}
    {L₂ : DerivedCategory A₂ ⥤ DerivedCategory B₂}
    (d₁ : L₁ ⊣ r₁.mapDerivedCategory) (d₂ : L₂ ⊣ r₂.mapDerivedCategory)
    (δ : r₂ ⋙ P ≅ Q ⋙ r₁)
    {X : CochainComplex A₁ ℤ} {Y : CochainComplex A₂ ℤ}
    (f : X ⟶ (P.mapHomologicalComplex (.up ℤ)).obj Y)
    (g : (e₁.mapHomologicalComplex (.up ℤ)).obj X ⟶
      (Q.mapHomologicalComplex (.up ℤ)).obj ((e₂.mapHomologicalComplex (.up ℤ)).obj Y))
    (hg : ∀ n : ℤ, adj₁.homEquiv _ _ (g.f n) =
      f.f n ≫ P.map (adj₂.unit.app (Y.X n)) ≫ δ.hom.app (e₂.obj (Y.X n))) :
    scalarAdjointMap d₁ d₂ (categoryScalarDerivedSquare δ)
        (DerivedCategory.Q.map f ≫ P.mapDerivedCategoryFactors.inv.app Y) ≫
      Q.mapDerivedCategory.map (scalarAdjointCochainComparison adj₂ d₂ Y) =
    scalarAdjointCochainComparison adj₁ d₁ X ≫ DerivedCategory.Q.map g ≫
      Q.mapDerivedCategoryFactors.inv.app ((e₂.mapHomologicalComplex (.up ℤ)).obj Y) := by
  sorry

/-- On K-flat representatives the chain exchange is the unit-normalized derived
exchange, using the augmentation-normalized bar model and canonical coefficient
comparisons. Source: Stacks 08PG, 08PH and 08Q8, bar-unit transpose argument
(blueprint: lem-trf-derived-colimit-scalar-coherence).

Proof: K-flatness of F[0] implies that each F(U) is flat: tensor with the constant
three-term acyclic complex of an arbitrary short exact sequence and evaluate at U.
The bar terms are then coproducts of flat modules. By derived change of rings the
canonical comparisons are invertible on the two displayed K-flat complexes.
The ordinary coefficient unit is x to 1 tensor x; its adjunct sends s tensor x to
s times the input arrow. The bar of the coefficient unit therefore sends (sigma,x)
to (sigma,1 tensor x); its adjunct is the inverse of the specified chain exchange.
The bar model's transpose and degree-zero augmentation normalization identify this
adjunct with the inverse normalized derived exchange. Inverting yields the displayed
equation. At both ends of bar_square these same adjunct formulas identify tS and kS
with the derived transposes t_S and b_R, and B.formula identifies the bar maps with
a_R and a_S. Thus the chain square represents the preceding derived square whenever
the displayed tensors are K-flat derived representatives. No flatness of phi is used. -/
theorem categoryColimitScalarCoherence_bar_represents
    (B : CategoryColimitBarSystem.{u}) {E : Type u} [SmallCategory E]
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (T : DerivedCategory (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤
      DerivedCategory (Eᵒᵖ ⥤ ModuleCat.{u} S))
    (adjT : T ⊣ ((Functor.whiskeringRight Eᵒᵖ (ModuleCat.{u} S) (ModuleCat.{u} R)).obj
      (ModuleCat.restrictScalars φ)).mapDerivedCategory)
    (T₀ : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (adjT₀ : T₀ ⊣ (ModuleCat.restrictScalars φ).mapDerivedCategory)
    (F : Eᵒᵖ ⥤ ModuleCat.{u} R)
    (hF : (HomologicalComplex.quasiIso (Eᵒᵖ ⥤ ModuleCat.{u} R) (.up ℤ)).kFlat
      ((CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0).obj F))
    (hK : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat
      ((B.models E R).bar.obj F))
    (Φ : (B.models E S).bar.obj (F ⋙ ModuleCat.extendScalars φ) ≅
      ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj
        ((B.models E R).bar.obj F))
    (hΦ : ∀ (n : ℕ) (c : ComposableArrows E n) (x : F.obj (op c.right)) (s : S),
      Φ.hom.f (-(n : ℤ))
          ((B.models E S).generator (F ⋙ ModuleCat.extendScalars φ) n c (s ⊗ₜ[R,φ] x)) =
        s ⊗ₜ[R,φ] ((B.models E R).generator F n c x)) :
    IsIso (scalarAdjointCochainComparison
      ((ModuleCat.extendRestrictScalarsAdj φ).whiskerRight Eᵒᵖ) adjT
        ((CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0).obj F)) ∧
    IsIso (scalarAdjointCochainComparison (ModuleCat.extendRestrictScalarsAdj φ) adjT₀
      ((B.models E R).bar.obj F)) ∧
    (categoryScalarExchange B E φ T adjT T₀ adjT₀).hom.app (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0).obj F)) ≫
      T₀.map ((B.models E R).model.hom.app F) ≫
        scalarAdjointCochainComparison (ModuleCat.extendRestrictScalarsAdj φ) adjT₀
          ((B.models E R).bar.obj F) =
    (B.models E S).derived.map
        (scalarAdjointCochainComparison
          ((ModuleCat.extendRestrictScalarsAdj φ).whiskerRight Eᵒᵖ) adjT
            ((CochainComplex.singleFunctor (Eᵒᵖ ⥤ ModuleCat.{u} R) 0).obj F)) ≫
      (B.models E S).derived.map (DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          ((Functor.whiskeringRight Eᵒᵖ (ModuleCat.{u} R) (ModuleCat.{u} S)).obj
            (ModuleCat.extendScalars φ)) (.up ℤ) 0).hom.app F)) ≫
      (B.models E S).model.hom.app (F ⋙ ModuleCat.extendScalars φ) ≫
        DerivedCategory.Q.map Φ.hom := by
  sorry

end CategoryTheory
