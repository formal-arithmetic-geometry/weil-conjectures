/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.RightAdjointTensorCompatibleExactStructures

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

private theorem qc_shift (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {K : schemeDerivedCategory X} (hK : schemeDerivedQCohProperty X K) (n : ℤ) :
    schemeDerivedQCohProperty X (K⟦n⟧) := by
  intro m
  let e := ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).shiftIso n m (n + m) rfl).app K
  exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
    e.symm (hK (n + m))

private theorem qc_stable (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    (schemeDerivedQCohProperty X).IsStableUnderShift ℤ :=
  { isStableUnderShiftBy := fun n ↦ { le_shift := fun _K hK ↦ qc_shift X hK n } }

private def triangleComparison
    {D E : Type*} [Category D] [Category E] [HasShift D ℤ] [HasShift E ℤ]
    (F G : D ⥤ E) [F.CommShift ℤ] [G.CommShift ℤ]
    (t : F ⟶ G) [NatTrans.CommShift t ℤ] (S : Pretriangulated.Triangle D) :
    F.mapTriangle.obj S ⟶ G.mapTriangle.obj S :=
  Pretriangulated.Triangle.homMk _ _ (t.app S.obj₁) (t.app S.obj₂) (t.app S.obj₃)
    (t.naturality S.mor₁) (t.naturality S.mor₂) (by
      dsimp [Functor.mapTriangle, Pretriangulated.Triangle.mk]
      rw [Category.assoc, NatTrans.shift_app_comm, ← Category.assoc, t.naturality, Category.assoc])

/-- Distinguished triangle diagram for the pinned right-adjoint tensor comparison.
Source: Stacks Project, Tag 0A9U, triangulated-subcategory argument, and
equation (48.8.0.1). This proof expands the comparison compatibility used there.
(blueprint: lem-sc-right-adjoint-tensor-comparison-triangle).

Proof. Put E = c(O_Y) and F(K) = Lf*(K) tensor E. Compute derived pullback and
this tensor on K-flat representatives. Shifting these representatives gives
F(K[n]) isomorphic to F(K)[n]; tensoring a cone gives the cone of the tensored
map, so F is exact. Restrict derived direct image to the quasi-coherent full
subcategory. Its shift comparison transports through adj to a comparison
c(K[n]) isomorphic to c(K)[n]: apply adj to Hom(Rf*(M), K[n]), move the shift
using exactness of Rf*, and apply adj again. Yoneda supplies the comparison.
The right adjoint of an exact functor is exact for this comparison.

The projection map is the a-mate of inverse monoidal comparison followed by
the pullback counit. The hypothesis hτ identifies τ with the adj-mate of its
inverse followed by tensoring the adj-counit at O_Y and the right unitor.
Compute this composite on shifted K-flat representatives. Moving the shift
through the tensor and pullback comparisons, use naturality of the counits
and the adjunction triangle identities to obtain the same composite for K,
shifted by n. Thus τ commutes with the constructed shift comparisons. Transport
these structures along the comparison isomorphisms for the specified monoidal
structure and adjunctions; the construction does not require canonical choices.

Transport the three arrows of T through the given vertex isomorphisms to
A, B, C, using the shifted first isomorphism on the connecting arrow. Since
all vertices are quasi-coherent, this is a distinguished triangle of the full
subcategory. Apply the exact functors F and c and then the ambient inclusion
to obtain distinguished triangles T₁ and T₂. Use τ at the three vertices as
the components of m. Naturality gives its first two commuting squares, and
the constructed shift compatibility gives the square for the connecting arrow.
The vertex isomorphisms from this transport are eF_i and ec_i. Conjugating the
components of m by these isomorphisms gives the three asserted formulas.
Zero triangles and zero components satisfy the same construction; no component
of τ is assumed invertible. -/
theorem rightAdjointTensorComparison_triangle
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hRf : ∀ E : schemeDerivedQCohCategory Z,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
    (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
    (hTensor : ∀ (K : schemeDerivedQCohCategory Y) (E : schemeDerivedQCohCategory Z),
      schemeDerivedQCohProperty Z (((derivedPullback f).obj K.obj) ⊗ E.obj))
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory Z)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage f) hRf ⊣ c)
    (τ : (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙
        tensorRight (c.obj ⟨𝟙_ _, hO⟩).obj)
      (fun K ↦ hTensor K (c.obj ⟨𝟙_ _, hO⟩))
      ⟶ c)
    (hτ : ∀ K : schemeDerivedQCohCategory Y,
      ∃ pf : (schemeDerivedDirectImage f).obj
            (((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
          K.obj ⊗ (schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj,
        pf.inv = (a.homEquiv _ _)
          ((Functor.Monoidal.μIso (derivedPullback f) K.obj
            ((schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
            (derivedPullback f).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj) ∧
        τ.app K = ((adj.homEquiv
          ⟨((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
            hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
          (ObjectProperty.homMk (pf.hom ≫
            K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom)))) :
    (∀ (A B C : schemeDerivedQCohCategory Y)
      (T : Pretriangulated.Triangle (schemeDerivedCategory Y)),
      T ∈ Pretriangulated.distinguishedTriangles →
      Nonempty (T.obj₁ ≅ A.obj) → Nonempty (T.obj₂ ≅ B.obj) →
      Nonempty (T.obj₃ ≅ C.obj) →
      ∃ (T₁ T₂ : Pretriangulated.Triangle (schemeDerivedCategory Z)) (m : T₁ ⟶ T₂),
        T₁ ∈ Pretriangulated.distinguishedTriangles ∧
        T₂ ∈ Pretriangulated.distinguishedTriangles ∧
        ∃ (eF₁ : T₁.obj₁ ≅ ((derivedPullback f).obj A.obj ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj))
          (ec₁ : T₂.obj₁ ≅ (c.obj A).obj)
          (eF₂ : T₁.obj₂ ≅ ((derivedPullback f).obj B.obj ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj))
          (ec₂ : T₂.obj₂ ≅ (c.obj B).obj)
          (eF₃ : T₁.obj₃ ≅ ((derivedPullback f).obj C.obj ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj))
          (ec₃ : T₂.obj₃ ≅ (c.obj C).obj),
          m.hom₁ = eF₁.hom ≫ (τ.app A).hom ≫ ec₁.inv ∧
          m.hom₂ = eF₂.hom ≫ (τ.app B).hom ≫ ec₂.inv ∧
          m.hom₃ = eF₃.hom ≫ (τ.app C).hom ≫ ec₃.inv) := by
  classical
  let : (schemeDerivedQCohProperty Y).IsStableUnderShift ℤ := qc_stable Y
  let F := (schemeDerivedQCohProperty Z).lift
    ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙
      tensorRight (c.obj ⟨𝟙_ _, hO⟩).obj)
    (fun K ↦ hTensor K (c.obj ⟨𝟙_ _, hO⟩)) ⋙ (schemeDerivedQCohProperty Z).ι
  let G := c ⋙ (schemeDerivedQCohProperty Z).ι
  let t : F ⟶ G := Functor.whiskerRight τ (schemeDerivedQCohProperty Z).ι
  obtain ⟨sF, sG, ht, hexact⟩ :=
    rightAdjointTensor_compatibleExactStructures f hRf hO hTensor a c adj τ hτ
  let := sF
  let := sG
  let : NatTrans.CommShift t ℤ := ht
  intro A B C T hT ⟨eA⟩ ⟨eB⟩ ⟨eC⟩
  let I := (schemeDerivedQCohProperty Y).ι
  let S : Pretriangulated.Triangle (schemeDerivedQCohCategory Y) :=
    Pretriangulated.Triangle.mk (X := A) (Y := B) (Z := C)
      (ObjectProperty.homMk (eA.inv ≫ T.mor₁ ≫ eB.hom))
      (ObjectProperty.homMk (eB.inv ≫ T.mor₂ ≫ eC.hom))
      (ObjectProperty.homMk (eC.inv ≫ T.mor₃ ≫ eA.hom⟦(1 : ℤ)⟧' ≫
        (I.commShiftIso (1 : ℤ)).inv.app A))
  have e : T ≅ I.mapTriangle.obj S :=
    Pretriangulated.Triangle.isoMk _ _ eA eB eC
      (by simp [S, I, Functor.mapTriangle, Pretriangulated.Triangle.mk])
      (by simp [S, I, Functor.mapTriangle, Pretriangulated.Triangle.mk])
      (by simp [S, I, Functor.mapTriangle, Pretriangulated.Triangle.mk])
  have hS : I.mapTriangle.obj S ∈ Pretriangulated.distinguishedTriangles :=
    Pretriangulated.isomorphic_distinguished T hT _ e.symm
  obtain ⟨hF, hG⟩ := hexact S hS
  refine ⟨F.mapTriangle.obj S, G.mapTriangle.obj S, triangleComparison F G t S,
    hF, hG, Iso.refl _, Iso.refl _, Iso.refl _, Iso.refl _, Iso.refl _, Iso.refl _, ?_⟩
  simp [triangleComparison, t, S, G, Functor.mapTriangle, Pretriangulated.Triangle.mk]

end AlgebraicGeometry
