/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.CategoryTheory.PresheafBarResolutionData
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
import Sheaf.CategoryTheory.DerivedCategory.RepresentableSumShriekAcyclic
import Sheaf.CategoryTheory.DerivedCategory.BoundedAboveAcyclicComputation
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import Sheaf.CategoryTheory.DerivedCategory.EverywhereDefinedDerivedFunctors
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift

/-! # Exact bar resolutions and cone connecting maps

Source: Stacks Project, Cohomology on Sites, Tags 08PG and 08PH; Derived Categories,
Tags 0152, 05S9 and 05SU (blueprint: lem-trf-exact-bar-cone-boundaries).

The bar objects and their generator formulas are the published PresheafBar.Resolution
interface. No object is selected from its existence theorem. The independent site,
coefficient and ring universes are retained. The cone and scalar statements use Mathlib's
canonical cone quotient, negative-projection triangle and exact derived scalar restriction.
-/

@[expose] public section

set_option autoImplicit false
universe u v r wE wR uA vA wA
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.PresheafBar

/-- Colimit is additive because it is a left adjoint between additive categories.
Source: Stacks 08PG; (blueprint: lem-trf-exact-bar-cone-boundaries).
This is a direct application of Mathlib's coproduct-preservation criterion. -/
instance colimit_additive {E : Type u} [SmallCategory E] {R : Type r} [CommRing R] :
    (C (E := E) (R := R) : Presheaves.{u, v} E R ⥤ ModuleCat.{max u v} R).Additive :=
  let _ := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (C (E := E) (R := R) : Presheaves.{u, v} E R ⥤ ModuleCat.{max u v} R)
  Functor.additive_of_preservesBinaryBiproducts _

attribute [instance] Resolution.B_additive Resolution.K_additive Resolution.quasiIso

/-- The map identifying the cone of the identity with the kernel of the cone quotient.
In the order (b,a) it is (x,y) ↦ (i(x),y).
Source: Stacks 0152, explicit kernel computation
(blueprint: lem-trf-exact-bar-cone-boundaries). -/
noncomputable def coneKernelι {A : Type uA} [Category.{vA} A] [Abelian A]
    (S : ShortComplex (CochainComplex A ℤ)) :
    CochainComplex.mappingCone (𝟙 S.X₁) ⟶ CochainComplex.mappingCone S.f :=
  CochainComplex.mappingCone.map (𝟙 S.X₁) S.f (𝟙 S.X₁) S.f rfl

/-- The cone quotient is a quasi-isomorphism, its negative-projection roof is the
boundary, its kernel is the explicitly contracted cone of the identity, and cone maps
are natural in all three terms.
Source: Stacks 0152, proof and preceding cone construction
(blueprint: lem-trf-exact-bar-cone-boundaries).

Proof (steps 2--3): the quotient is (b,a) ↦ p(b). Its kernel is (x,y) ↦ (i(x),y),
with differential (dx+y,-dy). The map h(x,y)=(0,x) has dh+hd=1, so the kernel
is acyclic. The homology long exact sequence makes the quotient a quasi-isomorphism.
The cone triangle has third arrow -pr; inversion of the quotient gives exactly
triangleOfSESδ. A diagonal cone map (b,a) ↦ (f_B(b),f_A(a)) commutes with the
quotient by the second square and with -pr by the first square. Canceling the two
invertible quotient maps proves naturality of the boundaries. -/
theorem cone_roof_kernel_naturality
    (A : Type uA) [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact) :
    QuasiIso (CochainComplex.mappingCone.descShortComplex S) ∧
    (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S) ≫
      DerivedCategory.triangleOfSESδ hS =
        DerivedCategory.Q.map (CochainComplex.mappingCone.triangle S.f).mor₃ ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app S.X₁) ∧
    (∃ e : CochainComplex.mappingCone (𝟙 S.X₁) ≅
        kernel (CochainComplex.mappingCone.descShortComplex S),
      e.hom ≫ kernel.ι (CochainComplex.mappingCone.descShortComplex S) = coneKernelι S) ∧
    (∃ h : Homotopy (𝟙 (CochainComplex.mappingCone (𝟙 S.X₁))) 0,
      ∀ i : ℤ, h.hom i (i + (-1)) =
        (CochainComplex.mappingCone.snd (𝟙 S.X₁)).v i i (add_zero i) ≫
          (CochainComplex.mappingCone.inl (𝟙 S.X₁)).v i (i + (-1)) rfl) ∧
    (∀ (T : ShortComplex (CochainComplex A ℤ)) (hT : T.ShortExact) (f : S ⟶ T),
      (CochainComplex.mappingCone.map S.f T.f f.τ₁ f.τ₂ f.comm₁₂.symm ≫
          CochainComplex.mappingCone.descShortComplex T =
        CochainComplex.mappingCone.descShortComplex S ≫ f.τ₃) ∧
      (CochainComplex.mappingCone.map S.f T.f f.τ₁ f.τ₂ f.comm₁₂.symm ≫
          (CochainComplex.mappingCone.triangle T.f).mor₃ =
        (CochainComplex.mappingCone.triangle S.f).mor₃ ≫ f.τ₁⟦(1 : ℤ)⟧') ∧
      (DerivedCategory.triangleOfSESδ hS ≫ (DerivedCategory.Q.map f.τ₁)⟦(1 : ℤ)⟧' =
        DerivedCategory.Q.map f.τ₃ ≫ DerivedCategory.triangleOfSESδ hT)) := by
  sorry

variable {E : Type u} [SmallCategory E] {R : Type r} [CommRing R]
variable [HasDerivedCategory.{wE} (Presheaves.{u, v} E R)]
  [HasDerivedCategory.{wR} (ModuleCat.{max u v} R)]

/-- The actual normalized derived comparison m_F, in diagrammatic composition order.
Source: Stacks 08PG and 0152, resolution comparison
(blueprint: lem-trf-exact-bar-cone-boundaries). -/
noncomputable def boundaryComparison (bar : Resolution.{u, v, r} E R)
    (LC : DerivedCategory (Presheaves.{u, v} E R) ⥤
      DerivedCategory (ModuleCat.{max u v} R))
    (ε : DerivedCategory.Q ⋙ LC ⟶ C.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (F : Presheaves.{u, v} E R) :
    LC.obj (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj F)) ⟶
      DerivedCategory.Q.obj (bar.K.obj F) :=
  inv (LC.map (DerivedCategory.Q.map (bar.a.app F))) ≫ ε.app (bar.B.obj F) ≫
    DerivedCategory.Q.map (bar.b.hom.app F)


/-- The normalization selecting the canonical derived shift structure: ε commutes
with every integer shift, including the localization and termwise comparisons.
Source: Stacks 05SU and 0152 (blueprint: lem-trf-exact-bar-cone-boundaries). -/
def comparisonShiftCompatibility
    (LC : DerivedCategory (Presheaves.{u, v} E R) ⥤
      DerivedCategory (ModuleCat.{max u v} R))
    (ε : DerivedCategory.Q ⋙ LC ⟶ C.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (s : LC.CommShift ℤ) : Prop :=
  ∀ (P : CochainComplex (Presheaves.{u, v} E R) ℤ) (n : ℤ),
    LC.map ((DerivedCategory.Q.commShiftIso n).hom.app P) ≫
      (s.commShiftIso n).hom.app (DerivedCategory.Q.obj P) ≫ (ε.app P)⟦n⟧' =
    ε.app (P⟦n⟧) ≫
      ((C.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).commShiftIso n).hom.app P

/-- Exactness and the canonical connecting-map comparison for the explicit bar resolution.
Source: Stacks 08PG, 0152, 05S9 and 05SU
(blueprint: lem-trf-exact-bar-cone-boundaries).

Proof (steps 1, 4--7): evaluate at U_0 and take direct sums of the coefficient short
exact sequences. Finite-support lifting proves exactness for B and K in each degree.
The augmentations are natural, including their degree-zero coefficient formula.
The bounded-above acyclic-computation theorem applies to B(F), since it is zero above
zero and its terms are left C-acyclic. Thus ε_B is invertible. The augmentation is a
quasi-isomorphism and b is the identity-on-coefficients colimit isomorphism, so their
specified composite m is invertible. The pointwise Kan bridge and assembly of derived
functors identify ε with the universal counit. The coherent-shift theorem therefore
supplies the unique normalized shift structure s with the displayed compatibility.
For T=Cone(B(i)), naturality of ε at q:T→B(F'') and r=-pr:T→B(F')[1] gives
Q(Cq) ε_T = ε_(B(F'')) LC(Qq) and Q(Cr) ε_T = ε_(B(F')[1]) LC(Qr).
Invert q and Cq using the cone-kernel computation. Shift compatibility then gives
δ_(CB) ε_(B(F'')) = ε_(B(F'))[1] s LC(δ_B). Apply cone naturality to the
augmentation sequence, multiply by the inverse augmented comparisons and the shifted
b, and obtain exactly the boundary equation below. No uniqueness of a triangulated
boundary and no exactness of colimit on arbitrary presheaf sequences is used. -/
theorem exact_bar_boundary_comparison (bar : Resolution.{u, v, r} E R)
    (LC : DerivedCategory (Presheaves.{u, v} E R) ⥤
      DerivedCategory (ModuleCat.{max u v} R))
    (ε : DerivedCategory.Q ⋙ LC ⟶ C.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [LC.CommShift ℤ] [LC.IsTriangulated]
    (hLC : LC.IsLeftDerivedFunctor ε
      (HomologicalComplex.quasiIso (Presheaves.{u, v} E R) (.up ℤ)))
    (hdefined : ∀ X : HomotopyCategory (Presheaves.{u, v} E R) (.up ℤ),
      (C.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).IsTriangulatedLeftDerivedDefinedAt
        (HomotopyCategory.quasiIso (Presheaves.{u, v} E R) (.up ℤ))
        ⟨⟨⟨(HomotopyCategory.quasiIso_saturated_triangulated (Presheaves.{u, v} E R)).1,
            (HomotopyCategory.quasiIso_saturated_triangulated
              (Presheaves.{u, v} E R)).2.1⟩,
          fun _ _ _ _ h g f ↦ (HomotopyCategory.quasiIso_saturated_triangulated
            (Presheaves.{u, v} E R)).2.2.2.1 _ _ _ _ g h f⟩,
          (HomotopyCategory.quasiIso_saturated_triangulated
            (Presheaves.{u, v} E R)).2.2.1⟩ X)
    (hacyclic : ∀ (F : Presheaves.{u, v} E R) (i : ℤ),
      IsIso (ε.app ((CochainComplex.singleFunctor _ 0).obj ((bar.B.obj F).X i)))) :
    (∀ F : Presheaves.{u, v} E R, IsIso (boundaryComparison bar LC ε F)) ∧
    ∃ s : LC.CommShift ℤ, comparisonShiftCompatibility LC ε s ∧
      ∀ (S : ShortComplex (Presheaves.{u, v} E R))
        (hS : ∀ V : E,
          (S.map ((evaluation Eᵒᵖ (ModuleCat.{max u v} R)).obj (op V))).ShortExact),
        (∀ i : ℤ, ((S.map bar.B).map
          (HomologicalComplex.eval (Presheaves.{u, v} E R) (.up ℤ) i)).ShortExact) ∧
        (∀ i : ℤ, ((S.map bar.K).map
          (HomologicalComplex.eval (ModuleCat.{max u v} R) (.up ℤ) i)).ShortExact) ∧
        ∃ h₀ : (S.map (CochainComplex.singleFunctor _ 0)).ShortExact,
          LC.map (DerivedCategory.triangleOfSESδ h₀) ≫
              (s.commShiftIso (1 : ℤ)).hom.app
                (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj S.X₁)) ≫
              (boundaryComparison bar LC ε S.X₁)⟦(1 : ℤ)⟧' =
            boundaryComparison bar LC ε S.X₃ ≫
              DerivedCategory.triangleOfSESδ (bar.K_shortExact S hS) := by
  sorry

/-- Ordinary colimit reindexing on complexes, defined by the colimit cocone.
Source: Stacks 08PH (blueprint: lem-trf-exact-bar-cone-boundaries).
This generalizes the same-bound helper categoryBarColimitReindex to independent ring
and coefficient universes, using the identical Mathlib colimit.pre construction. -/
noncomputable def complexColimitReindex {D : Type u} [SmallCategory D] (u : E ⥤ D) :
    ((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{max u v} R)).obj u.op).mapHomologicalComplex
        (.up ℤ) ⋙ C.mapHomologicalComplex (.up ℤ) ⟶
      (C (E := D) (R := R)).mapHomologicalComplex (.up ℤ) :=
  NatTrans.mapHomologicalComplex
    (F := ((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{max u v} R)).obj u.op) ⋙ C)
    (G := C (E := D) (R := R))
    { app := fun F ↦ colimit.pre F u.op
      naturality := fun _ _ t ↦ (colimit.pre_map t u.op).symm } (.up ℤ)

/-- The map on K-complexes induced by any supplied augmentation-compatible bar map.
All three factors are canonical: b_E inverse, ordinary colimit and its reindexing
cocone, and b_D. Source: Stacks 08PH and 0152
(blueprint: lem-trf-exact-bar-cone-boundaries). -/
noncomputable def reindexedBarMap {D : Type u} [SmallCategory D] (u : E ⥤ D)
    (bar : Resolution.{u, v, r} E R) (barD : Resolution.{u, v, r} D R)
    (F : Presheaves.{u, v} E R) (G : Presheaves.{u, v} D R)
    (t : bar.B.obj F ⟶
      (((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{max u v} R)).obj u.op).mapHomologicalComplex
        (.up ℤ)).obj (barD.B.obj G)) : bar.K.obj F ⟶ barD.K.obj G :=
  bar.b.inv.app F ≫ (C.mapHomologicalComplex (.up ℤ)).map t ≫
    (complexColimitReindex u).app (barD.B.obj G) ≫ barD.b.hom.app G

/-- Every compatible map of bar-resolution sequences, including one to a precomposed
sequence, induces a commuting boundary square after colimit. The output maps are the
specified colimit-cocone maps, not independently chosen maps on homology.
Source: Stacks 08PH and 0152 (blueprint: lem-trf-exact-bar-cone-boundaries).

Proof (step 8): apply ordinary colimit to each of the three supplied chain maps, then
compose with the target cocone. Its naturality gives a morphism of the exact K-sequences.
The diagonal cone map commutes with q and -pr, hence its localized boundary square
commutes by cone_roof_kernel_naturality. The final conjunct gives the square after
conjugation by the four
isomorphisms. Substitute the canonical comparisons of the preceding theorem to obtain
the derived boundary square, including its canonical shift comparisons. This
argument works for arbitrary augmentation-compatible maps, rather than only the map
specified on the usual reindexing generators. It does not apply u_! to an arbitrary
short exact sequence, or assume that colimit preserves arbitrary quasi-isomorphisms. -/
theorem reindexed_bar_boundary_naturality {D : Type u} [SmallCategory D] (u : E ⥤ D)
    (bar : Resolution.{u, v, r} E R) (barD : Resolution.{u, v, r} D R)
    (S : ShortComplex (Presheaves.{u, v} E R))
    (T : ShortComplex (Presheaves.{u, v} D R))
    (hS : ∀ V : E,
      (S.map ((evaluation Eᵒᵖ (ModuleCat.{max u v} R)).obj (op V))).ShortExact)
    (hT : ∀ V : D,
      (T.map ((evaluation Dᵒᵖ (ModuleCat.{max u v} R)).obj (op V))).ShortExact)
    (f : S.map bar.B ⟶ (T.map barD.B).map
      (((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{max u v} R)).obj u.op).mapHomologicalComplex
        (.up ℤ)))
    (t₁ : S.X₁ ⟶ u.op ⋙ T.X₁) (t₂ : S.X₂ ⟶ u.op ⋙ T.X₂)
    (t₃ : S.X₃ ⟶ u.op ⋙ T.X₃)
    (ha₁ : ∀ i : ℤ,
      f.τ₁.f i ≫ Functor.whiskerLeft u.op ((barD.a.app T.X₁).f i) ≫
          ((HomologicalComplex.singleMapHomologicalComplex
            ((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{max u v} R)).obj u.op)
            (.up ℤ) 0).hom.app T.X₁).f i =
        (bar.a.app S.X₁).f i ≫ ((CochainComplex.singleFunctor _ 0).map t₁).f i)
    (ha₂ : ∀ i : ℤ,
      f.τ₂.f i ≫ Functor.whiskerLeft u.op ((barD.a.app T.X₂).f i) ≫
          ((HomologicalComplex.singleMapHomologicalComplex
            ((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{max u v} R)).obj u.op)
            (.up ℤ) 0).hom.app T.X₂).f i =
        (bar.a.app S.X₂).f i ≫ ((CochainComplex.singleFunctor _ 0).map t₂).f i)
    (ha₃ : ∀ i : ℤ,
      f.τ₃.f i ≫ Functor.whiskerLeft u.op ((barD.a.app T.X₃).f i) ≫
          ((HomologicalComplex.singleMapHomologicalComplex
            ((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{max u v} R)).obj u.op)
            (.up ℤ) 0).hom.app T.X₃).f i =
        (bar.a.app S.X₃).f i ≫ ((CochainComplex.singleFunctor _ 0).map t₃).f i) :
    (∃ k : S.map bar.K ⟶ T.map barD.K,
      k.τ₁ = reindexedBarMap u bar barD S.X₁ T.X₁ f.τ₁ ∧
      k.τ₂ = reindexedBarMap u bar barD S.X₂ T.X₂ f.τ₂ ∧
      k.τ₃ = reindexedBarMap u bar barD S.X₃ T.X₃ f.τ₃) ∧
    (DerivedCategory.triangleOfSESδ (bar.K_shortExact S hS) ≫
        (DerivedCategory.Q.map (reindexedBarMap u bar barD S.X₁ T.X₁ f.τ₁))⟦(1 : ℤ)⟧' =
      DerivedCategory.Q.map (reindexedBarMap u bar barD S.X₃ T.X₃ f.τ₃) ≫
        DerivedCategory.triangleOfSESδ (barD.K_shortExact T hT)) ∧
    (∀ (X₁ X₃ Y₁ Y₃ : DerivedCategory (ModuleCat.{max u v} R))
      (m₁ : X₁ ≅ DerivedCategory.Q.obj (bar.K.obj S.X₁))
      (m₃ : X₃ ≅ DerivedCategory.Q.obj (bar.K.obj S.X₃))
      (n₁ : Y₁ ≅ DerivedCategory.Q.obj (barD.K.obj T.X₁))
      (n₃ : Y₃ ≅ DerivedCategory.Q.obj (barD.K.obj T.X₃)),
      (m₃.hom ≫ DerivedCategory.triangleOfSESδ (bar.K_shortExact S hS) ≫
          m₁.inv⟦(1 : ℤ)⟧') ≫
        (m₁.hom ≫ DerivedCategory.Q.map (reindexedBarMap u bar barD S.X₁ T.X₁ f.τ₁) ≫
          n₁.inv)⟦(1 : ℤ)⟧' =
      (m₃.hom ≫ DerivedCategory.Q.map (reindexedBarMap u bar barD S.X₃ T.X₃ f.τ₃) ≫
          n₃.inv) ≫
        (n₃.hom ≫ DerivedCategory.triangleOfSESδ (barD.K_shortExact T hT) ≫
          n₁.inv⟦(1 : ℤ)⟧')) := by
  sorry

end CategoryTheory.PresheafBar

namespace CategoryTheory

/-- Scalar restriction preserves finite limits at an arbitrary module universe.
Source: Stacks 0152, exact scalar restriction; Mathlib's direct limit comparison
(blueprint: lem-trf-exact-bar-cone-boundaries). -/
noncomputable instance scalarRestriction_preservesFiniteLimits
    {R₀ : Type uA} [CommRing R₀] {R : Type r} [CommRing R] (ρ : R₀ →+* R) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{v} ρ) where
  preservesFiniteLimits _ _ _ :=
    { preservesLimit := ModuleCat.preservesLimit_restrictScalars ρ _ }

/-- Scalar restriction preserves finite colimits at an arbitrary module universe.
Source: Stacks 0152, exact scalar restriction; Mathlib's direct colimit comparison
(blueprint: lem-trf-exact-bar-cone-boundaries). -/
instance scalarRestriction_preservesFiniteColimits
    {R₀ : Type uA} [CommRing R₀] {R : Type r} [CommRing R] (ρ : R₀ →+* R) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{v} ρ) where
  preservesFiniteColimits _ _ _ :=
    { preservesColimit := ModuleCat.preservesColimit_restrictScalars ρ _ }

/-- Exact scalar restriction preserves short exact complexes, cone roofs, their
connecting maps, and all equalities between maps and derived comparisons.
Source: Stacks 0152, exact restriction of the explicit cone construction
(blueprint: lem-trf-exact-bar-cone-boundaries).

Proof (step 9): restriction changes only scalar actions; kernels, images, quotients
and sums have the identical underlying groups and maps. It is therefore exact and
preserves homology and quasi-isomorphisms. Its termwise functor takes the cone to
the cone of the restricted injection, with q and -pr unchanged on underlying groups.
It takes the homotopy (0,x) to the identical contraction. Localization then takes
inverse Qq to inverse Q(Res q), giving the displayed boundary formula with the
canonical shift and localization comparisons. Functoriality preserves every equality,
in particular both the boundary comparison and each naturality square. No flatness
or preservation of projectives by scalar restriction is required. -/
theorem scalarRestriction_cone_boundaries
    {R₀ : Type uA} [CommRing R₀] {R : Type r} [CommRing R] (ρ : R₀ →+* R)
    [HasDerivedCategory.{wR} (ModuleCat.{v} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{v} R₀)]
    (S : ShortComplex (CochainComplex (ModuleCat.{v} R) ℤ)) (hS : S.ShortExact) :
    ∃ hRes : (S.map ((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ))).ShortExact,
      QuasiIso (((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCone.descShortComplex S)) ∧
      ((ModuleCat.restrictScalars ρ).mapDerivedCategory.map
          (DerivedCategory.triangleOfSESδ hS) =
        (ModuleCat.restrictScalars ρ).mapDerivedCategoryFactors.hom.app S.X₃ ≫
          DerivedCategory.triangleOfSESδ hRes ≫
          ((ModuleCat.restrictScalars ρ).mapDerivedCategoryFactors.inv.app S.X₁)⟦(1 : ℤ)⟧' ≫
          ((ModuleCat.restrictScalars ρ).mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app
            (DerivedCategory.Q.obj S.X₁)) ∧
      ((CochainComplex.mappingCone.mapHomologicalComplexIso S.f
          (ModuleCat.restrictScalars ρ)).hom ≫
          CochainComplex.mappingCone.descShortComplex
            (S.map ((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ))) =
        ((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)).map
          (CochainComplex.mappingCone.descShortComplex S)) ∧
      (((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)).map
          (CochainComplex.mappingCone.triangle S.f).mor₃ ≫
          (((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)).commShiftIso
            (1 : ℤ)).hom.app S.X₁ =
        (CochainComplex.mappingCone.mapHomologicalComplexIso S.f
          (ModuleCat.restrictScalars ρ)).hom ≫
          (CochainComplex.mappingCone.triangle
            (((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)).map S.f)).mor₃) := by
  sorry

end CategoryTheory
