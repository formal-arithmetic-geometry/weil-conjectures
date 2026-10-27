/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.RingTheory.TorCoefficientModule
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.RingTheory.RegularSequenceConormal
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular
import WeilConjectures.RingTheory.KoszulNormalizedProjectiveResolution
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Normalized Tor of a regular quotient with module coefficients

Source: Stacks Project, Tags 062I, 062F, 0623, 00LY, 00LZ, 00DM, 00HD and 02KH;
the coefficient, presentation and flat-base-change assembly is agent-supplied.
(blueprint: lem-sfb-regular-quotient-coefficient-tor).

The auxiliary definitions only spell out the objects and compatibility clauses of
this statement. Tor is Mathlib's `Tor'`, with the quotient action induced by
coefficient multiplication. The transport predicate specifies the map on arbitrary
resolution cycles, independently of the exterior comparison to be constructed.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry

/-- Ideals in the assertion, including its separately stipulated unit ideal.
Source: Stacks, Tags 062I and 00LF, with the node's zero-quotient extension.
(blueprint: lem-sfb-regular-quotient-coefficient-tor). -/
def IsRegularQuotientCoefficientIdeal (A : Type u) [CommRing A] (I : Ideal A) : Prop :=
  I = ⊤ ∨ ∃ (r : ℕ) (f : Fin r → A), Ideal.span (Set.range f) = I ∧
    RingTheory.Sequence.IsRegular A (List.ofFn f)

/-- The underlying ambient-ring Tor functor, restricted to quotient modules.
Source: Stacks, Tags 00LY and 00LZ.
(blueprint: lem-sfb-regular-quotient-coefficient-tor). -/
noncomputable abbrev coefficientTorFunctor (A : Type u) [CommRing A] (I : Ideal A)
    (q : ℕ) : ModuleCat.{u} (A ⧸ I) ⥤ ModuleCat.{u} A :=
  ModuleCat.restrictScalars (Ideal.Quotient.mk I) ⋙
    (Tor' (ModuleCat.{u} A) q).obj (ModuleCat.of A (A ⧸ I))

/-- The canonical quotient action: apply Tor to multiplication on the coefficient
module. This extends the existing coefficient-algebra action to module coefficients.
Source: Stacks, Tag 00M7 (1).
(blueprint: lem-sfb-regular-quotient-coefficient-tor). -/
noncomputable def coefficientTorAction (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{u} (A ⧸ I)) (q : ℕ) :
    (A ⧸ I) →+* End ((forget₂ (ModuleCat.{u} A) AddCommGrpCat).obj
      ((coefficientTorFunctor A I q).obj M)) :=
  let F := coefficientTorFunctor A I q ⋙ forget₂ (ModuleCat.{u} A) AddCommGrpCat
  { __ := (Functor.mapEnd M F).comp
      (((ModuleCat.endRingEquiv M).symm.toRingHom.comp
        (Module.toModuleEnd (A ⧸ I) M)).toMonoidHom)
    __ := (F.mapAddHom).comp
      (((ModuleCat.endRingEquiv M).symm.toRingHom.comp
        (Module.toModuleEnd (A ⧸ I) M)).toAddMonoidHom) }

/-- The actual ambient Tor group equipped with its specified quotient-module action.
Source: Stacks, Tags 00LY and 00M7.
(blueprint: lem-sfb-regular-quotient-coefficient-tor). -/
noncomputable def coefficientTor (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{u} (A ⧸ I)) (q : ℕ) : ModuleCat.{u} (A ⧸ I) :=
  ModuleCat.mkOfSMul (coefficientTorAction A I M q)

/-- The exterior-conormal tensor coefficient module in the assertion.
Source: Stacks, Tags 062I and 00DM; node's coefficient construction.
(blueprint: lem-sfb-regular-quotient-coefficient-tor). -/
noncomputable abbrev coefficientTorExterior (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{u} (A ⧸ I)) (q : ℕ) : ModuleCat.{u} (A ⧸ I) :=
  ModuleCat.of (A ⧸ I) ((⋀[A ⧸ I]^q I.Cotangent) ⊗[A ⧸ I] M)

/-- Tensoring a resolution complex with the specified coefficient module.
Source: Stacks, Tags 00LY and 00LZ.
(blueprint: lem-sfb-regular-quotient-coefficient-tor). -/
noncomputable abbrev coefficientTorTensor (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{u} (A ⧸ I)) :
    ChainComplex (ModuleCat.{u} A) ℕ ⥤ ChainComplex (ModuleCat.{u} A) ℕ :=
  (tensorRight ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M)).mapHomologicalComplex
    (.down ℕ)

/-- The canonical augmented-resolution identification of Tor.
Source: Stacks, Tag 00LZ; Mathlib `ProjectiveResolution.isoLeftDerivedObj`.
(blueprint: lem-sfb-regular-quotient-coefficient-tor). -/
noncomputable abbrev coefficientTorResolutionIso (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{u} (A ⧸ I)) (q : ℕ)
    (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I))) :=
  P.isoLeftDerivedObj (tensorRight
    ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M)) q

/-- Koszul normalization for every regular generating tuple and every
augmentation-preserving comparison into every projective resolution. Existence of
the displayed cycle is part of the predicate, including in degree zero.
Source: Stacks, Tags 0623, 062I and 00LZ; node proof steps 1--5.
(blueprint: lem-sfb-regular-quotient-coefficient-tor). -/
def IsNormalizedCoefficientTor (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{u} (A ⧸ I)) (q : ℕ)
    (c : coefficientTorExterior A I M q ≅ coefficientTor A I M q) : Prop :=
  ∀ (r : ℕ) (g : Fin r → I),
    Ideal.span (Set.range (fun j ↦ (g j : A))) = I →
    RingTheory.Sequence.IsRegular A (List.ofFn (fun j ↦ (g j : A))) →
    ∀ (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)))
      (a : ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)) ⟶ P.complex),
      a.f 0 ≫ P.π.f 0 = ModuleCat.ofHom (I.mkQ.comp
        (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap) →
      ∀ (v : Fin q → (Fin r →₀ A)) (m : M),
        ∃ z : ((coefficientTorTensor A I M).obj
            (ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)))).cycles q,
          ((coefficientTorTensor A I M).obj
              (ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)))).iCycles q z =
            (exteriorPower.ιMulti A q v) ⊗ₜ[A]
              (@id ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M) m) ∧
          (coefficientTorResolutionIso A I M q P).hom
              (c.hom ((exteriorPower.ιMulti (A ⧸ I) q
                (fun j ↦ I.toCotangent (Finsupp.linearCombination A g (v j))))
                  ⊗ₜ[A ⧸ I] m)) =
            (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.down ℕ) q).map
              ((coefficientTorTensor A I M).map a)
                (((coefficientTorTensor A I M).obj
                  (ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)))).homologyπ q z)

/-- Resolution-cycle specification of change of the ambient ring and coefficients.
The quotient map and coefficient map are given explicitly; no exterior comparison
is used to define this predicate. Quantification over all augmented resolutions
fixes the canonical Tor transport and its comparison-map independence.
Source: Stacks, Tag 00LZ; flat base change in Tag 02KH, node proof steps 6--8.
(blueprint: lem-sfb-regular-quotient-coefficient-tor). -/
def IsCoefficientTorTransport (A A' : Type u) [CommRing A] [CommRing A']
    (I : Ideal A) (J : Ideal A') (φ : A →+* A') (ψ : (A ⧸ I) →+* (A' ⧸ J))
    (M : ModuleCat.{u} (A ⧸ I)) (N : ModuleCat.{u} (A' ⧸ J))
    (u : M ⟶ (ModuleCat.restrictScalars ψ).obj N) (q : ℕ)
    (t : coefficientTor A I M q ⟶
      (ModuleCat.restrictScalars ψ).obj (coefficientTor A' J N q)) : Prop :=
  ∀ (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)))
    (Q : ProjectiveResolution (ModuleCat.of A' (A' ⧸ J))),
    ∃ (a : P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
          (.down ℕ)).obj Q.complex)
      (k : (coefficientTorTensor A I M).obj P.complex ⟶
        ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.down ℕ)).obj
          ((coefficientTorTensor A' J N).obj Q.complex)),
      (∀ x : P.complex.X 0, Q.π.f 0 (a.f 0 x) = ψ (P.π.f 0 x)) ∧
      (∀ (j : ℕ) (x : P.complex.X j) (m : M),
        k.f j (x ⊗ₜ[A]
          (@id ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M) m)) =
          (@id (Q.complex.X j) (a.f j x)) ⊗ₜ[A']
            (@id ((ModuleCat.restrictScalars (Ideal.Quotient.mk J)).obj N) (u m))) ∧
      ∀ (z : ((coefficientTorTensor A I M).obj P.complex).cycles q)
        (w : ((coefficientTorTensor A' J N).obj Q.complex).cycles q),
        ((coefficientTorTensor A' J N).obj Q.complex).iCycles q w =
          k.f q (((coefficientTorTensor A I M).obj P.complex).iCycles q z) →
        (coefficientTorResolutionIso A' J N q Q).hom
            (t ((coefficientTorResolutionIso A I M q P).inv
              (((coefficientTorTensor A I M).obj P.complex).homologyπ q z))) =
          ((coefficientTorTensor A' J N).obj Q.complex).homologyπ q w

/-- Composition of semilinear morphisms, using the canonical restriction associator.
Source: Stacks, Tags 00CV and 00LZ; node's composition convention.
(blueprint: lem-sfb-regular-quotient-coefficient-tor). -/
noncomputable def coefficientTorTransportComp {B C D : Type u}
    [CommRing B] [CommRing C] [CommRing D] (ψ : B →+* C) (χ : C →+* D)
    {X : ModuleCat.{u} B} {Y : ModuleCat.{u} C} {Z : ModuleCat.{u} D}
    (f : X ⟶ (ModuleCat.restrictScalars ψ).obj Y)
    (g : Y ⟶ (ModuleCat.restrictScalars χ).obj Z) :
    X ⟶ (ModuleCat.restrictScalars (χ.comp ψ)).obj Z :=
  f ≫ (ModuleCat.restrictScalars ψ).map g ≫
    (ModuleCat.restrictScalarsComp ψ χ).inv.app Z

/-- The image of an ideal element under the specified extension of ideals.
Source: Stacks, Tag 00HD; node proof step 6.
(blueprint: lem-sfb-regular-quotient-coefficient-tor). -/
def coefficientTorIdealImage {A A' : Type u} [CommRing A] [CommRing A']
    (I : Ideal A) (J : Ideal A') (φ : A →+* A') (h : I.map φ = J) (x : I) : J :=
  ⟨φ x, (Ideal.map_le_iff_le_comap.mp (le_of_eq h)) x.property⟩

/-- Generator formula specifying the canonical conormal scalar-extension map.
Source: Stacks, Tag 062I and flat tensor exactness, Tag 00HD; node proof step 6.
(blueprint: lem-sfb-regular-quotient-coefficient-tor). -/
def IsCoefficientConormalBaseChange (A A' : Type u) [CommRing A] [CommRing A']
    (I : Ideal A) (J : Ideal A') (φ : A →+* A')
    (ψ : (A ⧸ I) →+* (A' ⧸ J)) (hIJ : I.map φ = J)
    (e : (ModuleCat.extendScalars ψ).obj (ModuleCat.of (A ⧸ I) I.Cotangent) ≅
      ModuleCat.of (A' ⧸ J) J.Cotangent) : Prop :=
  ∀ x : I, e.hom ((1 : A' ⧸ J) ⊗ₜ[A ⧸ I, ψ] (I.toCotangent x)) =
    J.toCotangent (coefficientTorIdealImage I J φ hIJ x)

/-- The full assertion packaged as a family, so that choices are made simultaneously
and the flat-base-change and coefficient-naturality squares have actual common maps.
Its Tor transports are specified independently on arbitrary resolution cycles.
The pure-tensor formulas characterize the canonical conormal and exterior base-change
maps; uniqueness forces their identity and associativity compatibilities.
Source: Stacks, Tags 062I, 062F, 0623, 00LY, 00LZ, 00DM, 00HD and 02KH;
node proof steps 1--9, including its stipulated zero-module extensions.
(blueprint: lem-sfb-regular-quotient-coefficient-tor). -/
structure RegularQuotientCoefficientTorSystem where
  /-- The actual quotient-linear isomorphisms, for all coefficient modules and degrees. -/
  comparison : ∀ (A : Type u) [CommRing A] (I : Ideal A),
    IsRegularQuotientCoefficientIdeal A I → ∀ (M : ModuleCat.{u} (A ⧸ I)) (q : ℕ),
      coefficientTorExterior A I M q ≅ coefficientTor A I M q
  /-- Every regular presentation and every augmented comparison computes the same map. -/
  normalized : ∀ (A : Type u) [CommRing A] (I : Ideal A)
    (h : IsRegularQuotientCoefficientIdeal A I) (M : ModuleCat.{u} (A ⧸ I)) (q : ℕ),
    IsNormalizedCoefficientTor A I M q (comparison A I h M q)
  /-- Normalization determines the comparison, including for the unit ideal. -/
  unique : ∀ (A : Type u) [CommRing A] (I : Ideal A)
    (h : IsRegularQuotientCoefficientIdeal A I) (M : ModuleCat.{u} (A ⧸ I)) (q : ℕ)
    (c : coefficientTorExterior A I M q ≅ coefficientTor A I M q),
    IsNormalizedCoefficientTor A I M q c → c = comparison A I h M q
  /-- Naturality in an arbitrary quotient-linear coefficient morphism. -/
  naturality : ∀ (A : Type u) [CommRing A] (I : Ideal A)
    (h : IsRegularQuotientCoefficientIdeal A I) (M N : ModuleCat.{u} (A ⧸ I))
    (f : M ⟶ N) (q : ℕ) (x : coefficientTorExterior A I M q),
    (coefficientTorFunctor A I q).map f ((comparison A I h M q).hom x) =
      (comparison A I h N q).hom
        (TensorProduct.map (LinearMap.id : (⋀[A ⧸ I]^q I.Cotangent) →ₗ[A ⧸ I] _)
          f.hom x)
  /-- The coefficient action restricts to the original ambient-ring action on Tor. -/
  scalar_restriction : ∀ (A : Type u) [CommRing A] (I : Ideal A)
    (_h : IsRegularQuotientCoefficientIdeal A I) (M : ModuleCat.{u} (A ⧸ I)) (q : ℕ)
    (a : A) (x : coefficientTor A I M q),
    Ideal.Quotient.mk I a • x = a • @id ((coefficientTorFunctor A I q).obj M) x
  /-- The specified conormal generator classes form a basis. -/
  conormal_basis : ∀ (A : Type u) [CommRing A] (I : Ideal A)
    (r : ℕ) (f : Fin r → A) (hf : Ideal.span (Set.range f) = I),
    RingTheory.Sequence.IsRegular A (List.ofFn f) →
    ∃ b : Module.Basis (Fin r) (A ⧸ I) I.Cotangent,
      ∀ j, b j = I.toCotangent ⟨f j, hf ▸ Ideal.subset_span ⟨j, rfl⟩⟩
  /-- The image tuple stays regular whenever the base-changed quotient is nonzero. -/
  image_regular : ∀ (A A' : Type u) [CommRing A] [CommRing A']
    (I : Ideal A) (J : Ideal A') (φ : A →+* A') (r : ℕ) (f : Fin r → A),
    RingHom.Flat φ → I.map φ = J → Ideal.span (Set.range f) = I →
    RingTheory.Sequence.IsRegular A (List.ofFn f) → Nontrivial (A' ⧸ J) →
    RingTheory.Sequence.IsRegular A' (List.ofFn (fun j ↦ φ (f j)))
  /-- Both sides vanish above the length, without a flatness hypothesis on M. -/
  above_length : ∀ (A : Type u) [CommRing A] (I : Ideal A)
    (r : ℕ) (f : Fin r → A), Ideal.span (Set.range f) = I →
    RingTheory.Sequence.IsRegular A (List.ofFn f) →
    ∀ (M : ModuleCat.{u} (A ⧸ I)) (q : ℕ), r < q →
      IsZero (coefficientTorExterior A I M q) ∧ IsZero (coefficientTor A I M q)
  /-- All coefficient modules and both sides are zero for the separately extended case. -/
  unit_ideal : ∀ (A : Type u) [CommRing A] (I : Ideal A), I = ⊤ →
    ∀ (M : ModuleCat.{u} (A ⧸ I)) (q : ℕ), IsZero M ∧
      IsZero (coefficientTorExterior A I M q) ∧ IsZero (coefficientTor A I M q)
  /-- The canonical flat conormal comparison, characterized on ideal classes. -/
  conormal_baseChange : ∀ (A A' : Type u) [CommRing A] [CommRing A']
    (I : Ideal A) (J : Ideal A') (φ : A →+* A')
    (ψ : (A ⧸ I) →+* (A' ⧸ J)) (hIJ : I.map φ = J),
    RingHom.Flat φ → IsRegularQuotientCoefficientIdeal A I →
    (∀ a : A, ψ (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J (φ a)) →
    ∃! e : (ModuleCat.extendScalars ψ).obj (ModuleCat.of (A ⧸ I) I.Cotangent) ≅
        ModuleCat.of (A' ⧸ J) J.Cotangent,
      IsCoefficientConormalBaseChange A A' I J φ ψ hIJ e
  /-- Identity conormal transport is the usual tensor identity. -/
  conormal_identity : ∀ (A : Type u) [CommRing A] (I : Ideal A)
    (hII : I.map (RingHom.id A) = I), IsRegularQuotientCoefficientIdeal A I →
    IsCoefficientConormalBaseChange A A I I (RingHom.id A) (RingHom.id (A ⧸ I)) hII
      ((ModuleCat.extendScalarsId (A ⧸ I)).app (ModuleCat.of (A ⧸ I) I.Cotangent))
  /-- Conormal transport respects composition under the tensor associator. -/
  conormal_composition : ∀ (A A' A'' : Type u)
    [CommRing A] [CommRing A'] [CommRing A''] (I : Ideal A) (J : Ideal A') (L : Ideal A'')
    (φ : A →+* A') (φ' : A' →+* A'')
    (ψ : (A ⧸ I) →+* (A' ⧸ J)) (ψ' : (A' ⧸ J) →+* (A'' ⧸ L))
    (hIJ : I.map φ = J) (hJL : J.map φ' = L) (hIL : I.map (φ'.comp φ) = L),
    RingHom.Flat φ → RingHom.Flat φ' →
    (∀ a : A, ψ (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J (φ a)) →
    (∀ a : A', ψ' (Ideal.Quotient.mk J a) = Ideal.Quotient.mk L (φ' a)) →
    IsRegularQuotientCoefficientIdeal A I →
    ∀ (e : (ModuleCat.extendScalars ψ).obj (ModuleCat.of (A ⧸ I) I.Cotangent) ≅
        ModuleCat.of (A' ⧸ J) J.Cotangent)
      (e' : (ModuleCat.extendScalars ψ').obj (ModuleCat.of (A' ⧸ J) J.Cotangent) ≅
        ModuleCat.of (A'' ⧸ L) L.Cotangent)
      (e'' : (ModuleCat.extendScalars (ψ'.comp ψ)).obj
          (ModuleCat.of (A ⧸ I) I.Cotangent) ≅ ModuleCat.of (A'' ⧸ L) L.Cotangent),
      IsCoefficientConormalBaseChange A A' I J φ ψ hIJ e →
      IsCoefficientConormalBaseChange A' A'' J L φ' ψ' hJL e' →
      IsCoefficientConormalBaseChange A A'' I L (φ'.comp φ) (ψ'.comp ψ) hIL e'' →
      e''.hom = (ModuleCat.extendScalarsComp ψ ψ').hom.app
          (ModuleCat.of (A ⧸ I) I.Cotangent) ≫
        (ModuleCat.extendScalars ψ').map e.hom ≫ e'.hom
  /-- Existence and uniqueness of canonical transport, with arbitrary coefficient maps. -/
  transport : ∀ (A A' : Type u) [CommRing A] [CommRing A']
    (I : Ideal A) (J : Ideal A') (φ : A →+* A')
    (ψ : (A ⧸ I) →+* (A' ⧸ J)), RingHom.Flat φ → I.map φ = J →
    (∀ a : A, ψ (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J (φ a)) →
    IsRegularQuotientCoefficientIdeal A I → IsRegularQuotientCoefficientIdeal A' J →
    ∀ (M : ModuleCat.{u} (A ⧸ I)) (N : ModuleCat.{u} (A' ⧸ J))
      (u : M ⟶ (ModuleCat.restrictScalars ψ).obj N) (q : ℕ),
      ∃! t : coefficientTor A I M q ⟶
          (ModuleCat.restrictScalars ψ).obj (coefficientTor A' J N q),
        IsCoefficientTorTransport A A' I J φ ψ M N u q t
  /-- The base-change/naturality square on the generating conormal wedge tensors. -/
  transport_comparison : ∀ (A A' : Type u) [CommRing A] [CommRing A']
    (I : Ideal A) (J : Ideal A') (φ : A →+* A')
    (ψ : (A ⧸ I) →+* (A' ⧸ J)) (hIJ : I.map φ = J), RingHom.Flat φ →
    (∀ a : A, ψ (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J (φ a)) →
    ∀ (h : IsRegularQuotientCoefficientIdeal A I)
      (h' : IsRegularQuotientCoefficientIdeal A' J)
      (M : ModuleCat.{u} (A ⧸ I)) (N : ModuleCat.{u} (A' ⧸ J))
      (u : M ⟶ (ModuleCat.restrictScalars ψ).obj N) (q : ℕ)
      (t : coefficientTor A I M q ⟶
        (ModuleCat.restrictScalars ψ).obj (coefficientTor A' J N q)),
      IsCoefficientTorTransport A A' I J φ ψ M N u q t →
      ∀ (g : Fin q → I) (m : M),
        t ((comparison A I h M q).hom
          ((exteriorPower.ιMulti (A ⧸ I) q (fun j ↦ I.toCotangent (g j)))
            ⊗ₜ[A ⧸ I] m)) =
          (comparison A' J h' N q).hom
            ((exteriorPower.ιMulti (A' ⧸ J) q
              (fun j ↦ J.toCotangent (coefficientTorIdealImage I J φ hIJ (g j))))
                ⊗ₜ[A' ⧸ J] (u m))
  /-- For the scalar-extension coefficient module, both canonical vertical maps
  are invertible and the full B'-linear base-change square commutes. -/
  flat_baseChange : ∀ (A A' : Type u) [CommRing A] [CommRing A']
    (I : Ideal A) (J : Ideal A') (φ : A →+* A')
    (ψ : (A ⧸ I) →+* (A' ⧸ J)) (hIJ : I.map φ = J), RingHom.Flat φ →
    (∀ a : A, ψ (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J (φ a)) →
    ∀ (h : IsRegularQuotientCoefficientIdeal A I)
      (h' : IsRegularQuotientCoefficientIdeal A' J)
      (M : ModuleCat.{u} (A ⧸ I)) (q : ℕ)
      (t : coefficientTor A I M q ⟶ (ModuleCat.restrictScalars ψ).obj
        (coefficientTor A' J ((ModuleCat.extendScalars ψ).obj M) q)),
      IsCoefficientTorTransport A A' I J φ ψ M ((ModuleCat.extendScalars ψ).obj M)
        ((ModuleCat.extendRestrictScalarsAdj ψ).unit.app M) q t →
      IsIso (((ModuleCat.extendRestrictScalarsAdj ψ).homEquiv _ _).symm t) ∧
      ∃! e : (ModuleCat.extendScalars ψ).obj (coefficientTorExterior A I M q) ≅
          coefficientTorExterior A' J ((ModuleCat.extendScalars ψ).obj M) q,
        (∀ (g : Fin q → I) (m : M),
          e.hom ((1 : A' ⧸ J) ⊗ₜ[A ⧸ I, ψ]
              ((exteriorPower.ιMulti (A ⧸ I) q (fun j ↦ I.toCotangent (g j)))
                ⊗ₜ[A ⧸ I] m)) =
            (exteriorPower.ιMulti (A' ⧸ J) q
              (fun j ↦ J.toCotangent (coefficientTorIdealImage I J φ hIJ (g j))))
                ⊗ₜ[A' ⧸ J]
                  (@id ((ModuleCat.extendScalars ψ).obj M)
                    (((ModuleCat.extendRestrictScalarsAdj ψ).unit.app M) m))) ∧
        (ModuleCat.extendScalars ψ).map (comparison A I h M q).hom ≫
            ((ModuleCat.extendRestrictScalarsAdj ψ).homEquiv _ _).symm t =
          e.hom ≫ (comparison A' J h' ((ModuleCat.extendScalars ψ).obj M) q).hom
  /-- Identity transport is the canonical identity after restricting along the identity. -/
  transport_identity : ∀ (A : Type u) [CommRing A] (I : Ideal A),
    IsRegularQuotientCoefficientIdeal A I →
    ∀ (M : ModuleCat.{u} (A ⧸ I)) (q : ℕ),
      IsCoefficientTorTransport A A I I (RingHom.id A) (RingHom.id (A ⧸ I)) M M
        ((ModuleCat.restrictScalarsId (A ⧸ I)).inv.app M) q
        ((ModuleCat.restrictScalarsId (A ⧸ I)).inv.app (coefficientTor A I M q))
  /-- Composite certified transports are the direct transport, by its uniqueness.
  The restriction associator is the adjoint form of tensor associativity. -/
  transport_composition : ∀ (A A' A'' : Type u)
    [CommRing A] [CommRing A'] [CommRing A''] (I : Ideal A) (J : Ideal A') (L : Ideal A'')
    (φ : A →+* A') (φ' : A' →+* A'')
    (ψ : (A ⧸ I) →+* (A' ⧸ J)) (ψ' : (A' ⧸ J) →+* (A'' ⧸ L)),
    RingHom.Flat φ → RingHom.Flat φ' →
    I.map φ = J → J.map φ' = L →
    (∀ a : A, ψ (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J (φ a)) →
    (∀ a : A', ψ' (Ideal.Quotient.mk J a) = Ideal.Quotient.mk L (φ' a)) →
    IsRegularQuotientCoefficientIdeal A I → IsRegularQuotientCoefficientIdeal A' J →
    IsRegularQuotientCoefficientIdeal A'' L →
    ∀ (M : ModuleCat.{u} (A ⧸ I)) (N : ModuleCat.{u} (A' ⧸ J))
      (O : ModuleCat.{u} (A'' ⧸ L))
      (u : M ⟶ (ModuleCat.restrictScalars ψ).obj N)
      (v : N ⟶ (ModuleCat.restrictScalars ψ').obj O) (q : ℕ)
      (t : coefficientTor A I M q ⟶
        (ModuleCat.restrictScalars ψ).obj (coefficientTor A' J N q))
      (s : coefficientTor A' J N q ⟶
        (ModuleCat.restrictScalars ψ').obj (coefficientTor A'' L O q)),
      IsCoefficientTorTransport A A' I J φ ψ M N u q t →
      IsCoefficientTorTransport A' A'' J L φ' ψ' N O v q s →
      IsCoefficientTorTransport A A'' I L (φ'.comp φ) (ψ'.comp ψ) M O
        (coefficientTorTransportComp ψ ψ' u v) q (coefficientTorTransportComp ψ ψ' t s)

/-- Normalized Tor with arbitrary quotient-module coefficients, with all the
presentation and flat-base-change compatibilities, including the zero extensions.

Source: Stacks Project, Tags 062I, 062F, 0623, 00LY, 00LZ, 00DM, 00HD and 02KH;
agent-supplied assembly, as recorded in the node.
(blueprint: lem-sfb-regular-quotient-coefficient-tor).

Proof:
1. The conormal-basis theorem gives the classes of the regular generators as a
   quotient basis. Regular implies Koszul-regular; the normalized projective
   Koszul resolution has exactly the quotient augmentation (the three proof
   dependencies regular-sequence-conormal-free, regular-sequence-koszul-regular,
   and new-d3-koszul-normalized-projective-resolution).
2. Tensoring with M kills each differential since IM=0. Increasing exterior
   wedges identify its degree-q term with wedge^q(I/I²) tensor_B M, without any
   flatness hypothesis on M (exterior-power-free-basis and module-tensor-product).
3. Transfer this identification through the canonical resolution Tor isomorphism.
   A coefficient morphism acts on each tensor by m ↦ u(m), proving naturality
   and quotient linearity; ambient scalars act by their quotient classes.
4. For two regular generating tuples, choose the rectangular matrix expressing
   one tuple in the other. Its exterior powers form an augmented Koszul chain
   map: contraction commutes with the matrix since their defining linear forms
   do. The conormal classes transform by the same matrix modulo I.
5. Tor-map-via-resolution-lift identifies their induced homology maps. Hence both
   normalized comparisons agree on every wedge tensor, and every augmented
   resolution comparison gives this same value. Those tensors generate, giving
   uniqueness, including the separately stipulated unit ideal.
6. Flat tensor preserves the prefix multiplication injections, so the image
   tuple is regular when the new quotient is nonzero. Apply flat tensor exactness
   to I → A → B and I² → I → I/I². Products of finite sums give (IA')²=I²A'.
   Tensor-over-quotient identifies B' tensor_B(I/I²) with I'/I'² on ideal classes.
7. Scalar extension of the Koszul exterior basis identifies its complex with
   the image-tuple Koszul complex, with the same augmentation. Flat tensor
   commutes with homology (lem-pc-flat-tensor-complex-cohom, reindexing into
   [-r,0]); tensor associativity identifies the coefficients with B' tensor_B M.
   The resolution-cycle formula is exactly the canonical Tor base-change map.
8. Both paths of the comparison square send a pure conormal wedge tensor to
   the corresponding image Koszul cycle. The same formulas with u(m), and the
   associativity formula b'' tensor(b' tensor z) ↦ b''b' tensor z, prove
   naturality, identity and composition. Arbitrary resolution cycles determine
   transport uniquely by surjectivity of cycles onto homology.
9. Empty tuples give the ordinary degree-zero isomorphism M ≅ Tor_0(A,M),
   with zero positive degrees. The exterior basis is empty for q>r. When either
   quotient is zero all its modules vanish, so the maps are the unique maps
   between zero modules, also after further base change. This covers A=0.
-/
theorem exists_regularQuotientCoefficientTorSystem :
    Nonempty RegularQuotientCoefficientTorSystem.{u} := by
  sorry

end AlgebraicGeometry
