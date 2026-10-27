module

public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Sheaf.AlgebraicTopology.SimplicialAlgebraShuffleNormalization
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.RingTheory.FilteredColimitAlgebrasUnderlyingModule
import Sheaf.LinearAlgebra.TensorProduct.ColimitVaryingRings
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Standard normalized coefficient resolutions and filtered colimits

Source: Stacks Project, cotangent.tex, Tags 08PM and 08S9; simplicial.tex, Tag 019A;
algebra.tex, Tag 00DD. The dg and finite-equation conclusions are the DAG's agent refinement.
(blueprint: lem-sfb-standard-normalized-resolution-filtered-colimit).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open Algebra.CotangentResolution

namespace Algebra.StandardNormalizedResolution

variable (D : Type u) [CommRing D]
variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]

/-- The ring arrow underlying a D-algebra. Source: Stacks, Tag 08PM
(blueprint: lem-sfb-standard-normalized-resolution-filtered-colimit). -/
def arrow (B : CommAlgCat.{u} D) : Arrow CommRingCat.{u} :=
  Arrow.mk (CommRingCat.ofHom (algebraMap D B))

variable (K : Coherence.{u})

/-- The specified standard resolution, viewed as rings under D. Its data are determined
by the explicit terms, faces, degeneracies and augmentation of `IsStandard`.
Source: Stacks, Tag 08PM
(blueprint: lem-sfb-standard-normalized-resolution-filtered-colimit). -/
def standardUnder (B : CommAlgCat.{u} D) : SimplicialObject (Under (CommRingCat.of D)) where
  obj n := Under.mk ((K.standard (arrow D B)).base.app n)
  map f := Under.homMk
    ((K.standard (arrow D B)).algebra.map f)
    (by simpa using
      ((K.standard (arrow D B)).base.naturality f).symm)
  map_id n := by ext; simp
  map_comp f g := by ext; simp

/-- The coefficient-identity ring square attached to an algebra map.
Source: Stacks, Tag 08QL
(blueprint: lem-sfb-standard-normalized-resolution-filtered-colimit). -/
def arrowMap {B B' : CommAlgCat.{u} D} (f : B ⟶ B') : arrow D B ⟶ arrow D B' :=
  Arrow.homMk (𝟙 _) (CommRingCat.ofHom f.hom) (by ext x; exact (f.hom.commutes x).symm)

/-- The standard simplicial map, retaining its coefficient triangle.
Source: Stacks, Tags 08PM and 08QL
(blueprint: lem-sfb-standard-normalized-resolution-filtered-colimit). -/
def standardUnderMap {B B' : CommAlgCat.{u} D} (f : B ⟶ B') :
    standardUnder D K B ⟶ standardUnder D K B' where
  app n := Under.homMk ((K.standardMap (arrowMap D f)).map.app n)
    (by simpa [arrowMap, standardUnder] using
      (K.standardMap (arrowMap D f)).base n.unop.len)
  naturality n m g := by
    ext x
    exact ConcreteCategory.congr_hom ((K.standardMap (arrowMap D f)).map.naturality g) x

/-- Strict functorial standard polynomial resolution, with no constant replacement at B=D.
The coherence witness is fixed by the dependency's explicit polynomial formulas.
Source: Stacks, Tags 08PM and 08QL
(blueprint: lem-sfb-standard-normalized-resolution-filtered-colimit). -/
def standard : CommAlgCat.{u} D ⥤ SimplicialObject (CommAlgCat.{u} D) where
  obj B := standardUnder D K B ⋙ (commAlgCatEquivUnder (CommRingCat.of D)).inverse
  map f := Functor.whiskerRight (standardUnderMap D K f)
    (commAlgCatEquivUnder (CommRingCat.of D)).inverse
  map_id B := by
    have h : standardUnderMap D K (𝟙 B) = 𝟙 (standardUnder D K B) := by
      apply NatTrans.ext
      funext n
      apply StructuredArrow.hom_ext
      change (K.standardMap (arrowMap D (𝟙 B))).map.app n = 𝟙 _
      have hi : arrowMap D (𝟙 B) = 𝟙 (arrow D B) := by ext <;> rfl
      rw [hi, K.standardMap_id]
      rfl
    rw [h]
    exact Functor.whiskerRight_id _
  map_comp f g := by
    have h : standardUnderMap D K (f ≫ g) =
        standardUnderMap D K f ≫ standardUnderMap D K g := by
      apply NatTrans.ext
      funext n
      apply StructuredArrow.hom_ext
      change (K.standardMap (arrowMap D (f ≫ g))).map.app n =
        (K.standardMap (arrowMap D f)).map.app n ≫ (K.standardMap (arrowMap D g)).map.app n
      have hi : arrowMap D (f ≫ g) = arrowMap D f ≫ arrowMap D g := by ext <;> rfl
      rw [hi, K.standardMap_comp]
      rfl
    rw [h]
    exact Functor.whiskerRight_comp _ _ _

/-- The quotient shuffle normalization supplied by the normalization node. Its quotient
identifications, quotient map and shuffle formula determine it up to unique natural isomorphism.
Source: Stacks, Tag 019A, and the cited shuffle normalization refinement
(blueprint: lem-sfb-standard-normalized-resolution-filtered-colimit). -/
def normalized : CommAlgCat.{u} D ⥤
    CommMon (CochainComplex (ModuleCat.{u} (ULift.{u} D)) ℤ) :=
  standard D K ⋙
    (AlgebraicTopology.SimplicialAlgebraShuffleNormalization.exists_shuffle_normalization D).choose

/-- Degreewise ordinary extension of scalars, inducing the differential, product and unit.
Source: Stacks, Tag 00DD; the dg product is induced from the shuffle product
(blueprint: lem-sfb-standard-normalized-resolution-filtered-colimit). -/
def coefficients (S : Type u) [CommRing S] [Algebra D S] :
    CommAlgCat.{u} D ⥤ Mon (CochainComplex (ModuleCat.{u} (ULift.{u} S)) ℤ) :=
  let φ : ULift.{u} D →+* ULift.{u} S :=
    (ULift.ringEquiv.symm : S ≃+* ULift.{u} S).toRingHom.comp
      ((algebraMap D S).comp (ULift.ringEquiv : ULift.{u} D ≃+* D).toRingHom)
  letI := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).left_adjoint_additive
  normalized D K ⋙ CommMon.forget₂Mon _ ⋙
    ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (.up ℤ)).mapMon

/-- The degree-m module of the ordinary coefficient dg algebra.
Source: Stacks, Tags 08PM, 019A and 00DD
(blueprint: lem-sfb-standard-normalized-resolution-filtered-colimit). -/
def degree (S : Type u) [CommRing S] [Algebra D S] (m : ℤ) :
    CommAlgCat.{u} D ⥤ ModuleCat.{u} D :=
  coefficients D K S ⋙ Mon.forget _ ⋙ HomologicalComplex.eval _ (.up ℤ) m ⋙
    ModuleCat.restrictScalars
      ((ULift.ringEquiv.symm : S ≃+* ULift.{u} S).toRingHom.comp (algebraMap D S))

/-- The canonical dg comparison is invertible, its underlying colimit is degreewise,
and finite homogeneous elements and equalities descend. Equality is stated for arbitrary
homogeneous values; applying this to the values of the specified finite expressions gives
exactly the equation clause, since the transition dg-algebra maps preserve every operation.

Source: Stacks, cotangent.tex, Tags 08PM and 08S9; simplicial.tex, Tag 019A;
algebra.tex, Tags 00D6, 00D7 and 00DD. The dg and finite-expression conclusions are
agent refinements (blueprint: lem-sfb-standard-normalized-resolution-filtered-colimit).

Proof, following the seven steps of the DAG:
1. The universal property of `MvPolynomial` identifies compatible polynomial-algebra
   maps with compatible functions on generators, hence proves preservation of colimits.
2. Induct on the number of applications of free-algebra followed by underlying-set.
   Use lem-weil-pbc-filtered-colimit-algebras-underlying-module and
   lem-weil-pbc-filtered-colimit-modules-elementwise to recover representatives and
   eventual equality. The standard maps commute with all simplicial operators.
3. A normalized class lifts by lifting a representative. An equality modulo degeneracies
   is a finite sum of degeneracies from degree n-1. Lift those finitely many elements;
   the remaining equality holds later by eventual equality. At n=0 the sum is empty.
4. Apply lem-weil-pbc-filtered-colimit-modules-criterion degreewise. The alternating
   differential commutes with every comparison; positive cochain terms are zero.
5. Apply lem-weil-pbc-filtered-colimit-tensor-varying-rings to constant D and S and
   these normalized modules. The pure-tensor formula makes the comparison S-linear
   and compatible with the differentials, without any flatness requirement.
6. Each term of the finite shuffle sum is preserved by the simplicial maps, as is
   the unit. On the degreewise colimit, multiply representatives at a common stage;
   eventual equality proves independence. The inverse of the componentwise bijective
   comparison preserves multiplication and differential, giving the dg isomorphism.
7. Lift finitely many elements separately and take a common upper bound. For finite
   equalities subtract the sides, apply eventual vanishing, and take another common
   upper bound. This applies to evaluated expressions because all the specified
   operations commute with dg-algebra maps. Empty collections use nonemptiness of I;
   positive-degree elements, zero rings and zero modules cause no exception. -/
theorem filtered_colimit (S : Type u) [CommRing S] [Algebra D S]
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommAlgCat.{u} D) (c : Cocone F) (_hc : IsColimit c) :
    Nonempty (IsColimit ((coefficients D K S).mapCocone c)) ∧
    (∀ m : ℤ, Nonempty (IsColimit ((degree D K S m).mapCocone c))) ∧
    (∀ (l : Cocone (F ⋙ coefficients D K S)) (hl : IsColimit l),
      ∃ e : l.pt ≅ (coefficients D K S).obj c.pt,
        e.hom = hl.desc ((coefficients D K S).mapCocone c)) ∧
    (∀ (n : ℕ) (d : Fin n → ℤ)
        (x : ∀ a : Fin n, (degree D K S (d a)).obj c.pt),
      ∃ (i : I) (y : ∀ a : Fin n, (degree D K S (d a)).obj (F.obj i)),
        ∀ a : Fin n, (degree D K S (d a)).map (c.ι.app i) (y a) = x a) ∧
    (∀ (i : I) (n : ℕ) (d : Fin n → ℤ)
        (x y : ∀ a : Fin n, (degree D K S (d a)).obj (F.obj i)),
      (∀ a : Fin n, (degree D K S (d a)).map (c.ι.app i) (x a) =
        (degree D K S (d a)).map (c.ι.app i) (y a)) →
      ∃ (j : I) (h : i ≤ j), ∀ a : Fin n,
        (degree D K S (d a)).map (F.map (homOfLE h)) (x a) =
          (degree D K S (d a)).map (F.map (homOfLE h)) (y a)) := by
  sorry

end Algebra.StandardNormalizedResolution
