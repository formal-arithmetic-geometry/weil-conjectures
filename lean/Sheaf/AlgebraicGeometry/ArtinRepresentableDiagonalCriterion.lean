/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Algebra.DualNumber
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.RingTheory.IntGRing
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-! # Artin's criterion with representable diagonal over the integers

Source: Stacks Project, Artin's Axioms, Tag 07Y4, lemma-diagonal-representable
(blueprint: lem-sfb-artin-representable-diagonal-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.ArtinCriterion

/-- The integer base in the universe of the schemes.
Source: Stacks, Artin, Tag 07Y4 over Spec Z
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
noncomputable abbrev Base : Scheme.{u} := Spec (.of (ULift.{u} ℤ))

/-- The unique structure morphism to the integer base.
Source: Stacks, Artin, Tag 07Y4 over Spec Z
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
noncomputable def integerScheme (T : Scheme.{u}) : Over Base :=
  Over.mk (specULiftZIsTerminal.from T)

/-- A scheme map, regarded as a map over the integers.
Source: Stacks, Artin, Tag 07Y4 over Spec Z
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
noncomputable def overMap {T U : Scheme.{u}} (a : T ⟶ U) : integerScheme T ⟶ integerScheme U :=
  Over.homMk a (specULiftZIsTerminal.hom_ext _ _)

/-- An object in a specified fibre, retaining its automorphisms.
Source: Stacks, Categories, fibred groupoids, Tag 003T
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
abbrev Object (F : BasedCategory.{v, w} (Over Base.{u})) (T : Over Base.{u}) :=
  Functor.Fiber F.p T

/-- An arrow in the total category over exactly the specified map of bases.
Source: Stacks, Categories, Tag 003T
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
abbrev Lift {F : BasedCategory.{v, w} (Over Base.{u})} {T U : Over Base.{u}}
    (a : T ⟶ U) (x : Object F T) (y : Object F U) :=
  {b : x.val ⟶ y.val // F.p.IsHomLift a b}

/-- Every object at the inverse limit descends to a stage.
Source: Stacks, Artin, limit preserving, axiom [1]
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
def ObjectsDescend (F : BasedCategory.{v, w} (Over Base.{u})) : Prop :=
  ∀ (I : Type u) [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over Base.{u}) (c : Cone D),
    (∀ i : I, IsAffine (D.obj (op i)).left) → IsAffine c.pt.left →
    Nonempty (IsLimit c) → ∀ x : Object F c.pt,
      ∃ (i : I) (xi : Object F (D.obj (op i))), Nonempty (Lift (c.π.app (op i)) x xi)

/-- Arrows between stage objects descend after passage to a common later stage.
The two factorizations retain the specified identifications at the limit.
Source: Stacks, Artin, axiom [1]
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
def ArrowsDescend (F : BasedCategory.{v, w} (Over Base.{u})) : Prop :=
  ∀ (I : Type u) [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over Base.{u}) (c : Cone D),
    (∀ i : I, IsAffine (D.obj (op i)).left) → IsAffine c.pt.left →
    Nonempty (IsLimit c) → ∀ (i : I) (xi yi : Object F (D.obj (op i)))
      (x y : Object F c.pt) (px : Lift (c.π.app (op i)) x xi)
      (py : Lift (c.π.app (op i)) y yi) (a : x ⟶ y),
      ∃ (j : I) (hij : i ≤ j) (xj yj : Object F (D.obj (op j)))
        (qx : Lift (D.map (homOfLE hij).op) xj xi)
        (qy : Lift (D.map (homOfLE hij).op) yj yi)
        (rx : Lift (c.π.app (op j)) x xj) (ry : Lift (c.π.app (op j)) y yj)
        (b : xj ⟶ yj),
        rx.val ≫ qx.val = px.val ∧ ry.val ≫ qy.val = py.val ∧
          a.val ≫ ry.val = rx.val ≫ b.val

/-- Equality of stage arrows detected at the limit holds at a later stage.
Source: Stacks, Artin, axiom [1]
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
def ArrowEqualitiesDescend (F : BasedCategory.{v, w} (Over Base.{u})) : Prop :=
  ∀ (I : Type u) [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over Base.{u}) (c : Cone D),
    (∀ i : I, IsAffine (D.obj (op i)).left) → IsAffine c.pt.left →
    Nonempty (IsLimit c) → ∀ (i : I) (xi yi : Object F (D.obj (op i)))
      (a b : xi ⟶ yi) (x : Object F c.pt) (px : Lift (c.π.app (op i)) x xi),
      px.val ≫ a.val = px.val ≫ b.val →
      ∃ (j : I) (hij : i ≤ j) (xj : Object F (D.obj (op j)))
        (qx : Lift (D.map (homOfLE hij).op) xj xi), qx.val ≫ a.val = qx.val ≫ b.val

/-- Equivalence on directed affine 2-colimits, including arrows and their equalities.
Source: Stacks, Artin, axiom [1], Tag 07Y4
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
def IsLimitPreserving (F : BasedCategory.{v, w} (Over Base.{u})) : Prop :=
  ObjectsDescend F ∧ ArrowsDescend F ∧ ArrowEqualitiesDescend F

/-- Rim--Schlessinger gluing on finite-type Artinian local spectra. In a fibred
 groupoid, a pushout of lifted objects over a base pushout expresses precisely
 equivalence with the 2-fibre product of the three fibres, including its arrows.
Source: Stacks, Artin, axiom [2] and the Rim--Schlessinger condition
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
def RimSchlessinger (F : BasedCategory.{v, w} (Over Base.{u})) : Prop :=
  ∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [IsArtinianRing A] [IsArtinianRing B] [IsArtinianRing C],
    Algebra.FiniteType ℤ A → Algebra.FiniteType ℤ B → Algebra.FiniteType ℤ C →
    ∀ (f : A →+* B) (g : C →+* B), Function.Surjective g →
    IsNilpotent (RingHom.ker g) →
    ∀ (P : Over Base.{u}) (i : integerScheme (Spec (.of A)) ⟶ P)
      (j : integerScheme (Spec (.of C)) ⟶ P),
      IsPushout (overMap (Spec.map (CommRingCat.ofHom f)))
        (overMap (Spec.map (CommRingCat.ofHom g))) i j →
      ∀ (x : Object F (integerScheme (Spec (.of B))))
        (y : Object F (integerScheme (Spec (.of A)))) (z : Object F (integerScheme (Spec (.of C))))
        (a : Lift (overMap (Spec.map (CommRingCat.ofHom f))) x y)
        (b : Lift (overMap (Spec.map (CommRingCat.ofHom g))) x z),
        ∃ (q : Object F P) (c : Lift i y q) (d : Lift j z q),
          IsPushout a.val b.val c.val d.val

/-- A first-order deformation with its specified special-fibre identification.
The marking is a cartesian arrow over the reduction of the square-zero ring.
Source: Stacks, Artin, equation-tangent-space
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
structure MarkedDeformation (F : BasedCategory.{v, w} (Over Base.{u}))
    (K : Type u) [Field K] (x₀ : Object F (integerScheme (Spec (.of K))))
    (M : Type u) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M] where
  obj : Object F (integerScheme (Spec (.of (TrivSqZeroExt K M))))
  mark : Lift (overMap (Spec.map
    (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K M).toRingHom))) x₀ obj

/-- Isomorphism of marked deformations, fixing the special-fibre identification.
Source: Stacks, Artin, equation-tangent-space
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
def MarkedDeformation.Isomorphic {F : BasedCategory.{v, w} (Over Base.{u})}
    {K : Type u} [Field K] {x₀ : Object F (integerScheme (Spec (.of K)))}
    {M : Type u} [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
    (x y : MarkedDeformation F K x₀ M) : Prop :=
  ∃ a : x.obj ≅ y.obj, x.mark.val ≫ a.hom.val = y.mark.val

/-- Pullback along a linear map of square-zero ideals. Its arrow is tied to the
actual ring map; the special-fibre markings must agree.
Source: Stacks, Formal Deformation Theory, tangent-space operations
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
def MarkedDeformation.Induces {F : BasedCategory.{v, w} (Over Base.{u})}
    {K : Type u} [Field K] {x₀ : Object F (integerScheme (Spec (.of K)))}
    {M N : Type u} [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
    [AddCommGroup N] [Module K N] [Module Kᵐᵒᵖ N] [IsCentralScalar K N]
    (f : M →ₗ[K] N) (x : MarkedDeformation F K x₀ M)
    (y : MarkedDeformation F K x₀ N) : Prop :=
  ∃ a : Lift (overMap (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map f).toRingHom))) y.obj x.obj,
    y.mark.val ≫ a.val = x.mark.val

/-- Finite coordinates for the tangent space. They classify marked deformations
up to isomorphism and preserve the canonical sum and scalar operations, obtained
from projections, addition, and scalar multiplication of square-zero ideals.
Source: Stacks, Artin, equation-tangent-space and axiom [3]
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
def FiniteTangent (F : BasedCategory.{v, w} (Over Base.{u}))
    (K : Type u) [Field K] (x₀ : Object F (integerScheme (Spec (.of K)))) : Prop :=
  ∃ (n : ℕ) (coord : MarkedDeformation F K x₀ K → (Fin n → K)),
    Function.Surjective coord ∧
    (∀ x y, coord x = coord y ↔ x.Isomorphic y) ∧
    (∀ (z : MarkedDeformation F K x₀ (K × K))
      (x y s : MarkedDeformation F K x₀ K),
      z.Induces (LinearMap.fst K K K) x → z.Induces (LinearMap.snd K K K) y →
      z.Induces (LinearMap.fst K K K + LinearMap.snd K K K) s →
      coord s = coord x + coord y) ∧
    ∀ (c : K) (x y : MarkedDeformation F K x₀ K),
      x.Induces (c • LinearMap.id) y → coord y = c • coord x

/-- Infinitesimal automorphisms of a marked deformation. The deformation will be
required to be trivial when this type is used below.
Source: Stacks, Artin, equation-infinitesimal-automorphisms
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
abbrev InfinitesimalAutomorphism {F : BasedCategory.{v, w} (Over Base.{u})}
    {K : Type u} [Field K] {x₀ : Object F (integerScheme (Spec (.of K)))}
    (x : MarkedDeformation F K x₀ K) :=
  {a : x.obj ≅ x.obj // x.mark.val ≫ a.hom.val = x.mark.val}

/-- Finite coordinates on infinitesimal automorphisms, respecting composition as
addition and the canonical pullback action of scalars on the trivial deformation.
Source: Stacks, Artin, equation-infinitesimal-automorphisms, axiom [3]
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
def FiniteInfinitesimalAutomorphisms (F : BasedCategory.{v, w} (Over Base.{u}))
    (K : Type u) [Field K] (x₀ : Object F (integerScheme (Spec (.of K)))) : Prop :=
  ∀ (x : MarkedDeformation F K x₀ K)
    (p : Lift (overMap (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom K K)))) x.obj x₀),
    x.mark.val ≫ p.val = 𝟙 x₀.val →
    ∃ (n : ℕ) (coord : InfinitesimalAutomorphism x → (Fin n → K)),
      Function.Bijective coord ∧
      (∀ a b c : InfinitesimalAutomorphism x,
        a.val.hom.val ≫ b.val.hom.val = c.val.hom.val → coord c = coord a + coord b) ∧
      ∀ (c : K) (a b : InfinitesimalAutomorphism x)
        (h : Lift (overMap (Spec.map
          (CommRingCat.ofHom (TrivSqZeroExt.map (c • (LinearMap.id : K →ₗ[K] K))).toRingHom)))
          x.obj x.obj),
        h.val ≫ p.val = p.val → x.mark.val ≫ h.val = x.mark.val →
        b.val.hom.val ≫ h.val = h.val ≫ a.val.hom.val → coord b = c • coord a

/-- Both infinitesimal spaces are finite-dimensional for every finite-type field
and every object in its fibre.
Source: Stacks, Artin, axiom [3], Tag 07Y4
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
def FiniteInfinitesimalSpaces (F : BasedCategory.{v, w} (Over Base.{u})) : Prop :=
  ∀ (K : Type u) [Field K], Algebra.FiniteType ℤ K →
    ∀ x₀ : Object F (integerScheme (Spec (.of K))),
      FiniteTangent F K x₀ ∧ FiniteInfinitesimalAutomorphisms F K x₀

/-- The positive-indexed infinitesimal neighbourhood Spec(A/m^(n+1)).
Source: Stacks, Artin, formal objects
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
noncomputable abbrev AdicNeighbourhood (A : Type u) [CommRing A] [IsLocalRing A]
    (n : ℕ) : Over Base.{u} :=
  integerScheme (Spec (.of (A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1))))

/-- The canonical map between positive-indexed adic neighbourhoods.
Source: Stacks, Artin, formal objects
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
noncomputable def adicTransition (A : Type u) [CommRing A] [IsLocalRing A]
    {n m : ℕ} (h : n ≤ m) : AdicNeighbourhood A n ⟶ AdicNeighbourhood A m :=
  overMap (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)))))

/-- The canonical closed map from each infinitesimal neighbourhood to Spec A.
Source: Stacks, Artin, formal objects
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
noncomputable def adicInclusion (A : Type u) [CommRing A] [IsLocalRing A]
    (n : ℕ) : AdicNeighbourhood A n ⟶ integerScheme (Spec (.of A)) :=
  overMap (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1)))))

/-- A formal object, including every transition isomorphism through its cartesian
arrow, and the identity and composition coherence equations.
Source: Stacks, Artin, formal objects and equation-approximation
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
structure FormalSystem (F : BasedCategory.{v, w} (Over Base.{u}))
    (A : Type u) [CommRing A] [IsLocalRing A] where
  obj : ∀ n : ℕ, Object F (AdicNeighbourhood A n)
  transition : ∀ (n m : ℕ) (h : n ≤ m), Lift (adicTransition A h) (obj n) (obj m)
  identity : ∀ n : ℕ, (transition n n le_rfl).val = 𝟙 (obj n).val
  composition : ∀ (n m k : ℕ) (h : n ≤ m) (h' : m ≤ k),
    (transition n m h).val ≫ (transition m k h').val =
      (transition n k (h.trans h')).val

/-- Every formal object over a complete Noetherian local ring with finite-type
residue field is induced by an object over that ring, with all its transitions.
Source: Stacks, Artin, Tag 07Y4 assumption (3)
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
def FormalObjectsEffective (F : BasedCategory.{v, w} (Over Base.{u})) : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A],
    Algebra.FiniteType ℤ (IsLocalRing.ResidueField A) →
    ∀ s : FormalSystem F A,
      ∃ (x : Object F (integerScheme (Spec (.of A))))
        (a : ∀ n : ℕ, Lift (adicInclusion A n) (s.obj n) x),
        ∀ (n m : ℕ) (h : n ≤ m), (s.transition n m h).val ≫ (a m).val = (a n).val

/-- A finite-type point is defined by its canonical residue-field morphism being
of finite type, including quasi-compactness.
Source: Stacks, Morphisms, definition-finite-type-point; Artin, definition-versal
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
def FiniteTypePoint (U : Scheme.{u}) (u₀ : U) : Prop :=
  LocallyOfFiniteType (U.fromSpecResidueField u₀) ∧
    QuasiCompact (U.fromSpecResidueField u₀)

/-- The Artinian lifting definition of versality. The residue homomorphisms are
surjective with the maximal ideals as kernels and commute with the given small
extension. The lifted arrow factors the specified arrow over the smaller ring.
Source: Stacks, Artin, definition-versal, equation-hat-x
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
def IsVersalAt (F : BasedCategory.{v, w} (Over Base.{u}))
    (U : Scheme.{u}) (x : Object F (integerScheme U)) (u₀ : U) : Prop :=
  ∀ (A A' : Type u) [CommRing A] [CommRing A'] [IsLocalRing A] [IsLocalRing A']
    [IsArtinianRing A] [IsArtinianRing A']
    (ρ : A →+* U.residueField u₀) (ρ' : A' →+* U.residueField u₀),
    Function.Surjective ρ → RingHom.ker ρ = IsLocalRing.maximalIdeal A →
    Function.Surjective ρ' → RingHom.ker ρ' = IsLocalRing.maximalIdeal A' →
    ∀ (g : A' →+* A), Function.Surjective g → IsNilpotent (RingHom.ker g) →
      ρ.comp g = ρ' →
      ∀ (a : Spec (.of A) ⟶ U),
        Spec.map (CommRingCat.ofHom ρ) ≫ a = U.fromSpecResidueField u₀ →
        ∀ (y : Object F (integerScheme (Spec (.of A))))
          (y' : Object F (integerScheme (Spec (.of A'))))
          (b : Lift (overMap (Spec.map (CommRingCat.ofHom g))) y y')
          (c : Lift (overMap a) y x),
          ∃ (a' : Spec (.of A') ⟶ U) (d : Lift (overMap a') y' x),
            Spec.map (CommRingCat.ofHom g) ≫ a' = a ∧ b.val ≫ d.val = c.val

/-- Versality at one finite-type point extends to all finite-type points in an
open neighbourhood of it.
Source: Stacks, Artin, definition-openness-versality
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
def OpennessOfVersality (F : BasedCategory.{v, w} (Over Base.{u})) : Prop :=
  ∀ (U : Scheme.{u}), LocallyOfFiniteType (specULiftZIsTerminal.from U) →
    ∀ (x : Object F (integerScheme U)) (u₀ : U),
      FiniteTypePoint U u₀ → IsVersalAt F U x u₀ →
      ∃ V : U.Opens, u₀ ∈ V ∧ ∀ t : U, t ∈ V → FiniteTypePoint U t → IsVersalAt F U x t

/-- One scheme bounds the cardinalities of the isomorphism classes and all arrows
in every finite-type field fibre. The common cardinal universe is explicit.
Source: Stacks, Artin, axiom [-1], footnote
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
def HasSizeBound (F : BasedCategory.{v, w} (Over Base.{u})) : Prop :=
  ∃ U : Scheme.{u}, ∀ (K : Type u) [Field K], Algebra.FiniteType ℤ K →
    Cardinal.lift.{max u v w} (Cardinal.mk (Skeleton (Object F (integerScheme
      (Spec (.of K)))))) ≤ Cardinal.lift.{max u v w} (Cardinal.mk U) ∧
    Cardinal.lift.{max u v w} (Cardinal.mk
      (Σ x y : Object F (integerScheme (Spec (.of K))), (x ⟶ y))) ≤
      Cardinal.lift.{max u v w} (Cardinal.mk U)

/-- Smoothness of an algebraic-space map to a scheme is tested on every
representable étale scheme chart of its source.
Source: Stacks, Morphisms of Spaces, smooth morphisms; Artin, Tag 07Y4
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
def SpaceMapIsSmooth {S : Scheme.{u}} (Z : AlgebraicSpace S)
    (T : Over S) (a : Z.obj.obj ⟶ yoneda.obj T) : Prop :=
  ∀ (U : Over S) (b : yoneda.obj U ⟶ Z.obj.obj), AlgebraicSpace.IsEtale b →
    Smooth ((yoneda.preimage (b ≫ a)).left)

/-- A smooth surjective scheme atlas, representable by algebraic spaces. Each
base change retains its actual projection to the test scheme.
Source: Stacks, Artin, Tag 07Y4; Algebraic Stacks, definition-algebraic-stack
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
def HasSmoothSurjectiveAtlas (F : BasedCategory.{v, w} (Over Base.{u})) : Prop :=
  ∃ (U : Over Base.{u}) (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
    ∀ (T : Over Base.{u}) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F),
      ∃ (Z : AlgebraicSpace Base.{u}) (p : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange a T t Z p ∧ SpaceMapIsSmooth Z T p ∧ SpaceMapIsSurjective Z T p

/-- An algebraic stack in the étale-stack and representable-diagonal convention:
a stack in groupoids with an algebraic-space diagonal and a smooth surjective
scheme atlas. The atlas criterion upgrades étale descent to fppf descent.
Source: Stacks, Artin, Tag 07Y4 and Criteria for Representability, Tag 076V
(blueprint: lem-sfb-artin-representable-diagonal-criterion). -/
def IsAlgebraicModuliStack (F : BasedCategory.{v, w} (Over Base.{u})) : Prop :=
  IsModuliStack F ∧ HasAlgebraicSpaceDiagonal F ∧ HasSmoothSurjectiveAtlas F

/-- Artin's criterion over Z, retaining all seven conditions and the common size bound.
Source: Stacks, Artin's Axioms, Tag 07Y4, lemma-diagonal-representable
(blueprint: lem-sfb-artin-representable-diagonal-criterion).

Proof:
1. The integers are a G-ring (lem-weil-pbc-z-g-ring). Apply
lem-sfb-artin-smooth-point-neighbourhood to each object over each finite-type field.
It gives a finite-type affine neighbourhood with a smooth representable map to F
and a point with the specified residue field and specified fibre isomorphism.
2. Choose representatives of finite-type fields and object isomorphism classes. Fields
have finite polynomial presentations over Z and the common size bound makes the index
small. Form their scheme coproduct (lem-weil-pbc-scheme-coproduct-family). Étale descent
glues the chart objects, using empty off-diagonal overlaps and identities on each chart.
The diagonal hypothesis identifies every base change by a scheme with an algebraic space.
3. For a test scheme, the inverse images of the coproduct summands are disjoint open
subspaces. Their projections are smooth by the local chart construction. On an étale
scheme chart these inverse images are an open cover. Smoothness is local on the source
(lem-weil-pbc-smooth-local-on-source), proving smoothness of the assembled map.
4. Over an affine test scheme locally of finite presentation over Z, smoothness gives
flatness and local finite presentation (lem-pc-smooth-flat). Thus the image is open by
lem-sfb-flat-lfp-space-universally-open, using the algebraic-space chart definition.
5. Such an affine test is finite type, by affine quasi-compactness and local finite
presentation (lem-weil-pbc-affine-scheme-qcqs). Its finite-type points have residue fields
finite type over Z (lem-sfb-finite-type-composition-base-change). The chosen chart and
fibre isomorphism give a point of the base change over each such point. The open image
is everything by lem-sfb-finite-type-points-detect-open.
6. Limit preservation includes limit preservation on objects. The representable limit
surjectivity test (lem-sfb-limit-test-surjective-representable) extends surjectivity from
these affine finite-presentation tests to every scheme test.
7. We have the representable diagonal and a smooth surjective scheme atlas. Together
with étale stack descent, lem-sfb-etale-smooth-atlas-fppf-descent supplies fppf descent.
This is the asserted algebraic stack. -/
theorem isAlgebraicModuliStack_of_artin
    (F : BasedCategory.{v, w} (Over Base.{u}))
    (hFibred : IsFibredInGroupoids F)
    (hEtale : IsModuliStack F)
    (hDiagonal : HasAlgebraicSpaceDiagonal F)
    (hLimits : IsLimitPreserving F)
    (hRS : RimSchlessinger F)
    (hInfinitesimal : FiniteInfinitesimalSpaces F)
    (hEffective : FormalObjectsEffective F)
    (hVersal : OpennessOfVersality F)
    (hSize : HasSizeBound F) :
    IsAlgebraicModuliStack F := by
  sorry

end AlgebraicGeometry.ArtinCriterion
