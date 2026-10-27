/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Algebra.DualNumber
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-! # Geometric Artin axioms over an affine base

Source: Stacks Project, Artin's Axioms, section-axioms, definition-versal,
definition-openness-versality, and Tag 07XY (blueprint: def-sfb-artin-geometric-axioms).

These predicates retain objects, arrows, prescribed identifications, and their coherence.
The ring parameter records the actual base, including its action on test rings.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ArtinGeometry

variable {R : Type u} [CommRing R]

/-- The affine scheme of an R-algebra, with its given structure map.
Source: Stacks, Artin, section-axioms (blueprint: def-sfb-artin-geometric-axioms). -/
abbrev affine (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] :
    Over (Spec (.of R)) := (algSpec (.of R)).obj (op (CommAlgCat.of R A))

/-- The actual contravariant affine map of an R-algebra homomorphism.
Source: Stacks, Artin, section-axioms (blueprint: def-sfb-artin-geometric-axioms). -/
def affineMap {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) : affine R B ⟶ affine R A :=
  (algSpec (.of R)).map (CommAlgCat.ofHom f).op

/-- The existing fibre category, retaining all automorphisms.
Source: Stacks, Tag 003T (blueprint: def-sfb-artin-geometric-axioms). -/
abbrev Object (F : BasedCategory.{v, w} (Over (Spec (.of R)))) (T : Over (Spec (.of R))) :=
  Functor.Fiber F.p T

/-- An arrow over the specified base map, encoding the pullback identification.
Source: Stacks, Tag 003T (blueprint: def-sfb-artin-geometric-axioms). -/
abbrev Lift {F : BasedCategory.{v, w} (Over (Spec (.of R)))}
    {T U : Over (Spec (.of R))} (a : T ⟶ U) (x : Object F T) (y : Object F U) :=
  {b : x.val ⟶ y.val // F.p.IsHomLift a b}

/-- Every object at the inverse limit descends to a stage.
Source: Stacks, Artin, limit preserving, axiom [1]
(blueprint: def-sfb-artin-geometric-axioms). -/
def ObjectsDescend (F : BasedCategory.{v, w} (Over (Spec (.of R)))) : Prop :=
  ∀ (I : Type u) [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over (Spec (.of R))) (c : Cone D),
    (∀ i : I, IsAffine (D.obj (op i)).left) → IsAffine c.pt.left →
    Nonempty (IsLimit c) → ∀ x : Object F c.pt,
      ∃ (i : I) (xi : Object F (D.obj (op i))), Nonempty (Lift (c.π.app (op i)) x xi)

/-- Arrows between stage objects descend after passage to a common later stage.
The two factorizations retain the specified identifications at the limit.
Source: Stacks, Artin, axiom [1]
(blueprint: def-sfb-artin-geometric-axioms). -/
def ArrowsDescend (F : BasedCategory.{v, w} (Over (Spec (.of R)))) : Prop :=
  ∀ (I : Type u) [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over (Spec (.of R))) (c : Cone D),
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
(blueprint: def-sfb-artin-geometric-axioms). -/
def ArrowEqualitiesDescend (F : BasedCategory.{v, w} (Over (Spec (.of R)))) : Prop :=
  ∀ (I : Type u) [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over (Spec (.of R))) (c : Cone D),
    (∀ i : I, IsAffine (D.obj (op i)).left) → IsAffine c.pt.left →
    Nonempty (IsLimit c) → ∀ (i : I) (xi yi : Object F (D.obj (op i)))
      (a b : xi ⟶ yi) (x : Object F c.pt) (px : Lift (c.π.app (op i)) x xi),
      px.val ≫ a.val = px.val ≫ b.val →
      ∃ (j : I) (hij : i ≤ j) (xj : Object F (D.obj (op j)))
        (qx : Lift (D.map (homOfLE hij).op) xj xi), qx.val ≫ a.val = qx.val ≫ b.val

/-- Equivalence on directed affine 2-colimits, including arrows and their equalities.
Source: Stacks, Artin, axiom [1], Tag 07Y4
(blueprint: def-sfb-artin-geometric-axioms). -/
def IsLimitPreserving (F : BasedCategory.{v, w} (Over (Spec (.of R)))) : Prop :=
  ObjectsDescend F ∧ ArrowsDescend F ∧ ArrowEqualitiesDescend F

/-- Rim--Schlessinger gluing, including its full arrow universal property.
The lifted pushout is equivalent to the usual 2-fibre-product comparison being an
 equivalence: compatible arrows out of its vertex are uniquely determined on the legs.
Source: Stacks, Artin, axiom [2] (blueprint: def-sfb-artin-geometric-axioms). -/
def RimSchlessinger (F : BasedCategory.{v, w} (Over (Spec (.of R)))) : Prop :=
  ∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [IsArtinianRing A] [IsArtinianRing B] [IsArtinianRing C],
    Algebra.FiniteType R A → Algebra.FiniteType R B → Algebra.FiniteType R C →
    ∀ (f : A →ₐ[R] B) (g : C →ₐ[R] B), Function.Surjective g →
    IsNilpotent (RingHom.ker g.toRingHom) →
    ∀ (P : Over (Spec (.of R))) (i : affine R A ⟶ P) (j : affine R C ⟶ P),
      IsPushout (affineMap f) (affineMap g) i j →
      ∀ (x : Object F (affine R B)) (y : Object F (affine R A))
        (z : Object F (affine R C))
        (a : Lift (affineMap f) x y) (b : Lift (affineMap g) x z),
        ∃ (q : Object F P) (c : Lift i y q) (d : Lift j z q),
          IsPushout a.val b.val c.val d.val

/-- Square-zero extension with its R-action through K; no R-module structure on
M is required as separate data. Source: Stacks, Artin, equation-tangent-space
(blueprint: def-sfb-artin-geometric-axioms). -/
def squareZeroAffine (K : Type u) [Field K] [Algebra R K]
    (M : Type u) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M] :
    Over (Spec (.of R)) :=
  letI : Algebra R (TrivSqZeroExt K M) := Algebra.restrictScalars R K _
  affine R (TrivSqZeroExt K M)

/-- Reduction to the special fibre of a square-zero extension.
Source: Stacks, Artin, equation-tangent-space (blueprint: def-sfb-artin-geometric-axioms). -/
def squareZeroReduction (K : Type u) [Field K] [Algebra R K]
    (M : Type u) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M] :
    affine R K ⟶ squareZeroAffine (R := R) K M :=
  letI : Algebra R (TrivSqZeroExt K M) := Algebra.restrictScalars R K _
  affineMap { (TrivSqZeroExt.fstHom K K M).toRingHom with commutes' := fun _ ↦ rfl }

/-- Pullback of square-zero extensions along a K-linear map of their ideals.
Source: Stacks, Artin, tangent operations (blueprint: def-sfb-artin-geometric-axioms). -/
def squareZeroMap {K : Type u} [Field K] [Algebra R K]
    {M N : Type u} [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
    [AddCommGroup N] [Module K N] [Module Kᵐᵒᵖ N] [IsCentralScalar K N]
    (f : M →ₗ[K] N) : squareZeroAffine (R := R) K N ⟶ squareZeroAffine K M :=
  letI : Algebra R (TrivSqZeroExt K M) := Algebra.restrictScalars R K _
  letI : Algebra R (TrivSqZeroExt K N) := Algebra.restrictScalars R K _
  affineMap { (TrivSqZeroExt.map f).toRingHom with
    commutes' := fun r ↦ TrivSqZeroExt.map_inl f (algebraMap R K r) }

/-- The projection to K defining the trivial deformation.
Source: Stacks, Artin, infinitesimal automorphisms
(blueprint: def-sfb-artin-geometric-axioms). -/
def squareZeroProjection (K : Type u) [Field K] [Algebra R K] :
    squareZeroAffine (R := R) K K ⟶ affine R K :=
  letI : Algebra R (TrivSqZeroExt K K) := Algebra.restrictScalars R K _
  affineMap { TrivSqZeroExt.inlHom K K with commutes' := fun _ ↦ rfl }

/-- A first-order deformation with its specified special-fibre identification.
The marking is a cartesian arrow over the reduction of the square-zero ring.
Source: Stacks, Artin, equation-tangent-space
(blueprint: def-sfb-artin-geometric-axioms). -/
structure MarkedDeformation (F : BasedCategory.{v, w} (Over (Spec (.of R))))
    (K : Type u) [Field K] [Algebra R K] (x₀ : Object F (affine R K))
    (M : Type u) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M] where
  obj : Object F (squareZeroAffine (R := R) K M)
  mark : Lift (squareZeroReduction K M) x₀ obj

/-- Isomorphism of marked deformations, fixing the special-fibre identification.
Source: Stacks, Artin, equation-tangent-space
(blueprint: def-sfb-artin-geometric-axioms). -/
def MarkedDeformation.Isomorphic {F : BasedCategory.{v, w} (Over (Spec (.of R)))}
    {K : Type u} [Field K] [Algebra R K] {x₀ : Object F (affine R K)}
    {M : Type u} [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
    (x y : MarkedDeformation F K x₀ M) : Prop :=
  ∃ a : x.obj ≅ y.obj, x.mark.val ≫ a.hom.val = y.mark.val

/-- Pullback along a linear map of square-zero ideals. Its arrow is tied to the
actual ring map; the special-fibre markings must agree.
Source: Stacks, Formal Deformation Theory, tangent-space operations
(blueprint: def-sfb-artin-geometric-axioms). -/
def MarkedDeformation.Induces {F : BasedCategory.{v, w} (Over (Spec (.of R)))}
    {K : Type u} [Field K] [Algebra R K] {x₀ : Object F (affine R K)}
    {M N : Type u} [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
    [AddCommGroup N] [Module K N] [Module Kᵐᵒᵖ N] [IsCentralScalar K N]
    (f : M →ₗ[K] N) (x : MarkedDeformation F K x₀ M)
    (y : MarkedDeformation F K x₀ N) : Prop :=
  ∃ a : Lift (squareZeroMap f) y.obj x.obj,
    y.mark.val ≫ a.val = x.mark.val

/-- Finite coordinates for the tangent space. They classify marked deformations
up to isomorphism and preserve the canonical sum and scalar operations, obtained
from projections, addition, and scalar multiplication of square-zero ideals.
Source: Stacks, Artin, equation-tangent-space and axiom [3]
(blueprint: def-sfb-artin-geometric-axioms). -/
def FiniteTangent (F : BasedCategory.{v, w} (Over (Spec (.of R))))
    (K : Type u) [Field K] [Algebra R K] (x₀ : Object F (affine R K)) : Prop :=
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
(blueprint: def-sfb-artin-geometric-axioms). -/
abbrev InfinitesimalAutomorphism {F : BasedCategory.{v, w} (Over (Spec (.of R)))}
    {K : Type u} [Field K] [Algebra R K] {x₀ : Object F (affine R K)}
    (x : MarkedDeformation F K x₀ K) :=
  {a : x.obj ≅ x.obj // x.mark.val ≫ a.hom.val = x.mark.val}

/-- Finite coordinates on infinitesimal automorphisms, respecting composition as
addition and the canonical pullback action of scalars on the trivial deformation.
Source: Stacks, Artin, equation-infinitesimal-automorphisms, axiom [3]
(blueprint: def-sfb-artin-geometric-axioms). -/
def FiniteInfinitesimalAutomorphisms (F : BasedCategory.{v, w} (Over (Spec (.of R))))
    (K : Type u) [Field K] [Algebra R K] (x₀ : Object F (affine R K)) : Prop :=
  ∀ (x : MarkedDeformation F K x₀ K)
    (p : Lift (squareZeroProjection K) x.obj x₀),
    x.mark.val ≫ p.val = 𝟙 x₀.val →
    ∃ (n : ℕ) (coord : InfinitesimalAutomorphism x → (Fin n → K)),
      Function.Bijective coord ∧
      (∀ a b c : InfinitesimalAutomorphism x,
        a.val.hom.val ≫ b.val.hom.val = c.val.hom.val → coord c = coord a + coord b) ∧
      ∀ (c : K) (a b : InfinitesimalAutomorphism x)
        (h : Lift (squareZeroMap (c • (LinearMap.id : K →ₗ[K] K)))
          x.obj x.obj),
        h.val ≫ p.val = p.val → x.mark.val ≫ h.val = x.mark.val →
        b.val.hom.val ≫ h.val = h.val ≫ a.val.hom.val → coord b = c • coord a

/-- Both infinitesimal spaces are finite-dimensional for every finite-type field
and every object in its fibre.
Source: Stacks, Artin, axiom [3], Tag 07Y4
(blueprint: def-sfb-artin-geometric-axioms). -/
def FiniteInfinitesimalSpaces (F : BasedCategory.{v, w} (Over (Spec (.of R)))) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra R K], Algebra.FiniteType R K →
    ∀ x₀ : Object F (affine R K),
      FiniteTangent F K x₀ ∧ FiniteInfinitesimalAutomorphisms F K x₀

/-- Positive-indexed infinitesimal neighbourhood with its R-structure.
Source: Stacks, Artin, formal objects (blueprint: def-sfb-artin-geometric-axioms). -/
abbrev AdicNeighbourhood (A : Type u) [CommRing A] [Algebra R A] [IsLocalRing A]
    (n : ℕ) : Over (Spec (.of R)) :=
  affine R (A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1))

/-- Canonical reduction between infinitesimal neighbourhoods.
Source: Stacks, Artin, formal objects (blueprint: def-sfb-artin-geometric-axioms). -/
def adicTransition (A : Type u) [CommRing A] [Algebra R A] [IsLocalRing A]
    {n m : ℕ} (h : n ≤ m) : AdicNeighbourhood (R := R) A n ⟶ AdicNeighbourhood A m :=
  affineMap (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)))

/-- Canonical inclusion of a positive infinitesimal neighbourhood.
Source: Stacks, Artin, formal objects (blueprint: def-sfb-artin-geometric-axioms). -/
def adicInclusion (A : Type u) [CommRing A] [Algebra R A] [IsLocalRing A]
    (n : ℕ) : AdicNeighbourhood (R := R) A n ⟶ affine R A :=
  affineMap (Ideal.Quotient.mkₐ R (IsLocalRing.maximalIdeal A ^ (n + 1)))

/-- A formal object, with all transition arrows and their coherence.
Source: Stacks, Artin, formal objects (blueprint: def-sfb-artin-geometric-axioms). -/
structure FormalSystem (F : BasedCategory.{v, w} (Over (Spec (.of R))))
    (A : Type u) [CommRing A] [Algebra R A] [IsLocalRing A] where
  obj : ∀ n : ℕ, Object F (AdicNeighbourhood A n)
  transition : ∀ (n m : ℕ) (h : n ≤ m), Lift (adicTransition A h) (obj n) (obj m)
  identity : ∀ n : ℕ, (transition n n le_rfl).val = 𝟙 (obj n).val
  composition : ∀ (n m k : ℕ) (h : n ≤ m) (h' : m ≤ k),
    (transition n m h).val ≫ (transition m k h').val =
      (transition n k (h.trans h')).val

/-- Effectivity with the specified transition identifications retained.
Source: Stacks, Artin, Tag 07XY (blueprint: def-sfb-artin-geometric-axioms). -/
def FormalObjectsEffective (F : BasedCategory.{v, w} (Over (Spec (.of R)))) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra R A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A],
    Algebra.FiniteType R (IsLocalRing.ResidueField A) →
    ∀ s : FormalSystem F A,
      ∃ (x : Object F (affine R A))
        (a : ∀ n : ℕ, Lift (adicInclusion A n) (s.obj n) x),
        ∀ (n m : ℕ) (h : n ≤ m), (s.transition n m h).val ≫ (a m).val = (a n).val

/-- Versality at the canonical residue-field point. Surjective residue maps with
maximal kernel specify the residue-field identifications without coefficient fields.
The last equation preserves the prescribed isomorphism of the original deformation.
Source: Stacks, Artin, definition-versal (blueprint: def-sfb-artin-geometric-axioms). -/
def IsVersalAt (F : BasedCategory.{v, w} (Over (Spec (.of R))))
    (U : Over (Spec (.of R))) (x : Object F U) (u₀ : U.left) : Prop :=
  ∀ (A A' : Type u) [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
    [IsLocalRing A] [IsLocalRing A'] [IsArtinianRing A] [IsArtinianRing A']
    (ρ : A →+* U.left.residueField u₀) (ρ' : A' →+* U.left.residueField u₀),
    Function.Surjective ρ → RingHom.ker ρ = IsLocalRing.maximalIdeal A →
    Function.Surjective ρ' → RingHom.ker ρ' = IsLocalRing.maximalIdeal A' →
    ∀ (g : A' →ₐ[R] A), Function.Surjective g → IsNilpotent (RingHom.ker g.toRingHom) →
      ρ.comp g.toRingHom = ρ' →
      ∀ (a : affine R A ⟶ U),
        Spec.map (CommRingCat.ofHom ρ) ≫ a.left = U.left.fromSpecResidueField u₀ →
        ∀ (y : Object F (affine R A)) (y' : Object F (affine R A'))
          (b : Lift (affineMap g) y y') (c : Lift a y x),
          ∃ (a' : affine R A' ⟶ U) (d : Lift a' y' x),
            affineMap g ≫ a' = a ∧ b.val ≫ d.val = c.val

/-- Versality propagates to finite type points of an open neighbourhood.
Source: Stacks, Artin, definition-openness-versality
(blueprint: def-sfb-artin-geometric-axioms). -/
def OpennessOfVersality (F : BasedCategory.{v, w} (Over (Spec (.of R)))) : Prop :=
  ∀ (U : Over (Spec (.of R))), LocallyOfFiniteType U.hom →
    ∀ (x : Object F U) (u₀ : U.left),
      (LocallyOfFiniteType (U.left.fromSpecResidueField u₀) ∧
        QuasiCompact (U.left.fromSpecResidueField u₀)) → IsVersalAt F U x u₀ →
      ∃ V : U.left.Opens, u₀ ∈ V ∧ ∀ t : U.left, t ∈ V →
        (LocallyOfFiniteType (U.left.fromSpecResidueField t) ∧
          QuasiCompact (U.left.fromSpecResidueField t)) → IsVersalAt F U x t

end AlgebraicGeometry.ArtinGeometry
