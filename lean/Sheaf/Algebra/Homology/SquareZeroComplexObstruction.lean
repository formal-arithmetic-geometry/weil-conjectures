/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q138
-/
module

public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Maps
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.Algebra.Homology.SubcategoryLeftResolution
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # The canonical obstruction to lifting a module complex

Source: Stacks Project, defos.tex, Tag 0DYR, lemma-canonical-class-algebra.
(blueprint: lem-sfb-square-zero-complex-obstruction).

The kernel is supplied as an R-module with an injective additive map to R'.
The exactness and action equations identify it with ker(q), including its
quotient-module action. The curvature predicate fixes the actual obstruction,
not merely its zero locus. All tensor products in the derived category are the
published K-flat derived monoidal structure on ordinary ModuleCat categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

/-- The degree-zero complex on the obstruction coefficient.
Source: Stacks 0DYR (blueprint: lem-sfb-square-zero-complex-obstruction). -/
abbrev obstructionCoefficientComplex {R : Type u} [CommRing R] (J : ModuleCat.{u} R) :=
  (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj J

/-- Tensoring a complex termwise with J. This is the total tensor with J[0],
via the published single-complex tensor comparison.
Source: Stacks 0DYR (blueprint: lem-sfb-square-zero-complex-obstruction). -/
abbrev obstructionTensorComplex {R : Type u} [CommRing R] (J : ModuleCat.{u} R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :=
  ((tensorRight J).mapHomologicalComplex (.up ℤ)).obj P

/-- The canonical comparison from derived tensor to ordinary tensor on a model.
It is invertible when P is K-flat. Its formula uses only the published lax
monoidal comparison of Q and the single-complex tensor identification.
Source: Stacks 0DYR (blueprint: lem-sfb-square-zero-complex-obstruction). -/
def obstructionTensorComparison {R : Type u} [CommRing R] (J : ModuleCat.{u} R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj (obstructionCoefficientComplex J) ⟶
      DerivedCategory.Q.obj (obstructionTensorComplex J P) :=
  Functor.LaxMonoidal.μ DerivedCategory.Q P (obstructionCoefficientComplex J) ≫
    DerivedCategory.Q.map (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) J P).hom

/-- A curvature-normalized obstruction for a particular bounded-above object.
The quantifiers range over every free model, every graded free lift, and every
lift of its differentials. The injective maps i identify P^n tensor J with JF^n
by the pure-tensor formula. The final identity is the curvature d'^2, transported
through Q, its shift comparison, and the canonical derived-tensor comparison.

Source: Stacks 0DYR, construction in the proof
(blueprint: lem-sfb-square-zero-complex-obstruction). -/
def IsSquareZeroComplexObstruction
    {Rp R : Type u} [CommRing Rp] [CommRing R] (q : Rp →+* R)
    (J : ModuleCat.{u} R) (j : J →+ Rp) (C : DerivedCategory (ModuleCat.{u} R))
    (ω : C ⟶ (C ⊗ DerivedCategory.Q.obj (obstructionCoefficientComplex J))⟦(2 : ℤ)⟧) :
    Prop :=
  ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (_hfree : ∀ n, Module.Free R (P.X n))
    (_hbounded : ∃ b : ℤ, ∀ n, b < n → IsZero (P.X n))
    (e : DerivedCategory.Q.obj P ≅ C)
    (F : ℤ → ModuleCat.{u} Rp) (_hF : ∀ n, Module.Free Rp (F n))
    (_hFb : ∃ b : ℤ, ∀ n, b < n → IsZero (F n))
    (p : ∀ n, F n →ₛₗ[q] P.X n) (_hp : ∀ n, Function.Surjective (p n))
    (_hpker : ∀ n, LinearMap.ker (p n) = RingHom.ker q • (⊤ : Submodule Rp (F n)))
    (i : ∀ n, P.X n ⊗[R] J →+ F n) (_hi : ∀ n, Function.Injective (i n))
    (_hi_formula : ∀ n (x : F n) (a : J), i n (p n x ⊗ₜ[R] a) = j a • x)
    (d : ∀ n, F n ⟶ F (n + 1))
    (_hd : ∀ n (x : F n), p (n + 1) (d n x) = P.d n (n + 1) (p n x))
    (w : P ⟶ (obstructionTensorComplex J P)⟦(2 : ℤ)⟧)
    (_hw : ∀ n (x : F n),
      HEq (i (n + 2) ((CochainComplex.shiftFunctorObjXIso
        (obstructionTensorComplex J P) 2 n (n + 2) rfl).hom (w.f n (p n x))))
        (d (n + 1) (d n x))),
    e.hom ≫ ω ≫
        ((e.inv ▷ DerivedCategory.Q.obj (obstructionCoefficientComplex J)) ≫
          obstructionTensorComparison J P)⟦(2 : ℤ)⟧' =
      DerivedCategory.Q.map w ≫
        (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app (obstructionTensorComplex J P)

/-- The unshifted comparison on a degree-zero coefficient for ordinary derived
scalar extension. Its counit fixes it on all modules, without a flatness choice.
Source: Stacks 0DYR, flat scalar-extension clause
(blueprint: lem-sfb-square-zero-complex-obstruction). -/
def obstructionCoefficientBaseChange
    {R U : Type u} [CommRing R] [CommRing U] (g : R →+* U)
    (J : ModuleCat.{u} R) (JU : ModuleCat.{u} U)
    (θ : (extendScalars g).obj J ≅ JU) :
    (ordinaryDerivedExtendScalars g).obj
        (DerivedCategory.Q.obj (obstructionCoefficientComplex J)) ⟶
      DerivedCategory.Q.obj (obstructionCoefficientComplex JU) :=
  (ordinaryDerivedChangeOfRings g).counit.app (obstructionCoefficientComplex J) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex (extendScalars g) (.up ℤ) 0).hom.app J ≫
        (HomologicalComplex.single (ModuleCat.{u} U) (.up ℤ) 0).map θ.hom)

/-- The existing exact derived-functor construction at a flat ring map, at the
same universe as the ordinary derived change of rings. This is only an abbreviation
for mapDerivedCategory, not a second derived scalar-extension construction.
Source: Stacks 0DYR (blueprint: lem-sfb-square-zero-complex-obstruction). -/
abbrev obstructionExactFlatExtension {R U : Type u} [CommRing R] [CommRing U]
    (g : R →+* U) (hg : g.Flat) :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} U) :=
  haveI : PreservesFiniteLimits (extendScalars g) :=
    preservesFiniteLimits_extendScalars_of_flat hg
  (extendScalars g).mapDerivedCategory

/-- The unique counit-compatible comparison with the exact derived functor.
The universal property fixes the isomorphism, hence also the transported shifts.
Source: Stacks 0DYR and 06YY (blueprint: lem-sfb-square-zero-complex-obstruction). -/
def obstructionFlatExtensionIso {R U : Type u} [CommRing R] [CommRing U]
    (g : R →+* U) (hg : g.Flat) :
    ordinaryDerivedExtendScalars g ≅ obstructionExactFlatExtension g hg :=
  haveI : PreservesFiniteLimits (extendScalars g) :=
    preservesFiniteLimits_extendScalars_of_flat hg
  haveI : (ordinaryDerivedExtendScalars g).IsLeftDerivedFunctor
      (ordinaryDerivedChangeOfRings g).counit
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)) :=
    (ordinaryDerivedChangeOfRings g).universal
  haveI := Functor.isLeftDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
    (extendScalars g).mapDerivedCategory (extendScalars g).mapDerivedCategoryFactors
  Functor.leftDerivedUnique (extendScalars g).mapDerivedCategory
    (ordinaryDerivedExtendScalars g) (ordinaryDerivedChangeOfRings g).counit
    (extendScalars g).mapDerivedCategoryFactors.hom
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))

/-- The canonical shift transport, obtained from the exact functor through the
unique counit-compatible comparison. An arbitrary triangulated shift is not chosen.
Source: Stacks 0DYR (blueprint: lem-sfb-square-zero-complex-obstruction). -/
@[instance_reducible]
def obstructionScalarShift {R U : Type u} [CommRing R] [CommRing U]
    (g : R →+* U) (hg : g.Flat) : (ordinaryDerivedExtendScalars g).CommShift ℤ :=
  haveI : PreservesFiniteLimits (extendScalars g) :=
    preservesFiniteLimits_extendScalars_of_flat hg
  Functor.CommShift.ofIso (obstructionFlatExtensionIso g hg).symm ℤ

/-- The derived scalar-extension comparison, using the normalized monoidal
structure, the coefficient comparison and the shift transport above.
Source: Stacks 0DYR (blueprint: lem-sfb-square-zero-complex-obstruction). -/
def obstructionBaseChangeComparison
    {R U : Type u} [CommRing R] [CommRing U] (g : R →+* U) (hg : g.Flat)
    (J : ModuleCat.{u} R) (JU : ModuleCat.{u} U)
    (θ : (extendScalars g).obj J ≅ JU) (C : DerivedCategory (ModuleCat.{u} R)) :
    (ordinaryDerivedExtendScalars g).obj
        ((C ⊗ DerivedCategory.Q.obj (obstructionCoefficientComplex J))⟦(2 : ℤ)⟧) ⟶
      ((ordinaryDerivedExtendScalars g).obj C ⊗
        DerivedCategory.Q.obj (obstructionCoefficientComplex JU))⟦(2 : ℤ)⟧ :=
  (Functor.CommShift.commShiftIso (F := ordinaryDerivedExtendScalars g)
      (self := obstructionScalarShift g hg) (2 : ℤ)).hom.app _ ≫
    (Functor.OplaxMonoidal.δ (ordinaryDerivedExtendScalars g) C
        (DerivedCategory.Q.obj (obstructionCoefficientComplex J)) ≫
      (ordinaryDerivedExtendScalars g).obj C ◁
        obstructionCoefficientBaseChange g J JU θ)⟦(2 : ℤ)⟧'

/-- Existence of the canonical square-zero lifting obstruction, its complete
vanishing criterion, naturality, and flat scalar-extension compatibility.

The coefficient map j is injective, has image ker(q), and has the prescribed
quotient action. Thus no auxiliary kernel module or action is assumed. The
base-change square is a pushout of commutative rings; hence it expresses exactly
U = U' tensor_R' R. The formula for θ pins the canonical isomorphism J tensor_R U
with the extended ideal. Curvature normalization fixes both obstruction maps.

Source: Stacks Project, defos.tex, Tag 0DYR, lemma-canonical-class-algebra (1)-(3),
restricted to flat scalar extension as in the DAG
(blueprint: lem-sfb-square-zero-complex-obstruction).

Proof (the eight steps of the accepted DAG split):
1. Truncate a representative above a cohomological bound using
   lem-weil-pbc-truncation-cohomology. Apply lem-sfb-subcategory-left-resolution
   to free modules. The resulting bounded-above free model is K-flat by
   lem-pc-module-bounded-flat-kflat.
2. Lift its free terms and differentials across q. Their consecutive composites
   land in JF and kill JF since J^2 = 0. Associativity of three differentials
   makes the factored curvature a chain map P -> (P tensor J)[2].
3. Lift a chain map between free models. Its differential defect factors through
   J. Expanding e'b' + b'd' gives e'e'a' - a'd'd', the homotopy comparing the two
   curvature maps. The target of the defect is degree n+1.
4. The bijection in lem-pc-ring-derived-map-representative realizes all derived
   maps and detects their homotopies. Step 3 proves choice independence and
   naturality; K-flatness identifies ordinary and derived tensor comparisons.
5. If the class vanishes, the same bijection gives a null homotopy g. Subtract
   its ideal-valued lift from d'. The correction squares to zero because J^2=0,
   so (d'-g)^2=0. This constructs the required bounded-above free lift.
6. Conversely resolve a given bounded-above lift by a bounded-above free complex.
   Its genuine differential gives zero curvature, so the canonical class is zero.
7. Tensor 0 -> J -> R' -> R -> 0 with U'. Use lem-weil-pbc-flat-tensor-exact and
   lem-weil-pbc-tensor-right-exact. This identifies J tensor_R U with JU' and
   proves U flat over R by the injection criterion of def-weil-pbc-flat-ring-map.
8. Base change the chosen free terms and lifted differentials. The equality
   (d' tensor 1)^2 = d'^2 tensor 1 identifies the curvature classes. Balancing
   gives (P tensor J) tensor U = (P tensor U) tensor_U JU'. These are derived
   identifications by flatness and K-flatness, with the coefficient formula for θ.
-/
theorem exists_squareZeroComplexObstruction
    {Rp R : Type u} [CommRing Rp] [CommRing R] (q : Rp →+* R)
    (hq : Function.Surjective q) (hJ : RingHom.ker q ^ 2 = ⊥)
    (J : ModuleCat.{u} R) (j : J →+ Rp) (hj : Function.Injective j)
    (hker : Set.range j = RingHom.ker q)
    (haction : ∀ (a : Rp) (x : J), j (q a • x) = a * j x) :
    ∃ ω : ∀ C : DerivedCategory (ModuleCat.{u} R),
        (∃ b : ℤ, C.IsLE b) →
          (C ⟶ (C ⊗ DerivedCategory.Q.obj (obstructionCoefficientComplex J))⟦(2 : ℤ)⟧),
      (∀ C hC, IsSquareZeroComplexObstruction q J j C (ω C hC)) ∧
      (∀ C hC, ω C hC = 0 ↔
        ∃ Cp : DerivedCategory (ModuleCat.{u} Rp), (∃ b : ℤ, Cp.IsLE b) ∧
          Nonempty ((ordinaryDerivedExtendScalars q).obj Cp ≅ C)) ∧
      (∀ (C D : DerivedCategory (ModuleCat.{u} R)) hC hD (f : C ⟶ D),
        f ≫ ω D hD = ω C hC ≫
          (f ▷ DerivedCategory.Q.obj (obstructionCoefficientComplex J))⟦(2 : ℤ)⟧') ∧
      (∀ (Up U : Type u) [CommRing Up] [CommRing U]
        (qp : Up →+* U) (f : Rp →+* Up) (g : R →+* U)
        (_hqp : Function.Surjective qp) (_hJU : RingHom.ker qp ^ 2 = ⊥)
        (_hf : f.Flat)
        (_hsquare : IsPushout (CommRingCat.ofHom q) (CommRingCat.ofHom f)
          (CommRingCat.ofHom g) (CommRingCat.ofHom qp))
        (JU : ModuleCat.{u} U) (jU : JU →+ Up) (_hjU : Function.Injective jU)
        (_hkerU : Set.range jU = RingHom.ker qp)
        (_hactionU : ∀ (a : Up) (x : JU), jU (qp a • x) = a * jU x)
        (C : DerivedCategory (ModuleCat.{u} R)) (hC : ∃ b : ℤ, C.IsLE b),
        ∃ hg : g.Flat, ∃ θ : (extendScalars g).obj J ≅ JU,
          (∀ (a : Up) (x : J), jU (θ.hom (qp a ⊗ₜ[R, g] x)) = a * f (j x)) ∧
          IsIso (obstructionBaseChangeComparison g hg J JU θ C) ∧
          (∃ b : ℤ, ((ordinaryDerivedExtendScalars g).obj C).IsLE b) ∧
          ∃ ωU : (ordinaryDerivedExtendScalars g).obj C ⟶
              ((ordinaryDerivedExtendScalars g).obj C ⊗
                DerivedCategory.Q.obj (obstructionCoefficientComplex JU))⟦(2 : ℤ)⟧,
            IsSquareZeroComplexObstruction qp JU jU _ ωU ∧
              (ordinaryDerivedExtendScalars g).map (ω C hC) ≫
                obstructionBaseChangeComparison g hg J JU θ C = ωU) := by
  sorry

end ModuleCat
