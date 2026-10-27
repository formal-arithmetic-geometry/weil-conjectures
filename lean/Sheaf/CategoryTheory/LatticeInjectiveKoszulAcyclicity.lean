/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.CategoryTheory.LatticeCubicalSheafResolution
public import Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-! # Sectionwise injective acyclicity of the lattice Koszul complex

Source: current blueprint, direct-image stability proof paragraph (3), algebraic lattice
input; Stacks Tags 03CY, 03DI and 03EV
(blueprint: lem-sfb-lattice-injective-koszul-acyclicity).

The existing `KoszulModel` fixes the ordered differential and invariant augmentation.
The fixed internal Hom below uses the recorded sheaf Hom, through the section-module
equivalence, rather than a separately chosen closed structure on internal modules.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Profinite.DiscreteLattice

namespace Profinite.LatticeInjectiveKoszul

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

/-- The recorded equivalence, specialized to the coherent profinite site.
Source: paragraph (3), internal-module interpretation
(blueprint: lem-sfb-lattice-injective-koszul-acyclicity). -/
abbrev sectionEquivalence :=
  InternalAbelianSheafModule.sectionModuleEquivalence (coherentTopology Profinite.{u}) R.X

/-- The sheaf Hom from the regular-coefficient cubical term to the given module.
Source: paragraph (3), internal Hom clause
(blueprint: lem-sfb-lattice-injective-koszul-acyclicity). -/
abbrev rawHom (r : ℕ) (a : ℤ) (P : Equivariant R r) :=
  SheafOfModules.homObj.{u + 1, u, u + 1, u + 1}
    (R := InternalAbelianSheafModule.sectionRingSheaf (coherentTopology Profinite.{u}) R.X)
    ((sectionEquivalence R).functor.obj (LatticeCubical.term R r a (𝟙_ (Modules R))))
    ((sectionEquivalence R).functor.obj P.V)

/-- The simultaneous conjugation-minus-identity map, one component for every lattice vector.
Source: paragraph (3), conjugation-fixed internal Hom
(blueprint: lem-sfb-lattice-injective-koszul-acyclicity). -/
def conjugationDifference (r : ℕ) (a : ℤ) (P : Equivariant R r) :
    rawHom R r a P ⟶ ∏ᶜ fun _ : Fin r → ℤ ↦ rawHom R r a P :=
  Pi.lift fun v ↦
    SheafOfModules.homObjMap.{u + 1, u, u + 1, u + 1}
      (R := InternalAbelianSheafModule.sectionRingSheaf
        (coherentTopology Profinite.{u}) R.X)
      ((sectionEquivalence R).functor.map
        (LatticeCubical.translation R r a (-v) (𝟙_ (Modules R))))
      ((sectionEquivalence R).functor.map (P.ρ (Multiplicative.ofAdd v))) - 𝟙 _

/-- The submodule of sheaf Hom fixed by conjugation by every lattice vector.
Its inclusion is the kernel inclusion of `conjugationDifference`.
Source: paragraph (3), fixed internal Hom clause
(blueprint: lem-sfb-lattice-injective-koszul-acyclicity). -/
def fixedHom (r : ℕ) (a : ℤ) (P : Equivariant R r) :=
  kernel (conjugationDifference R r a P)

/-- The underlying abelian-group map on sections of an internal module morphism.
Source: paragraph (3), sectionwise exactness clause
(blueprint: lem-sfb-lattice-injective-koszul-acyclicity). -/
def sectionMap {M N : Modules R} (f : M ⟶ N) (U : Profinite.{u}) :
    M.X.obj.obj (op U) → N.X.obj.obj (op U) :=
  (f.hom.hom.app (op U)).hom

/-- A cubical generator evaluated at the section-ring unit. The tensor unit of internal
modules is the regular module, so its underlying abelian sheaf is the coefficient ring.
Source: paragraph (3), generators [v,I]
(blueprint: lem-sfb-lattice-injective-koszul-acyclicity). -/
def generatorSection (r : ℕ) (a : ℤ) (v : Fin r → ℤ)
    (I : IntegralLatticeCubical.Directions r a) (U : Profinite.{u}) :
    ((sectionEquivalence R).functor.obj
      (LatticeCubical.term R r a (𝟙_ (Modules R)))).val.obj (op U) :=
  (((sectionEquivalence R).functor.map
    (Limits.Sigma.ι (fun _ : (Fin r → ℤ) × IntegralLatticeCubical.Directions r a ↦
      𝟙_ (Modules R)) (v, I))).val.app (op U))
    (1 : (InternalAbelianSheafModule.sectionRings
      (coherentTopology Profinite.{u}) R.X).obj (op U))

/-- The Koszul functor is additive and degreewise exact. Evaluation on origin generators
identifies it naturally, as an augmented cochain complex, with the conjugation-fixed sheaf
Hom of the cubical resolution. The inverse has value T^v x_I on [v,I]. For equivariantly
injective coefficients its invariant augmentation is exact on every profinite object
and is a quasi-isomorphism.

Source: current blueprint, direct-image stability proof paragraph (3), algebraic lattice
input; Stacks Tags 03CY, 03DI, 03EV
(blueprint: lem-sfb-lattice-injective-koszul-acyclicity).

Proof, following the six DAG steps:
1. Put A_i=T_i-1. Commutativity and opposite ordered-subset signs cancel d squared.
Equivariant maps act coordinatewise. Forgetting the action creates kernels and cokernels
by lem-sfb-lattice-cubical-sheaf-resolution; finite biproducts are exact. Invariant sections
are killed by all A_i, giving the natural augmentation.
2. Pass through def-weil-pbc-internal-abelian-sheaf-module-equivalence. The tensor-Hom
adjunction lem-pc-sheaf-modules-tensor-closed identifies maps into fixed sheaf Hom with
equivariant maps L_a(Q) to P. Tensor preserves the cubical coproduct, and each such map
is determined by its values at [0,I], with [v,I] sent to T^v x_I.
3. Precomposition with the cubical boundary at [0,J] is the displayed signed sum of
(T_i-1)x_(J-i). The augmentation is evaluation at 1 followed by the cubical augmentation.
These calculations give the natural augmented cochain isomorphism and its inverse formula.
4. For any profinite U, sheafify the free module on its representable. By
 def-weil-presheaf-modules-sheafification and lem-weil-pbc-free-yoneda-presheaf-module,
Hom(Q_U,M)=M(U). The previous coordinates identify sections with Hom(L_a(Q_U),J).
5. The cubical resolution of Q_U is exact equivariantly, since it is split exact after
forgetting. A cocycle vanishes on the kernel of the outgoing boundary and factors through
its image. Injectivity extends the factored map to the preceding term. In degree zero
factor uniquely through the augmentation; at the top use the zero incoming boundary.
6. Thus the augmented section sequence is exact for every U. Sectionwise exactness
implies sheaf exactness, giving H^0=J^D and vanishing in all other degrees, hence QuasiIso.
No projectivity of Q_U or exactness of sections on arbitrary short exact sequences is used.
-/
theorem acyclicity (r : ℕ) :
    ∃ (K : KoszulModel R r),
      K.functor.Additive ∧
      (∀ a : ℤ, exactFunctor _ _
        (K.functor ⋙ HomologicalComplex.eval (Modules R) (.up ℤ) a)) ∧
      ∃ (H : Equivariant R r ⥤
          CochainComplex (SheafOfModules.{u + 1}
            ((sheafCompose (coherentTopology Profinite.{u}) (forget₂ CommRingCat RingCat)).obj
              (InternalAbelianSheafModule.sectionRingSheaf
                (coherentTopology Profinite.{u}) R.X))) ℤ)
        (c : ∀ (P : Equivariant R r) (a : ℤ), (H.obj P).X a ≅ fixedHom R r a P)
        (e : H ≅ K.functor ⋙ (sectionEquivalence R).functor.mapHomologicalComplex (.up ℤ)),
      ∃ A : ((invariants R r ⋙ (sectionEquivalence R).functor) ⋙
          HomologicalComplex.single _ (.up ℤ) 0) ⟶ H,
      (∀ P : Equivariant R r,
        A.app P ≫ e.hom.app P =
          (HomologicalComplex.singleMapHomologicalComplex
            (sectionEquivalence R).functor (.up ℤ) 0).inv.app ((invariants R r).obj P) ≫
          ((sectionEquivalence R).functor.mapHomologicalComplex (.up ℤ)).map
            (K.augmentation.app P)) ∧
      (∀ (P : Equivariant R r) (a : ℤ),
        (H.obj P).d a (a + 1) ≫ (c P (a + 1)).hom ≫
            kernel.ι (conjugationDifference R r (a + 1) P) =
          (c P a).hom ≫ kernel.ι (conjugationDifference R r a P) ≫
            SheafOfModules.homObjMap.{u + 1, u, u + 1, u + 1}
              (R := InternalAbelianSheafModule.sectionRingSheaf
                (coherentTopology Profinite.{u}) R.X)
              ((sectionEquivalence R).functor.map
                (LatticeCubical.incoming R r a (𝟙_ (Modules R))))
              (𝟙 ((sectionEquivalence R).functor.obj P.V))) ∧
      (∀ {P Q : Equivariant R r} (f : P ⟶ Q) (a : ℤ),
        (H.map f).f a ≫ (c Q a).hom ≫ kernel.ι (conjugationDifference R r a Q) =
          (c P a).hom ≫ kernel.ι (conjugationDifference R r a P) ≫
            SheafOfModules.homObjMap.{u + 1, u, u + 1, u + 1}
              (R := InternalAbelianSheafModule.sectionRingSheaf
                (coherentTopology Profinite.{u}) R.X) (𝟙 _)
              ((sectionEquivalence R).functor.map f.hom)) ∧
      (∀ (P : Equivariant R r) (a : ℤ) (U : Profinite.{u})
        (x : ((sectionEquivalence R).functor.obj ((K.functor.obj P).X a)).val.obj (op U))
        (v : Fin r → ℤ) (I : IntegralLatticeCubical.Directions r a),
        (((((e.inv.app P).f a ≫ (c P a).hom ≫
            kernel.ι (conjugationDifference R r a P)).val.app (op U)) x).app
              (op (Over.mk (𝟙 U)))).hom (generatorSection R r a v I U) =
        sectionMap R (P.ρ (Multiplicative.ofAdd v)) U
          ((((sectionEquivalence R).functor.map
            ((K.coordinates P a).hom ≫ biproduct.π _ ⟨I.val, I.property⟩)).val.app
              (op U)) x)) ∧
      (∀ (J : Equivariant R r) [Injective J],
        QuasiIso (K.augmentation.app J) ∧
        (∀ U : Profinite.{u}, Function.Injective
          (sectionMap R ((K.augmentation.app J).f 0) U)) ∧
        (∀ U : Profinite.{u}, Function.Exact
          (sectionMap R ((K.augmentation.app J).f 0) U)
          (sectionMap R ((K.functor.obj J).d 0 1) U)) ∧
        (∀ (a : ℤ), 0 < a → ∀ U : Profinite.{u}, Function.Exact
          (sectionMap R ((K.functor.obj J).d (a - 1) a) U)
          (sectionMap R ((K.functor.obj J).d a (a + 1)) U))) := by
  sorry

end Profinite.LatticeInjectiveKoszul
