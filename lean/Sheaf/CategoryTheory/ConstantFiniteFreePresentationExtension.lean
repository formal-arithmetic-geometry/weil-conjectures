/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.CategoryTheory.SiteConstantModuleHom
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.CategoryTheory.RingedSiteModules

/-! # Constant finite free presentations after scalar extension

Source: Stacks Project, Modules on Sites, Tags 03EI, 03DA, 03ER(3), Section 03EK;
blueprint main-20261015, ctf-equals-bc, Local models
(blueprint: lem-sfb-constant-finite-free-presentation-extension).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ConstantFiniteFreePresentationExtension

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type (max u v)) [CommRing R]

/-- The finite categorical power of the regular module, including the empty power.
Source: Stacks 03EK (blueprint: lem-sfb-constant-finite-free-presentation-extension). -/
abbrev power (T : Sheaf J RingCat.{max u v}) (s : ℕ) : SheafOfModules.{max u v} T :=
  ∏ᶜ (fun _ : Fin s ↦ SheafOfModules.unit T)

/-- Evaluate a finite-power projection on sections. Source: Stacks 03EK
(blueprint: lem-sfb-constant-finite-free-presentation-extension). -/
abbrev coordinate (T : Sheaf J RingCat.{max u v}) (s : ℕ) (U : Cᵒᵖ)
    (x : (power J T s).val.obj U) (i : Fin s) : T.obj.obj U :=
  (Pi.π (fun _ : Fin s ↦ SheafOfModules.unit T) i).val.app U x

/-- Evaluate coordinates with the original commutative coefficient carrier.
Source: Stacks 03EK (blueprint: lem-sfb-constant-finite-free-presentation-extension). -/
abbrev commCoordinate (T : Sheaf J CommRingCat.{max u v}) (s : ℕ) (U : Cᵒᵖ)
    (x : (power J ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T) s).val.obj U)
    (i : Fin s) : T.obj.obj U :=
  coordinate J _ s U x i

variable (B : Sheaf J CommRingCat.{max u v})
  (σ : (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of R) ⟶ B)

/-- The specified object B tensor P_C, using the recorded scalar-extension construction.
Source: Stacks 03EK (blueprint: lem-sfb-constant-finite-free-presentation-extension). -/
def extension (P : ModuleCat.{max u v} R) :
    SheafOfModules.{max u v} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) :=
  SheafOfModules.changeOfRingsOfUniverses (C := C) (J := J) σ ((constantModuleHomFunctor J R).obj P)

/-- The specified map id tensor f_C. Source: Stacks 03EK
(blueprint: lem-sfb-constant-finite-free-presentation-extension). -/
def extensionMap {P Q : ModuleCat.{max u v} R} (f : P ⟶ Q) :
    extension J R B σ P ⟶ extension J R B σ Q :=
  SheafOfModules.changeOfRingsHomOfUniverses (C := C) (J := J) σ
    ((constantModuleHomFunctor J R).obj P)
    ((constantModuleHomFunctor J R).map f)

/-- All finite-power coordinate identifications, the same-matrix equation, and the
specified short exact presentation and isomorphism after scalar extension.
Source: Stacks 03EI, 03DA, 03ER(3), 03EK; blueprint Local models
(blueprint: lem-sfb-constant-finite-free-presentation-extension).

Proof: (1) Exact module sequences are exact constant presheaf sequences sectionwise;
exact module sheafification (lem-weil-pbc-site-r-module-presheaf-sheafification-exact)
gives exactness of the recorded constant functor, with the extended scalar actions.
(2) Sheafify coordinate projections; finite-limit preservation gives alpha, including
the empty product. Constant basis vectors go to coordinate basis sections.
(3) On section tensors define beta by b tensor x -> (b sigma(x_i))_i and its inverse
by (b_i) -> sum_i b_i tensor e_i. Balancing and basis expansion show the two composites
are identities. Restrictions commute with both formulas, and the finite power is a
sheaf, so module sheafification gives the asserted isomorphisms.
(4) Apply these formulas to A(e_j); its ith coordinate is a_ij. Thus conjugation gives
exactly the matrix with entries sigma(a_ij). This also proves naturality on finite free
modules. Empty sums handle either rank zero.
(5) Flatness (def-pc-flat-sheaf-modules) makes tensor exact. The tensor symmetry
identifies its order with this scalar extension. Exactness is detected on underlying
abelian sheaves, since kernels are sectionwise and cokernels sheafified sectionwise.
Apply lem-sp-exact-functor-preserves-homology and conjugate by beta: the arrows are
precisely A_B and beta_n.inv followed by E(v).
(6) A specified inverse to v remains inverse after constant sheafification and tensor;
compose with beta.inv. No flatness is used in this last step, including rank zero. -/
theorem constantFiniteFreePresentationExtension :
    exactFunctor _ _ (siteConstantModuleFunctorGeneral J R) ∧
    ∃ α : ∀ s : ℕ, (constantModuleHomFunctor J R).obj (ModuleCat.of R (Fin s → R)) ≅
        power J ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          ((constantSheaf J CommRingCat).obj (CommRingCat.of R))) s,
    ∃ β : ∀ s : ℕ, extension J R B σ (ModuleCat.of R (Fin s → R)) ≅
        power J ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) s,
      (∀ (s : ℕ) (U : Cᵒᵖ) (x : Fin s → R) (i : Fin s),
        commCoordinate J _ s U ((α s).hom.val.app U
          ((constantModuleHomUnit J R (ModuleCat.of R (Fin s → R))).app U x)) i =
        (constantModuleHomRingIso J R).hom.hom.app U
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app U (x i))) ∧
      (∀ (s : ℕ) (U : Cᵒᵖ)
        (x : ((constantModuleHomFunctor J R).obj
          (ModuleCat.of R (Fin s → R))).val.obj U) (b : B.obj.obj U) (i : Fin s),
        commCoordinate J _ s U ((β s).hom.val.app U
          (SheafOfModules.scalarExtensionRingIsoTmul σ _ U x b)) i =
        b * σ.hom.app U (commCoordinate J _ s U ((α s).hom.val.app U x) i)) ∧
      (∀ (s : ℕ) (U : Cᵒᵖ)
        (y : (power J ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) s).val.obj U),
        (β s).inv.val.app U y = ∑ i : Fin s,
          SheafOfModules.scalarExtensionRingIsoTmul σ _ U
            ((constantModuleHomUnit J R (ModuleCat.of R (Fin s → R))).app U
              (Pi.single i 1)) (commCoordinate J _ s U y i)) ∧
      (∀ (m n : ℕ) (A : ModuleCat.of R (Fin m → R) ⟶ ModuleCat.of R (Fin n → R)),
        ∃ A_B : power J ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) m ⟶
            power J ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) n,
          extensionMap J R B σ A ≫ (β n).hom = (β m).hom ≫ A_B ∧
          (∀ (U : Cᵒᵖ)
            (y : (power J ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) m).val.obj U)
            (i : Fin n),
            commCoordinate J _ n U (A_B.val.app U y) i = ∑ j : Fin m,
              σ.hom.app U ((constantModuleHomRingIso J R).hom.hom.app U
                ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app U
                  (A (Pi.single j 1) i))) * commCoordinate J _ m U y j) ∧
          (SheafOfModules.IsFlatOnSite (C := C) (J := J)
            (R := (constantSheaf J CommRingCat).obj (CommRingCat.of R))
            ((SheafOfModules.restrictScalars
              ((sheafCompose J (forget₂ CommRingCat RingCat)).map σ)).obj
                (SheafOfModules.unit ((sheafCompose J
                  (forget₂ CommRingCat RingCat)).obj B))) →
            ∀ (P : ModuleCat.{max u v} R) (q : ModuleCat.of R (Fin n → R) ⟶ P),
              Function.Injective A → Function.Exact A q → Function.Surjective q →
              ∃ h : A_B ≫ ((β n).inv ≫ extensionMap J R B σ q) = 0,
                (ShortComplex.mk A_B ((β n).inv ≫ extensionMap J R B σ q) h).ShortExact)) ∧
      (∀ (r : ℕ) (P : ModuleCat.{max u v} R)
        (q : ModuleCat.of R (Fin r → R) ≅ P),
        IsIso ((β r).inv ≫ extensionMap J R B σ q.hom)) := by
  sorry

end CategoryTheory.ConstantFiniteFreePresentationExtension
