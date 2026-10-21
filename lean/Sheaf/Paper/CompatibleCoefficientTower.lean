/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Compatible coefficient tensor towers

Source: Stacks Project, Modules on Sites, Tags 03EK, 03CY and 03DA;
Homology, Tag 011G (blueprint: lem-pur-compatible-coefficient-tower).

The natural-number index `n` represents the paper's positive index `n + 1`.
The tensor API writes the coefficient factor first, so `z ⊗ x` below is the
paper's `x ⊗ z`. Generators always mean images under the sheafification unit.
-/

@[expose] public section

universe uC vC u uk

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules

set_option autoImplicit false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}

/-- Forget commutativity of the coefficient sheaf, using the existing sheaf-composition
functor. Source: Stacks 03EK (blueprint: lem-pur-compatible-coefficient-tower). -/
abbrev coefficientTensorRing (R : Sheaf J CommRingCat.{u}) : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

variable {R S : Sheaf J CommRingCat.{u}} {B : ℕ → Sheaf J CommRingCat.{u}}
  (r : ∀ n, R ⟶ B n) (p : ∀ n, S ⟶ B n)

/-- The level module is the existing change of rings followed by restriction of scalars.
Source: Stacks 03EK (blueprint: lem-pur-compatible-coefficient-tower). -/
noncomputable def coefficientTensorLevel (n : ℕ)
    (M : ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing R)) :
    ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing S) :=
  (restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map (p n))).obj
      (changeOfRings.{vC, uC, u} (r n) M)

/-- Image of a presheaf pure tensor under the sheafification unit. The scalar factor
comes first in the existing change-of-rings API. Source: Stacks 03CY and 03EK
(blueprint: lem-pur-compatible-coefficient-tower). -/
noncomputable def coefficientTowerGenerator (n : ℕ)
    (M : ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing R)) (U : Cᵒᵖ)
    (x : M.val.obj U) (z : (B n).obj.obj U) :
    (coefficientTensorLevel r p n M).val.obj U :=
  (toSheafify J (changeOfRingsPresheaf.{vC, uC, u} (r n) M).presheaf).app U
    (z ⊗ₜ[R.obj.obj U, ((r n).hom.app U).hom] x)

/-- Restrict the existing global-sections linear structure along a coefficient map.
This specifies the induced scalar action used in the theorem, without choosing an
arbitrary linear structure. Source: Stacks 03EK, common-scalar calculation
(blueprint: lem-pur-compatible-coefficient-tower). -/
@[instance_reducible]
noncomputable def coefficientTowerScalarLinear (k : Type uk) [CommRing k]
    (T : Sheaf J CommRingCat.{u})
    (a : k →+* RingCat.sectionsSubring (T.obj ⋙ forget₂ CommRingCat RingCat)) :
    Linear k (ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing T)) :=
  letI : Linear (RingCat.sectionsSubring (T.obj ⋙ forget₂ CommRingCat RingCat))
      (ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing T)) :=
    homLinear T.obj (coefficientTensorRing T).property
  { homModule := fun M N ↦ Module.compHom (M ⟶ N) a
    smul_comp := fun M N P s f g ↦ Linear.smul_comp M N P (a s) f g
    comp_smul := fun M N P f s g ↦ Linear.comp_smul M N P f (a s) g }

/-- The linear-functor predicate with precisely the induced source scalar action and
componentwise induced target scalar action. Source: Stacks 03EK, common-scalar calculation
(blueprint: lem-pur-compatible-coefficient-tower). -/
def CoefficientTowerIsLinear
    (V : ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing R) ⥤
      (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing S)))
    (k : Type uk) [CommRing k]
    (aR : k →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
    (aS : k →+* RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat)) : Prop :=
  letI := coefficientTowerScalarLinear k R aR
  letI := coefficientTowerScalarLinear k S aS
  V.Linear k

/-- Compatible coefficient maps give an additive strict tensor tower, compatible with
homotopies, integer shifts and common scalars.

Source: Stacks 03EK (section-tensor-product), 03CY
(lemma-sheafification-presheaf-modules), 03DA (lemma-abelian), and Homology 011G
(definition-shift-cochain), with the agent-written strict-tower refinement
(blueprint: lem-pur-compatible-coefficient-tower).

Proof plan, following the node:
1. The balancing relation and the two coefficient compatibilities make
   `x ⊗ z ↦ x ⊗ b_n(z)` a natural map of presheaves of S-modules.
2. Apply lem-pc-sites-module-sheafification-interface and def-weil-pbc-sheafification.
   Sheafifying after restriction has the same abelian sheafification and the same
   extended S-action. The unit and pure tensors therefore determine a unique sheaf map.
3. The maps `f ⊗ 1` commute with transitions: both composites send a generator to
   `f(x) ⊗ b_n(z)`. Identity, composition and addition follow on the same generators.
4. Assemble adjacent transitions with def-weil-inverse-system. Functor laws and
   additivity hold componentwise; all longer transitions are the prescribed composites.
5. Apply this additive functor degreewise. Applying it to the homotopy equation
   gives the termwise image homotopy (def-weil-abstract-derived-category).
6. The integer-shift comparison is the identity in each degree. Additivity preserves
   the sign in the differential. Its tower naturality gives compatibility with every
   transition. Zero and addition coherence follow from identity components and reindexing.
7. By lem-weil-pbc-module-sheaves-colimits-forgetful, the two forgetful functors to
   abelian sheaves preserve kernels and cokernels. Restriction changes neither the
   underlying abelian sheaf nor its cohomology.
8. An inverse of an invertible underlying abelian-sheaf map is module-linear.
   Thus restriction preserves and reflects quasi-isomorphisms; no tensor flatness is used.
9. Global sections induce the displayed linear structures. On pure tensors, balancing
   and the equality of the two images of each scalar show `V(a f) = a V(f)`.

The level isomorphisms identify the values with the specified tensor modules, rather
than asking that two presentations of the same sheaf be definitionally equal. Uniqueness
is asserted for maps of those actual tensor modules, tested on presheaf generators.
The shift comparison is a morphism of towers, so its naturality already includes the
transition squares; its identity components fix the termwise comparison uniquely. -/
theorem exists_compatibleCoefficientTower
    (b : ∀ n, B (n + 1) ⟶ B n)
    (hr : ∀ n, r (n + 1) ≫ b n = r n)
    (hp : ∀ n, p (n + 1) ≫ b n = p n) :
    ∃ V : ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing R) ⥤
        (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing S)),
      ∃ e : ∀ (M : ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing R)) (n : ℕ),
        (V.obj M).obj (op n) ≅ coefficientTensorLevel r p n M,
      ∃ (_hV : V.Additive),
        (∀ (M : ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing R)) (n : ℕ),
          (∀ (U : Cᵒᵖ) (x : M.val.obj U) (z : (B (n + 1)).obj.obj U),
            (((e M (n + 1)).inv ≫
                (V.obj M).map (homOfLE (Nat.le_succ n)).op ≫ (e M n).hom).val.app U)
              (coefficientTowerGenerator r p (n + 1) M U x z) =
              coefficientTowerGenerator r p n M U x (((b n).hom.app U) z)) ∧
          (∀ t : coefficientTensorLevel r p (n + 1) M ⟶ coefficientTensorLevel r p n M,
            (∀ (U : Cᵒᵖ) (x : M.val.obj U) (z : (B (n + 1)).obj.obj U),
              t.val.app U (coefficientTowerGenerator r p (n + 1) M U x z) =
                coefficientTowerGenerator r p n M U x (((b n).hom.app U) z)) →
            t = (e M (n + 1)).inv ≫
              (V.obj M).map (homOfLE (Nat.le_succ n)).op ≫ (e M n).hom)) ∧
        (∀ (M N : ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing R))
          (f : M ⟶ N) (n : ℕ) (U : Cᵒᵖ) (x : M.val.obj U) (z : (B n).obj.obj U),
          (((e M n).inv ≫ (V.map f).app (op n) ≫ (e N n).hom).val.app U)
              (coefficientTowerGenerator r p n M U x z) =
            coefficientTowerGenerator r p n N U (f.val.app U x) z) ∧
        (∀ (K L : CochainComplex
            (ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing R)) ℤ)
          (f g : K ⟶ L), Homotopy f g →
          Nonempty (Homotopy ((V.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
            ((V.mapHomologicalComplex (ComplexShape.up ℤ)).map g))) ∧
        (∃ cs : (V.mapHomologicalComplex (ComplexShape.up ℤ)).CommShift ℤ,
          ∀ (K : CochainComplex
              (ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing R)) ℤ) (a i : ℤ),
            ((cs.commShiftIso a).hom.app K).f i = 𝟙 _) ∧
        (∀ (n : ℕ) (K L : CochainComplex
            (ringedSiteModules.{u, u, vC, uC} (coefficientTensorRing (B n))) ℤ)
          (f : K ⟶ L),
          QuasiIso (((restrictScalars.{u}
            ((sheafCompose J
              (forget₂ CommRingCat.{u} RingCat.{u})).map (p n))).mapHomologicalComplex
                (ComplexShape.up ℤ)).map f) ↔ QuasiIso f) ∧
        (∀ (k : Type uk) [CommRing k]
          (aR : k →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
          (aS : k →+* RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat)),
          (∀ (n : ℕ) (a : k) (U : Cᵒᵖ),
            ((r n).hom.app U) ((aR a).val U) = ((p n).hom.app U) ((aS a).val U)) →
          CoefficientTowerIsLinear V k aR aS) := by
  sorry

end SheafOfModules
