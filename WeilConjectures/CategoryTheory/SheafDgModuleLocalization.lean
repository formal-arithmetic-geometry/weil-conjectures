/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Triangulated.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import Mathlib.Topology.Sheaves.Sheaf

/-! # Left sheaf dg modules and their localization

Source: Stacks Project, sdga.tex, Tags 0FRF, 0FRI, 0FT5 and 0FS5,
section-shift and definition-pullback (blueprint: def-sfb-sheaf-dg-module-localization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated

namespace CategoryTheory.SheafDg

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} (S : Sheaf J CommRingCat.{w})

/-- The coefficient ring sheaf. Source: Stacks, sdga.tex, definition-dga
(blueprint: def-sfb-sheaf-dg-module-localization). -/
abbrev rings := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj S

/-- Integer cochain complexes of coefficient-module sheaves. Source: Stacks, definition-dga
(blueprint: def-sfb-sheaf-dg-module-localization). -/
abbrev Complex := CochainComplex (ringedSiteModules.{w} (rings S)) ℤ

/-- The total tensor of coefficient complexes, with Koszul differential.
Source: Stacks, definition-dga (blueprint: def-sfb-sheaf-dg-module-localization). -/
instance complexMonoidal : MonoidalCategory (Complex S) := by
  unfold Complex rings ringedSiteModules
  exact HomologicalComplex.monoidalCategory _ _

/-- Additivity of the fixed total tensor. Source: Stacks, definition-dga
(blueprint: def-sfb-sheaf-dg-module-localization).
Proof: on each summand the tensor of sheaf maps is additive in each argument.
The coproduct injections jointly detect equality, so the total tensor has the same property. -/
@[instance] theorem complexMonoidalPreadditive : MonoidalPreadditive (Complex S) := by
  sorry

/-- Tensor preserves the finite colimits used to impose balancing relations.
Source: Stacks, definition-pullback (blueprint: def-sfb-sheaf-dg-module-localization).
Proof: colimits of complexes are degreewise. Each term of total tensor is a coproduct
of sheaf tensors, each of which is a left adjoint. Interchange these colimits. -/
@[instance] theorem complexTensorPreservesFiniteColimits (M : Complex S) :
    PreservesFiniteColimits (tensorLeft M) := by
  sorry

/-- A sheaf dg algebra is an associative unital monoid in the total tensor of complexes.
The multiplication chain-map identity is precisely the signed Leibniz identity.
Source: Stacks, 0FRF (blueprint: def-sfb-sheaf-dg-module-localization). -/
abbrev Algebra := Mon (Complex S)

variable {S}

/-- Left modules, with action a chain map from A tensor M and with unit and associativity.
Source: Stacks, 0FRI, left-module convention
(blueprint: def-sfb-sheaf-dg-module-localization). -/
abbrev LeftModule (A : Algebra S) := Mod (Complex S) A.X

/-- The homogeneous action, as a map of coefficient-module sheaves.
Source: Stacks, 0FRI (blueprint: def-sfb-sheaf-dg-module-localization). -/
def action (A : Algebra S) (M : LeftModule A) (p q : ℤ) :
    A.X.X p ⊗ M.X.X q ⟶ M.X.X (p + q) :=
  HomologicalComplex.ιTensorObj A.X M.X p q (p + q) rfl ≫
    (ModObj.smul (M := A.X) (X := M.X)).f (p + q)

/-- The Koszul linearity condition on a degree r family of coefficient-linear sheaf maps.
HEq only transports the equality (p+q)+r=p+(q+r).
Source: Stacks, sdga.tex, section-homotopy, left convention
(blueprint: def-sfb-sheaf-dg-module-localization). -/
def GradedLinear (A : Algebra S) (M N : LeftModule A) (r : ℤ)
    (h : CochainComplex.HomComplex.Cochain M.X N.X r) : Prop :=
  ∀ p q : ℤ, HEq
    (action A M p q ≫ h.v (p + q) (p + q + r) rfl)
    (((r * p).negOnePow : ℤ) •
      (A.X.X p ◁ h.v q (q + r) rfl ≫ action A N p (q + r)))

/-- Degree-r graded left-module maps, without a differential-commutation requirement.
Source: Stacks, sdga.tex, section-homotopy
(blueprint: def-sfb-sheaf-dg-module-localization). -/
abbrev GradedMap (A : Algebra S) (M N : LeftModule A) (r : ℤ) :=
  { h : CochainComplex.HomComplex.Cochain M.X N.X r // GradedLinear A M N r h }

/-- Action-preserving homotopy: f-g=d h+h d, with the degree -1 Koszul linearity.
Source: Stacks, sdga.tex, section-homotopy, left convention
(blueprint: def-sfb-sheaf-dg-module-localization). -/
def homotopyRel (A : Algebra S) : HomRel (LeftModule A) :=
  fun M N f g ↦ ∃ h : Homotopy f.hom g.hom,
    GradedLinear A M N (-1) (CochainComplex.HomComplex.Cochain.ofHomotopy h)

/-- K_X(A), the quotient of module chain maps by the indicated homotopy congruence.
Source: Stacks, sdga.tex, section-homotopy
(blueprint: def-sfb-sheaf-dg-module-localization). -/
abbrev Homotopy (A : Algebra S) := CategoryTheory.Quotient (homotopyRel A)

/-- The quotient functor from dg modules to their homotopy category.
Source: Stacks, sdga.tex, section-homotopy
(blueprint: def-sfb-sheaf-dg-module-localization). -/
abbrev q (A : Algebra S) : LeftModule A ⥤ Homotopy A := Quotient.functor (homotopyRel A)

/-- Underlying cohomology sheaves on the homotopy quotient.
Source: Stacks, 0FT5 (blueprint: def-sfb-sheaf-dg-module-localization). -/
def cohomology (A : Algebra S) (n : ℤ) : Homotopy A ⥤ ringedSiteModules.{w} (rings S) :=
  Quotient.lift (homotopyRel A)
    (Mod.forget A.X ⋙ HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n)
    (fun _ _ _ _ h ↦ h.choose.homologyMap_eq n)

/-- Maps inducing isomorphisms on all underlying cohomology sheaves.
Source: Stacks, 0FT5 (blueprint: def-sfb-sheaf-dg-module-localization). -/
def quasiIsomorphisms (A : Algebra S) : MorphismProperty (Homotopy A) :=
  fun _ _ f ↦ ∀ n : ℤ, IsIso ((cohomology A n).map f)

/-- D_X(A): actual finite words in maps of K_X(A) and formal inverses to W, modulo
identity, composition and inverse relations, in the larger universe.
Source: Stacks, 0FT5 (blueprint: def-sfb-sheaf-dg-module-localization). -/
abbrev Derived (A : Algebra S) := (quasiIsomorphisms A).Localization

/-- The canonical word-localization functor Q_A.
Source: Stacks, 0FT5 (blueprint: def-sfb-sheaf-dg-module-localization). -/
abbrev Q (A : Algebra S) : Homotopy A ⥤ Derived A := (quasiIsomorphisms A).Q

/-- The canonical functor on dg modules, q followed by Q_A.
Source: Stacks, 0FT5 (blueprint: def-sfb-sheaf-dg-module-localization). -/
abbrev moduleQ (A : Algebra S) : LeftModule A ⥤ Derived A := q A ⋙ Q A

/-- The regular left module, with action multiplication.
Source: Stacks, 0FRI (blueprint: def-sfb-sheaf-dg-module-localization). -/
abbrev regular (A : Algebra S) : LeftModule A := Mod.regular A.X

/-- The module attached to an action on a fixed complex.
Source: Stacks, 0FRI (blueprint: def-sfb-sheaf-dg-module-localization). -/
def moduleOn (A : Algebra S) (K : Complex S) (a : ModObj A.X K) : LeftModule A :=
  @Mod.mk _ _ _ _ _ _ _ _ K a

/-- The prescribed shifted action: (-1)^(k p) on elements of algebra degree p.
The ordinary complex shift already has differential (-1)^k d.
Source: Stacks, section-shift, left convention
(blueprint: def-sfb-sheaf-dg-module-localization). -/
def IsShiftAction (A : Algebra S) (M : LeftModule A) (k : ℤ)
    (a : ModObj A.X (M.X⟦k⟧)) : Prop :=
  ∀ p q : ℤ, HEq
    (action A (moduleOn A _ a) p q ≫
      (M.X.shiftFunctorObjXIso k (p + q) (p + q + k) rfl).hom)
    (((k * p).negOnePow : ℤ) •
      (A.X.X p ◁ (M.X.shiftFunctorObjXIso k q (q + k) rfl).hom ≫
        action A M p (q + k)))

/-- The signed formula determines a unique action on the actual shifted complex.
Source: Stacks, section-shift and section-shift-dg, left convention
(blueprint: def-sfb-sheaf-dg-module-localization).
Proof: on each tensor summand put (-1)^(k p) times the old action, transported
through the degree identifications. The coproduct universal property assembles it.
The Leibniz identity verifies the chain-map condition; signs multiply under algebra
multiplication. The unit has degree zero. Tensor generators give uniqueness. -/
theorem existsUnique_shiftAction (A : Algebra S) (M : LeftModule A) (k : ℤ) :
    ∃! a : ModObj A.X (M.X⟦k⟧), IsShiftAction A M k a := by
  sorry

/-- Shifted modules, using the unique signed action on the specified complex.
Source: Stacks, section-shift-dg (blueprint: def-sfb-sheaf-dg-module-localization). -/
def shift (A : Algebra S) (k : ℤ) (M : LeftModule A) : LeftModule A :=
  moduleOn A (M.X⟦k⟧) (existsUnique_shiftAction A M k).choose

/-- The shifted chain map preserves the signed left actions.
Source: Stacks, section-shift-dg (blueprint: def-sfb-sheaf-dg-module-localization).
Proof: both actions multiply the old action equation for f by the same sign
(-1)^(k p); degree identifications are natural in the complex. -/
theorem shiftMap_linear (A : Algebra S) (k : ℤ) {M N : LeftModule A} (f : M ⟶ N) :
    IsModHom A.X (@id ((shift A k M).X ⟶ (shift A k N).X) (f.hom⟦k⟧')) := by
  sorry

/-- The shift functor on dg modules, acting by the shifted chain maps.
Source: Stacks, section-shift-dg (blueprint: def-sfb-sheaf-dg-module-localization). -/
def shiftFunctor (A : Algebra S) (k : ℤ) : LeftModule A ⥤ LeftModule A where
  obj := shift A k
  map f := { hom := f.hom⟦k⟧', isModHom := shiftMap_linear A k f }
  map_id M := Mod.hom_ext _ _ ((CategoryTheory.shiftFunctor (Complex S) k).map_id M.X)
  map_comp f g := Mod.hom_ext _ _
    ((CategoryTheory.shiftFunctor (Complex S) k).map_comp f.hom g.hom)

/-- The canonical shift on the word localization, uniquely determined on module maps.
Source: Stacks, 0FT5 and section-shift-dg
(blueprint: def-sfb-sheaf-dg-module-localization).
Proof: shifting a signed homotopy gives a signed homotopy, and shifted cohomology
is reindexed cohomology. Descend through the homotopy quotient and the word
localization. Both quotient and word localization have unique factorization,
which proves the uniqueness asserted here. -/
theorem existsUnique_derivedShift (A : Algebra S) (k : ℤ) :
    ∃! F : Derived A ⥤ Derived A,
      moduleQ A ⋙ F = shiftFunctor A k ⋙ moduleQ A := by
  sorry

/-- Derived shift, determined by the actual signed shift before localization.
Source: Stacks, 0FT5 (blueprint: def-sfb-sheaf-dg-module-localization). -/
def derivedShift (A : Algebra S) (k : ℤ) : Derived A ⥤ Derived A :=
  (existsUnique_derivedShift A k).choose

/-- Derived shift agrees on objects with the image of the specified signed module shift.
Source: Stacks, 0FT5 and section-shift-dg
(blueprint: def-sfb-sheaf-dg-module-localization).
Proof: the defining factorization of derivedShift equates moduleQ followed by derivedShift
with shiftFunctor followed by moduleQ. Evaluate that equality of functors at M; the
object part of shiftFunctor is the signed module shift. -/
theorem derivedShift_obj (A : Algebra S) (k : ℤ) (M : LeftModule A) :
    (derivedShift A k).obj ((moduleQ A).obj M) = (moduleQ A).obj (shift A k M) := by
  sorry

/-- The cone action is componentwise, with the Koszul sign on its shifted source.
Mathlib orders its cone as source[1] plus target; the projections fix this convention.
Source: Stacks, 0FS5, left convention
(blueprint: def-sfb-sheaf-dg-module-localization). -/
def IsConeAction (A : Algebra S) {M N : LeftModule A} (f : M ⟶ N)
    (a : ModObj A.X (CochainComplex.mappingCone f.hom)) : Prop :=
  (∀ p q : ℤ, HEq
    (action A (moduleOn A _ a) p q ≫
      (CochainComplex.mappingCone.snd f.hom).v (p + q) (p + q) (add_zero _))
    (A.X.X p ◁ (CochainComplex.mappingCone.snd f.hom).v q q (add_zero _) ≫
      action A N p q)) ∧
  (∀ p q : ℤ, HEq
    (action A (moduleOn A _ a) p q ≫
      (CochainComplex.mappingCone.fst f.hom).val.v (p + q) (p + q + 1) rfl)
    ((p.negOnePow : ℤ) •
      (A.X.X p ◁ (CochainComplex.mappingCone.fst f.hom).val.v q (q + 1) rfl ≫
        action A M p (q + 1))))

/-- The specified cone complex carries exactly one componentwise left action.
Source: Stacks, 0FS5 (blueprint: def-sfb-sheaf-dg-module-localization).
Proof: use the target action on the target summand and the signed shifted action
on the source summand. The two biproduct projections determine each component.
The off-diagonal differential is compatible because f preserves the action;
the diagonal terms satisfy the Leibniz identities. Unit and associativity hold
on each projection. Joint injectivity of the projections proves uniqueness. -/
theorem existsUnique_coneAction (A : Algebra S) {M N : LeftModule A} (f : M ⟶ N) :
    ∃! a : ModObj A.X (CochainComplex.mappingCone f.hom), IsConeAction A f a := by
  sorry

/-- The actual cone module, whose differential is (d_N n+f m,-d_M m).
Source: Stacks, 0FS5 (blueprint: def-sfb-sheaf-dg-module-localization). -/
def cone (A : Algebra S) {M N : LeftModule A} (f : M ⟶ N) : LeftModule A :=
  moduleOn A _ (existsUnique_coneAction A f).choose

/-- The inclusion and negative projection are module chain maps.
Source: Stacks, 0FS5 and the signed cone convention of the abstract derived category
(blueprint: def-sfb-sheaf-dg-module-localization).
Proof: apply the two componentwise action equations for the cone. The inclusion
has zero shifted component. The connecting map is the negative source projection;
its sign occurs on both sides of the action equation. -/
theorem coneMaps_linear (A : Algebra S) {M N : LeftModule A} (f : M ⟶ N) :
    IsModHom A.X
      (@id (N.X ⟶ (cone A f).X) (CochainComplex.mappingCone.inr f.hom)) ∧
    IsModHom A.X (@id ((cone A f).X ⟶ (shift A 1 M).X)
      (CochainComplex.mappingCone.triangle f.hom).mor₃) := by
  sorry

/-- Inclusion into the cone.
Source: Stacks, 0FS5 (blueprint: def-sfb-sheaf-dg-module-localization). -/
def coneIn (A : Algebra S) {M N : LeftModule A} (f : M ⟶ N) : N ⟶ cone A f :=
  { hom := CochainComplex.mappingCone.inr f.hom, isModHom := (coneMaps_linear A f).1 }

/-- The specified negative projection from the cone to the shifted source.
Source: Stacks, 0FS5 (blueprint: def-sfb-sheaf-dg-module-localization). -/
def coneConnecting (A : Algebra S) {M N : LeftModule A} (f : M ⟶ N) :
    cone A f ⟶ shift A 1 M :=
  { hom := (CochainComplex.mappingCone.triangle f.hom).mor₃,
    isModHom := (coneMaps_linear A f).2 }

/-- The zero-shift comparison M[0] → M of complexes preserves the actions.
Source: Stacks, section-shift-dg (blueprint: def-sfb-sheaf-dg-module-localization).
Proof: in each degree the comparison is the index identification i+0=i. For k=0
the Koszul sign (-1)^(0 p) is one, so IsShiftAction is the old action equation. -/
theorem shiftZero_linear (A : Algebra S) (M : LeftModule A) :
    IsModHom A.X (@id ((shift A 0 M).X ⟶ M.X)
      ((CategoryTheory.shiftFunctorZero (Complex S) ℤ).hom.app M.X)) := by
  sorry

/-- The canonical module map M[0] → M, the complex zero-shift comparison.
Source: Stacks, section-shift-dg (blueprint: def-sfb-sheaf-dg-module-localization). -/
def shiftZeroHom (A : Algebra S) (M : LeftModule A) : shift A 0 M ⟶ M :=
  { hom := (CategoryTheory.shiftFunctorZero (Complex S) ℤ).hom.app M.X,
    isModHom := shiftZero_linear A M }

/-- The addition comparison M[a+b] → M[a][b] of complexes preserves the actions.
Source: Stacks, section-shift-dg (blueprint: def-sfb-sheaf-dg-module-localization).
Proof: in each degree the comparison is an index identification without sign.
The action on M[a][b] carries (-1)^(b p)(-1)^(a p)=(-1)^((a+b) p), which is the
sign on M[a+b]; so the two IsShiftAction equations agree. -/
theorem shiftAdd_linear (A : Algebra S) (a b : ℤ) (M : LeftModule A) :
    IsModHom A.X (@id ((shift A (a + b) M).X ⟶ (shift A b (shift A a M)).X)
      ((CategoryTheory.shiftFunctorAdd (Complex S) a b).hom.app M.X)) := by
  sorry

/-- The canonical module map M[a+b] → M[a][b], the complex addition comparison.
Source: Stacks, section-shift-dg (blueprint: def-sfb-sheaf-dg-module-localization). -/
def shiftAddHom (A : Algebra S) (a b : ℤ) (M : LeftModule A) :
    shift A (a + b) M ⟶ shift A b (shift A a M) :=
  { hom := (CategoryTheory.shiftFunctorAdd (Complex S) a b).hom.app M.X,
    isModHom := shiftAdd_linear A a b M }

/-- An integer-shift structure on D_X(A) whose functors are the derived shifts and
whose zero and addition comparisons are the localized complex comparisons.
Every object of the word localization is the image of a module, so these
components fix both comparisons.
Source: Stacks, section-shift-dg (blueprint: def-sfb-sheaf-dg-module-localization). -/
def IsDerivedShift (A : Algebra S) (H : HasShift (Derived A) ℤ) : Prop :=
  ∃ hF : ∀ k : ℤ, @CategoryTheory.shiftFunctor (Derived A) ℤ _ _ H k = derivedShift A k,
    (∀ M : LeftModule A,
      (@shiftFunctorZero (Derived A) ℤ _ _ H).hom.app ((moduleQ A).obj M) =
        eqToHom (by rw [hF]; exact derivedShift_obj A 0 M) ≫
          (moduleQ A).map (shiftZeroHom A M)) ∧
    (∀ (a b : ℤ) (M : LeftModule A),
      (@shiftFunctorAdd (Derived A) ℤ _ _ H a b).hom.app ((moduleQ A).obj M) =
        eqToHom (by rw [hF]; exact derivedShift_obj A (a + b) M) ≫
          (moduleQ A).map (shiftAddHom A a b M) ≫
          eqToHom (by
            rw [hF, hF]
            exact (derivedShift_obj A b (shift A a M)).symm.trans
              (congrArg (derivedShift A b).obj (derivedShift_obj A a M).symm)))

/-- The integer-shift structure with the already fixed functors on the localization
and the localized canonical zero and addition comparisons.
Source: Stacks, section-shift-dg (blueprint: def-sfb-sheaf-dg-module-localization).
Proof: shiftZeroHom and shiftAddHom are natural module isomorphisms and send signed
homotopies and cohomology isomorphisms to the same; descend them through the homotopy
quotient and the word localization. The unit and pentagon identities descend from
those of complex shifts, since localization is faithful on transformations out of it.
Uniqueness: every object of the word localization is the image of a module, so the
functors and these components determine the monoidal shift functor. -/
theorem existsUnique_derivedHasShift (A : Algebra S) :
    ∃! H : HasShift (Derived A) ℤ, IsDerivedShift A H := by
  sorry

/-- Integer shifts with the prescribed signed functors and canonical comparisons.
Source: Stacks, section-shift-dg (blueprint: def-sfb-sheaf-dg-module-localization). -/
instance derivedHasShift (A : Algebra S) : HasShift (Derived A) ℤ :=
  (existsUnique_derivedHasShift A).choose

/-- The comparison between the image of the actual shifted module and derived shift.
Both functors and their values are fixed by their exact localization factorizations.
Source: Stacks, section-shift-dg (blueprint: def-sfb-sheaf-dg-module-localization). -/
def shiftObjectIso (A : Algebra S) (k : ℤ) (M : LeftModule A) :
    (moduleQ A).obj (shift A k M) ≅ ((moduleQ A).obj M)⟦k⟧ :=
  eqToIso ((derivedShift_obj A k M).symm.trans
      (congrArg (fun F : Derived A ⥤ Derived A ↦ F.obj ((moduleQ A).obj M))
        ((existsUnique_derivedHasShift A).choose_spec.1.choose k).symm))

/-- The specified cone triangle has the negative projection as connecting morphism.
Source: Stacks, 0FS5 and the signed convention of def-weil-abstract-derived-category
(blueprint: def-sfb-sheaf-dg-module-localization). -/
def coneTriangle (A : Algebra S) {M N : LeftModule A} (f : M ⟶ N) :
    Triangle (Derived A) :=
  Triangle.mk ((moduleQ A).map f) ((moduleQ A).map (coneIn A f))
    ((moduleQ A).map (coneConnecting A f) ≫ (shiftObjectIso A 1 M).hom)

/-- The specified triangles and exactly their isomorphic images.
Source: Stacks, 0FT5, section-distinguished
(blueprint: def-sfb-sheaf-dg-module-localization). -/
def IsConeTriangle (A : Algebra S) (t : Triangle (Derived A)) : Prop :=
  ∃ (M N : LeftModule A) (f : M ⟶ N), Nonempty (t ≅ coneTriangle A f)

/-- Underlying complexes, modulo ordinary homotopy.
Source: Stacks, 0FT5 (blueprint: def-sfb-sheaf-dg-module-localization). -/
def forgetHomotopy (A : Algebra S) :
    Homotopy A ⥤ HomotopyCategory (ringedSiteModules.{w} (rings S)) (ComplexShape.up ℤ) :=
  Quotient.lift (homotopyRel A)
    (Mod.forget A.X ⋙ HomotopyCategory.quotient _ (ComplexShape.up ℤ))
    (fun _ _ _ _ h ↦ HomotopyCategory.eq_of_homotopy _ _ h.choose)

section Forget

variable [HasDerivedCategory (ringedSiteModules.{w} (rings S))]

/-- Underlying homotopy maps followed by the ordinary derived localization.
Source: Stacks, 0FT5 (blueprint: def-sfb-sheaf-dg-module-localization). -/
def forgetBeforeLocalization (A : Algebra S) :
    Homotopy A ⥤ DerivedCategory (ringedSiteModules.{w} (rings S)) :=
  forgetHomotopy A ⋙ DerivedCategory.Qh

/-- The underlying derived functor inverts precisely the cohomology-isomorphism input W.
Source: Stacks, 0FT5 (blueprint: def-sfb-sheaf-dg-module-localization).
Proof: represent a homotopy class by a chain map. The cohomology functors used
here are the ordinary cohomology functors of this underlying complex, so the
hypothesis makes its representative a quasi-isomorphism. DerivedCategory.Q
inverts it. Quotient induction then gives the assertion for every class. -/
theorem forget_inverts (A : Algebra S) :
    (quasiIsomorphisms A).IsInvertedBy (forgetBeforeLocalization A) := by
  sorry

/-- Forget the action on words; a formal inverse is sent to the inverse of the
underlying derived map. This is the actual word-localization lift.
Source: Stacks, 0FT5 (blueprint: def-sfb-sheaf-dg-module-localization). -/
def forget (A : Algebra S) :
    Derived A ⥤ DerivedCategory (ringedSiteModules.{w} (rings S)) :=
  Localization.Construction.lift (forgetBeforeLocalization A) (forget_inverts A)

end Forget

/-- Restriction of scalars keeps the complex and precomposes the left action with φ.
Source: Stacks, definition-pullback (blueprint: def-sfb-sheaf-dg-module-localization). -/
abbrev restrictScalars {A B : Algebra S} (φ : A ⟶ B) : LeftModule B ⥤ LeftModule A :=
  Mod.comap φ.hom

/-- The first balancing arrow, (b,a,m) ↦ (b φ(a),m), expressed by the free-module
adjunction. No commutativity of the dg algebra is required.
Source: Stacks, definition-pullback (blueprint: def-sfb-sheaf-dg-module-localization). -/
def balanceLeft {A B : Algebra S} (φ : A ⟶ B) (M : LeftModule A) :
    (Mod.free B.X).obj (A.X ⊗ M.X) ⟶ (Mod.free B.X).obj M.X :=
  Mod.freeDesc B.X (φ.hom ▷ M.X)

/-- The second balancing arrow, (b,a,m) ↦ (b,a m).
Source: Stacks, definition-pullback (blueprint: def-sfb-sheaf-dg-module-localization). -/
def balanceRight {A B : Algebra S} (_φ : A ⟶ B) (M : LeftModule A) :
    (Mod.free B.X).obj (A.X ⊗ M.X) ⟶ (Mod.free B.X).obj M.X :=
  (Mod.free B.X).map (ModObj.smul (M := A.X) (X := M.X))

/-- Ordinary extension is the actual balanced quotient of the sheafified direct-sum
 total tensor. Its differential and left action are inherited from the free B-module.
Source: Stacks, definition-pullback (blueprint: def-sfb-sheaf-dg-module-localization). -/
def extensionObj {A B : Algebra S} (φ : A ⟶ B) (M : LeftModule A) : LeftModule B :=
  coequalizer (balanceLeft φ M) (balanceRight φ M)

/-- The quotient map from B tensor M onto its balanced tensor.
Source: Stacks, definition-pullback (blueprint: def-sfb-sheaf-dg-module-localization). -/
def extensionπ {A B : Algebra S} (φ : A ⟶ B) (M : LeftModule A) :
    (Mod.free B.X).obj M.X ⟶ extensionObj φ M :=
  coequalizer.π (balanceLeft φ M) (balanceRight φ M)

/-- Tensoring a module map descends uniquely to the balanced quotient.
Source: Stacks, definition-pullback (blueprint: def-sfb-sheaf-dg-module-localization).
Proof: id_B tensor f sends both relations to the same relation, since f preserves
A-action. The coequalizer universal property gives the unique descended map. -/
theorem existsUnique_extensionMap {A B : Algebra S} (φ : A ⟶ B)
    {M N : LeftModule A} (f : M ⟶ N) :
    ∃! g : extensionObj φ M ⟶ extensionObj φ N,
      extensionπ φ M ≫ g = (Mod.free B.X).map f.hom ≫ extensionπ φ N := by
  sorry

/-- Extension on a chain map, uniquely determined on pure tensor generators.
Source: Stacks, definition-pullback (blueprint: def-sfb-sheaf-dg-module-localization). -/
def extensionMap {A B : Algebra S} (φ : A ⟶ B) {M N : LeftModule A} (f : M ⟶ N) :
    extensionObj φ M ⟶ extensionObj φ N := (existsUnique_extensionMap φ f).choose

/-- The descended maps satisfy functor identities.
Source: Stacks, definition-pullback (blueprint: def-sfb-sheaf-dg-module-localization).
Proof: precompose each identity with the quotient projection. The defining equations
reduce the claims to functoriality of the free-module functor; uniqueness of the
coequalizer factorization proves both equations. -/
theorem extensionMap_laws {A B : Algebra S} (φ : A ⟶ B) :
    (∀ M : LeftModule A, extensionMap φ (𝟙 M) = 𝟙 (extensionObj φ M)) ∧
    (∀ (M N P : LeftModule A) (f : M ⟶ N) (g : N ⟶ P),
      extensionMap φ (f ≫ g) = extensionMap φ f ≫ extensionMap φ g) := by
  sorry

/-- Ordinary extension of scalars, by the actual coequalizers of the balancing arrows.
Source: Stacks, definition-pullback (blueprint: def-sfb-sheaf-dg-module-localization). -/
def extension {A B : Algebra S} (φ : A ⟶ B) : LeftModule A ⥤ LeftModule B where
  obj := extensionObj φ
  map := extensionMap φ
  map_id := (extensionMap_laws φ).1
  map_comp := (extensionMap_laws φ).2 _ _ _

/-- Extension carries signed A-linear homotopies to signed B-linear homotopies,
so its localization descends to K_X(A).
Source: Stacks, definition-pullback (blueprint: def-sfb-sheaf-dg-module-localization).
Proof: on homogeneous tensors set H(b tensor m)=(-1)^degree(b) b tensor h(m).
The graded A-linearity of h makes H balanced. Its boundary is id_B tensor (f-g).
Thus the two extensions are B-linearly homotopic, hence have the same image under q_B. -/
theorem extension_homotopy {A B : Algebra S} (φ : A ⟶ B)
    (M N : LeftModule A) (f g : M ⟶ N) (h : homotopyRel A f g) :
    (extension φ ⋙ moduleQ B).map f = (extension φ ⋙ moduleQ B).map g := by
  sorry

/-- The ordinary extension followed by Q_B, on the homotopy category K_X(A).
Source: Stacks, definition-pullback (blueprint: def-sfb-sheaf-dg-module-localization). -/
def extensionBar {A B : Algebra S} (φ : A ⟶ B) : Homotopy A ⥤ Derived B :=
  Quotient.lift (homotopyRel A) (extension φ ⋙ moduleQ B) (extension_homotopy φ)

/-- Derived extension notation consists of a functor and a right Kan extension
comparison. Existence is not asserted. The displayed bijectivity is precisely
Nat(V,LF) ≃ Nat(Q_A ⋙ V,Fbar), by postcomposition with epsilon.
Source: Stacks, definition-pullback and the universal-property convention in the node
(blueprint: def-sfb-sheaf-dg-module-localization). -/
structure DerivedExtension {A B : Algebra S} (φ : A ⟶ B) where
  functor : Derived A ⥤ Derived B
  comparison : Q A ⋙ functor ⟶ extensionBar φ
  universal (V : Derived A ⥤ Derived B) : Function.Bijective
    (fun η : V ⟶ functor ↦ CategoryTheory.Functor.whiskerLeft (Q A) η ≫ comparison)

/-- Multiplication b tensor n ↦ b n descends uniquely through the balanced quotient.
Source: Stacks, definition-pullback (blueprint: def-sfb-sheaf-dg-module-localization).
Proof: the two balancing maps followed by the B-action agree by the module
associativity axiom and the definition of the restricted action. Factor the
B-linear free action map through the coequalizer. Its projection is epi, giving uniqueness. -/
theorem existsUnique_actionCounit {A B : Algebra S} (φ : A ⟶ B) (N : LeftModule B) :
    ∃! g : extensionObj φ ((restrictScalars φ).obj N) ⟶ N,
      extensionπ φ ((restrictScalars φ).obj N) ≫ g = Mod.freeDesc B.X (𝟙 N.X) := by
  sorry

/-- The ordinary specified action counit on the balanced tensor.
Source: Stacks, definition-pullback (blueprint: def-sfb-sheaf-dg-module-localization). -/
def actionCounit {A B : Algebra S} (φ : A ⟶ B) (N : LeftModule B) :
    extensionObj φ ((restrictScalars φ).obj N) ⟶ N :=
  (existsUnique_actionCounit φ N).choose

/-- The specified derived action counit: comparison epsilon, then localized multiplication.
Source: Stacks, definition-pullback (blueprint: def-sfb-sheaf-dg-module-localization). -/
def derivedActionCounit {A B : Algebra S} {φ : A ⟶ B} (L : DerivedExtension φ)
    (N : LeftModule B) :
    L.functor.obj ((moduleQ A).obj ((restrictScalars φ).obj N)) ⟶ (moduleQ B).obj N :=
  L.comparison.app ((q A).obj ((restrictScalars φ).obj N)) ≫
    (moduleQ B).map (actionCounit φ N)

/-- Evaluate a pure tensor using the canonical sheafification unit.
Source: Stacks, 03EK and definition-dga
(blueprint: def-sfb-sheaf-dg-module-localization). -/
def tensorSection (P N : ringedSiteModules.{w} (rings S)) (U : Cᵒᵖ)
    (x : P.val.obj U) (y : N.val.obj U) : (P ⊗ N).val.obj U :=
  (SheafOfModules.tensorObjIsoSheafification P N).inv.val.app U
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (rings S).obj)).unit.app
      (P.val ⊗ N.val)).app U (TensorProduct.tmul (S.obj.obj U) x y))

/-- Evaluate the homogeneous left action on sections.
Source: Stacks, 0FRI (blueprint: def-sfb-sheaf-dg-module-localization). -/
def actionSection (A : Algebra S) (M : LeftModule A) (p q : ℤ) (U : Cᵒᵖ)
    (a : (A.X.X p).val.obj U) (m : (M.X.X q).val.obj U) :
    (M.X.X (p + q)).val.obj U :=
  (action A M p q).val.app U (tensorSection (A.X.X p) (M.X.X q) U a m)

/-- An essentially small site has essentially small slice sites in the same bound.
Source: the size convention and Stacks, restriction to a slice site
(blueprint: def-sfb-sheaf-dg-module-localization).
Proof: replace C by its small skeleton in universe w. Each slice is equivalent
to the corresponding slice of that skeleton; its objects and arrows are w-small.
Transport essential smallness back through this equivalence. -/
@[instance] theorem sliceEssentiallySmall (U : C) : EssentiallySmall.{w} (Over U) := by
  sorry

/-- Restriction of the underlying complex to the slice site C/U.
For the site of opens this is the ordinary restriction to the open subspace.
Source: Stacks, sdga.tex, restriction conventions
(blueprint: def-sfb-sheaf-dg-module-localization). -/
def restrictionComplex (S : Sheaf J CommRingCat.{w}) (U : C) :
    Complex S ⥤ Complex (S.over U) := by
  letI := module_overFunctor_preservesZero.{u, v, w, w} (rings S) U
  exact (SheafOfModules.overFunctor.{w} (rings S) U).mapHomologicalComplex (.up ℤ)


/-- Algebra data on a fixed complex.
Source: Stacks, 0FRF (blueprint: def-sfb-sheaf-dg-module-localization). -/
def algebraOn (K : Complex S) (a : MonObj K) : Algebra S := @Mon.mk _ _ _ K a

/-- Restriction of multiplication is exactly restriction of its values on sections.
The unit is forced by multiplication and the monoid unit axioms.
Source: Stacks, sdga.tex, restriction conventions
(blueprint: def-sfb-sheaf-dg-module-localization). -/
def IsRestrictedAlgebra (A : Algebra S) (U : C)
    (a : MonObj ((restrictionComplex S U).obj A.X)) : Prop :=
  ∀ (p q : ℤ) (V : (Over U)ᵒᵖ) (x : (A.X.X p).val.obj (Opposite.op V.unop.left))
      (y : (A.X.X q).val.obj (Opposite.op V.unop.left)),
    actionSection (algebraOn _ a) (regular (algebraOn _ a)) p q V x y =
      actionSection A (regular A) p q (Opposite.op V.unop.left) x y

/-- The restricted algebra has the unique multiplication prescribed on sections.
Source: Stacks, sdga.tex, restriction conventions
(blueprint: def-sfb-sheaf-dg-module-localization).
Proof: restrict the coefficient-linear multiplication maps and the unit section
at each object V of C/U. Tensor sheafification gives the action on the restricted
total tensor, since restriction commutes with its sums and tensor. All axioms
are checked on sections. Tensor generators determine multiplication, and an
associative multiplication has at most one two-sided unit. -/
theorem existsUnique_restrictedAlgebra (A : Algebra S) (U : C) :
    ∃! a : MonObj ((restrictionComplex S U).obj A.X), IsRestrictedAlgebra A U a := by
  sorry

/-- The algebra restricted to an open (or, more generally, an object of the site).
Source: Stacks, sdga.tex, restriction conventions
(blueprint: def-sfb-sheaf-dg-module-localization). -/
def restrictAlgebra (A : Algebra S) (U : C) : Algebra (S.over U) :=
  algebraOn _ (existsUnique_restrictedAlgebra A U).choose

/-- The module action after restriction agrees with the original on all sections.
Source: Stacks, sdga.tex, restriction conventions
(blueprint: def-sfb-sheaf-dg-module-localization). -/
def IsRestrictedAction (A : Algebra S) (U : C) (M : LeftModule A)
    (a : ModObj (restrictAlgebra A U).X ((restrictionComplex S U).obj M.X)) : Prop :=
  ∀ (p q : ℤ) (V : (Over U)ᵒᵖ) (x : (A.X.X p).val.obj (Opposite.op V.unop.left))
      (m : (M.X.X q).val.obj (Opposite.op V.unop.left)),
    actionSection (restrictAlgebra A U) (moduleOn _ _ a) p q V x m =
      actionSection A M p q (Opposite.op V.unop.left) x m

/-- There is a unique action given by restriction of the original structure maps.
Source: Stacks, sdga.tex, restriction conventions
(blueprint: def-sfb-sheaf-dg-module-localization).
Proof: restrict each bilinear action and its differential, unit and associativity
identities. The sheaf tensor universal property assembles the action, and its
generators prove uniqueness. -/
theorem existsUnique_restrictedAction (A : Algebra S) (U : C) (M : LeftModule A) :
    ∃! a : ModObj (restrictAlgebra A U).X ((restrictionComplex S U).obj M.X),
      IsRestrictedAction A U M a := by
  sorry

/-- The restricted module on the actual restricted complex.
Source: Stacks, sdga.tex, restriction conventions
(blueprint: def-sfb-sheaf-dg-module-localization). -/
def restrictModule (A : Algebra S) (U : C) (M : LeftModule A) :
    LeftModule (restrictAlgebra A U) :=
  moduleOn _ _ (existsUnique_restrictedAction A U M).choose

/-- Restriction of a module chain map preserves the restricted actions.
Source: Stacks, sdga.tex, restriction conventions
(blueprint: def-sfb-sheaf-dg-module-localization).
Proof: evaluate at every slice object; the required identity is the original
module-map identity there. -/
theorem restrictMap_linear (A : Algebra S) (U : C) {M N : LeftModule A} (f : M ⟶ N) :
    IsModHom (restrictAlgebra A U).X
      (@id ((restrictModule A U M).X ⟶ (restrictModule A U N).X)
        ((restrictionComplex S U).map f.hom)) := by
  sorry

/-- Restriction of modules and their structure maps to the slice site.
Source: Stacks, sdga.tex, restriction conventions
(blueprint: def-sfb-sheaf-dg-module-localization). -/
def restriction (A : Algebra S) (U : C) : LeftModule A ⥤ LeftModule (restrictAlgebra A U) where
  obj := restrictModule A U
  map f :=
    { hom := (restrictionComplex S U).map f.hom
      isModHom := restrictMap_linear A U f }
  map_id M := Mod.hom_ext _ _ ((restrictionComplex S U).map_id M.X)
  map_comp f g := Mod.hom_ext _ _ ((restrictionComplex S U).map_comp f.hom g.hom)

/-- Restriction descends uniquely to the derived word localizations.
Source: Stacks, 0FT5 and restriction conventions
(blueprint: def-sfb-sheaf-dg-module-localization).
Proof: restriction takes signed homotopies to signed homotopies and is exact on
sheaves on an open or slice site. It therefore preserves cohomology isomorphisms.
Descend successively through the homotopy and word quotients. Their universal
properties give the exact factorization and uniqueness. -/
theorem existsUnique_derivedRestriction (A : Algebra S) (U : C) :
    ∃! F : Derived A ⥤ Derived (restrictAlgebra A U),
      moduleQ A ⋙ F = restriction A U ⋙ moduleQ (restrictAlgebra A U) := by
  sorry

/-- Derived restriction, fixed by restriction of every sheaf structure map.
Source: Stacks, 0FT5 (blueprint: def-sfb-sheaf-dg-module-localization). -/
def derivedRestriction (A : Algebra S) (U : C) : Derived A ⥤ Derived (restrictAlgebra A U) :=
  (existsUnique_derivedRestriction A U).choose

/-- Closure under exactly the five operations in the local perfectness definition.
Finite sums are finite coproducts; in the additive derived category these are the
finite direct sums. A retract is explicitly i followed by r equal to the identity.
Source: the finite-operations convention of the node and Stacks, section-perfect
(blueprint: def-sfb-sheaf-dg-module-localization). -/
def IsPerfectClosure (A : Algebra S) (P : ObjectProperty (Derived A)) : Prop :=
  P ((moduleQ A).obj (regular A)) ∧
  (∀ (M N : Derived A), P M → Nonempty (M ≅ N) → P N) ∧
  (∀ (n : ℕ) (F : Fin n → Derived A) (c : Cofan F), IsColimit c →
    (∀ i : Fin n, P (F i)) → P c.pt) ∧
  (∀ (M : Derived A) (k : ℤ), P M → P ((derivedShift A k).obj M)) ∧
  (∀ t : Triangle (Derived A), IsConeTriangle A t → P t.obj₁ → P t.obj₂ → P t.obj₃) ∧
  (∀ (L M : Derived A) (i : L ⟶ M) (r : M ⟶ L), i ≫ r = 𝟙 L → P M → P L)

/-- Intersection of all full subcategories containing the regular module and closed
under isomorphisms, finite sums, integer shifts, cones and retracts.
Source: the local perfectness convention in the node
(blueprint: def-sfb-sheaf-dg-module-localization). -/
def IsPerfect (A : Algebra S) (M : Derived A) : Prop :=
  ∀ P : ObjectProperty (Derived A), IsPerfectClosure A P → P M

/-- Local perfectness on a topological space, with an arbitrary open cover. Slice
restriction over U is identified with ordinary restriction to the subspace U.
Source: the local perfectness convention in the node
(blueprint: def-sfb-sheaf-dg-module-localization). -/
def IsLocallyPerfect {X : TopCat.{u}}
    (S : TopCat.Sheaf CommRingCat.{w} X)
    [EssentiallySmall.{w} (TopologicalSpace.Opens X)] (A : Algebra S) (M : Derived A) : Prop :=
  ∃ cover : Set (TopologicalSpace.Opens X),
    (∀ x : X, ∃ U ∈ cover, x ∈ U) ∧
    ∀ U ∈ cover, IsPerfect (restrictAlgebra A U) ((derivedRestriction A U).obj M)

end CategoryTheory.SheafDg
