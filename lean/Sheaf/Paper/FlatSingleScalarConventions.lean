/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedTotalTensor
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Flat degree-zero scalar extension in two conventions

Source: Stacks Project, Modules on Sites, Tags 03EK and 03ER(3), Cohomology on
Sites, Tags 06YQ and 06YY, and blueprint `sk-def-sfb-change-of-scalars`(2)
and `sk-def-sfb-derived-categories` (blueprint: lem-sfb-flat-single-scalar-conventions).

The identifications below retain the given underlying module actions. The monoid-side
extension is the recorded `Mod.extendScalars`, including its coequalizer projection.
The section-side extension is the prescribed sheafified `changeOfRings`, as recorded
by `DerivedChangeOfRingsCochainModel`. No flatness of the target ring is required.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v r wR wB

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped ChangeOfRings

namespace SheafOfModules.FlatSingleScalar

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]

/-- The existing module-sheaf category, without a change in coefficient universe.
Source: Stacks 03EK (blueprint: lem-sfb-flat-single-scalar-conventions). -/
abbrev Modules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

variable {R B : Sheaf J CommRingCat.{r}} (φ : R ⟶ B)

/-- The target ring as an R-module, with its given scalar action through φ.
Source: Stacks 03EK (blueprint: lem-sfb-flat-single-scalar-conventions). -/
abbrev scalarAlgebra : Modules R :=
  (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
    (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))

/-- A local pure tensor in the existing localization tensor, via sheafification.
Source: Stacks 03EK (blueprint: lem-sfb-flat-single-scalar-conventions). -/
def tensorSection (M N : Modules R) (U : Cᵒᵖ) (m : M.val.obj U) (n : N.val.obj U) :
    (M ⊗ N).val.obj U :=
  (tensorObjIsoSheafification M N).inv.val.app U
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
        (M.val ⊗ N.val)).app U (m ⊗ₜ[R.obj.obj U] n))

/-- Presentations of precisely the two action-preserving identifications in the node.
The monoid unit is φ, its multiplication is that of B, and the module equivalence
intertwines the given B-actions on all local pure tensors. The unit-module equivalence
is identified with the identity on underlying R-modules; unitality forces its action.
These are presentations of the prescribed notions, not additional assumptions.
Source: Stacks 03EK and blueprint change of scalars (2)
(blueprint: lem-sfb-flat-single-scalar-conventions). -/
structure Identifications where
  /-- B with its actual multiplication as an R-algebra object. -/
  [monoid : MonObj (scalarAlgebra φ)]
  /-- Commutativity of the given ring multiplication. -/
  [commutative : IsCommMonObj (scalarAlgebra φ)]
  /-- Its unit is a monoid homomorphism from the tensor unit. -/
  [unitHom : IsMonHom (η[scalarAlgebra φ])]
  /-- The monoid unit is exactly the given ring morphism. -/
  one_sections : ∀ (U : Cᵒᵖ) (a : R.obj.obj U),
    (η[scalarAlgebra φ]).val.app U a = (φ.hom.app U) a
  /-- The monoid multiplication is the local ring multiplication. -/
  mul_sections : ∀ (U : Cᵒᵖ) (b b' : B.obj.obj U),
    (μ[scalarAlgebra φ]).val.app U
      (tensorSection (scalarAlgebra φ) (scalarAlgebra φ) U b b') = b * b'
  /-- Modules over the unit monoid are R-module sheaves. -/
  unitModules : Modules R ≌ Mod (Modules R) (𝟙_ (Modules R))
  /-- This identification retains the underlying module. -/
  unitUnderlying : unitModules.functor ⋙ Mod.forget (𝟙_ (Modules R)) ≅ 𝟭 (Modules R)
  /-- Modules over B internally are sheaves of B-modules. -/
  modules : Modules B ≌ Mod (Modules R) (scalarAlgebra φ)
  /-- This identification retains the underlying R-module. -/
  underlying : modules.functor ⋙ Mod.forget (scalarAlgebra φ) ≅
    restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  /-- The internal module action is exactly its given sectionwise B-action. -/
  action_sections : ∀ (N : Modules B) (U : Cᵒᵖ) (b : B.obj.obj U)
      (n : (modules.functor.obj N).X.val.obj U),
    (underlying.hom.app N).val.app U
      ((ModObj.smul (M := scalarAlgebra φ) (X := (modules.functor.obj N).X)).val.app U
        (tensorSection (scalarAlgebra φ) (modules.functor.obj N).X U b n)) =
      b • (@id (N.val.obj U) ((underlying.hom.app N).val.app U n))
  /-- The transported ordinary extension is additive. -/
  [additive : (unitModules.functor ⋙ Mod.extendScalars (η[scalarAlgebra φ]) ⋙
    modules.inverse).Additive]

/-- The actual coequalizer extension, transported along the action identifications.
Source: blueprint change of scalars (2)
(blueprint: lem-sfb-flat-single-scalar-conventions). -/
abbrev monExtension (d : Identifications φ) : Modules R ⥤ Modules B :=
  letI := d.monoid
  letI := d.unitHom
  d.unitModules.functor ⋙ Mod.extendScalars (η[scalarAlgebra φ]) ⋙ d.modules.inverse

/-- Additivity retained from the ordinary action identification.
Source: Stacks 03EK (blueprint: lem-sfb-flat-single-scalar-conventions). -/
instance monExtension_additive (d : Identifications φ) : (monExtension φ d).Additive :=
  d.additive

/-- The balancing-coequalizer projection on underlying R-modules. The factors are
only the specified underlying identifications and the actual `Mod.extendπ`.
Source: blueprint change of scalars (2)
(blueprint: lem-sfb-flat-single-scalar-conventions). -/
def projection (d : Identifications φ) (M : Modules R) :
    scalarAlgebra φ ⊗ M ⟶
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        ((monExtension φ d).obj M) :=
  letI := d.monoid
  letI := d.unitHom
  scalarAlgebra φ ◁ (d.unitUnderlying.app M).inv ≫
    Mod.extendπ (η[scalarAlgebra φ]) (d.unitModules.functor.obj M) ≫
    (d.modules.counitIso.app
      ((Mod.extendScalars (η[scalarAlgebra φ])).obj (d.unitModules.functor.obj M))).inv.hom ≫
    (d.underlying.app ((monExtension φ d).obj M)).hom

variable [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wB} (Modules B)]

/-- The canonical degree-zero counit, including the termwise-single-complex comparison.
It is a natural transformation on all modules, hence also on the full subcategory of
flat modules. Source: Stacks 06YY and Derived Categories 06XN
(blueprint: lem-sfb-flat-single-scalar-conventions). -/
def degreeZeroCounit (F : Modules R ⥤ Modules B) [F.Additive]
    (L : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules B))
    (ε : DerivedCategory.Q ⋙ L ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :
    HomologicalComplex.single (Modules R) (.up ℤ) 0 ⋙ DerivedCategory.Q ⋙ L ⟶
      F ⋙ HomologicalComplex.single (Modules B) (.up ℤ) 0 ⋙ DerivedCategory.Q :=
  Functor.whiskerLeft (HomologicalComplex.single (Modules R) (.up ℤ) 0) ε ≫
    Functor.whiskerRight (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom
      DerivedCategory.Q

/-- The ordinary comparison preserves balancing projections on every local pure tensor.
Source: Stacks 03EK and blueprint change of scalars (2)
(blueprint: lem-sfb-flat-single-scalar-conventions). -/
def Normalized (d : Identifications φ) (s : DerivedChangeOfRingsCochainModel φ)
    (e : monExtension φ d ≅ s.E) : Prop :=
  ∀ (M : Modules R) (U : Cᵒᵖ) (b : B.obj.obj U) (m : M.val.obj U),
    ((eqToHom (s.obj_eq M)).val.app U)
      ((e.hom.app M).val.app U
        ((projection φ d M).val.app U (tensorSection (scalarAlgebra φ) M U b m))) =
      (toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
        (b ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)

/-- Counit-preserving derived comparison, invertible flat degree-zero comparisons,
and their natural compatibility square. Naturality is built into the three natural
transformations, so the square restricts naturally to all maps between flat modules.
Source: Stacks 06YY, 06XN and blueprint total left derived functors
(blueprint: lem-sfb-flat-single-scalar-conventions). -/
def DerivedCompatible (d : Identifications φ) (s : DerivedChangeOfRingsCochainModel φ)
    (e : monExtension φ d ≅ s.E) : Prop :=
  ∀ (L : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules B))
    (ε : DerivedCategory.Q ⋙ L ⟶
      (monExtension φ d).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
    L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso (Modules R) (.up ℤ)) →
    ∃ eL : L ≅ s.T,
      (Functor.whiskerLeft DerivedCategory.Q eL.hom ≫ s.ε =
        ε ≫ Functor.whiskerRight (NatIso.mapHomologicalComplex e (.up ℤ)).hom
          DerivedCategory.Q) ∧
      ∀ (M : Modules R), IsFlatOnSite M →
        IsIso ((degreeZeroCounit (monExtension φ d) L ε).app M) ∧
        IsIso ((degreeZeroCounit s.E s.T s.ε).app M) ∧
        eL.hom.app (DerivedCategory.Q.obj
            ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj M)) ≫
          (degreeZeroCounit s.E s.T s.ε).app M =
        (degreeZeroCounit (monExtension φ d) L ε).app M ≫
          DerivedCategory.Q.map
            ((HomologicalComplex.single (Modules B) (.up ℤ) 0).map (e.hom.app M))

/-- Flat degree-zero scalar comparisons agree in the two conventions, without local
freeness or flatness of B. Source: Stacks 03EK, 03ER(3), 06YQ, 06YY, 06XN and blueprint
change of scalars (2) (blueprint: lem-sfb-flat-single-scalar-conventions).

Proof, following all six steps of the DAG:
1. In Mod(R) the middle monoid in Mod.extendScalars is the tensor unit R. The two
   arrows send b tensor r tensor m to b φ(r) tensor m and b tensor rm. They agree
   by sectionwise balancing and sheafification (def-pur-sheaf-tensor-product,
   def-weil-pbc-sheafification). The identity of B tensor_R M descends through the
   coequalizer, and coequalizer uniqueness proves both inverse identities.
2. The first-factor action makes this inverse B-linear: after B tensor q both
   action formulas are multiplication b'b tensor m. For f:M to N, both composites
   after q send b tensor m to b tensor f(m). Coequalizer uniqueness gives naturality.
   These computations take place before sheafification, not on arbitrary global
   tensor sections (sk-def-sfb-change-of-scalars).
3. Flatness says that - tensor_R M is exact. Exact-functor homology comparison
   (lem-weil-pbc-exact-functor-complex-cohomology) proves preservation of acyclicity
   and quasi-isomorphisms. The sum-total tensor with M[0] has only one summand in
   each degree; the reverse order agrees by symmetry with sign (-1)^0 = 1.
   Thus both recorded K-flat predicates hold (def-sfb-preserves-kflat-quasi-iso,
   def-pc-kflat-complex).
4. The identity K-flat resolution computes the ringed-site derived counit
   (lem-pur-derived-change-of-rings). Its degree-zero component is invertible.
   The sectionwise tensor flip agrees with the chosen first-factor convention.
5. The universal property of the total left derived counits
   (def-sfb-left-derived-functor) lifts the ordinary natural isomorphism to eL.
   Lift its inverse as well. Counit uniqueness gives the two inverse identities
   and the displayed counit equation; no exactness of scalar extension is used.
6. Evaluate that equation on M[0] and use the natural single-complex comparison.
   This is the stated square. Its other three arrows are isomorphisms, hence so
   is the monoid-side degree-zero counit. All comparisons are natural
   transformations, so the square is natural on maps between flat sheaves.
   Flatness is used only for M[0], never for B over R. -/
theorem flat_single_scalar_conventions :
    (∀ (M : Modules R), IsFlatOnSite M →
      CochainComplex.IsKFlatForTotalTensor
        ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj M) ∧
      CochainComplex.IsKFlatIndependentCoefficients
        ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj M)) ∧
    ∃ d : Identifications φ, ∀ s : DerivedChangeOfRingsCochainModel φ,
      ∃ e : monExtension φ d ≅ s.E, Normalized φ d s e ∧ DerivedCompatible φ d s e := by
  sorry

end SheafOfModules.FlatSingleScalar
