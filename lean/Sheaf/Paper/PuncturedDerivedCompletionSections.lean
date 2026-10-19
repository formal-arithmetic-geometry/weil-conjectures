/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Sheaf.Topology.OpenModuleDerivedSections
public import WeilConjectures.Algebra.Homology.IdealPowerTorsionFunctor
public import Sheaf.Paper.CoefTowerCoaugmentation
import Sheaf.Topology.RingedSpaceRGammaDerivedLimit
import Sheaf.Paper.RingedPushforwardCompletion
import Sheaf.Paper.ConstantCompletionEquivalence
import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-!
# Derived completion of sections on a punctured spectrum

Source: Stacks Project, algebraization.tex, Tag 0DXI, with its degree-zero version
on an arbitrary open, using Tags 0BLX and 0D60.
(blueprint: lem-per-punctured-derived-completion-sections).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u wA wT wX

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.PuncturedCompletion

variable (A : Type u) [CommRing A]

/-- The ordinary quotient tower, with index `n` denoting the positive power `n+1`.
Source: Stacks Tag 0DXI (blueprint: lem-per-punctured-derived-completion-sections). -/
def reductions (I : Ideal A) : ModuleCat.{u} A ⥤ (ℕᵒᵖ ⥤ ModuleCat.{u} A) where
  obj M :=
    { obj n := ModuleCat.of A (M ⧸ (I ^ (n.unop + 1) • ⊤ : Submodule A M))
      map f := ModuleCat.ofHom (Submodule.factorPow I M (Nat.add_le_add_right
        (leOfHom f.unop) 1))
      map_id _ := by
        apply ModuleCat.hom_ext
        exact Submodule.mapQ_id _
      map_comp f g := by
        apply ModuleCat.hom_ext
        exact (Submodule.factor_comp
          (Submodule.pow_smul_top_le I M (Nat.add_le_add_right (leOfHom f.unop) 1))
          (Submodule.pow_smul_top_le I M (Nat.add_le_add_right (leOfHom g.unop) 1))).symm }
  map f :=
    { app n := ModuleCat.ofHom
        (Submodule.mapQ _ _ f.hom (by
          intro x hx
          refine Submodule.smul_induction_on hx (fun a ha x _ ↦ ?_)
            (fun x y hx hy ↦ ?_)
          · simpa using Submodule.smul_mem_smul ha (Submodule.mem_top : f.hom x ∈ ⊤)
          · exact Submodule.add_mem _ hx hy))
      naturality _ _ _ := by ext x; rfl }
  map_id _ := by ext n x; rfl
  map_comp _ _ := by ext n x; rfl

/-- Additivity of the concrete quotient tower.
Source: Stacks Tag 0DXI (blueprint: lem-per-punctured-derived-completion-sections). -/
instance reductions_additive (I : Ideal A) : (reductions A I).Additive where
  map_add := by
    intro M N f g
    apply NatTrans.ext
    funext n
    apply ModuleCat.hom_ext
    apply Submodule.linearMap_qext
    ext x
    rfl

/-- The compatible quotient maps to the positive-power reductions.
Source: Stacks Tag 0DXI (blueprint: lem-per-punctured-derived-completion-sections). -/
def reductionCone (I : Ideal A) (M : ModuleCat.{u} A) : Cone ((reductions A I).obj M) where
  pt := M
  π :=
    { app n := ModuleCat.ofHom (Submodule.mkQ (I ^ (n.unop + 1) • ⊤ : Submodule A M))
      naturality _ _ _ := by ext x; rfl }

/-- The ordinary inverse-limit map of a quotient-tower complex, fixed by its projections.
Source: Stacks Tags 0DXI and 0940
(blueprint: lem-per-punctured-derived-completion-sections). -/
def ordinaryUnit (I : Ideal A) (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    P ⟶ ((lim : (ℕᵒᵖ ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        (((reductions A I).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) where
  f q := limit.lift _ (reductionCone A I (P.X q))
  comm' q r _ := by
    apply limit.hom_ext
    intro n
    simp only [Functor.mapHomologicalComplex_obj_d, Category.assoc]
    change limit.lift _ _ ≫ limMap _ ≫ limit.π ((reductions A I).obj (P.X r)) n = _
    erw [limMap_π, limit.lift_π_assoc, limit.lift_π]
    ext x
    rfl

/-- Sections on an open of Spec A with their canonical A-action, using Mathlib's
`modulesSpecToSheaf` scalar transport through the affine global-section isomorphism.
Source: Stacks Tags 01EO and 0DXI
(blueprint: lem-per-punctured-derived-completion-sections). -/
def sections (V : (Spec (.of A)).Opens) :
    SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤ ModuleCat.{u} A :=
  modulesSpecToSheaf ⋙ TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (op V)

/-- Sections restriction is the actual presheaf restriction map.
Source: Stacks Tag 01EO (blueprint: lem-per-punctured-derived-completion-sections). -/
def restriction {V W : (Spec (.of A)).Opens} (h : W ≤ V) :
    sections A V ⟶ sections A W :=
  Functor.whiskerLeft (modulesSpecToSheaf ⋙ TopCat.Sheaf.forget _ _)
    ((evaluation _ _).map (homOfLE h).op)

/-- Additivity of sections with the affine scalar action.
Source: Stacks Tag 01EO (blueprint: lem-per-punctured-derived-completion-sections). -/
instance sections_additive (V : (Spec (.of A)).Opens) : (sections A V).Additive where
  map_add := by
    intro M N f g
    ext x
    rfl

variable [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
  [HasDerivedCategory.{wT} (ℕᵒᵖ ⥤ ModuleCat.{u} A)]
  [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]

/-- Derived sections of the associated sheaf, using K-injective resolutions.
Source: Stacks Tags 01EO and 0DXI
(blueprint: lem-per-punctured-derived-completion-sections). -/
def derivedSections (V : (Spec (.of A)).Opens) :
    ModuleCat.{u} A ⥤ DerivedCategory (ModuleCat.{u} A) :=
  tilde.functor (.of A) ⋙
    DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) 0 ⋙
    (sections A V).rightDerivedFunctor

/-- Derived open restriction, obtained by deriving the actual restriction transformation.
Source: Stacks Tags 01EO and 0D60
(blueprint: lem-per-punctured-derived-completion-sections). -/
def derivedRestriction {V W : (Spec (.of A)).Opens} (h : W ≤ V) :
    derivedSections A V ⟶ derivedSections A W :=
  Functor.whiskerLeft
    (tilde.functor (.of A) ⋙ DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) 0)
    (Functor.rightDerivedFunctorNatTrans (restriction A h))

/-- The universal comparison from ordinary strict limit to total right derived limit.
In modules this is canonically the strict shifted cone of one minus shift on products;
no choice of an abstract triangulated cone is used.
Source: Stacks Tags 0940 and 08TC
(blueprint: lem-per-punctured-derived-completion-sections). -/
def limitComparison (P : CochainComplex (ℕᵒᵖ ⥤ ModuleCat.{u} A) ℤ) :
    DerivedCategory.Q.obj
      (((lim : (ℕᵒᵖ ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) ⟶
    (lim : (ℕᵒᵖ ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A).rightDerivedFunctor.obj
      (DerivedCategory.Q.obj P) :=
  (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).inv.app _ ≫
    (lim : (ℕᵒᵖ ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ≫
    (lim : (ℕᵒᵖ ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A).rightDerivedFunctor.map
      ((DerivedCategory.quotientCompQhIso (ℕᵒᵖ ⥤ ModuleCat.{u} A)).hom.app P)

/-- Integer Zariski cohomology, including its vanishing negative degrees.
Source: Stacks Tag 0DXI (blueprint: lem-per-punctured-derived-completion-sections). -/
def cohomology (V : (Spec (.of A)).Opens) (i : ℤ) : ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  derivedSections A V ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) i

/-- Derived I-adic completion in the universal strict quotient-tower model.
The tower is the total left derived functor of `reductions`; right derived inverse
limit is computed by K-injective tower resolutions, canonically compared in modules
with the mapping fibre of one minus shift on termwise products.
Source: Stacks Tags 0DXI, 0940 and 08TC
(blueprint: lem-per-punctured-derived-completion-sections). -/
def completion
    (T : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ℕᵒᵖ ⥤ ModuleCat.{u} A)) :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  T ⋙ (lim : (ℕᵒᵖ ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A).rightDerivedFunctor

/-- The completed section-cohomology functor, for the specified universal reduction model.
The second functor is total right derived inverse limit of strict module towers.
Source: Stacks Tags 0DXI, 0940 and 08TC
(blueprint: lem-per-punctured-derived-completion-sections). -/
def completedCohomology
    (T : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ℕᵒᵖ ⥤ ModuleCat.{u} A))
    (V : (Spec (.of A)).Opens) (i : ℤ) : ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  derivedSections A V ⋙ T ⋙
    (lim : (ℕᵒᵖ ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) i

/-- The infinitesimal cohomology tower, with its genuine reduction transitions.
Source: Stacks Tag 0DXI (blueprint: lem-per-punctured-derived-completion-sections). -/
def cohomologyTower (I : Ideal A) (V : (Spec (.of A)).Opens) (i : ℤ)
    (M : ModuleCat.{u} A) : ℕᵒᵖ ⥤ ModuleCat.{u} A :=
  (reductions A I).obj M ⋙ cohomology A V i

/-- Canonical reduction at a positive power, as a map of A-modules.
Source: Stacks Tag 0DXI (blueprint: lem-per-punctured-derived-completion-sections). -/
def reductionMap (I : Ideal A) (M : ModuleCat.{u} A) (n : ℕ) :
    M ⟶ ((reductions A I).obj M).obj (op n) :=
  (reductionCone A I M).π.app (op n)

/-- The actual completed restriction in degree i.
Source: Stacks Tags 0DXI and 0D60
(blueprint: lem-per-punctured-derived-completion-sections). -/
def completedRestriction
    (T : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ℕᵒᵖ ⥤ ModuleCat.{u} A))
    {V W : (Spec (.of A)).Opens} (h : W ≤ V) (i : ℤ) :
    completedCohomology A T V i ⟶ completedCohomology A T W i :=
  Functor.whiskerRight (derivedRestriction A h)
    (T ⋙ (lim : (ℕᵒᵖ ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) i)

/-- Ordinary cohomology restriction as a map of the infinitesimal towers.
Source: Stacks Tags 0DXI and 01EO
(blueprint: lem-per-punctured-derived-completion-sections). -/
def towerRestriction (I : Ideal A) {V W : (Spec (.of A)).Opens}
    (h : W ≤ V) (i : ℤ) (M : ModuleCat.{u} A) :
    cohomologyTower A I V i M ⟶ cohomologyTower A I W i M :=
  Functor.whiskerLeft ((reductions A I).obj M)
    (Functor.whiskerRight (derivedRestriction A h)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i))

/-- Derived completion computes infinitesimal cohomology on the punctured spectrum,
and degree-zero sections on every open of it. The quotient-unit normalization of the
universal derived model is imposed on every complex, so arbitrary cone maps cannot
be substituted. The arrows into each reduced section complex are uniquely determined
by their composite with the completion unit. The isomorphisms are induced by these
arrows, are natural in finite modules, and commute with degree-zero open restriction.

Source: Stacks Project, algebraization.tex, Tag 0DXI; the open degree-zero clause uses
Tags 0BLX and 0D60 (blueprint: lem-per-punctured-derived-completion-sections).

Proof:
1. The tilde sheaves of M and M/I^n M are quasi-coherent and finite type, hence coherent
   on the locally Noetherian opens by pqf-lem-coherent-ft-locnoeth. Localization commutes
   with the quotients, compatibly with reduction and further localization.
2. Apply lem-weil-pbc-constant-completion-equivalence on the one-point ringed site and
   lem-weil-pbc-ringed-pushforward-completion to the structure morphism to that site.
   Then lem-per-derived-completion-pseudocoherent identifies completed derived sections
   with derived sections of the derived limit of the coherent reductions. All units
   become quotient maps. The reduced targets are derived complete, so reflection gives
   the unique arrows displayed below.
3. Apply lem-pc-ringed-space-rgamma-derived-limit. Its Milnor sequence has right map
   induced by the reduction projections and left term R^1 lim H^(i-1).
4. For positive degrees, lem-per-punctured-cohomology-ml gives Mittag-Leffler. Negative
   degrees vanish. In degree zero use lem-per-affine-support-cech-localization to obtain
   M_n -> B_n -> C_n -> 0, with B_n = H^0(U,F_n) and C_n = H^1_m(M_n).
5. The images Q_n of M_n in B_n have surjective transitions. Consequently the image of
   B_m in B_n is the inverse image of the image of C_m in C_n. The local-cohomology
   clause of lem-per-punctured-cohomology-ml makes these images stabilize, hence B is ML.
6. Apply lem-per-mittag-leffler-derived-limit-acyclic to kill the Milnor left term.
   Functoriality gives naturality in M, and the projection equations give the reduction
   coordinates after the completion unit.
7. On any open V repeat the same comparison in degree zero. Its Milnor left term is
   R^1 lim H^(-1) = 0, without ML. Reflection uniqueness makes the comparison commute
   with restriction, since both composites with the completion unit are restriction
   followed by reduction. The Milnor maps also commute with restriction coordinatewise.
   Using one family e makes the V=U, i=0 cases literally the same isomorphism. -/
theorem punctured_derivedCompletion_sections [IsNoetherianRing A] [IsLocalRing A]
    (I : Ideal A) (U : (Spec (.of A)).Opens)
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x.asIdeal ≠ IsLocalRing.maximalIdeal A)
    (T : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ℕᵒᵖ ⥤ ModuleCat.{u} A))
    (c : DerivedCategory.Q ⋙ T ⟶
      (reductions A I).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [T.IsLeftDerivedFunctor c
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))]
    (η : 𝟭 (DerivedCategory (ModuleCat.{u} A)) ⟶ completion A T)
    (hη : ∀ P : CochainComplex (ModuleCat.{u} A) ℤ,
      η.app (DerivedCategory.Q.obj P) ≫
        (lim : (ℕᵒᵖ ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A).rightDerivedFunctor.map
          (c.app P) =
      DerivedCategory.Q.map (ordinaryUnit A I P) ≫
        limitComparison A (((reductions A I).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)) :
    ∃ e : ∀ (V : (Spec (.of A)).Opens) (_ : V ≤ U) (i : ℤ) (_ : i = 0 ∨ V = U)
      (M : ModuleCat.{u} A) [Module.Finite A M],
      (completedCohomology A T V i).obj M ≅ limit (cohomologyTower A I V i M),
      (∀ (V : (Spec (.of A)).Opens) (hV : V ≤ U) (i : ℤ) (hi : i = 0 ∨ V = U)
        (M : ModuleCat.{u} A) [Module.Finite A M] (n : ℕ),
        ∃ a : (completion A T).obj ((derivedSections A V).obj M) ⟶
            (derivedSections A V).obj (((reductions A I).obj M).obj (op n)),
          (η.app ((derivedSections A V).obj M) ≫ a =
            (derivedSections A V).map (reductionMap A I M n)) ∧
          (∀ b : (completion A T).obj ((derivedSections A V).obj M) ⟶
              (derivedSections A V).obj (((reductions A I).obj M).obj (op n)),
            η.app ((derivedSections A V).obj M) ≫ b =
              (derivedSections A V).map (reductionMap A I M n) → b = a) ∧
          ((e V hV i hi M).hom ≫ limit.π (cohomologyTower A I V i M) (op n) =
            (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map a) ∧
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
              (η.app ((derivedSections A V).obj M)) ≫
            (e V hV i hi M).hom ≫ limit.π (cohomologyTower A I V i M) (op n) =
              (cohomology A V i).map (reductionMap A I M n))) ∧
      (∀ (V : (Spec (.of A)).Opens) (hV : V ≤ U) (i : ℤ) (hi : i = 0 ∨ V = U)
        (M N : ModuleCat.{u} A) [Module.Finite A M] [Module.Finite A N] (f : M ⟶ N),
        (completedCohomology A T V i).map f ≫ (e V hV i hi N).hom =
          (e V hV i hi M).hom ≫ lim.map
            (Functor.whiskerRight ((reductions A I).map f) (cohomology A V i))) ∧
      (∀ (V W : (Spec (.of A)).Opens) (hV : V ≤ U) (hWV : W ≤ V)
        (M : ModuleCat.{u} A) [Module.Finite A M],
        (completedRestriction A T hWV 0).app M ≫
            (e W (hWV.trans hV) 0 (Or.inl rfl) M).hom =
          (e V hV 0 (Or.inl rfl) M).hom ≫ lim.map (towerRestriction A I hWV 0 M)) := by
  sorry

end AlgebraicGeometry.PuncturedCompletion
