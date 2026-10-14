/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import Sheaf.Algebra.Homology.HomologyEvaluationDefinitions

/-! # Internal Hom transport squares for cycles and homology

Source: Stacks Project, Tags 0A8X and 08DL.
(blueprint: new-t4-open-over-internal-hom-cycle-homology-squares). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

local instance (priority := 2000) openOverInternalHomCycleHomologySquaresCategory
    (X : Scheme.{u}) : Category X.Modules :=
  SheafOfModules.instCategory (R := X.ringCatSheaf)
local instance (priority := 2000) openOverInternalHomCycleHomologySquaresPreadditive
    (X : Scheme.{u}) : Preadditive X.Modules :=
  SheafOfModules.instPreadditive X.ringCatSheaf
noncomputable local instance (priority := 2000) openOverInternalHomCycleHomologySquaresAbelian
    (X : Scheme.{u}) : Abelian X.Modules :=
  SheafOfModules.instAbelian X.ringCatSheaf

attribute [local irreducible] Scheme.Modules.restrictFunctor SheafOfModules.overFunctor
attribute [local irreducible] homComplexFunctor

/-- Transport of source and target cycles and homology through internal Hom.
Source: Stacks Project, Tag 08DL; step 2 of the parent restriction-diagram plan.
(blueprint: new-t4-open-over-internal-hom-cycle-homology-squares).

Proof: Restriction is exact by the localization finite-limit and finite-colimit
 comparisons, the open-site equivalence and overFunctorEquiv. For L=T,J, take
 z_L:F(Z(L)) ≅ Z(F(L)) and d_L:F(H(L)) ≅ H(F(L)), the inverses of the
 ShortComplex mapCyclesIso and mapHomologyIso comparisons. They commute with cycle
 inclusions and homology quotients by their kernel and cokernel universal properties.
 Compose e with Hom(z_T inverse,z_J) to define s, with Hom(z_T inverse,identity)
 to define t, with Hom(z_T inverse,d_J) to define v, and with Hom(d_T inverse,d_J)
 to define b. Apply the naturality equation he to (T.iCycles,identity),
 (identity,J.iCycles), (identity,J.homologyπ), and (T.homologyπ,identity).
 Cancel the cycle and homology isomorphisms using their inclusion and quotient
 squares to obtain the four equations. This uses neither the Hom complex nor its
 products or differential. No finiteness or nonempty-open assumption is needed;
 zero and identity maps satisfy the same naturality equations. -/
theorem openOver_internalHom_cycle_homology_squares (X : Scheme.{u})
    (V : X.Opens) (W : V.toScheme.Opens)
    (e : ∀ M N : X.Modules,
      (Scheme.Modules.restrictFunctor V.ι ⋙
        SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).obj
          (SheafOfModules.homObj (R := X.sheaf) M N) ≅
      SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
        ((Scheme.Modules.restrictFunctor V.ι ⋙
          SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).obj M)
        ((Scheme.Modules.restrictFunctor V.ι ⋙
          SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).obj N))
    (he : ∀ (M M' N N' : X.Modules) (f : M' ⟶ M) (g : N ⟶ N'),
      (Scheme.Modules.restrictFunctor V.ι ⋙
        SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).map
          (SheafOfModules.homObjMap (R := X.sheaf) f g) ≫ (e M' N').hom =
        (e M N).hom ≫ SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W)
          ((Scheme.Modules.restrictFunctor V.ι ⋙
            SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).map f)
          ((Scheme.Modules.restrictFunctor V.ι ⋙
            SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).map g))
    (T J : CochainComplex X.Modules ℤ) (n : ℤ) :
    let F := Scheme.Modules.restrictFunctor V.ι ⋙
      SheafOfModules.overFunctor V.toScheme.ringCatSheaf W
    let A := (moduleOpenOverComplexFunctor X V W).obj T
    let K := (moduleOpenOverComplexFunctor X V W).obj J
    ∃ b : F.obj (SheafOfModules.homObj (R := X.sheaf)
          (T.homology (-n)) (J.homology 0)) ≅
          SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
            (A.homology (-n)) (K.homology 0),
      ∃ s : F.obj (SheafOfModules.homObj (R := X.sheaf)
          (T.cycles (-n)) (J.cycles 0)) ≅
          SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
            (A.cycles (-n)) (K.cycles 0),
      ∃ t : F.obj (SheafOfModules.homObj (R := X.sheaf)
          (T.cycles (-n)) (J.X 0)) ≅
          SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
            (A.cycles (-n)) (K.X 0),
      ∃ v : F.obj (SheafOfModules.homObj (R := X.sheaf)
          (T.cycles (-n)) (J.homology 0)) ≅
          SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
            (A.cycles (-n)) (K.homology 0),
        F.map (SheafOfModules.homObjMap (R := X.sheaf) (T.iCycles (-n)) (𝟙 _)) ≫
            t.hom = (e (T.X (-n)) (J.X 0)).hom ≫
          SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W)
            (A.iCycles (-n)) (𝟙 _) ∧
        F.map (SheafOfModules.homObjMap (R := X.sheaf) (𝟙 _) (J.iCycles 0)) ≫ t.hom =
          s.hom ≫ SheafOfModules.homObjMap
            (R := V.toScheme.sheaf.over W) (𝟙 _) (K.iCycles 0) ∧
        F.map (SheafOfModules.homObjMap (R := X.sheaf) (𝟙 _) (J.homologyπ 0)) ≫ v.hom =
          s.hom ≫ SheafOfModules.homObjMap
            (R := V.toScheme.sheaf.over W) (𝟙 _) (K.homologyπ 0) ∧
        F.map (SheafOfModules.homObjMap (R := X.sheaf) (T.homologyπ (-n)) (𝟙 _)) ≫
            v.hom = b.hom ≫ SheafOfModules.homObjMap
              (R := V.toScheme.sheaf.over W) (A.homologyπ (-n)) (𝟙 _) := by sorry

end CategoryTheory
