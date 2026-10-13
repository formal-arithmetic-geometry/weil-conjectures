/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.Picard.TwistedDescent
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.PerfectDescendMorphisms
import Sheaf.AlgebraicGeometry.DerivedPullbackPerfect
import Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses

public import Sheaf.AlgebraicGeometry.TwoOpenComparisonDiagram

/-! # Finite-stage descent of a prescribed overlap transition

Source: Stacks Project, Tags 09RE and 09RF.
(blueprint: lem-pc-perfect-overlap-transition-comparison-diagram).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
  schemeOpenRestriction_additive schemeOpenRestriction_preservesFiniteLimits
  schemeOpenRestriction_preservesFiniteColimits schemeOpenOverlapRestriction_additive
  schemeOpenOverlapRestriction_preservesFiniteLimits
  schemeOpenOverlapRestriction_preservesFiniteColimits

set_option synthInstance.maxHeartbeats 400000 in
-- Elaborating simultaneous exact restriction comparisons needs this instance budget.
set_option maxHeartbeats 1600000 in
-- The dependent comparison diagram requires this elaboration budget.
/-- Descend the prescribed overlap transition with coherent comparison data.
This only concerns the two local objects and one overlap equation: it has no
quantification over a global stage object or its realizations.
Source: Stacks Project, Tags 09RE, 09RF, 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-transition-comparison-diagram).

Proof: Work on the directed tail above j. The quasi-separated finitely presented
stage Yj has compact intersection W of its compact opens. The open immersion
W into Yj is quasi-compact, hence W is finitely presented over Spec Rj.
Restrict A and B to W; they remain perfect. Compose the restrictions of φU
and φV inverse to obtain the prescribed isomorphism between their limit
pullbacks. Use the canonical derived composition and open-restriction
comparisons to identify the cartesian base changes of W with the inverse-image
intersections. Apply perfect_descend_morphisms, including its invertibility
clause, to descend that isomorphism to a stage k on the tail. Transport it to
the exact overlap restrictions of A' and B' to obtain e.
Construct HU,HV,HW as derived pullback on the three open subschemes followed
by the derived inverse open equivalences. The canonical restriction/pullback
comparisons give βU,βV,βW and γU,γV. On K-flat representatives their coherence
is tensor associativity and the unit/counit identities for open equivalences;
the derived universal property preserves these identities. These actual
functors and canonical comparisons supply d, rather than an arbitrary diagram.
Composition comparisons identify HU A' and HV B' with the original limit
pullbacks on localized sites; compose with φU,φV to get θU,θV. The descended
pullback equation for e is exactly the displayed equation after these
canonical identifications. This argument constructs no global stage object F.
Empty or coincident opens use the same comparisons and inverse equations. -/
theorem perfect_overlap_transition_comparison
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    :
    let Yj := pullback t (Spec.map (R.map (homOfLE hij)))
    let X := pullback t (Spec.map (c.ι.app i))
    let gj := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
    ∀ (U V : Yj.Opens) (hcover : U ⊔ V = ⊤)
      (hU : IsCompact (U : Set Yj)) (hV : IsCompact (V : Set Yj))
      (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
      (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
      (E : schemeDerivedCategory X),
    let instP : Category (schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme) := inferInstance
    let instQ : Category (schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme) := inferInstance
    let instX : Category (schemeDerivedCategory X) := inferInstance
    let PU : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ U)).mapDerivedCategory
    let PV : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ V)).mapDerivedCategory
    ∀ (φU : (derivedPullback (gj ∣_ U)).obj A ≅
        PU.obj E)
      (φV : (derivedPullback (gj ∣_ V)).obj B ≅
        PV.obj E),
    ∃ (k : I) (hjk : j ≤ k),
      let g := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app k))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE (hij.trans hjk))]))
      let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans hjk))))
      let f := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (Over.homMk (Spec.map (R.map (homOfLE hjk)))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      let U' := f ⁻¹ᵁ U
      let V' := f ⁻¹ᵁ V
      let instY : Category (schemeDerivedCategory Yk) := inferInstance
      let instU : Category (schemeDerivedCategory U'.toScheme) := inferInstance
      let instV : Category (schemeDerivedCategory V'.toScheme) := inferInstance
      let instW : Category (schemeDerivedCategory (U' ⊓ V').toScheme) := inferInstance
      let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
      let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
      let SU : schemeDerivedCategory U'.toScheme ⥤
          schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
        (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))).mapDerivedCategory
      let SV : schemeDerivedCategory V'.toScheme ⥤
          schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
        (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))).mapDerivedCategory
      let TU : schemeDerivedCategory Yk ⥤ schemeDerivedCategory U'.toScheme :=
        (schemeOpenRestriction Yk U').mapDerivedCategory
      let TV : schemeDerivedCategory Yk ⥤ schemeDerivedCategory V'.toScheme :=
        (schemeOpenRestriction Yk V').mapDerivedCategory
      let TW : schemeDerivedCategory Yk ⥤ schemeDerivedCategory (U' ⊓ V').toScheme :=
        (schemeOpenRestriction Yk (U' ⊓ V')).mapDerivedCategory
      let αU : TU ⋙ SU ≅ TW := schemeDerivedOpenRestrictionCompIso Yk
        (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))
      let αV : TV ⋙ SV ≅ TW := schemeDerivedOpenRestrictionCompIso Yk
        (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))
      let P := gj ⁻¹ᵁ U
      let Q := gj ⁻¹ᵁ V
      let RU := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) P).mapDerivedCategory
      let RV := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) Q).mapDerivedCategory
      let RW := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) (P ⊓ Q)).mapDerivedCategory
      let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ P from inf_le_left))).mapDerivedCategory
      let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ Q from inf_le_right))).mapDerivedCategory
      let τU : RU ⋙ SP ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ P from inf_le_left)))
      let τV : RV ⋙ SQ ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ Q from inf_le_right)))
      ∃ (d : SchemeTwoOpenComparisonDiagram X Yk g U' V' P Q)
        (e : SU.obj A' ≅ SV.obj B')
        (θU : d.toDiagram.HU.obj A' ≅ RU.obj E)
        (θV : d.toDiagram.HV.obj B' ≅ RV.obj E),
        d.toDiagram.γU.inv.app A' ≫ SP.map θU.hom ≫ τU.hom.app E =
          d.toDiagram.HW.map e.hom ≫ d.toDiagram.γV.inv.app B' ≫
            SQ.map θV.hom ≫ τV.hom.app E := by sorry

end AlgebraicGeometry
