/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses

/-!
Shared definitions for the normalized inverse-image comparison.

Source: Stacks Project, `sites-modules.tex`, Tags 03EK, 03CY and 03D2;
`proetale.tex`, Tag 09A5 (blueprint: def-pur-inverse-image-tensor-hom-sections).
These are the five original conventions of
`lem-pur-isomorphism-inverse-image-tensor-hom`, relocated without changing their bodies.
-/


@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

/-- Extension of scalars after inverse image, for the coefficient-extension clause. Source:
Stacks Tag 03EK (blueprint: lem-pur-isomorphism-inverse-image-tensor-hom). -/
noncomputable abbrev inverseImageScalarExtension
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    (O O' : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) (α : O ⟶ O')
    (F : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)) :
    SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj O')) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} (J := ProEt.topology X)
    ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map α)
    ((proEtaleModuleInverseImage g O).obj F)

/-- Positive tensor powers in the mixed-universe module category, using the sectionwise tensor
product followed by sheafification.
Source: Stacks Tag 03EK (blueprint: lem-pur-isomorphism-inverse-image-tensor-hom). -/
noncomputable def positiveTensorPowerMixed {X : AlgebraicGeometry.Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    (n : ℕ) → 0 < n → SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  | 0, h => False.elim (Nat.not_lt_zero 0 h)
  | 1, _ => M
  | n + 2, _ =>
      (show SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) from
        (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} M).obj
          (positiveTensorPowerMixed R M (n + 1) (Nat.succ_pos n)))

/-- A pure tensor followed by module sheafification. Source: Stacks Tag 03EK
(blueprint: lem-pur-isomorphism-inverse-image-tensor-hom). -/
noncomputable def purTensorSection {X : AlgebraicGeometry.Scheme.{u}}
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (F G : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
    (V : X.ProEt) (s : F.val.obj (op V)) (t : G.val.obj (op V)) :
    ((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} G).obj F).val.obj
      (op V) :=
  (CategoryTheory.toSheafify (ProEt.topology X)
    (SheafOfModules.siteTensorPresheaf F.val G.val).presheaf).app (op V)
      (s ⊗ₜ[O.obj.obj (op V)] t)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual module inverse-image unit on sections, using the recorded small model.
Source: Stacks Tags 03D2 and 09A5
(blueprint: lem-pur-isomorphism-inverse-image-tensor-hom). -/
noncomputable def purInverseImageSection {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) (O : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (F : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
    (V : Y.ProEt) (s : F.val.obj (op V)) :
    ((proEtaleModuleInverseImage g O).obj F).val.obj
      (op ((proEtaleBaseChange g).obj V)) :=
  (((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit g O)).unit.app
    ((proEtaleModuleToModel ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)).obj F)).val.app
        (op (AsSmall.up.obj V))) s

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pure scalar-extension sections, in the recorded mixed-universe construction.
Source: Stacks Tag 03EK (blueprint: lem-pur-isomorphism-inverse-image-tensor-hom). -/
noncomputable def purScalarSection {X : AlgebraicGeometry.Scheme.{u}}
    (O O' : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (α : O ⟶ O')
    (F : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
    (V : X.ProEt) (b : O'.obj.obj (op V)) (s : F.val.obj (op V)) :
    (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α F).val.obj
      (op V) :=
  (CategoryTheory.toSheafify (ProEt.topology X)
    (SheafOfModules.changeOfRingsPresheafOfUniverses α F).presheaf).app (op V)
      (b ⊗ₜ[O.obj.obj (op V), (α.hom.app (op V)).hom] s)


end AlgebraicGeometry.Scheme
