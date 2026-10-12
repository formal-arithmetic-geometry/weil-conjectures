/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Acyclicity of extended injective torsion module sheaves

Source: Stacks Project, Tags 0F1C, 03QU and 03FD.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- The inverse image of an injective Z/n-module sheaf is acyclic after extending
algebraically closed scalars, when n is invertible in the base field.
Source: Stacks Project, Tag 0F1C (field-extension exchange), Tag 03QU (cohomology over
separably closed bases) and Tag 03FD (abelian acyclicity of injective module sheaves).
(blueprint: lem-sc-algclosed-extension-injective-acyclic)

Proof: regard J as a module over the constant Z/n ring sheaf. Its underlying abelian
sheaf is acyclic on X by Tag 03FD; thus the positive cohomology sheaves of its derived
direct image along f to Spec k vanish: sections on the small etale topos of an
algebraically closed field are exact and conservative (the topos is that of sets).
All its cohomology stalks are killed by n, which is invertible in k.
Apply the field-extension exchange of Tag 0F1C to identify the derived direct image
of the inverse image on X_K with the inverse image of that direct image on Spec K.
Exactness of inverse image makes its positive cohomology sheaves zero. Global sections
on Spec K are exact because K is algebraically closed, so Leray identifies the positive
abelian cohomology on X_K with these zero groups. Forgetting modules commutes with
inverse image, so this is precisely the group in the statement. For n = 1 every module
sheaf is zero; n = 0 is excluded by hn. The empty scheme causes no exception.
The remaining input is relative field-extension exchange, not the asserted comparison
for the particular constant sheaf. -/
theorem subsingleton_cohomology_upperStar_injective_algClosed_extension
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (n : ℕ) (hn : (n : k) ≠ 0)
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))))
    [Injective J] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
        AddCommGrpCat.{u + 1})).obj
          ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj J)) q) := by sorry

end AlgebraicGeometry.Etale
