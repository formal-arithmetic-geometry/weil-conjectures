/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisData
import Sheaf.AlgebraicGeometry.InjectiveRestrictionSurjective
import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps

/-! Degreewise exactness for the concrete Mayer--Vietoris complex.

Source: Stacks Project, Cohomology, Tag 08BV, using Tags 01EB and 01EA.
(blueprint: lem-pc-kinjective-mayer-vietoris-degreewise).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false

noncomputable section
namespace AlgebraicGeometry

/-- The concrete Mayer--Vietoris sequence is short exact in a degree whose term is injective.
Source: Stacks Project, Cohomology, Tag 08BV, using Tags 01EB and 01EA.
(blueprint: lem-pc-kinjective-mayer-vietoris-degreewise).

Proof: Fix n and put M = I.X n. Evaluation preserves the biproduct and
identifies the first arrow with the pair of underived restriction units. The
transported adjunction identifies sections of its direct image over T with
M(T ∩ U). Its unit is restriction. For W ⊆ U, transpose the restriction
M(T ∩ U) → M(T ∩ W) along the smaller adjunction. In the definition of
schemeOpenModuleImageRestriction, the inverse composition comparison restricts
twice, the counit removes the repeated U-restriction, and the forward comparison
identifies the result with restriction to W. Thus the second arrow is the
difference of the restrictions from U and V to U ∩ V.

For every test open T, the opens T ∩ U and T ∩ V cover T. Sheaf uniqueness
makes the first map injective; sheaf gluing says its image is the kernel of
the difference map. Since M is injective, injective_restriction_surjective
lifts every section on T ∩ U ∩ V to T ∩ U. Pair this lift with zero on
T ∩ V to prove surjectivity of the second map. These constructions commute
with restriction to smaller test opens, so they give a kernel universal
property in presheaf modules. The fully faithful inclusion of sheaf modules
into presheaf modules transports that kernel property to sheaves. Sectionwise
injectivity implies monicity, and sectionwise surjectivity implies epicity,
which together give short exactness. Empty opens, the empty scheme, and
repeated opens are covered by the same gluing and lifting argument.
-/
theorem schemeMayerVietorisComplex_degreewise_shortExact
    (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (n : ℤ) (hI : Injective (I.X n)) :
    ((schemeMayerVietorisComplex X U V I).map
      (HomologicalComplex.eval (SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (ComplexShape.up ℤ) n)).ShortExact := by sorry

end AlgebraicGeometry
