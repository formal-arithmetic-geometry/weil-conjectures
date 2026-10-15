/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import Sheaf.AlgebraicGeometry.EtaleConstantRingInverseImageComparison
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.RingedToposMorphism
import WeilConjectures.AlgebraicGeometry.EtaleSheaves

/-! # Underlying abelian direct-image acyclicity of module K-injectives

Source: Stacks Project, Cohomology on Sites, Tag 0D6J(3).
(blueprint: lem-kun-module-abelian-kinjective-direct-image-acyclic)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Abelian replacement of a module K-injective remains a quasi-isomorphism after direct image.
This asserts acyclicity for the indicated direct image, without asserting that forgetting
preserves K-injectivity.

Source: Stacks Project, Cohomology on Sites, Tag 0D6J(3), including its resolution
normalization; equivalently apply Tag 0D6E to coefficient restriction and direct image.
(blueprint: lem-kun-module-abelian-kinjective-direct-image-acyclic).

Proof: Use the constant-ring module equivalence, retaining the underlying additive
sheaf. Encode abelian sheaves as modules over the constant integers; ULift of the
integers supplies the coefficient universe when necessary. The coefficient forgetful
functor is the module direct image of the identity-topos ring map from the constant
integers to the constant Lambda sheaf. The geometric morphism induced by v, equipped
with its constant-integer structural map, gives a second ringed-topos morphism. Its
module direct image is ordinary abelian direct image under the integer encoding.
The structural maps preserve the ring operations, and the direct-image scalar action
is sectionwise, so the generalized-element module-linearity identities hold.

For the abstract ringed-topos interface, replace each etale site by ULiftHom,
with morphisms lifted to the object universe and the induced topology. Precomposition
by the site equivalence transports rings, modules, and underlying additive sheaves.
Its unit and counit give exact inverse equivalences. Conjugate base change and the
set inverse-image adjunction by these equivalences; finite-limit preservation is
retained. Thus the site, ring and module universes match the abstract theorem.

Transport I, J, and j through these exact equivalences. K-injectivity is preserved:
the inverse equivalence is exact, so the adjunction transports null-homotopies from
acyclic complexes. Quasi-isomorphisms are preserved and reflected by the homology
comparison for an exact equivalence. Apply the final resolution-normalization clause
of ringedToposDerivedPushforwardComposition (Tag 0D6E) to the two morphisms above.
It asserts directly that the second module direct image of j is a quasi-isomorphism.
The underlying-sheaf identifications turn that map into v_*j, proving the claim.
The identity morphism, zero ring, zero complex, empty etale objects, and arbitrary
shifts are included; no boundedness or finite cohomological dimension is used.
-/
theorem moduleAbelianForget_kInjective_directImage_quasiIso
    (Λ : Type (u + 1)) [CommRing Λ] {A B : Scheme.{u}} (v : A ⟶ B)
    (I : CochainComplex (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    [I.IsKInjective]
    (J : CochainComplex (Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    [J.IsKInjective]
    (j : ((moduleAbelianForget Λ A).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] :
    QuasiIso ((((v)_*[AddCommGrpCat.{u + 1}]).mapHomologicalComplex (.up ℤ)).map j) := by sorry

end AlgebraicGeometry.Etale
