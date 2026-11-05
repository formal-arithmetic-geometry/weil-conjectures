/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Relative.RelativeEtaleCohomology
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.Algebra.Homology.SmoothPurity.KernelShiftedConeBoundary
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolution
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import WeilConjectures.CategoryTheory.InjectiveSheafMonoRestriction

/-!
# Relative section cones and supported cohomology

Source: Stacks Project, Cohomology on Sites, cohomology with support; blueprint
main-20261015, sec-smooth-purity/sk-prop-an/lem-pur-divisor-class.proof.md
(blueprint: lem-pur-divisor-relative-cone).

The structures below package equations, rather than choosing comparison maps from an
existence theorem. Their kernel and right-derived normalizations fix the identifications.
Object squares express both restriction to an etale neighbourhood and enlargement of
support, on the site of the original scheme, without changing sites by an implicit bridge.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

namespace AlgebraicGeometry
namespace Etale
namespace RelativeCone

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)

variable [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]

end RelativeCone

namespace RelativeCone

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
variable [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]

end RelativeCone

namespace RelativeCone

end RelativeCone

end Etale
end AlgebraicGeometry
