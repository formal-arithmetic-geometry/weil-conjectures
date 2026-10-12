module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Homology.QuasiIso
public import Sheaf.Topology.RingedSpaceModuleCohomology

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Degree-zero part of the augmented Čech quasi-isomorphism.

Source: Stacks Project, Cohomology of Sheaves, Tag 01EP.
(blueprint: lem-sc-injective-module-cech-augmentation-zero)

Proof: identify categorical products of opens with their finite intersections
and products of modules with families of sections. The differential from degree
zero to degree one sends a family to the difference of its restrictions on each
pairwise intersection. Its kernel therefore consists precisely of compatible
families. The sheaf gluing axiom gives a unique section on the union for every
such family. The union is X by hU, so restriction from J(X) to this kernel is
bijective and linear. There are no incoming boundaries in either degree-zero
complex. The source's zero homology is its sole term; the target's zero homology
is the kernel just described. The equality ht identifies the global-section
scalar restriction with the identity, and hb identifies the induced homology
map with restriction. Thus it is an isomorphism. This argument does not need
injectivity. If the cover is empty, hU forces X to be empty; the empty-cover
sheaf axiom gives J(X) = 0, and the target is the empty product, also zero. -/
theorem injectiveModuleCechAugmentation_quasiIsoAt_zero {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (J : X.Modules) [Injective J]
    (ht : (X.ringCatSheaf.obj.map (isTerminalTop.op.to (op ⊤))).hom =
      RingHom.id Γ(X, ⊤))
    (b : (CochainComplex.single₀ (ModuleCat.{u} Γ(X, ⊤))).obj
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj J) ⟶
      (CategoryTheory.cechComplexFunctor U).obj J.presheafModuleCat)
    (hb : b.f 0 =
      (ModuleCat.restrictScalarsId'App
        (X.ringCatSheaf.obj.map (isTerminalTop.op.to (op ⊤))).hom ht
        (J.val.obj (op ⊤))).inv ≫
      Pi.lift fun y : Fin 1 → ι =>
        J.presheafModuleCat.map (homOfLE (le_top (a := ∏ᶜ fun l => U (y l)))).op) :
    QuasiIsoAt b 0 := by sorry

end AlgebraicGeometry.Scheme.Modules
