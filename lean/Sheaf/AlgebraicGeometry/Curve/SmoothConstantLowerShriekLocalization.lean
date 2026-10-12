/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs

/-! # Localization of smooth constant-coefficient curve assertions

Source: Stacks Project, Tag 03SG, proof.
(blueprint: lem-pbc-u2-smooth-constant-lower-shriek-localization)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

/-- The constant-coefficient calculations on all smooth curves imply the corresponding
extension-by-zero calculations for every open immersion into a smooth curve.
Source: Stacks Project, Tag 03SG, proof, using Tag 0GJA for dense-open localization.
(blueprint: lem-pbc-u2-smooth-constant-lower-shriek-localization)

Proof: A smooth finite-type scheme over an algebraically closed field is Noetherian and
has normal local rings. Two distinct components through a point would give two minimal
primes in its local domain, which is impossible. Thus the finitely many components are
pairwise disjoint. Each is closed; its complement is a finite union of the other closed
components, so each is also open. For each component C, the inverse image of U is either empty
or a dense open. In the empty case extension by zero is the zero sheaf, which satisfies
all eight assertions: its cohomology groups are zero and every comparison is the unique
map between zero groups. Otherwise apply H to the smooth curve C. The constant coefficient
sheaf is constructible and killed by r. Its pullback to the dense open is canonically the
constant coefficient sheaf there. Dense-open prime-torsion localization then gives the
assertions for its extension by zero. This includes zero-dimensional components: a nonempty
open in such a component is the whole component, so localization is the identity.
Push each component's sheaf along the finite open-and-closed component inclusion. Finite
pushforward preserves the assertions. To use its abelian-sheaf formulation, forget the
R-module structure on both sheaves. The underlying abelian sheaf of the R-module direct
image is canonically the abelian direct image: both have the same sections and restriction
maps. This is a comparison after forgetting coefficients, not an equivalence between
R-modules and abelian groups. The definitions of all eight assertions use this underlying
abelian sheaf. The comparison respects inverse image, cohomology pullback and restriction;
constructibility and torsion conditions agree here because R is the finite prime field.
Affineness and properness of X imply the corresponding conditions on every component.
Their finite direct sum is the extension by zero on X, as checked on the disjoint component
cover. Assemble the summands using split short exact sequences and curve devissage.
The component projections preserve primary and invertible torsion conditions, and every
comparison map is the direct sum of the component maps. Thus the conditional hypotheses
and the comparison maps are precisely those in the eight assertions. The empty scheme is
the empty direct sum, hence gives the zero case. -/
theorem smoothConstantLowerShriekAssertions_of_constant
    {k : Type u} [Field k] [IsAlgClosed k] (r : ℕ) [Fact r.Prime]
    (H : ∀ {C : Scheme.{u}} (g : C ⟶ Spec (.of k)) [IsCurve g] [Smooth g],
      IsCurve.Assertions (ULift.{u + 1} (ZMod r)) g
        (Etale.constantModSheaf (ULift.{u + 1} (ZMod r)) C r))
    {X U : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] [Smooth f]
    (j : U ⟶ X) [IsOpenImmersion j] :
    IsCurve.Assertions (ULift.{u + 1} (ZMod r)) f
      ((Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) j).obj
        (Etale.constantModSheaf (ULift.{u + 1} (ZMod r)) U r)) := by sorry

end AlgebraicGeometry.IsCurve
