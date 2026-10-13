/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.OpenModuleStalkFunctor
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.AlgebraicGeometry.AffinePerfectHomColimit
import Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence

/-! # Detecting a quasi-isomorphism of strictly perfect complexes near a point

Source: Stacks Project, Tags 09RE, 0BC7 (2), and 00CR.
(blueprint: lem-sc-perfect-stalk-quasi-iso-detection).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- A fixed chain map of strictly perfect complexes on an affine open which is a
quasi-isomorphism at one stalk becomes a quasi-isomorphism on a smaller affine open.

Source: Stacks Project, Tags 09RE, 0BC7 (2), and 00CR.
(blueprint: lem-sc-perfect-stalk-quasi-iso-detection).

Proof: Use the affine tilde/Gamma correspondence to construct the bounded section
complexes of P and Q. The finite-free retractions give finite projective terms. Form the
cone C of the section map corresponding to f; in degree n it is P in degree n+1 plus Q
in degree n, so it is bounded with finite projective terms. Exactness of the open-site
stalk functor identifies its localization at the prime of x with the cone of the stalk
map. The hypothesis makes this cone acyclic. Consequently the identity of Q(C) and its
zero endomorphism agree after prime localization. By 00CR the prime localization is the
filtered colimit of the principal localizations outside the prime. Injectivity of the
perfect Hom comparison (09RE, or 0BC7 (2)), applied to C,C, says that the two elements of
the colimit represented by identity and zero are equal. The equality criterion for a
filtered colimit of sets gives a common principal localization where these endomorphisms
are already equal. An object whose identity is zero is a zero object, so the localized
cone is zero in the derived category. The cone triangle then makes Q(f) an isomorphism;
the localization criterion says f is a quasi-isomorphism there. Transport back through
the affine correspondence and restriction comparisons. The principal open is affine,
contains x, and is contained in U. Zero complexes, disjoint support bounds, and
non-Noetherian rings all satisfy the same argument. No coherence of cone cohomology or
closedness of its support is used. -/
theorem exists_affine_restriction_quasiIso_of_perfect_stalk_quasiIso
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U) (hU : IsAffineOpen U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P) (hQ : IsStrictlyPerfect X U Q) (f : P ⟶ Q)
    (hf : QuasiIso (((openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex
      (.up ℤ)).map f)) :
    ∃ (W : X.Opens) (_hxW : x ∈ W) (_hW : IsAffineOpen W) (hWU : W ≤ U),
      QuasiIso (((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)).map f) := by sorry

end
end AlgebraicGeometry.Scheme
