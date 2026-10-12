/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilated
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.RingTheory.FiniteIffFormalGlueing
import Sheaf.RingTheory.FormalGlueingIsogeny
import Sheaf.Topology.GlueSheavesOfModules
import Sheaf.AlgebraicGeometry.CompletionIsogenyFromHomLift
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Sheaf.AlgebraicGeometry.Coherent

/-! # Existence of outgoing coherent formal algebraizations

Source: Stacks Project, Lemma 0889, proof of (2)
(blueprint: lem-weil-pbc-grothendieck-existence-easy-from-exists).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Existence, without uniqueness, of an algebraization of a map out of a completion.
Source: Stacks Project, Cohomology of Schemes, Lemma 0889, proof of (2);
More on Algebra, Lemma 0ALK(2) and Remark 05EU
(blueprint: lem-weil-pbc-grothendieck-existence-easy-from-exists).

Proof. Restrict to Noetherian affine opens. Restriction is exact and commutes with
ideal products, quotients, and completion. On Spec A put S = A^, M = Gamma(G), and
N' = lim Gamma(F_n). Lemma 087W identifies the formal category with finite S-modules;
00MA identifies completion of M with S tensor M. Remark 0888 identifies the uniform
componentwise bound with a bound on the kernel and cokernel of S tensor M -> N'.
The map A -> S is flat, I is finitely generated, and A/I -> S/IS is an isomorphism.
Apply 0ALK(2) to construct psi : M -> N with I-power-torsion kernel and cokernel,
and b : S tensor N isomorphic to N' with b composed with the base change of psi
being the given formal map. Localizing psi at each generator of I makes it an
isomorphism, so each N_f is finite. Its base change is N', also finite. By 05EU,
N is a finite A-module. Its kernel and cokernel are finite over Noetherian A;
take the maximum of exponents killing their finite generating families, enlarged
to be positive. The affine dictionary gives a coherent triple with this bound.

The Hom-lifting theorem completion_isogeny_from_hom_lift gives unique comparison
maps between two such local triples on each affine inside their overlap. Lift the
inverse formal comparison too; uniqueness makes their composites identities.
Uniqueness also makes the lifts compatible with restriction. Glue them using 04TN
to comparison isomorphisms on overlaps; uniqueness forces the cocycle identity.
Glue the modules using 00AL/00AM; coherence is local. Glue a and the components of
b and its inverse using 04TN and restriction of quotients. Naturality of b and the
factorization identity hold locally, hence globally. A finite affine cover exists
since X is Noetherian. The maximum of its finitely many exponents kills the global
kernel and cokernel of a. For the empty scheme use exponent one. No uniqueness
of triples is asserted here; its categorical assembly is in the parent module.
-/
theorem grothendieckExistenceEasy_exists_from (X : Scheme.{u}) [IsNoetherian X]
    (I : X.IdealSheafData) (G : CoherentModules X)
    (F : CoherentFormalModule X I) :
    ∀ (α : (completion X I).obj G ⟶ F),
      (∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ,
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower I.toModulesι t).2
          (kernel (α.hom.app (op n)))) ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower I.toModulesι t).2
          (cokernel (α.hom.app (op n))))) →
      ∃ (H : CoherentModules X) (a : G ⟶ H)
        (β : (completion X I).obj H ≅ F),
        (∃ t : ℕ, 1 ≤ t ∧
          IsZero (Scheme.idealModuleProduct
            (Scheme.idealSheafPower I.toModulesι t).2 (kernel a.hom)) ∧
          IsZero (Scheme.idealModuleProduct
            (Scheme.idealSheafPower I.toModulesι t).2 (cokernel a.hom))) ∧
        α = (completion X I).map a ≫ β.hom := by sorry

end AlgebraicGeometry
