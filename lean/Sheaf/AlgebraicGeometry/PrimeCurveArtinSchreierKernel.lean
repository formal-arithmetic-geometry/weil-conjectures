/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T8
-/
module

public import Sheaf.AlgebraicGeometry.FrobeniusVectorBundleKernel
public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import Sheaf.AlgebraicGeometry.ArtinSchreierSchemeSectionData
import Sheaf.AlgebraicGeometry.ArtinSchreierSchemeSectionExact
import Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages
import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor

/-!
# The degree-one Artin--Schreier kernel in a smooth proper curve family

Source: Stacks Project, Tag 0GKV, case (b), the exact sequence and its kernel.
(blueprint: lem-weil-pbc-prime-curve-artin-schreier-kernel)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The first direct image with prime coefficients is the fixed-point kernel of a
Frobenius-semilinear endomorphism of a finite locally free structure module.
Source: Stacks Project, Tag 0GKV, case (b), second and third paragraphs.
(blueprint: lem-weil-pbc-prime-curve-artin-schreier-kernel)

Proof: Pullback of global functions makes p zero on X. The scheme Artin--Schreier
section-data and exactness lemmas give the short exact sequence of constant Z/p,
the lifted associated structure sheaf, and that same structure sheaf with map wp.
Transport its tensor-unit model to X.etaleAdditiveSheaf by the natural coordinate
identifications: on U the component sends x to ULift.up (a U x). Naturality is the
restriction identity in the section data, and each component is an additive
isomorphism. Thus the structure-direct-image theorem applies to these coefficients.
The right-derived delta functor of abelian direct image supplies the exact segment
from the cokernel of f_*wp to R1 f_* Z/p to the kernel of R1 f_*wp. The smooth-curve
structure direct-image theorem identifies f_*O with O_S and R1 f_*O with the lifted
associated sheaf of a finite locally free quasi-coherent module E. On f_*O, wp is
p-th power minus identity; the rank-one case of the Frobenius vector-bundle theorem
makes its cokernel zero. Here use E = O_S and sectionwise p-th power, whose
additivity follows from p = 0 and whose semilinearity is (ab)^p = a^p b^p.
The zero-degree derived comparison is natural in wp, so this also says that
R0 f_*wp is epic. The connecting morphism is then zero by epi cancellation;
exactness at R1 f_* Z/p makes its map into R1 f_*O monic. Exactness at R1 f_*O
identifies this monomorphism with the kernel. Hence the exact segment identifies
R1 f_* Z/p with the
kernel on R1 f_*O. Put F = R1 f_*wp + identity and transport through the specified
structure comparison. To verify F(ae) = a^p F(e), first take a raw local cohomology
class over an etale object. Sectionwise p-th power intertwines multiplication by
a with multiplication by a^p. Functoriality of cohomology and the scalar formula of
the structure direct-image theorem give the same equation on raw classes. The
higher-image presheaf theorem says sections are locally represented by such classes,
so sheaf separation proves the equation for every section. Finally the exact
module/abelian direct-image comparison identifies the left term with the forgotten
prime-module higher direct image. The construction uses the full characteristic-p
closed subscheme, including nilpotents. For an empty base take the zero module. -/
theorem exists_prime_curve_artinSchreier_kernel
    {X S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1)
    (p : ℕ) [Fact p.Prime] (hp : (p : Γ(S, ⊤)) = 0) :
    ∃ (E : S.Modules) (_ : E.IsFiniteLocallyFree) (_ : E.IsQuasicoherent)
      (F : Scheme.Modules.liftedCoherentEtaleSheaf E ⟶
        Scheme.Modules.liftedCoherentEtaleSheaf E),
      (∀ (U : S.Etaleᵒᵖ) (a : ULift.{u + 1} Γ(U.unop.left, ⊤))
        (e : ULift.{u + 1} Γ((Scheme.Modules.tensorPullback U.unop.hom).obj E, ⊤)),
        F.hom.app U (ULift.up (a.down • e.down)) =
          ULift.up (a.down ^ p •
            (@id Γ((Scheme.Modules.tensorPullback U.unop.hom).obj E, ⊤)
              (F.hom.app U e).down))) ∧
      Nonempty ((moduleAbelianForget (ULift.{u + 1} (ZMod p)) S).obj
        (higherDirectImage (ULift.{u + 1} (ZMod p)) f 1
          ((constantSheaf X.smallEtaleTopology _).obj
            (ModuleCat.of (ULift.{u + 1} (ZMod p)) (ULift.{u + 1} (ZMod p))))) ≅
        kernel (F - 𝟙 _)) := by sorry

end AlgebraicGeometry.Etale
