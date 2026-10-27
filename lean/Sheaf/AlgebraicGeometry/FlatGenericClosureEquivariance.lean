/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Topology.KrullDimension
import Sheaf.TraceFormula.ReducedSchemeImage
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Equivariance of flat schematic generic closures

Source: ILO, Travaux de Gabber, Expose X, Theorem 3.4, proof Step 2, printed p. 160;
Stacks Tags 080F, 01RE, 01R8 and 01QP. Equivariance is the invariant-kernel enhancement
(blueprint: lem-sfb-flat-generic-closure-equivariance).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Base changing flat generic closures along a domination recovers the intrinsic closures
and their actions. The given `PartialIso` witnesses restrict the specified morphisms, not merely
an unrelated birational correspondence. The maps `ηS` and `ηV`, with their cartesian squares,
express the canonical generic identifications over `S₀.functionField`. They carry no actions.
The maps into fibre products, and all closure representatives, are specified over their ambient
schemes. Equalities of `ker` are equalities of closed subschemes, including their nilpotents.

Source: ILO X, Theorem 3.4, Step 2, p. 160; Stacks Tags 080F, 01RE, 01R8 and 01QP
(blueprint: lem-sfb-flat-generic-closure-equivariance).

Proof (the eleven steps of the DAG):
1. Birationality identifies the generic bases with Spec K. On affine domain charts A and B,
   A injects into B, both have fraction field K, and (A minus zero) inverse B is K.
   The equation r followed by v equals u identifies the generic map of r with the identity.
   Use lem-sc-integral-function-field-affine-fraction and def-pc-integral-scheme.
2. For a generic closed ideal J in E inverse B, the closure ideal is the kernel I of
   B to E inverse B modulo J. Exact localization gives E inverse I equals J. The generic
   point maps and their base changes are quasi-compact. Hence the generic fibres of the
   closures are the original N and D, compatibly with T and Spec K. Use lem-weil-pbc-
   scheme-image-qc-kernel, lem-weil-pbc-qcqs-morphism-permanence, lem-weil-pbc-localization-
   module-exact and lem-weil-pbc-fibre-product-affine-spectra.
3. Base change preserves flatness, finite presentation, finiteness and closed immersions.
   The composite of the two closed immersions is closed, as the composite of quotient maps.
   Use lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-qcqs-morphism-permanence,
   lem-weil-pbc-finite-morphism-permanence and lem-weil-pbc-closed-immersion-base-change.
4. Base change the finite projective-space embedding of T_V. Projective-space base change
   identifies its target with projective space over S. Use the closed-immersion base-change
   lemma and lemma-nagata-projective-space-base-change-pullback.
5. The geometric fibre over s is the fibre over r(s) extended to an algebraic closure of
   the residue field of s. Geometric purity gives local dimension one on the ordinary fibre;
   arbitrary field extension preserves the component dimensions. Use lem-trf-geometric-pure-
   fibre-point-dimension and lem-trf-field-extension-component-local-dimension.
6. On an affine base domain A, every affine chart C of P or M is A-flat, so C injects into
   its generic localization: nonzero scalars cannot kill an element. Use lem-weil-pbc-flat-
   morphism-affine-criterion, lem-trf-flat-module-torsionfree-domain, def-weil-pbc-module-
   localization and the affine fibre-product formula. This includes the empty marking.
7. On an affine chart B of W, write P as B/I. The preceding injection identifies the
   kernel of restriction B to the generic N with I. The same calculation for M and D
   identifies both intrinsic closure ideals on an affine basis. Thus any allowed domination
   gives these same closed subschemes of W. Use lem-weil-pbc-scheme-image-qc-kernel and
   lem-weil-pbc-closed-immersions-equal-ideal-isomorphic.
8. N is integral. Its schematic image P is reduced by lem-trf-reduced-scheme-image, and its
   underlying closure is nonempty and irreducible. Thus P is integral by def-pc-integral-scheme.
9. Localizing a nonempty affine domain C of P at nonzero base scalars does not change its
   fraction field. The generic localization is an affine chart of N. Apply lem-sc-integral-
   function-field-affine-fraction to obtain the displayed equivalence via the generic inclusion.
10. Each group automorphism commutes with generic restriction on translated opens, hence
    preserves both kernel ideals of Step 7. Apply its inverse for equality. The equal-ideal
    closed-immersion lemma gives unique automorphisms of P and M. Monomorphy gives their
    identity and multiplication laws, compatibility with M to P, and equivariance over T and S.
    This uses only ring isomorphisms, so permits nonfaithful and semilinear actions.
11. Repeat Step 7 inside P to identify M with the closure of D there. If D is empty,
    injectivity of generic restriction forces each affine ring of M to be zero, so M is empty.
-/
theorem flat_generic_closure_equivariance
    (k : Type u) [Field k] (S₀ S T V : Scheme.{u})
    [IsIntegral S₀] [IsIntegral S] [IsIntegral T] [IsIntegral V]
    (p₀ : S₀ ⟶ Spec (.of k)) (pS : S ⟶ Spec (.of k))
    (pT : T ⟶ Spec (.of k)) (pV : V ⟶ Spec (.of k))
    [LocallyOfFiniteType p₀] [QuasiCompact p₀]
    [LocallyOfFiniteType pS] [QuasiCompact pS]
    [LocallyOfFiniteType pT] [QuasiCompact pT]
    [LocallyOfFiniteType pV] [QuasiCompact pV]
    (u : S ⟶ S₀) (t : T ⟶ S₀) [IsHProjective t]
    (hu : u ≫ p₀ = pS) (ht : t ≫ p₀ = pT)
    (bu : S.PartialIso S₀) (hbu : bu.iso.hom ≫ bu.target.ι = bu.source.ι ≫ u)
    (v : V ⟶ S₀) (r : S ⟶ V) (hvr : r ≫ v = u)
    (hv : v ≫ p₀ = pV) (hr : r ≫ pV = pS)
    (bv : V.PartialIso S₀) (hbv : bv.iso.hom ≫ bv.target.ι = bv.source.ι ≫ v)
    (ηS : Spec S₀.functionField ⟶ S) (ηV : Spec S₀.functionField ⟶ V)
    (hηS : IsPullback ηS (𝟙 _) u (S₀.fromSpecStalk (genericPoint S₀)))
    (hηV : IsPullback ηV (𝟙 _) v (S₀.fromSpecStalk (genericPoint S₀)))
    (hηr : ηS ≫ r = ηV)
    (N D : Scheme.{u}) [IsIntegral N]
    (n : N ⟶ T) (q : N ⟶ Spec S₀.functionField)
    (hN : IsPullback n q t (S₀.fromSpecStalk (genericPoint S₀)))
    [Smooth q] [GeometricallyIntegral q] (hdim : topologicalKrullDim N = 1)
    (d : D ⟶ N) [IsClosedImmersion d] [IsFinite (d ≫ q)] [Etale (d ≫ q)]
    (L : Scheme.{u}) (iL : L ⟶ T) [IsClosedImmersion iL]
    (hL : iL.ker = (d ≫ n).ker)
    (H : Type v) [Group H] [Finite H]
    (σk : H →* Aut (Spec (.of k)))
    (σ₀ : H →* Aut S₀) (σS : H →* Aut S) (σT : H →* Aut T)
    (σK : H →* Aut (Spec S₀.functionField)) (σN : H →* Aut N) (σD : H →* Aut D)
    (heq₀ : ∀ h : H, (σ₀ h).hom ≫ p₀ = p₀ ≫ (σk h).hom)
    (heqS : ∀ h : H, (σS h).hom ≫ pS = pS ≫ (σk h).hom)
    (heqT : ∀ h : H, (σT h).hom ≫ pT = pT ≫ (σk h).hom)
    (hequ : ∀ h : H, (σS h).hom ≫ u = u ≫ (σ₀ h).hom)
    (heqt : ∀ h : H, (σT h).hom ≫ t = t ≫ (σ₀ h).hom)
    (heqK : ∀ h : H, (σK h).hom ≫ S₀.fromSpecStalk (genericPoint S₀) =
      S₀.fromSpecStalk (genericPoint S₀) ≫ (σ₀ h).hom)
    (heqn : ∀ h : H, (σN h).hom ≫ n = n ≫ (σT h).hom)
    (heqq : ∀ h : H, (σN h).hom ≫ q = q ≫ (σK h).hom)
    (heqd : ∀ h : H, (σD h).hom ≫ d = d ≫ (σN h).hom)
    (TV LV : Scheme.{u}) (iV : TV ⟶ pullback t v)
    [IsClosedImmersion iV] (fV : TV ⟶ V)
    (hfV : iV ≫ pullback.snd t v = fV)
    (nV : N ⟶ TV)
    (hnVT : nV ≫ iV ≫ pullback.fst t v = n)
    (hnVV : nV ≫ fV = q ≫ ηV)
    (hTV : iV.ker = (nV ≫ iV).ker)
    (jV : LV ⟶ TV) [IsClosedImmersion jV] (hLV : jV.ker = (d ≫ nV).ker)
    [IsHProjective fV] [Flat fV] [LocallyOfFinitePresentation fV]
    [QuasiCompact fV] [QuasiSeparated fV]
    (hpureV : ∀ z : V,
      ∀ Z ∈ irreducibleComponents (pullback (C := Scheme.{u}) fV
        (Spec.map (CommRingCat.ofHom (algebraMap (V.residueField z)
          (AlgebraicClosure (V.residueField z)))) ≫ V.fromSpecResidueField z)),
        topologicalKrullDim Z = 1)
    [IsFinite (jV ≫ fV)] [Flat (jV ≫ fV)]
    [LocallyOfFinitePresentation (jV ≫ fV)] [QuasiCompact (jV ≫ fV)]
    [QuasiSeparated (jV ≫ fV)]
    (P M : Scheme.{u}) (π : P ⟶ TV) (p : P ⟶ S)
    (hP : IsPullback π p fV r)
    (πM : M ⟶ LV) (iM : M ⟶ P) (hM : IsPullback πM iM jV π)
    (iP : P ⟶ pullback t u)
    (hiPT : iP ≫ pullback.fst t u = π ≫ iV ≫ pullback.fst t v)
    (hiPS : iP ≫ pullback.snd t u = p) :
    ∃ (_ : IsIntegral P),
      IsClosedImmersion iP ∧ IsClosedImmersion iM ∧
      IsHProjective p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧
      QuasiCompact p ∧ QuasiSeparated p ∧
      (∀ s : S,
        ∀ Z ∈ irreducibleComponents (pullback (C := Scheme.{u}) p
          (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
            (AlgebraicClosure (S.residueField s)))) ≫ S.fromSpecResidueField s)),
          topologicalKrullDim Z = 1) ∧
      IsFinite (iM ≫ p) ∧ Flat (iM ≫ p) ∧ LocallyOfFinitePresentation (iM ≫ p) ∧
      QuasiCompact (iM ≫ p) ∧ QuasiSeparated (iM ≫ p) ∧
      ∃ (nP : N ⟶ P) (dM : D ⟶ M),
        nP ≫ π = nV ∧
        nP ≫ iP ≫ pullback.fst t u = n ∧
        IsPullback nP q p ηS ∧
        dM ≫ iM = d ≫ nP ∧
        IsPullback dM (d ≫ q) (iM ≫ p) ηS ∧
        iP.ker = (nP ≫ iP).ker ∧
        (iM ≫ iP).ker = (d ≫ nP ≫ iP).ker ∧
        iM.ker = (d ≫ nP).ker ∧
        (IsEmpty D → IsEmpty M) ∧
        (∃ hgeneric : nP (genericPoint N) = genericPoint P,
          ∃ e : P.functionField ≃+* N.functionField,
            e.toRingHom =
              (P.presheaf.stalkSpecializes (specializes_of_eq hgeneric) ≫
                nP.stalkMap (genericPoint N)).hom) ∧
        ∃ (τP : H →* Aut P) (τM : H →* Aut M),
          (∀ h : H, (τP h).hom ≫ p = p ≫ (σS h).hom) ∧
          (∀ h : H, (τP h).hom ≫ iP ≫ pullback.fst t u =
            iP ≫ pullback.fst t u ≫ (σT h).hom) ∧
          (∀ h : H, (τM h).hom ≫ iM = iM ≫ (τP h).hom) ∧
          (∀ h : H, (τM h).hom ≫ iM ≫ p = iM ≫ p ≫ (σS h).hom) ∧
          (∀ h : H, (τM h).hom ≫ iM ≫ iP ≫ pullback.fst t u =
            iM ≫ iP ≫ pullback.fst t u ≫ (σT h).hom) ∧
          (∀ h : H, (σN h).hom ≫ nP = nP ≫ (τP h).hom) ∧
          (∀ h : H, (σD h).hom ≫ dM = dM ≫ (τM h).hom) := by
  sorry

end AlgebraicGeometry
