module

public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing

import WeilConjectures.AlgebraicGeometry.GeometricallyConnectedCheckAfterExtension
import Sheaf.AlgebraicGeometry.GeometricSemiabelianSplitQuotient
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import WeilConjectures.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres
import Mathlib.LinearAlgebra.FreeModule.PID
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcSheaf
import Sheaf.AlgebraicGeometry.LfpSmoothFlatBaseChange

/-! # Existence of a Néron lft-model for a geometrically semiabelian group

Source: Bosch–Lütkebohmert–Raynaud, *Néron Models* (1990), 10.1 Definition 1
and 10.2 Theorem 2 (printed pp. 289, 297).
(blueprint: lem-sfb-semiabelian-neron-lft-existence)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A smooth separated commutative group scheme of finite type over the fraction
field of a DVR with semiabelian geometric fibres has a Néron lft-model.  The model
satisfies the Néron mapping property for all smooth test schemes and for smooth
commutative group schemes, where the latter is the restriction to homomorphisms.

Source: Bosch–Lütkebohmert–Raynaud, *Néron Models* (1990), 10.1 Definition 1
and 10.2 Theorem 2 (printed pp. 289, 297).
(blueprint: lem-sfb-semiabelian-neron-lft-existence)

Proof plan:
1. On each algebraically closed fibre, the quotient onto the abelian variety is a
   split-torus torsor by lem-sfb-smooth-affine-group-torsor-representability. It is
   open with connected fibres and connected base, hence its total space is connected.
   Apply lem-weil-geometrically-connected-check-after-extension, then
   lem-sfb-geometric-semiabelian-split-quotient, to split P over a finite Galois
   extension L/F as an extension of an abelian variety B by a split torus.
2. Let C be the integral closure of R in L. The PID Noetherian/normal lemma and
   lem-sc-dvr-dimension-one allow application of the finite separable integral
   closure lemma. The closure is Dedekind with surjective spectrum map by
   lem-sc-integral-closure-dedekind-surjective-fibres. Clearing denominators shows
   its fraction field is L. It is torsion-free and finite over the DVR, so
   lem-sc-dvr-fg-torsionfree-free makes it free of positive rank and faithfully flat.
3. Apply lem-sfb-abelian-neron-model to B over C.
4. The B-to-G_m clause of lem-sfb-torus-abelian-hom-vanishing, followed by fpqc
   descent of equality from lem-a1-algebraic-space-fpqc-sheaf, makes every character
   of B vanish. Apply lem-sfb-split-torus-extension-neron-lft to obtain the model
   of P_L over C.
5. Apply lem-sfb-finite-flat-neron-lft-descent with G = H = P and the identity
   closed immersion. It gives N, the generic-fibre isomorphism, and the restriction
   bijection for every smooth test scheme; no quasi-compactness of N is needed.
6. Given a generic group homomorphism, extend it by step 5. The smooth-flat lemma,
   lem-sfb-scheme-lfp-smooth-flat-base-change and lem-trf-smooth-composition make
   X times X smooth over the trait. Uniqueness in step 5, applied to X times X,
   the trait, and X, respectively, forces preservation of multiplication, identity,
   and inverse. Restriction preserves group homomorphisms, and injectivity on all
   morphisms gives injectivity on homomorphisms. -/
theorem semiabelian_neron_lft_existence
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (F : Type u) [Field F] [Algebra R F] [IsFractionRing R F]
    (P : Grp (Over (Spec (.of F)))) [IsCommMonObj P.X]
    [Smooth P.X.hom] [IsSeparated P.X.hom]
    [LocallyOfFiniteType P.X.hom] [QuasiCompact P.X.hom]
    (hP : HasSemiabelianGeometricFibres P) :
    ∃ N : Grp (Over (Spec (.of R))),
      IsCommMonObj N.X ∧ Smooth N.X.hom ∧ IsSeparated N.X.hom ∧
      LocallyOfFiniteType N.X.hom ∧
      ∃ α : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).mapGrp.obj N ≅ P,
        (∀ X : Over (Spec (.of R)), Smooth X.hom →
          Function.Bijective (fun (f : X ⟶ N.X) ↦
            (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map f ≫
              α.hom.hom.hom)) ∧
        (∀ X : Grp (Over (Spec (.of R))), IsCommMonObj X.X → Smooth X.X.hom →
          Function.Bijective (fun (f : X ⟶ N) ↦
            (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).mapGrp.map f ≫
              α.hom)) := by
  sorry

end AlgebraicGeometry
