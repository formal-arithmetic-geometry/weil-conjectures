/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.CategoryTheory.InternalBarRoofAdjunction
public import Sheaf.CategoryTheory.InternalInflationGradedCup
public import Sheaf.CategoryTheory.InternalShiftedRoof

/-! # Normalization of one internal character lift

Source: latest blueprint, six-functors direct-images proof, paragraph (3),
agent-formulated internal bar normalization, steps 1–3 of the character-roof argument
(blueprint: lem-sfb-internal-bar-character-lift-normalization).
The assertion concerns one degree-one lift; finite ordered products are not involved.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CondensedBar CategoryTheory.CondensedBarRoof
open Profinite.CondensedAction.InternalBar
namespace CategoryTheory.CondensedDerivedRestriction

/-- A normalized degree-one bar lift represents the negative extension boundary and,
under the canonical shifted adjunction, the negative positive character class.
Source: latest direct-images proof, paragraph (3), agent-formulated internal
character normalization, steps 1–3 of lem-sfb-internal-bar-character-roof-cup
(blueprint: lem-sfb-internal-bar-character-lift-normalization).

Proof:
1. The character identities give the existing extension E_a with action
   g(x,y)=(x+a(g)y,y). On generalized generators define ell[g]=(a(g),1).
   The free internal-module adjunction gives an underlying module map; naturality
   of a makes it natural on profinite tests, and a(hg)=a(h)+a(g) proves
   equivariance. Projection gives the augmentation. Alternating deletion gives
   ell partial_1[g0,g1]=(a(g1)-a(g0),0)=(a(g0^-1 g1),0).
2. Use the cone argument of the extension clause of normalized_roofs directly in
   the specified coefficient localization. The kernel property of the extension
   inclusion i gives a unique f with f;i=partial_1;ell, and monicity of i gives
   partial_2;f=0. Freeness and step 1 identify f with the assumed augmented
   component of L. Hence e[1]L is the single-component cocycle map fbar: maps to
   A[1] are determined by that component. The cone C(i) has A in degree -1, E_a
   in degree zero, and differential i. Its projection v to A[0] is a
   quasi-isomorphism by the short exact sequence. The components (f,ell) define
   kappa:P->C(i), with v kappa=e and pr kappa=fbar. The canonical triangle
   boundary is -Q(pr) Q(v)^-1. Since Q(v) Q(kappa)=Q(e), cancellation gives
   Q(fbar) Q(e)^-1=-delta_a. The prescribed augmentation equation gives equality
   of the degree-zero components of v kappa and e; all other target components
   vanish. Insert the canonical singleFunctorIsoCompQ and shift comparisons.
   This is the extension clause's cone proof itself, so no change of the
   localization universe or choice of a bar comparison model is needed.
3. The invariant-inclusion adjunction sends the extension boundary to the
   derived-invariants boundary after the invariant unit. Its canonical shift
   comparison, followed by shifting down once, is exactly characterClass, by
   classShifted and characterClass. Additivity of derived invariants, shifts,
   composition, and the adjunction bijection preserves the minus sign.
   The argument also applies to the zero ring, trivial character, trivial group,
   and characteristic two; it uses no projectivity of a bar term.
-/
theorem internalBarCharacterLiftNormalization
    (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (R : Resolution A.toMon G) (e : RoofAugmentation R) [QuasiIso e]
    (he : augmentationEquation R e) (a : Character A G)
    (L : complex R ⟶ (complex R)⟦(1 : ℤ)⟧)
    (hL : ∀ (S : Profinite.{u}) (x : Fin 2 → C(S, G)),
      onSections A.toMon
        ((termIso R 1).inv ≫ L.f (-1) ≫
          (CochainComplex.shiftFunctorObjXIso (complex R) 1 (-1) 0 rfl).hom ≫
            (termIso R 0).hom ≫ R.augmentation).val S
        (basis A.toMon G 2 (R.objects 1) (R.freeIso 1) S x) =
          a.app S ((x 0)⁻¹ * x 1)) :
    let rho : coefficient A G ⟶ (coefficient A G)⟦(1 : ℤ)⟧ :=
      localizedShiftedRoof DerivedCategory.Q.{u + 1} e
        ((DerivedCategory.singleFunctorIsoCompQ (Equivariant A G) 0).app
          (regularTrivial A G)) (1 : ℤ) L
    rho = -(extensionExact a).singleδ ∧
      inflationPhi A G 1 rho = -characterClass a := by sorry

end CategoryTheory.CondensedDerivedRestriction
