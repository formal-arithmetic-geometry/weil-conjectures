module

public import Sheaf.AlgebraicGeometry.SpaceCoherentAdicSystem
public import Mathlib.RingTheory.AdicCompletion.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus
import Mathlib.RingTheory.Finiteness.Nakayama

/-! # Algebraization by exceptional-ideal torsion dévissage

Source: Stacks Project, spaces-more-morphisms.tex, Tag 08BC (lemma-existence-tricky),
Situation 08B7 and the bounded ordinary component convention of Tag 08BA
(blueprint: lem-sfb-space-adic-torsion-devissage).

As in the first paragraph of the source proof, coherent modules and adic systems on
X_e are identified with those on X annihilated by K^e. The equivalence hypothesis is
spelled out as bijectivity on Hom sets and essential surjectivity for these full
subcategories. Every map is induced by the recorded completion functor.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Algebraization from a bounded-torsion approximate coherent model and completion
on every exceptional thickening. The equality on affine charts specifies J = I O_X.
The two clauses of hthickenings are precisely full faithfulness and essential
surjectivity of completion on modules annihilated by K^e, using the closed-subspace
dictionary in the first paragraph of the source proof. Proper support always retains
a closed proper carrier, and the error bound concerns ordinary component maps.
Source: Stacks, Tag 08BC (lemma-existence-tricky), Situation 08B7, Tag 08BA
(blueprint: lem-sfb-space-adic-torsion-devissage).

Proof:
1. The finite-type separated inheritance lemma lem-sfb-space-noetherian-coherent-acc
makes X Noetherian. For each e form Q_e with terms M_n/K^e M_n using the chart calculus
lem-sfb-space-qcoh-affine-chart-calculus. Quotient interchange makes this J-adic.
The closed dictionary lem-sfb-space-closed-adic-dictionary and the assumed equivalence
algebraize it to G_e, with proper support by lem-sfb-space-proper-support-closed-operations
and lem-sfb-space-module-proper-carrier-support.
2. Fullness lifts the maps Q_(e+1) to Q_e, and faithfulness imposes their relations.
Quotient interchange identifies G_(e+1)/K^e with G_e. Thus N = (G_e) is K-adic and its
J-quotients identify with the K-quotients of M, naturally in both indices.
3. Reduce a modulo K^e and lift by fullness to d_e : G_e to H/K^e H. Faithfulness makes
them compatible. The comparison square is the canonical quotient-interchange square.
Apply lem-sfb-space-second-adic-torsion-transfer to bound both ordinary errors by K^(4t).
4. Apply lem-sfb-space-easy-torsion-algebraization to N and d, obtaining F, b : F to H
and the K-completion isomorphism. If K^s kills ker b and coker b, products of two
sections of K^s give lift-independent maps H to F whose composites with b are scalar
multiplication. After quotient by J^n they kill both errors, so the bound is K^(2s).
5. Apply uniqueness in the same easy algebraization lemma at each n to M_n and F/J^n F,
using the double-quotient identifications. It gives F/J^n F isomorphic to M_n.
Uniqueness after reduction of n+1 to n proves transition compatibility, hence an
isomorphism of the complete diagrams.
6. Outside V(K), ker b vanishes. On V(K), finite-module Nakayama
lem-weil-pbc-nakayama-one-plus-ideal-annihilator identifies Supp(F) intersect V(K)
with Supp(F/KF) = Supp(G_1). Since im b has support in Supp(H), the support of F lies
in Supp(G_1) union Supp(H). The closed-operations and carrier lemmas of step 1 show
this support has a proper closed carrier. No flatness or exactness of tensor is used. -/
theorem coherentAdic_algebraization_of_bounded_exceptional_torsion
    {S : Scheme.{u}} {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A] (aS : Spec (.of A) ⟶ S)
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace (Over.mk aS))
    (hsep : MapIsSeparated f) (hft : MapIsFiniteType f)
    (J K : QuasiCoherentIdeal X)
    (hJ : ∀ T : X.EtaleSite, IsAffine (X.etaleForget.obj T) →
      idealSectionImage J.val.arrow T =
        Ideal.map (((Scheme.ΓSpecIso (.of A)).inv ≫
          (yoneda.preimage (T.obj.hom ≫ f.hom.hom)).left.appTop).hom) I)
    (hthickenings : ∀ e : ℕ, 1 ≤ e →
      (∀ F G : CoherentProperSupportModules f,
        AdicPowerKills K e F.obj → AdicPowerKills K e G.obj →
          Function.Bijective (fun v : F ⟶ G ↦
            (coherentAdicCompletionDiagram J).map v.hom)) ∧
      (∀ N : ℕᵒᵖ ⥤ X.Modules, IsCoherentAdicSystem J N →
        CoherentAdicHasProperSupportOver f N →
        (∀ n : ℕ, AdicPowerKills K e (N.obj (op n))) →
          ∃ F : CoherentProperSupportModules f, AdicPowerKills K e F.obj ∧
            Nonempty ((coherentAdicCompletionDiagram J).obj F.obj ≅ N)))
    (M : ℕᵒᵖ ⥤ X.Modules) (hM : IsCoherentAdicSystem J M)
    (hMproper : CoherentAdicHasProperSupportOver f M)
    (H : CoherentProperSupportModules f)
    (a : M ⟶ (coherentAdicCompletionDiagram J).obj H.obj)
    (ha : CoherentAdicKernelCokernelKilled K a) :
    ∃ F : CoherentProperSupportModules f,
      Nonempty ((coherentAdicCompletionDiagram J).obj F.obj ≅ M) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
