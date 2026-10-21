/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.ContinuousRightTorsor
public import Sheaf.Paper.FieldSeparableCechCoordinates
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction

/-! # Complete-group torsors and continuous monodromy

Source: Bhatt--Scholze, Proposition 7.1.5, Theorem 7.2.5, Lemmas 7.3.9,
7.4.1, 7.4.7 and 7.4.10 (blueprint: lem-sfb-complete-group-torsor-monodromy).
The equivalence is expressed by its fully faithful arrow bijections and essential
surjectivity, with fibre-point coordinates. Thus no arbitrary skeleton is selected.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite
namespace AlgebraicGeometry.ProEtale
open ContinuousRightTorsor

/-- Pullback along a pointed scheme map, in its adjoint description. The supplied
fibre-functor path includes the comparison of geometric points, so different algebraically
closed fields and arbitrary paths are allowed. The induced map of fundamental groups is
specified on every finite fibre rather than replaced by an unconstrained homomorphism.
Source: Stacks 0BND (3); Bhatt--Scholze, Section 7.4
(blueprint: lem-sfb-complete-group-torsor-monodromy). -/
structure PointedTorsorMap (A B : NormalTorsorBase.{u}) where
  f : A.X ⟶ B.X
  fieldMap : B.Ω →+* A.Ω
  point_eq : A.x ≫ f = Spec.map (CommRingCat.ofHom fieldMap) ≫ B.x
  path : Scheme.FiniteEtale.pullback f ⋙ Scheme.FiniteEtale.fiber A.x ≅
    Scheme.FiniteEtale.fiber B.x
  path_normalization : ∀ (V : B.X.FiniteEtale)
    (z : (Scheme.FiniteEtale.fiber B.x).obj V),
    ((path.inv.app V z).left ≫ pullback.fst V.obj.hom f) =
      Spec.map (CommRingCat.ofHom fieldMap) ≫ z.left
  piMap : A.pi →ₜ* B.pi
  piMap_normalization : ∀ (g : A.pi) (V : B.X.FiniteEtale)
    (z : (Scheme.FiniteEtale.fiber A.x).obj ((Scheme.FiniteEtale.pullback f).obj V)),
    piMap g • path.hom.app V z = path.hom.app V
      (@SMul.smul A.pi ((Scheme.FiniteEtale.fiber A.x).obj
        ((Scheme.FiniteEtale.pullback f).obj V)) (A.actions _).toSMul g z)

/-- The canonical map on fibres of a pointed pullback, including the actual
restriction across the embedding of algebraically closed fields.
Source: Bhatt--Scholze, Section 7.4; Stacks 0BND (3)
(blueprint: lem-sfb-complete-group-torsor-monodromy). -/
def PointedTorsorMap.fibreMap {A B : NormalTorsorBase.{u}}
    (f : PointedTorsorMap A B) {G : TorsorCoefficientGroup.{u}}
    {P : ContinuousRightTorsor B.X G} {Q : ContinuousRightTorsor A.X G}
    (a : Along f.f (ContinuousMonoidHom.id _) P Q) : P.fibre B.x → Q.fibre A.x :=
  fun p ↦ a.fibreMap A.x
    (Eq.mp (congrArg P.fibre f.point_eq.symm)
      (P.fibreFieldRestriction B.x f.fieldMap p))

/-- Field normalization in actual sections on the separable-closure Cech nerve.
The finite-fibre equation specifies the usual identification with the absolute Galois
group, including its side convention. Pullback of sections to the algebraic closure
is the recorded `sectionToFibre`, not an arbitrary bijection.
Source: Bhatt--Scholze, proof of Lemma 7.4.7; the separable Cech coordinates
(blueprint: lem-sfb-complete-group-torsor-monodromy). -/
def IsFieldTorsorNormalization
    (ρ : ∀ (B : NormalTorsorBase.{u}) (G : TorsorCoefficientGroup.{u})
      (P : ContinuousRightTorsor B.X G), P.fibre B.x → (B.pi →ₜ* G.carrier)) : Prop :=
  ∀ (B : NormalTorsorBase.{u}) (G : TorsorCoefficientGroup.{u})
    (k ks : Type u) [Field k] [Field ks] [Algebra k ks] [IsSepClosure k ks]
    (e : B.X ≅ Spec (.of k)) (i : ks →+* B.Ω)
    (_hx : B.x ≫ e.hom =
      Spec.map (CommRingCat.ofHom (i.comp (algebraMap k ks))))
    (j : (ks ≃ₐ[k] ks) ≃ₜ* B.pi)
    (_hj : ∀ (V : B.X.FiniteEtale) (z : Spec (.of ks) ⟶ V.obj.left)
      (_hz : z ≫ V.obj.hom = Spec.map (CommRingCat.ofHom (algebraMap k ks)) ≫ e.inv)
      (σ : ks ≃ₐ[k] ks),
      ∀ a : (Scheme.FiniteEtale.fiber B.x).obj V,
      a.left = Spec.map (CommRingCat.ofHom i) ≫ z →
      (j σ • a).left = Spec.map (CommRingCat.ofHom i) ≫
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ z)
    (P : ContinuousRightTorsor B.X G),
    ∃ (V : B.X.ProEt) (v : V.left ≅ Spec (.of ks))
      (_hv : V.hom = v.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k ks)) ≫ e.inv)
      (t : Spec (.of B.Ω) ⟶ V.left) (ht : t ≫ V.hom = B.x),
      t ≫ v.hom = Spec.map (CommRingCat.ofHom i) ∧
      Function.Bijective (P.sectionToFibre B.x V t ht) ∧
      ∃ d : ∀ q : ℕ, (FieldSeparableCech.object k ks q).left ≅
        ((profiniteToProEtOf (Spec (.of ks))).obj (FieldSeparableCech.power k ks q)).left,
        FieldSeparableCech.AreCoordinates k ks d ∧
        ∀ (a : P.sheaf.obj.obj (op V))
          (W : B.X.ProEt) (w : W.left ≅ (FieldSeparableCech.object k ks 1).left)
          (r₁ r₂ : W ⟶ V)
          (_hr₁ : r₁.left ≫ v.hom = w.hom ≫
            (WidePullback.π (fun _ : Fin 2 ↦ (FieldSeparableCech.closureArrow k ks).hom) 0).left)
          (_hr₂ : r₂.left ≫ v.hom = w.hom ≫
            (WidePullback.π (fun _ : Fin 2 ↦ (FieldSeparableCech.closureArrow k ks).hom) 1).left),
          ∃ c : C(W.left, G.carrier),
            P.sheaf.obj.map r₂.op a = P.act (op W) (P.sheaf.obj.map r₁.op a) c ∧
            ∀ σ : ks ≃ₐ[k] ks,
              ∀ z : W.left,
              w.hom.base z = ((d 1).inv.base
                ((FieldSeparableCech.testPoint k ks 1 (fun _ ↦ σ)).base
                  (default : Spec (.of ks)))) →
              c z = ρ B G P (P.sectionToFibre B.x V t ht a) (j σ)

/-- Classification of continuous-function torsors by continuous homomorphisms.
The arrow equivalence sends b to the unique equivariant map taking p to q b.
It respects identity and composition by this fibre formula; point-preserving maps
are precisely the b=1 arrows, giving pointed classification by actual homomorphisms.

Source: Bhatt--Scholze, Proposition 7.1.5, Theorem 7.2.5, Lemmas 7.3.9,
7.4.1, 7.4.7 and 7.4.10 (blueprint: lem-sfb-complete-group-torsor-monodromy).

Proof (the node's sixteen steps):
1. Open subgroups are clopen and separate points. Thus G is totally disconnected.
   The continuous-function realization supplies F_G and all coefficient pullbacks;
   completeGroup_forgetful_automorphisms reconstructs G from its small orbit category.
2. Pull a trivializing cover to Spec Ω and refine to affine ind-etale objects Ω[S].
   A nonempty profinite S has a point; evaluation gives a section. Its fibre is a G-torsor.
3. The pointed finite-etale inverse limit T is connected and covers X; its Cech
   components are powers of pi. Local Noetherianness gives quasi-separatedness.
4. Represent each locally constant pro-etale set sheaf by a geometric cover. Normality
   decomposes it into clopen finite-etale connected components. Yoneda identifies maps.
5. Take the union of their finite fibres, with the finite fibre-functor action of pi.
   Each component splits on T, naturally; coproductCopiesMorphismsClopen identifies
   the resulting sheaf with the continuous-function sheaf of this discrete fibre.
6. For each discrete continuous G-set S glue the sheaves F_S with transitions b_ij.
   Their symbols satisfy [a g,s]=[a,g s]. The fibre point p identifies their fibres with S.
7. Their monodromy is a continuous natural automorphism of the orbit forgetful functor:
   every coordinate stabilizer is open. Reconstruction yields the continuous rho_P.
8. Recover P as the sheaf of natural isomorphisms F_S -> P_S on the small orbit category.
   Locally these are continuous maps into Aut(omega_G)=G: each coordinate and inverse
   coordinate is locally constant. Hence this recovery is an actual sheaf isomorphism.
9. The natural T-trivializations give a section a lifting p. It is unique: two such
   sections differ by a continuous T -> G, constant by connectedness of T.
10. Write a_2=a_1 c. The Cech coordinates give c(gh)=c(g)c(h), and the associated
    discrete sheaves identify c with rho_P, with no inversion.
11. Conversely glue regular torsors on T by left multiplication by rho(g).
    setSheafCoverDescent gives P_rho and its point; the two constructions are inverse.
12. An equivariant map has a -> a' b and descends exactly when rho_Q(g)b=b rho_P(g).
    Changing p to p b changes rho to b inverse rho b. This proves the arrow bijection.
13. Pointed pullback of associated discrete sheaves acts through the fundamental-group
    map on every finite summand. Reconstruction gives rho composed with f_*.
14. Change of group glues with u(b_ij), the universal contracted product with symbols
    [a g,h]=[a,u(g)h]. Its fibre point is [p,1] and its monodromy is u composed with rho.
15. Over a separable closure any torsor has a section by the same profinite-point
    argument. Restriction to Ω is the identity in G-coordinates, hence bijective.
16. FieldSeparableCech.coordinates identifies the overlap label with the Galois
    automorphism. The equation pr2*a=pr1*a c therefore gives exactly rho, normalized
    on every finite fibre and with c(gh)=c(g)c(h). All indexing diagrams are small. -/
theorem complete_group_torsor_monodromy :
    ∃ ρ : ∀ (B : NormalTorsorBase.{u}) (G : TorsorCoefficientGroup.{u})
      (P : ContinuousRightTorsor B.X G), P.fibre B.x → (B.pi →ₜ* G.carrier),
      (∀ (B : NormalTorsorBase.{u}) (G : TorsorCoefficientGroup.{u})
        (P : ContinuousRightTorsor B.X G),
        Nonempty (P.fibre B.x) ∧
        (∀ p, P.fibreAct B.x p 1 = p) ∧
        (∀ p g h, P.fibreAct B.x (P.fibreAct B.x p g) h = P.fibreAct B.x p (g * h)) ∧
        (∀ p, Function.Bijective (P.fibreAct B.x p))) ∧
      (∀ (B : NormalTorsorBase.{u}) (G : TorsorCoefficientGroup.{u})
        (P Q : ContinuousRightTorsor B.X G) (p : P.fibre B.x) (q : Q.fibre B.x),
        ∃ E : {b : G.carrier // ∀ γ : B.pi,
          ρ B G Q q γ * b = b * ρ B G P p γ} ≃ P.Equiv Q,
          ∀ b, (E b).fibreMap B.x p = Q.fibreAct B.x q b.val) ∧
      (∀ (B : NormalTorsorBase.{u}) (G : TorsorCoefficientGroup.{u})
        (r : B.pi →ₜ* G.carrier),
        ∃ (P : ContinuousRightTorsor B.X G) (p : P.fibre B.x), ρ B G P p = r) ∧
      (∀ (B : NormalTorsorBase.{u}) (G : TorsorCoefficientGroup.{u})
        (P : ContinuousRightTorsor B.X G) (p : P.fibre B.x) (b : G.carrier) (γ : B.pi),
        ρ B G P (P.fibreAct B.x p b) γ = b⁻¹ * ρ B G P p γ * b) ∧
      (∀ (A B : NormalTorsorBase.{u}) (f : PointedTorsorMap A B)
        (G : TorsorCoefficientGroup.{u}) (P : ContinuousRightTorsor B.X G),
        ∃ (Q : ContinuousRightTorsor A.X G) (a : Along f.f (ContinuousMonoidHom.id _) P Q),
          IsIso (((Scheme.proEtaleSheafAdjunction f.f (Type (u + 1))).homEquiv _ _).symm
            a.hom) ∧
          ∀ p, ρ A G Q (f.fibreMap a p) = (ρ B G P p).comp f.piMap) ∧
      (∀ (B : NormalTorsorBase.{u}) (G H : TorsorCoefficientGroup.{u})
        (v : G.carrier →ₜ* H.carrier) (P : ContinuousRightTorsor B.X G),
        ∃ (Q : ContinuousRightTorsor B.X H) (E : ExtensionPresentation v P Q),
          ∀ p, ρ B H Q (E.fibreMap B.x p) = v.comp (ρ B G P p)) ∧
      IsFieldTorsorNormalization ρ := by
  sorry

end AlgebraicGeometry.ProEtale
