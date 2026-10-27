/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Sheaf.Paper.ProductExchangeCoordinateDefinitions
public import Sheaf.Paper.ProEtaleCompositionTowerNormalization
import Sheaf.Paper.ProductOpenAdjunctionNormalization
import Sheaf.Paper.ProductHorizontalExchangeFactorization
import Sheaf.Paper.ProductCompositionCoordinateComparison
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Product exchange and the open counit square

Source: latest blueprint, sec-six-functors/sk-thm-sf-kunneth-relative,
lem-sf-kunneth-coherence.proof.md, symmetry paragraph, reduction to proper maps
(blueprint: lem-pur-product-exchange-counit-coordinates).

The coordinate names below denote the canonical products, maps and composites in the
statement. In particular rho is derived from sectionwise restriction, independently of
exchange; Gamma is the existing proper/open mate, and alpha is the existing origin
composition transported to the supplied compactifications.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

namespace ProductExchangeCoordinates

private theorem counits_from_adjunct
    {C D : Type*} [Category C] [Category D]
    {J : C ⥤ D} {P : D ⥤ C} (adj : J ⊣ P)
    {A : C} {B Q : D} (G : J.obj A ⟶ B) (c : B ⟶ Q)
    (a : P.obj Q ≅ A) (l : P.obj B ≅ A)
    (hG : adj.homEquiv _ _ G = l.inv)
    (hc : P.map c ≫ a.hom = l.hom) :
    (adj.unit.app A ≫ P.map (G ≫ c)) ≫ a.hom = 𝟙 A ∧
      J.map a.hom ≫ G ≫ c = adj.counit.app Q := by
  have ht : adj.homEquiv _ _ (G ≫ c) ≫ a.hom = 𝟙 A := by
    rw [adj.homEquiv_naturality_right, Category.assoc, hG, hc, l.inv_hom_id]
  constructor
  · exact ht
  · apply (adj.homEquiv _ _).injective
    apply (cancel_mono a.hom).mp
    rw [adj.homEquiv_naturality_left, Category.assoc, ht]
    simp only [Category.comp_id, Adjunction.homEquiv_unit,
      adj.right_triangle_components, Category.id_comp]

private theorem square_from_factorization
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {J : C ⥤ D} {P : D ⥤ C} (adj : J ⊣ P)
    (V : E ⥤ C) (T : F ⥤ D) (I : E ⥤ F)
    (G : V ⋙ J ⟶ I ⋙ T)
    {L : D} {H : F} {N K : E} (b : N ≅ K)
    (a : L ⟶ T.obj H) (r : P.obj (T.obj H) ⟶ V.obj N)
    (B : P.obj L ⟶ V.obj K) (e : I.obj N ⟶ H)
    (hB : B = P.map a ≫ r ≫ V.map b.hom)
    (hc : J.map r ≫ G.app N ≫ T.map e = adj.counit.app (T.obj H)) :
    (J.map B ≫ G.app K) ≫ T.map (I.map b.inv ≫ e) = adj.counit.app L ≫ a := by
  have hn := G.naturality b.inv
  dsimp only [Functor.comp_map] at hn
  rw [T.map_comp, Category.assoc, ← Category.assoc (G.app K), ← hn]
  have hcancel : B ≫ V.map b.inv = P.map a ≫ r := by
    rw [hB]
    simp only [Category.assoc]
    rw [← V.map_comp, b.hom_inv_id, V.map_id, Category.comp_id]
  simp only [Category.assoc]
  rw [← J.map_comp_assoc, hcancel, J.map_comp, Category.assoc, hc]
  exact adj.counit.naturality a

private theorem counits_of_normalization
    {B X Z : Scheme.{u}} {f : X ⟶ B} {g : Z ⟶ B}
    (cf : Compactification f) (cg : Compactification g) [QuasiCompact g]
    (A : Type u) [CommRing A] [Finite A]
    (Q : ProperOpenDerived (ULift.{u + 1} A) (pullback cf.g cg.g)) :
    CounitIdentities cf cg A Q := by
  obtain ⟨_, hG, he⟩ := productOpenAdjunctionNormalization cf cg A Q
  simpa only [CounitIdentities, Category.assoc, Iso.app_hom, Functor.id_obj] using
    counits_from_adjunct (properOpenAdj (ULift.{u + 1} A) cg.i)
    ((properOpenMate (ULift.{u + 1} A) (i cf cg) (pullback.snd cf.g g)
      (pullback.snd cf.g cg.g) cg.i (comm cf cg)).app
        ((ProperOpenPull (ULift.{u + 1} A) (i cf cg)).obj Q))
    ((ProperOpenPush (ULift.{u + 1} A) (pullback.snd cf.g cg.g)).map
      ((properOpenAdj (ULift.{u + 1} A) (i cf cg)).counit.app Q))
    ((rho A (pullback.snd cf.g g) (i cf cg) cg.i
      (pullback.snd cf.g cg.g) (square cf cg)).app Q)
    (lambda cf cg A ((ProperOpenPull (ULift.{u + 1} A) (i cf cg)).obj Q)) hG he

private theorem counit_square_of_factorization
    {B X Z : Scheme.{u}} {f : X ⟶ B} {g : Z ⟶ B}
    (cf : Compactification f) (cg : Compactification g) [QuasiCompact g]
    (A : Type u) [CommRing A] [Finite A]
    (M : ProperOpenDerived (ULift.{u + 1} A) X) :
    s cf cg A M ≫
        (ProperOpenPush (ULift.{u + 1} A) (pullback.snd cf.g cg.g)).map
          (chi cf cg A M) =
      (properOpenAdj (ULift.{u + 1} A) cg.i).counit.app (L0 cf cg A M) ≫
        A0 cf cg A M := by
  dsimp only [s, chi]
  exact square_from_factorization (properOpenAdj (ULift.{u + 1} A) cg.i)
    (ProperOpenPush (ULift.{u + 1} A) (pullback.snd cf.g g))
    (ProperOpenPush (ULift.{u + 1} A) (pullback.snd cf.g cg.g))
    (ProperOpenShriek (ULift.{u + 1} A) (i cf cg))
    (properOpenMate (ULift.{u + 1} A) (i cf cg) (pullback.snd cf.g g)
      (pullback.snd cf.g cg.g) cg.i (comm cf cg))
    (beta cf cg A M) (A0 cf cg A M)
    ((rho A (pullback.snd cf.g g) (i cf cg) cg.i
      (pullback.snd cf.g cg.g) (square cf cg)).hom.app (F cf cg A M))
    (B0 cf cg A M)
    ((properOpenAdj (ULift.{u + 1} A) (i cf cg)).counit.app (F cf cg A M))
    (productHorizontalExchangeFactorization cf cg A M)
    (counits_of_normalization cf cg A (F cf cg A M)).2

end ProductExchangeCoordinates

/-- Product geometry and the specified exchange, proper/open and open-counit coordinates.
All derived categories are the ordinary unbounded constant-module categories. M,N,Q
are bounded below and retain their given etale antecedents; no constructibility, tensor
Tor bound, proper base-change invertibility or projection-formula invertibility is added.
The other tensor objects in the node (J,D,K_D) name setup objects only: none occurs in
these conclusions. Their tensors are the existing signed derived tensors.
Source: latest blueprint, lem-sf-kunneth-coherence.proof.md, symmetry paragraph
(blueprint: lem-pur-product-exchange-counit-coordinates).

Proof, following the eight steps of the DAG node.
1. Use the universal property of the three fibre products. W is the base change of C
by k, and P is the base change of W by j. Thus ti=kv, ri j_q=jp, vj_q=q,
and cu=gq=h. Proper stability gives proper t,v; open base change gives open i,j_q,u.
The compactifications are exactly cf.baseChange g and compositeChoice cf cg.
2. Proper maps are finite type, and composition and base change preserve finite type.
Every displayed scheme is finite type over the field and hence Noetherian
(lem-weil-pbc-finite-type-over-noetherian). Opens in Noetherian schemes are qc;
use locally-Noetherian quasi-separatedness and qcqs permanence for the displayed maps.
Quasi-compact open immersions are finite type. The closed-diagonal description also
makes the product tower separated, as required by the tower-normalization theorem.
3. On a K-injective representative I, sectionwise open restriction identifies
k^*t_*I with v_*i^*I. Open inverse image preserves K-injectives, being right adjoint
to exact extension by zero. Its transpose is P_i(epsilon_t) after the pullback square;
thus rho is precisely the specified exchange of def-exchange-projection.
4. Apply lem-pur-relative-compact-support-pasting to the proper compactification
(id,a) and base maps b,k. Its finite-coefficient agreement clause applies to A_(E,n):
all maps are separated finite type over k and ell is invertible. It gives exchange
along bk as rho P_k(A0). The chosen-compactification exchange appends R_v(beta),
where lem-sf-open-tensor-normalization identifies beta with the unit-normalized map.
5. Specialize lem-sf-proper-open-tensor-compatibility to (i,v,t,k). The square is
Cartesian, so its clopen intermediate map is the identity. Its lambda is precisely
rho followed by R_v of inverse open unit. Therefore the actual Gamma is the open
adjunct of lambda inverse; this is an identity of specified maps, not a choice.
6. Naturality of rho at epsilon_i and the open triangle identity give
rho P_k R_t(epsilon_i)=lambda. The adjunct identity of step 5 gives the first
counit formula after inserting eta_k. The adjunct of R_t(epsilon_i) Gamma is rho
inverse. After k_!(rho), its adjunct is identity, proving the second counit formula.
7. Naturality of Gamma at beta inverse, step 4, and step 6 yield
R_t(chi)s=T_F k_!(rho P_k A0)=epsilon_(k,R_t F) k_!P_k A0.
Counit naturality makes this A0 epsilon_(k,L0), exactly the required square.
8. Apply lem-trf-proetale-composition-tower-normalization to the compatible tower
(P,Z,B;q,g;k,b;u,t;i,v;j_q). Its exchange and unit give the lambda of steps 3--5,
so its Gamma is the actual proper/open mate. Its candidate comparison is the
canonical origin composition used by alpha. The direct-image compositor is exactly
finiteDirectImageComposition, and the last factor is the open-extension compositor.
For any retained witness nu^*Q_e isomorphic to Q, naturality transports this equality
from Q_e and cancels its specified isomorphism. This gives every witnessed Q, with
no assertion of invertibility on arbitrary ambient objects. -/
theorem productExchangeCounitCoordinates
    (C : WeilConjectures.PurityFiniteSetting.{u})
    {B X Z : Scheme.{u}}
    [B.Over (Spec (.of C.field.k))] [X.Over (Spec (.of C.field.k))]
    [Z.Over (Spec (.of C.field.k))]
    [IsSeparated (B ↘ Spec (.of C.field.k))]
    [IsSeparated (X ↘ Spec (.of C.field.k))]
    [IsSeparated (Z ↘ Spec (.of C.field.k))]
    [LocallyOfFiniteType (B ↘ Spec (.of C.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of C.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of C.field.k))]
    [QuasiCompact (B ↘ Spec (.of C.field.k))]
    [QuasiCompact (X ↘ Spec (.of C.field.k))]
    [QuasiCompact (Z ↘ Spec (.of C.field.k))]
    (f : X ⟶ B) (g : Z ⟶ B)
    [f.IsOver (Spec (.of C.field.k))] [g.IsOver (Spec (.of C.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (M : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} C.Coefficient)))
    (_N : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} C.Coefficient)))
    (_wM : Scheme.FixedEtaleOriginWitness X C.Coefficient M)
    (_wN : Scheme.FixedEtaleOriginWitness Z C.Coefficient _N) :
    ProductExchangeCoordinates.Geometry cf cg C.field.k
      (B ↘ Spec (.of C.field.k)) (X ↘ Spec (.of C.field.k)) (Z ↘ Spec (.of C.field.k)) ∧
    ProductExchangeCoordinates.Equations cf cg C.Ring M.obj ∧
    ∀ (Q : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology (pullback f g)) (ModuleCat.{u + 1} C.Coefficient)))
      (wQ : Scheme.FixedEtaleOriginWitness (pullback f g) C.Coefficient Q),
      ProductExchangeCoordinates.alpha cf cg C.Ring Q.obj
        ⟨wQ.complex.obj, wQ.complex.property, ⟨wQ.iso⟩⟩ =
      ProductExchangeCoordinates.compositionRoute cf cg C.Ring Q.obj := by
  have noetherian_of_map {S T : Scheme.{u}} [IsNoetherian T]
      (a : S ⟶ T) [LocallyOfFiniteType a] [QuasiCompact a] : IsNoetherian S := by
    let := LocallyOfFiniteType.isLocallyNoetherian a
    let := QuasiCompact.compactSpace_of_compactSpace a
    exact {}
  let : IsNoetherianRing C.field.k := PrincipalIdealRing.isNoetherianRing
  let : IsNoetherianRing (CommRingCat.of C.field.k) :=
    inferInstanceAs (IsNoetherianRing C.field.k)
  let : IsLocallyNoetherian (Spec (.of C.field.k)) :=
    isLocallyNoetherian_Spec.mpr inferInstance
  let : IsNoetherian (Spec (.of C.field.k)) := {}
  let : IsNoetherian B := noetherian_of_map (B ↘ Spec (.of C.field.k))
  let : IsNoetherian X := noetherian_of_map (X ↘ Spec (.of C.field.k))
  let : IsNoetherian Z := noetherian_of_map (Z ↘ Spec (.of C.field.k))
  let : IsNoetherian cf.Z := noetherian_of_map cf.g
  let : IsNoetherian cg.Z := noetherian_of_map cg.g
  let : IsNoetherian (pullback f g) := noetherian_of_map (pullback.snd f g)
  let : IsNoetherian (pullback cf.g g) := noetherian_of_map (pullback.snd cf.g g)
  let : IsNoetherian (pullback cf.g cg.g) := noetherian_of_map (pullback.snd cf.g cg.g)
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [ProductExchangeCoordinates.Geometry]
    repeat' apply And.intro
    all_goals infer_instance
  · obtain ⟨hρ, hΓ, _⟩ :=
      ProductExchangeCoordinates.productOpenAdjunctionNormalization cf cg C.Ring
        (ProductExchangeCoordinates.F cf cg C.Ring M.obj)
    exact ⟨hρ,
      ProductExchangeCoordinates.productHorizontalExchangeFactorization cf cg C.Ring M.obj,
      ProductExchangeCoordinates.counit_square_of_factorization cf cg C.Ring M.obj,
      hΓ, ProductExchangeCoordinates.counits_of_normalization cf cg C.Ring
        (ProductExchangeCoordinates.F cf cg C.Ring M.obj)⟩
  · intro Q wQ
    exact ProductExchangeCoordinates.productCompositionCoordinateComparison cf cg C.Ring Q.obj
      ⟨wQ.complex.obj, wQ.complex.property, ⟨wQ.iso⟩⟩

end AlgebraicGeometry.ProEtale
