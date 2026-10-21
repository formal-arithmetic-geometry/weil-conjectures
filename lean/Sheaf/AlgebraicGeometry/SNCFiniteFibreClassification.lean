module

public import Sheaf.AlgebraicGeometry.SNCFiniteFibreData
public import Mathlib.Algebra.Category.ModuleCat.AB

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.IsRegularSystemOfParameters
import Sheaf.FieldTheory.TameRootsProduct
import Sheaf.AlgebraicGeometry.ConstantSheafSetsRepresentable
import Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech
import Sheaf.AlgebraicGeometry.SNCTameRootEtaleExtension
import Sheaf.AlgebraicGeometry.SNCUniversalResidualCharts
import WeilConjectures.AlgebraicGeometry.NilpotentBaseChangeIdempotents
import WeilConjectures.AlgebraicGeometry.DescendFinite
import WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent
import WeilConjectures.RingTheory.IntegralOverHenselianPair
import Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheaves
import Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence
import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale

/-!
# Finite-fibre classification of tame sheaves

Source: ILO Expose IX Proposition 2.1(i)-(iii), printed pages 133-134;
Stacks 09ZS; Bhatt--Scholze Corollary 5.1.5 and Lemma 7.4.3.
(blueprint: lem-sfb-snc-tame-finite-fibre-classification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped FintypeCatDiscrete
namespace AlgebraicGeometry.ProEtale

/-- Finite tame classification, normalized at the chosen geometric point. Chart data are
those of the existing residual-chart construction; for the node take the identity affine
chart with all the labelled boundary components. Thus regularity, Noetherianness,
nonempty connected residual stratum, pair henselization, the pointed universal residual
cover, compatible primitive roots, unit root differences and the actual root tower are
supplied by Q, not replaced by arbitrary maps.
Source: ILO IX Proposition 2.1(i)-(iii), printed 133-134; Stacks 09ZS;
Bhatt--Scholze Corollary 5.1.5 and Lemma 7.4.3
(blueprint: lem-sfb-snc-tame-finite-fibre-classification).

Proof:
1. Apply the universal residual chart lemma to the identity affine chart. The finite and
full punctured root levels are connected and the full tower covers the residual puncture.
2. The finite frame torsor of F0 has local sections. The locally-classical comparison gives
etale finite frames, including the empty fibre. The finite-cover equivalence represents F0.
3. The finite tame root-extension lemma extends the represented cover to one finite root
level, with no restriction on its total degree, then base change from B to H.
4. Descend a finite etale cover of the residual limit to a pointed Galois stage. Split its
composite over S using the universal-cover lemma and select the summand at the chosen point.
5. The monic root algebra is finite free. Modulo J its root ideal is nilpotent of exponent
r(n-1)+1, and the finite algebra remains henselian over the lifted ideal.
6. Lift the residual splitting across the nilpotent thickening and then across the
henselian pair using finite etale lifting, applied to the identity proper scheme.
7. Pull the splitting to the full connected tower and normalize on the chosen stalk. Maps
of finite constant sheaves are determined by that fibre, giving uniqueness and naturality.
8. CRT and the chosen roots identify the root torsor with X[G]. The comparison is (x,gx),
and its root coordinates are the stated prime-power residues. Compatible finite levels
identify the whole profinite parameter scheme.
9. The normalized splitting produces the permutation action by deck descent. The group
is abelian, so the descent cocycle is a left action; it factors through a finite root level
and is continuous. Equality of universal sections gives the whole descent arrow.
10. Descent for sheaves identifies all maps with equivariant fibre maps, proving full
faithfulness, including empty fibres.
11. Uniqueness of the normalized splitting preserves terminal objects and finite products.
Apply this to addition, zero, negation and every scalar map to obtain the linear fibre.
Tensor scalar reduction is normalized on b tensor q, as in the companion assertion.
12. A pointed chart/residual refinement preserving the compatible roots carries the
normalized splitting to one with the same point normalization. Connectedness makes it the
unique such splitting. With no parameters, the inertia group is trivial and the tower is
the residual puncture, so every object is a finite constant sheaf. -/
theorem nonempty_sncFiniteFibreClassification (p : ℕ) [Fact p.Prime]
    {Y : Scheme.{u}} {a : ℕ} {C : Fin a → Y.IdealSheafData} {I : Finset (Fin a)}
    (Q : SNCResidualChart p C I) (k : Type u) [Field k] [CharP k p]
    [(Spec Q.B).Over (Spec (.of k))]
    [LocallyOfFiniteType ((Spec Q.B) ↘ Spec (.of k))]
    [QuasiCompact ((Spec Q.B) ↘ Spec (.of k))]
    [IsSeparated ((Spec Q.B) ↘ Spec (.of k))]
    (_hD : IsStrictNormalCrossingsBoundary Q.chartBoundary)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ Q.puncturedTower) :
    ∃ d : SNCFiniteFibreClassification Q z,
      (letI := d.products; ∀ (R : Type v) [Ring R] [Finite R]
        (M : InternalModule R Q.FiniteTame),
        Nonempty (SNCFiniteLinearFibre d R M)) ∧
      (Fintype.card I = 0 →
        (∀ g : SNCInertia.{u} p (Fintype.card I), g = 1) ∧
        ∀ F : Q.FiniteTame, Nonempty
          (F.obj ≅ (constantSheaf (Scheme.ProEt.topology Q.puncturedResidual)
            (Type (u + 1))).obj (ULift.{u + 1, u} (d.fibre.obj F).obj.V))) := by
  sorry

/-- Pointed chart and residual-cover refinements carry the normalized splitting to the
normalized splitting. The morphism theta is pinned by both pullback projections; alpha
is an equivariant bijection of the actual finite fibres. The equality compares universal
sections on the entire refined tower with finite labels.
Source: ILO IX 2.1, Stacks 09ZS and Bhatt--Scholze 7.4.3
(blueprint: lem-sfb-snc-tame-finite-fibre-classification).

Proof: Step 12 of the node. The supplied root maps preserve the coefficients and all
root generators and commute with the covering projections. They preserve the root
rotations because the primitive roots agree. Pull back the splitting along these maps
and the given inverse-image identification. Its germ is the same at the compatible
geometric points. Connectedness and Step 7 give the unique normalized splitting, and
Step 9 identifies its action. The displayed equality follows on the universal finite
label object; hence it holds after every site base change and is natural in sheaf maps. -/
theorem sncFiniteFibreClassification_refinement {p : ℕ} {Y : Scheme.{u}} {a : ℕ}
    {C : Fin a → Y.IdealSheafData} {I : Finset (Fin a)}
    (Q Q' : SNCResidualChart p C I) (e : SNCResidualRefinement Q Q')
    (_hζ : ∀ n, e.lift.hom (Q.zeta n) = Q'.zeta n)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (z : Spec (.of Ω) ⟶ Q.puncturedTower)
    (z' : Spec (.of Ω) ⟶ Q'.puncturedTower)
    (_hz : z' ≫ Spec.map (CommRingCat.ofHom e.puncturedFullMap) = z)
    (d : SNCFiniteFibreClassification Q z) (d' : SNCFiniteFibreClassification Q' z')
    (F : Q.FiniteTame) (F' : Q'.FiniteTame)
    (g : F.obj ⟶ (Scheme.proEtaleSheafDirectImage
      (Spec.map (CommRingCat.ofHom e.puncturedBaseMap)) (Type (u + 1))).obj F'.obj)
    [_hg : IsIso ((Scheme.proEtaleSheafAdjunction
      (Spec.map (CommRingCat.ofHom e.puncturedBaseMap)) (Type (u + 1))).homEquiv _ _ |>.symm g)] :
    ∃ α : d.fibre.obj F ≅ d'.fibre.obj F',
      ∃ θ : Q'.towerProduct.obj (FintypeCat.toProfinite.obj (d.fibre.obj F).obj.V) ⟶
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤
          (Spec.map (CommRingCat.ofHom e.puncturedBaseMap))).obj
            (Q.towerProduct.obj (FintypeCat.toProfinite.obj (d.fibre.obj F).obj.V)),
        θ.left ≫ pullback.fst _ _ =
          Scheme.UniversalCover.profiniteProductMap
            (Spec.map (CommRingCat.ofHom e.puncturedFullMap)) (𝟙 _) ∧
        θ.left ≫ pullback.snd _ _ =
          (Q'.towerProduct.obj (FintypeCat.toProfinite.obj (d.fibre.obj F).obj.V)).hom ∧
        F'.obj.obj.map θ.op (g.hom.app _ (d.splitting F)) =
          F'.obj.obj.map (Q'.towerLabelMap
            (FintypeCat.toProfinite.map ((forget₂ _ FintypeCat).map α.hom))).op
              (d'.splitting F') := by
  sorry

/-- Scalar reduction is the sheafification of the coefficient left adjoint, and its
stalk comparison is normalized by the actual sheafification unit at every pointed
neighborhood. Giving the scalar adjunction determines the scalar extension uniquely,
including for noncommutative finite rings. The comparison intertwines the stalk
actions pinned by the normalized finite labels. No arbitrary comparison map is assumed.
Source: ILO IX 2.1 and Bhatt--Scholze 5.1.5, finite coefficient consequence
(blueprint: lem-sfb-snc-tame-finite-fibre-classification).

Proof: Step 11 of the node. Scalar extension is a left adjoint and commutes with the
filtered colimit defining the geometric stalk. Sheafification preserves that stalk.
Their composite gives the displayed isomorphism with the specified coprojection
formula. The normalization agrees with the finite-set splitting by Step 7, so the
comparison is root-equivariant by Step 9 and natural in finite sheaf maps by Step 10.
For ordinary commutative scalar extension its unit formula is b tensor q. -/
theorem sncFiniteFibreClassification_scalarReduction
    {p : ℕ} [Fact p.Prime] {Y : Scheme.{u}} {a : ℕ}
    {C : Fin a → Y.IdealSheafData} {I : Finset (Fin a)} (Q : SNCResidualChart p C I)
    (k : Type u) [Field k] [CharP k p]
    [(Spec Q.B).Over (Spec (.of k))]
    [LocallyOfFiniteType ((Spec Q.B) ↘ Spec (.of k))]
    [QuasiCompact ((Spec Q.B) ↘ Spec (.of k))]
    [IsSeparated ((Spec Q.B) ↘ Spec (.of k))]
    (_hD : IsStrictNormalCrossingsBoundary Q.chartBoundary)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ Q.puncturedTower)
    (R S : Type (u + 1)) [Ring R] [Ring S] [Finite R] [Finite S] (φ : R →+* S)
    (E : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} S)
    (_adj : E ⊣ ModuleCat.restrictScalars φ)
    (M : Sheaf (Scheme.ProEt.topology Q.puncturedResidual) (ModuleCat.{u + 1} R))
    (_hM : Q.finiteTame ((sheafCompose (Scheme.ProEt.topology Q.puncturedResidual)
      (forget (ModuleCat.{u + 1} R))).obj M)) :
    let N := (presheafToSheaf (Scheme.ProEt.topology Q.puncturedResidual)
      (ModuleCat.{u + 1} S)).obj (M.obj ⋙ E)
    ∃ hN : Q.finiteTame ((sheafCompose (Scheme.ProEt.topology Q.puncturedResidual)
      (forget (ModuleCat.{u + 1} S))).obj N),
    ∃ c : E.obj (Scheme.proEtaleGeometricStalk (z ≫ Q.towerMap) M) ≅
        Scheme.proEtaleGeometricStalk (z ≫ Q.towerMap) N,
      (∀ V : Scheme.ProEtaleGeometricNeighbourhood (z ≫ Q.towerMap),
        E.map (colimit.ι (Scheme.proEtaleGeometricStalkDiagram (z ≫ Q.towerMap) M)
          (op V)) ≫ c.hom =
          (toSheafify (Scheme.ProEt.topology Q.puncturedResidual) (M.obj ⋙ E)).app
            (op V.right) ≫
          colimit.ι (Scheme.proEtaleGeometricStalkDiagram (z ≫ Q.towerMap) N) (op V)) ∧
      ∀ d : SNCFiniteFibreClassification Q z,
        ∃ (A : SNCFiniteModuleStalkAction d M _hM)
          (B : SNCFiniteModuleStalkAction d N hN),
          ∀ g : SNCInertia.{u} p (Fintype.card I),
            E.map (A.action g) ≫ c.hom = c.hom ≫ B.action g := by
  sorry

end AlgebraicGeometry.ProEtale
