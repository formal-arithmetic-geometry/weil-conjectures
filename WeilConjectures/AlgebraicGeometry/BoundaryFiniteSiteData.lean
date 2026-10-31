/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundaryProEtaleQCompatibility
public import WeilConjectures.AlgebraicGeometry.BoundaryDualizingComposition
public import WeilConjectures.AlgebraicGeometry.BoundaryEtaleAdjunctionRestriction
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeProEtaleModule
public import WeilConjectures.AlgebraicGeometry.ComparisonTorInterval

/-! # Data for finite-stage realization of boundary evaluation

Source: blueprint `cor-weil-boundary-duality-discharge`, second proof paragraph
(blueprint: lem-weil-boundary-finite-site-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale.BoundaryFiniteSite

section Formal
universe v w x y
variable {CT : Type v} [Category.{w} CT] [MonoidalCategory CT]
  [BraidedCategory CT] [MonoidalClosed CT]
  {CZ : Type x} [Category.{y} CZ] [MonoidalCategory CZ]
  [BraidedCategory CZ] [MonoidalClosed CZ]

/-- The evaluation-defined alpha, with q and the dualizing identification explicit.
Source: boundary-duality discharge, tensor-Hom transpose
(blueprint: lem-weil-boundary-finite-site-realization). -/
def alpha (s G : CT ⥤ CZ) (W : CT) (V : CZ)
    (h : G.obj W ≅ V) (K : CT)
    (q : s.obj K ⊗ G.obj ((ihom K).obj W) ⟶ G.obj (K ⊗ (ihom K).obj W)) :
    G.obj ((ihom K).obj W) ⟶ (ihom (s.obj K)).obj V :=
  (ihom.adjunction (s.obj K)).homEquiv _ _
    (q ≫ G.map ((ihom.ev K).app W) ≫ h.hom)

/-- The evaluation-defined beta. The evaluation on D(L) tensor L includes symmetry.
Source: boundary-duality discharge, tensor-Hom transpose
(blueprint: lem-weil-boundary-finite-site-realization). -/
def beta (s G : CT ⥤ CZ) (W : CT) (V : CZ)
    (h : G.obj W ≅ V) (L : CT)
    (q : s.obj ((ihom L).obj W) ⊗ G.obj L ⟶ G.obj ((ihom L).obj W ⊗ L)) :
    s.obj ((ihom L).obj W) ⟶ (ihom (G.obj L)).obj V :=
  (ihom.adjunction (G.obj L)).homEquiv _ _
    ((β_ _ _).hom ≫ q ≫
      G.map ((β_ _ _).hom ≫ (ihom.ev L).app W) ≫ h.hom)

/-- The two boundary composites, using the canonical evaluation biduality map.
Source: boundary-duality discharge, double-dual compatibility
(blueprint: lem-weil-boundary-finite-site-realization). -/
def CompositeIdentity (s G : CT ⥤ CZ) (W : CT) (V : CZ) (K : CT)
    (a : G.obj ((ihom K).obj W) ⟶ (ihom (s.obj K)).obj V)
    (b : s.obj ((ihom ((ihom K).obj W)).obj W) ⟶
      (ihom (G.obj ((ihom K).obj W))).obj V) : Prop :=
  s.map (MonoidalClosed.toIhomIhom W K) ≫ b =
    MonoidalClosed.toIhomIhom V (s.obj K) ≫ (MonoidalClosed.pre a).app V

/-- Preservation and biduality on the etale finite-Tor domains, exactly the hypotheses
of site realization. Source: boundary-duality discharge, finite-stage setup
(blueprint: lem-weil-boundary-finite-site-realization). -/
def EtaleHypotheses (s G : CT ⥤ CZ) (W : CT) (V : CZ)
    (PT : ObjectProperty CT) (PZ : ObjectProperty CZ) : Prop :=
  (∀ K : CT, PT K → PZ (s.obj K)) ∧
  (∀ K : CT, PT K → PZ (G.obj K)) ∧
  (∀ K : CT, PT K → PT ((ihom K).obj W)) ∧
  (∀ K : CZ, PZ K → PZ ((ihom K).obj V)) ∧
  (∀ K : CT, PT K → IsIso (MonoidalClosed.toIhomIhom W K)) ∧
  (∀ K : CZ, PZ K → IsIso (MonoidalClosed.toIhomIhom V K))

/-- Alpha for a q family on the finite-Tor domain.
Source: boundary-duality discharge, alpha formula
(blueprint: lem-weil-boundary-finite-site-realization). -/
def alphaOf (s G : CT ⥤ CZ) (W : CT) (V : CZ) (h : G.obj W ≅ V)
    (P : ObjectProperty CT)
    (d : ∀ K : CT, P K → P ((ihom K).obj W))
    (q : ∀ M N : CT, P M → P N → (s.obj M ⊗ G.obj N ⟶ G.obj (M ⊗ N)))
    (K : CT) (hK : P K) :
    G.obj ((ihom K).obj W) ⟶ (ihom (s.obj K)).obj V :=
  alpha s G W V h K (q K ((ihom K).obj W) hK (d K hK))

/-- Beta for the same q family and the same canonical evaluation.
Source: boundary-duality discharge, beta formula
(blueprint: lem-weil-boundary-finite-site-realization). -/
def betaOf (s G : CT ⥤ CZ) (W : CT) (V : CZ) (h : G.obj W ≅ V)
    (P : ObjectProperty CT)
    (d : ∀ K : CT, P K → P ((ihom K).obj W))
    (q : ∀ M N : CT, P M → P N → (s.obj M ⊗ G.obj N ⟶ G.obj (M ⊗ N)))
    (K : CT) (hK : P K) :
    s.obj ((ihom K).obj W) ⟶ (ihom (G.obj K)).obj V :=
  beta s G W V h K (q ((ihom K).obj W) K (d K hK) hK)

end Formal

section Transport
universe v w x y v' w' x' y'
variable {CT : Type v} [Category.{w} CT] [MonoidalCategory CT]
  [BraidedCategory CT] [MonoidalClosed CT]
  {CZ : Type x} [Category.{y} CZ] [MonoidalCategory CZ]
  [BraidedCategory CZ] [MonoidalClosed CZ]
  {PT : Type v'} [Category.{w'} PT] [MonoidalCategory PT]
  [BraidedCategory PT] [MonoidalClosed PT]
  {PZ : Type x'} [Category.{y'} PZ] [MonoidalCategory PZ]
  [BraidedCategory PZ] [MonoidalClosed PZ]

/-- The explicit alpha/beta comparison squares and their consequences. Every argument
is specialized below to the actual site functors, dualizing objects and q transposes.
The existential isomorphisms have prescribed evaluation normalizations in that specialization.
Source: boundary-duality discharge, evaluation and double-dual comparison
(blueprint: lem-weil-boundary-finite-site-realization). -/
def EvaluationTransport (s G : CT ⥤ CZ) (sp Gp : PT ⥤ PZ)
    (W : CT) (V : CZ) (Wp : PT) (Vp : PZ)
    (he : G.obj W ≅ V) (hp : Gp.obj Wp ≅ Vp)
    (Pe : ObjectProperty CT) (Qe : ObjectProperty CZ) (Pp : ObjectProperty PT)
    (de : ∀ K : CT, Pe K → Pe ((ihom K).obj W))
    (dp : ∀ K : PT, Pp K → Pp ((ihom K).obj Wp))
    (qe : ∀ M N : CT, Pe M → Pe N → (s.obj M ⊗ G.obj N ⟶ G.obj (M ⊗ N)))
    (qp : ∀ M N : PT, Pp M → Pp N → (sp.obj M ⊗ Gp.obj N ⟶ Gp.obj (M ⊗ N)))
    (F : CT ⥤ PT) (FZ : CZ ⥤ PZ)
    (hf : ∀ K : CT, Pe K → Pp (F.obj K))
    (χT : ∀ K : CT, Pe K → (F.obj ((ihom K).obj W) ≅ (ihom (F.obj K)).obj Wp))
    (χZ : ∀ K : CZ, Qe K → (FZ.obj ((ihom K).obj V) ≅ (ihom (FZ.obj K)).obj Vp))
    (hs : ∀ K : CT, Pe K → Qe (s.obj K))
    (hg : ∀ K : CT, Pe K → Qe (G.obj K))
    (ψ : ∀ K : CT, Pe K → (FZ.obj (s.obj K) ≅ sp.obj (F.obj K)))
    (θ : ∀ K : CT, Pe K → (FZ.obj (G.obj K) ≅ Gp.obj (F.obj K))) : Prop :=
  (∀ (K : CT) (hK : Pe K),
    (θ _ (de K hK)).hom ≫ Gp.map (χT K hK).hom ≫
        alphaOf sp Gp Wp Vp hp Pp dp qp (F.obj K) (hf K hK) =
      FZ.map (alphaOf s G W V he Pe de qe K hK) ≫
        (χZ _ (hs K hK)).hom ≫ (MonoidalClosed.pre (ψ K hK).inv).app Vp) ∧
  (∀ (K : CT) (hK : Pe K),
    (ψ _ (de K hK)).hom ≫ sp.map (χT K hK).hom ≫
        betaOf sp Gp Wp Vp hp Pp dp qp (F.obj K) (hf K hK) ≫
          (MonoidalClosed.pre (θ K hK).hom).app Vp =
      FZ.map (betaOf s G W V he Pe de qe K hK) ≫ (χZ _ (hg K hK)).hom) ∧
  (∀ (K : CT) (hK : Pe K),
    CompositeIdentity s G W V K (alphaOf s G W V he Pe de qe K hK)
      (betaOf s G W V he Pe de qe _ (de K hK)) →
    CompositeIdentity sp Gp Wp Vp (F.obj K)
      (alphaOf sp Gp Wp Vp hp Pp dp qp _ (hf K hK))
      (betaOf sp Gp Wp Vp hp Pp dp qp _ (dp _ (hf K hK)))) ∧
  (∀ (K : CT) (hK : Pe K),
    (IsIso (alphaOf s G W V he Pe de qe K hK) →
      IsIso (alphaOf sp Gp Wp Vp hp Pp dp qp _ (hf K hK))) ∧
    (IsIso (betaOf s G W V he Pe de qe K hK) →
      IsIso (betaOf sp Gp Wp Vp hp Pp dp qp _ (hf K hK)))) ∧
  ((∀ (K : CT) (hK : Pe K), IsIso (alphaOf s G W V he Pe de qe K hK)) →
    ∀ (K : PT) (hK : Pp K), IsIso (alphaOf sp Gp Wp Vp hp Pp dp qp K hK)) ∧
  ((∀ (K : CT) (hK : Pe K), IsIso (betaOf s G W V he Pe de qe K hK)) →
    ∀ (K : PT) (hK : Pp K), IsIso (betaOf sp Gp Wp Vp hp Pp dp qp K hK))

end Transport

section Sites
open BoundaryComparison
open BoundaryComparisonOfCoefficients

/-- Evaluation realization with the functors kept as parameters during elaboration.
Its specialization below fixes them to the canonical operations, not arbitrary maps.
Source: boundary-duality discharge, evaluation comparison
(blueprint: lem-weil-boundary-finite-site-realization). -/
def EvaluationConclusion
    (C : Type (u + 2)) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [Etale.UpperStarPreservesFlat C] [ProEtale.UpperStarPreservesFlat C]
    [∀ X : Scheme.{u}, (comparisonUpperStar C X).PreservesFlat]
    {Z T : Scheme.{u}} (i : Z ⟶ T)
    (G : DerivedCategory (Sheaf T.smallEtaleTopology C) ⥤
      DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (Gp : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Z) C))
    (adj : etaleImage C i ⊣ G)
    (tr : ∀ (H : DerivedCategory (Sheaf Z.smallEtaleTopology C))
      (L : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C)),
      ((proetaleImage C i).obj ((comparison C Z).obj H) ⟶ L) →
        ((comparison C Z).obj H ⟶ Gp.obj L))
    (origin : ∀ K : DerivedCategory (Sheaf T.smallEtaleTopology C),
      (comparison C Z).obj (G.obj K) ⟶ Gp.obj ((comparison C T).obj K))
    (Hc : DerivedCategory.Plus (Sheaf T.smallEtaleTopology C) → Prop)
    (μ : ∀ N : DerivedCategory.Plus (Sheaf T.smallEtaleTopology C), Hc N →
      ((proetaleImage C i).obj (Gp.obj ((comparison C T).obj N.obj)) ⟶
        (comparison C T).obj N.obj))
    (W : DerivedCategory (Sheaf T.smallEtaleTopology C))
    (V : DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (he : G.obj W ≅ V)
    (Wp : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C))
    (Vp : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) C))
    (hp : Gp.obj Wp ≅ Vp)
    (wT : (comparison C T).obj W ≅ Wp)
    (wZ : (comparison C Z).obj V ≅ Vp)
    (PeT : ObjectProperty (DerivedCategory (Sheaf T.smallEtaleTopology C)))
    (PeZ : ObjectProperty (DerivedCategory (Sheaf Z.smallEtaleTopology C)))
    (PpT : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology T) C)))
    (PpZ : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology Z) C))) : Prop :=
  letI : BraidedCategory (DerivedCategory (Sheaf T.smallEtaleTopology C)) :=
    DerivedCategory.braidedCategory' _
  letI : BraidedCategory (DerivedCategory (Sheaf Z.smallEtaleTopology C)) :=
    DerivedCategory.braidedCategory' _
  letI : BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology T) C)) :=
    DerivedCategory.braidedCategory' _
  letI : BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology Z) C)) :=
    DerivedCategory.braidedCategory' _
  let F := comparison C T
  let FZ := comparison C Z
  let s := (Etale.upperStar C i).leftDerivedFunctor
  let sp := (ProEtale.upperStar C i).leftDerivedFunctor
  PeT W ∧ PeZ V ∧ PpT Wp ∧ PpZ Vp ∧
  ∃ (hfT : ∀ K, PeT K → PpT (F.obj K))
    (_hfZ : ∀ K, PeZ K → PpZ (FZ.obj K))
    (_hsp : ∀ K, PpT K → PpZ (sp.obj K))
    (hgp : ∀ K, PpT K → PpZ (Gp.obj K))
    (de : ∀ K, PeT K → PeT ((ihom K).obj W))
    (_dz : ∀ K, PeZ K → PeZ ((ihom K).obj V))
    (dp : ∀ K, PpT K → PpT ((ihom K).obj Wp))
    (_dpz : ∀ K, PpZ K → PpZ ((ihom K).obj Vp))
    (hs : ∀ K, PeT K → PeZ (s.obj K))
    (hg : ∀ K, PeT K → PeZ (G.obj K))
    (θ : ∀ K, PeT K → (FZ.obj (G.obj K) ≅ Gp.obj (F.obj K))),
    (∀ K hK, (θ K hK).hom =
      origin K) ∧
    (∀ hW : PeT W, FZ.map he.hom ≫ wZ.hom =
      (θ W hW).hom ≫ Gp.map wT.hom ≫ hp.hom) ∧
    ∃ (χT : ∀ K, PeT K → (F.obj ((ihom K).obj W) ≅ (ihom (F.obj K)).obj Wp))
      (χZ : ∀ K, PeZ K → (FZ.obj ((ihom K).obj V) ≅ (ihom (FZ.obj K)).obj Vp)),
      (∀ K hK, IsEvaluationComparison C T K W Wp wT (χT K hK)) ∧
      (∀ K hK, IsEvaluationComparison C Z K V Vp wZ (χZ K hK)) ∧
      (∃ (hTe : Etale.AmbientDualityPairing C T W)
        (hTp : ProEtale.AmbientDualityPairing C T Wp)
        (hZe : Etale.AmbientDualityPairing C Z V)
        (hZp : ProEtale.AmbientDualityPairing C Z Vp),
        (∀ K, PeT K → FiniteDualityCompatibility C T W Wp wT hTe hTp K) ∧
        (∀ K, PeZ K → FiniteDualityCompatibility C Z V Vp wZ hZe hZp K)) ∧
      ∀ (σeZ : EtaleSignedSymmetry C Z) (σeT : EtaleSignedSymmetry C T)
        (σpZ : ProSignedSymmetry C Z) (σpT : ProSignedSymmetry C T),
        ∃ (ep : ∀ M N, PeT M → PeT N → IsIso (etaleProjection C i (G.obj N) M))
          (pp : ∀ B M, PpZ B → PpT M →
            IsIso (((ProEtale.rightDerivedLowerStarProjectionMap C i).app B).app M))
          (qp : ∀ M N, PpT M → PpT N → (sp.obj M ⊗ Gp.obj N ⟶ Gp.obj (M ⊗ N))),
          (∀ (M N M' N' : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C))
            (hM : PpT M) (hN : PpT N) (hM' : PpT M') (hN' : PpT N')
            (f : M ⟶ M') (g : N ⟶ N'),
            (sp.map f ⊗ₘ Gp.map g) ≫ qp M' N' hM' hN' =
              qp M N hM hN ≫ Gp.map (f ⊗ₘ g)) ∧
          (∀ (M N : DerivedCategory.Plus (Sheaf T.smallEtaleTopology C))
            (hM : PeT M.obj) (hN : PeT N.obj)
            (hc : Hc N),
            letI := ep M.obj N.obj hM hN
            letI := pp _ _ (hgp _ (hfT _ hN)) (hfT _ hM)
            (qSourceIso C i M.obj (G.obj N.obj)).hom ≫
                ((ProEtale.derivedTensor C Z).obj (sp.obj (F.obj M.obj))).map
                  (θ N.obj hN).hom ≫
                qp _ _ (hfT _ hM) (hfT _ hN) ≫
                Gp.map (tensorComparison C T M.obj N.obj).inv =
              assembleProQ C i σpZ σpT G Gp tr M.obj N.obj (origin N.obj) (μ N hc) ∧
            assembleProQ C i σpZ σpT G Gp tr M.obj N.obj (origin N.obj) (μ N hc) =
              comparedEtaleQ C i σeZ σeT G Gp adj origin M.obj N.obj) ∧
          EvaluationTransport s G sp Gp W V Wp Vp he hp PeT PeZ PpT de dp
            (fun M N hM hN ↦
              letI := ep M N hM hN
              etaleQForAdjunction C i σeZ σeT G
                adj M N)
            qp F FZ hfT χT χZ hs hg
            (fun K _ ↦ (pullbackSquare C i).symm.app K) θ


/-- The comparison equivalences on the finite-Tor constructible subcategories, preservation
and reflection of every Tor interval, and etale representatives of pro-etale inputs.
The remaining clauses specify bounded-below exceptional Hom bijectivity, Noetherianity
and finite dimension of the identity-open compactification, invertibility of the canonical
direct-image mate, and the counit and projection comparison squares with their inverses.
Source: boundary-duality discharge, second proof paragraph
(blueprint: lem-weil-boundary-finite-site-realization). -/
def BasicRemainder (A : Type u) [CommRing A] [Finite A]
    {Z T S : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] (a : T ⟶ S)
    [HasCompactification a] [HasCompactification (i ≫ a)]
    [QuasiCompact (i ≫ a)] [CompactSpace T] [CompactSpace S]
    (PeT : ObjectProperty (DerivedCategory (Sheaf T.smallEtaleTopology
      (BoundaryComparison.coefficients A))))
    (_PeZ : ObjectProperty (DerivedCategory (Sheaf Z.smallEtaleTopology
      (BoundaryComparison.coefficients A))))
    (_PpT : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (BoundaryComparison.coefficients A))))
    (_PpZ : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology Z)
      (BoundaryComparison.coefficients A)))) : Prop :=
  let C := BoundaryComparison.coefficients A
  (∀ (H : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology C))
    (L : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology T) C)),
      Function.Bijective (BoundaryComparison.homTransport A i H L)) ∧
  IsNoetherian Z ∧
  (∃ d : ℕ, topologicalKrullDim Z ≤ (d : WithBot ℕ∞)) ∧
  (∀ H : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology C),
    IsIso ((directImageMate C i).app H.obj)) ∧
  (∀ N : DerivedCategory.Plus (Sheaf T.smallEtaleTopology C), PeT N.obj →
    BoundaryComparisonOfCoefficients.CounitComparison (ULift.{u + 1, u} A) i N) ∧
  (∀ (B : DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (M : DerivedCategory (Sheaf T.smallEtaleTopology C)),
    Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1, u} A) Z B → PeT M →
      ProjectionComparison C i B M ∧ IsIso (etaleProjection C i B M) ∧
        IsIso (proetaleProjection C i B M))

/-- The basic site comparison clauses, with their remaining boundary assertions.
Source: boundary finite-site realization
(blueprint: def-weil-boundary-finite-site-data). -/
def BasicConclusion (A : Type u) [CommRing A] [Finite A]
    {Z T S : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] (a : T ⟶ S)
    [HasCompactification a] [HasCompactification (i ≫ a)]
    [QuasiCompact (i ≫ a)] [CompactSpace T] [CompactSpace S]
    (PeT : ObjectProperty (DerivedCategory (Sheaf T.smallEtaleTopology
      (BoundaryComparison.coefficients A))))
    (PeZ : ObjectProperty (DerivedCategory (Sheaf Z.smallEtaleTopology
      (BoundaryComparison.coefficients A))))
    (PpT : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (BoundaryComparison.coefficients A))))
    (PpZ : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology Z)
      (BoundaryComparison.coefficients A)))) : Prop :=
  let C := BoundaryComparison.coefficients A
  let F := comparison C T
  let FZ := comparison C Z
  (∃ e : PeT.FullSubcategory ≌ PpT.FullSubcategory,
    Nonempty (e.functor ⋙ PpT.ι ≅ PeT.ι ⋙ F)) ∧
  (∃ e : PeZ.FullSubcategory ≌ PpZ.FullSubcategory,
    Nonempty (e.functor ⋙ PpZ.ι ≅ PeZ.ι ⋙ FZ)) ∧
  (∀ (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology C)), PeT K.obj →
    ∀ (b c : ℤ), b ≤ c →
      (Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1, u} A) T b c K.obj ↔
        ProEtale.DerivedCategory.torAmplitudeIn C T b c (F.obj K.obj))) ∧
  (∀ (K : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology C)), PeZ K.obj →
    ∀ (b c : ℤ), b ≤ c →
      (Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1, u} A) Z b c K.obj ↔
        ProEtale.DerivedCategory.torAmplitudeIn C Z b c (FZ.obj K.obj))) ∧
  (∀ K, PpT K → ∃ H, PeT H ∧ Nonempty (F.obj H ≅ K)) ∧
  (∀ K, PpZ K → ∃ H, PeZ H ∧ Nonempty (FZ.obj H ≅ K)) ∧
  BasicRemainder A i a PeT PeZ PpT PpZ

/-- The ordinary-site realization conclusion. The q family on the pro-etale finite-Tor
subcategory is fixed on every etale representative by its ordinary-counit Hom transpose.
The last assertion uses the literal evaluation-defined alpha and beta from this module.
Source: boundary-duality discharge, second proof paragraph
(blueprint: lem-weil-boundary-finite-site-realization). -/
def EvaluationAt (A : Type u) [CommRing A] [Finite A]
    {Z T S : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] (a : T ⟶ S)
    [HasCompactification a] [HasCompactification (i ≫ a)]
    [QuasiCompact (i ≫ a)] [CompactSpace T] [CompactSpace S]
    (PeT : ObjectProperty (DerivedCategory (Sheaf T.smallEtaleTopology
      (BoundaryComparison.coefficients A))))
    (PeZ : ObjectProperty (DerivedCategory (Sheaf Z.smallEtaleTopology
      (BoundaryComparison.coefficients A))))
    (PpT : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (BoundaryComparison.coefficients A))))
    (PpZ : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology Z)
      (BoundaryComparison.coefficients A)))) : Prop :=
  let C := BoundaryComparison.coefficients A
  let FZ := comparison C Z
  let G := BoundaryComparisonOfCoefficients.etaleExceptional (ULift.{u + 1, u} A) i
  let Gp := BoundaryComparisonOfCoefficients.proetaleExceptional (ULift.{u + 1, u} A) i
  let W := Etale.dualizingComplex (ULift.{u + 1, u} A) a
  let V := G.obj W
  let Wp := (ProEtale.rightDerivedUpperShriek (ULift.{u + 1, u} A) a).obj (𝟙_ _)
  let Vp := (ProEtale.rightDerivedUpperShriek (ULift.{u + 1, u} A) (i ≫ a)).obj (𝟙_ _)
  let hp := Etale.boundaryDualizingProIso (ULift.{u + 1, u} A) i a
  let wT := Etale.boundaryDualizingComparisonIso (ULift.{u + 1, u} A) a
  let wZ := FZ.mapIso (Etale.boundaryDualizingEtaleIso (ULift.{u + 1, u} A) i a) ≪≫
    Etale.boundaryDualizingComparisonIso (ULift.{u + 1, u} A) (i ≫ a)
  EvaluationConclusion C i G Gp
    (BoundaryComparisonOfCoefficients.exceptionalAdjunction (ULift.{u + 1, u} A) i)
    (rawHomTransport (ULift.{u + 1, u} A) i)
    (rawOriginMap (ULift.{u + 1, u} A) i)
    (BoundaryComparisonOfCoefficients.CounitComparison (ULift.{u + 1, u} A) i)
    (proCounit (ULift.{u + 1, u} A) i)
    W V (Iso.refl V) Wp Vp hp wT wZ PeT PeZ PpT PpZ

/-- The basic and evaluation conclusions at the specified canonical operations.
Source: boundary finite-site realization
(blueprint: def-weil-boundary-finite-site-data). -/
def SiteConclusion (A : Type u) [CommRing A] [Finite A]
    {Z T S : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] (a : T ⟶ S)
    [HasCompactification a] [HasCompactification (i ≫ a)]
    [QuasiCompact (i ≫ a)] [CompactSpace T] [CompactSpace S]
    (PeT : ObjectProperty (DerivedCategory (Sheaf T.smallEtaleTopology
      (BoundaryComparison.coefficients A))))
    (PeZ : ObjectProperty (DerivedCategory (Sheaf Z.smallEtaleTopology
      (BoundaryComparison.coefficients A))))
    (PpT : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (BoundaryComparison.coefficients A))))
    (PpZ : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology Z)
      (BoundaryComparison.coefficients A)))) : Prop :=
  BasicConclusion A i a PeT PeZ PpT PpZ ∧ EvaluationAt A i a PeT PeZ PpT PpZ

/-- Specialization to the fixed finite-field datum and every positive finite coefficient
level. The two Tor predicates are the published ordinary constant-module presentations
of the intrinsic predicates, and the hypotheses refer to the etale duals into G omega_T.
Source: boundary-duality discharge, finite-stage realization
(blueprint: lem-weil-boundary-finite-site-realization). -/
def FiniteStatement (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {Z T : Scheme.{u}} (i : Z ⟶ T)
    [Z.Over (Spec (.of D.k))] [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))] [IsSeparated (Z ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))] [IsSeparated (T ↘ Spec (.of D.k))]
    [i.IsOver (Spec (.of D.k))] [IsClosedImmersion i] : Prop :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  letI : CompactSpace T :=
    QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of D.k))
  let A := Padic.coefficientExtensionRing l E n
  let C := BoundaryComparison.coefficients A
  let a := T ↘ Spec (.of D.k)
  let G := BoundaryComparisonOfCoefficients.etaleExceptional (ULift.{u + 1, u} A) i
  let W := Etale.dualizingComplex (ULift.{u + 1, u} A) a
  letI : BraidedCategory (DerivedCategory (Sheaf T.smallEtaleTopology C)) :=
    DerivedCategory.braidedCategory' _
  letI : BraidedCategory (DerivedCategory (Sheaf Z.smallEtaleTopology C)) :=
    DerivedCategory.braidedCategory' _
  EtaleHypotheses ((Etale.upperStar C i).leftDerivedFunctor) G W (G.obj W)
      (WeilConjectures.finiteTorConstructibleEtale l E n hn T)
      (WeilConjectures.finiteTorConstructibleEtale l E n hn Z) →
    SiteConclusion A i a
      (WeilConjectures.finiteTorConstructibleEtale l E n hn T)
      (WeilConjectures.finiteTorConstructibleEtale l E n hn Z)
      (WeilConjectures.finiteTorConstructibleProEtaleModule l E n hn T)
      (WeilConjectures.finiteTorConstructibleProEtaleModule l E n hn Z)

end Sites

end AlgebraicGeometry.ProEtale.BoundaryFiniteSite
