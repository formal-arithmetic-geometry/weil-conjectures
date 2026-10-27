module

public import Sheaf.AlgebraicGeometry.SNCFiniteFibreData
public import Mathlib.Algebra.Category.ModuleCat.AB

import Sheaf.AlgebraicGeometry.SNCFiniteModuleStalkNaturality
import Sheaf.AlgebraicGeometry.SNCFiniteTameScalarExtension
import Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

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

open AlgebraicGeometry.Scheme

private theorem lift_geometricPoint_cover
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {V : X.ProEt} (S : Sieve V) (hS : S ∈ ProEt.topology X V)
    (v : Spec (.of Ω) ⟶ V.left) :
    ∃ (W : X.ProEt) (g : W ⟶ V) (_ : S g) (w : Spec (.of Ω) ⟶ W.left),
      w ≫ g.left = v := by
  obtain ⟨R, hR, hRS⟩ := ProEt.mem_topology_iff.1 hS
  obtain ⟨ι, Z, f, rfl⟩ := R.exists_eq_ofArrows
  have hR' : Presieve.ofArrows (fun i ↦ (Z i).left) (fun i ↦ (f i).left) ∈
      proetalePrecoverage V.left := by
    simpa only [ProEt.mem_precoverage_iff, Presieve.map_ofArrows,
      Functor.comp_obj, Functor.comp_map, ProEt.forget, MorphismProperty.Over.forget,
      MorphismProperty.Comma.forget, Over.forget, Comma.fst] using hR
  have hb := Precoverage.mem_coverings_of_isPullback (fun i ↦ (f i).left) hR' v
    (fun i ↦ pullback.snd (f i).left v) (fun i ↦ pullback.fst (f i).left v)
    (fun i ↦ (IsPullback.of_hasPullback (f i).left v).flip)
  have hb' := propQCPrecoverage_le_precoverage _ hb
  obtain ⟨i, z, hz⟩ :=
    ((ofArrows_mem_precoverage_iff _).1 hb').1 (IsLocalRing.closedPoint Ω)
  have hf : WeaklyEtale (f i).left :=
    ((ofArrows_mem_precoverage_iff _).1 (propQCPrecoverage_le_precoverage _ hR')).2 i
  let := hf
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale
    (pullback.snd (f i).left v) z
  refine ⟨Z i, f i, hRS _ _ ⟨i⟩, σ ≫ pullback.fst (f i).left v, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]

private theorem moduleSheafificationStalk_isIso
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (R : Type (u + 1)) [Ring R]
    (P : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} R) :
    IsIso (colim.map (Functor.whiskerLeft (Scheme.proEtaleGeometricNeighbourhoodForget x).op
      (toSheafify (Scheme.ProEt.topology X) P))) := by
  let p := Scheme.proEtaleGeometricNeighbourhoodForget x
  have hp : ∀ ⦃Y : X.ProEt⦄ (R : Sieve Y) (_ : R ∈ ProEt.topology X Y)
      ⦃U : Scheme.ProEtaleGeometricNeighbourhood x⦄ (f : p.obj U ⟶ Y),
      ∃ (Z : X.ProEt) (g : Z ⟶ Y) (_ : R g)
        (V : Scheme.ProEtaleGeometricNeighbourhood x) (q : V ⟶ U) (a : p.obj V ⟶ Z),
        a ≫ g = p.map q ≫ f := by
    intro Y R hR U f
    obtain ⟨Z, g, hg, z, hz⟩ := lift_geometricPoint_cover
      (R.pullback f) ((ProEt.topology X).pullback_stable f hR) U.hom.left
    let V : Scheme.ProEtaleGeometricNeighbourhood x :=
      StructuredArrow.mk (Over.homMk z (by
        change z ≫ Z.hom = x
        rw [← MorphismProperty.Over.w g, ← Category.assoc, hz]
        exact Over.w U.hom))
    let q : V ⟶ U := StructuredArrow.homMk g (by
      apply Over.OverMorphism.ext
      exact hz)
    refine ⟨Z, g ≫ f, hg, V, q, 𝟙 _, ?_⟩
    change 𝟙 Z ≫ (g ≫ f) = g ≫ f
    exact Category.id_comp _
  let Φ : (ProEt.topology X).Point.{u + 1} :=
    GrothendieckTopology.Point.ofIsCofiltered.{u + 1} p hp
  let e (F : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} R) :
      colimit (p.op ⋙ F) ≅ Φ.presheafFiber.obj F :=
    (colimit.isColimit (p.op ⋙ F)).coconePointUniqueUpToIso
      (GrothendieckTopology.Point.isColimitPresheafFiberOfIsCofilteredCocone.{u + 1}
        p hp F)
  have he (F : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} R)
      (j : (Scheme.ProEtaleGeometricNeighbourhood x)ᵒᵖ) :
      colimit.ι (p.op ⋙ F) j ≫ (e F).hom =
        GrothendieckTopology.Point.toPresheafFiberOfIsCofiltered.{u + 1}
          p hp j.unop F :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ j
  have hei (F : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} R)
      (j : (Scheme.ProEtaleGeometricNeighbourhood x)ᵒᵖ) :
      GrothendieckTopology.Point.toPresheafFiberOfIsCofiltered.{u + 1}
          p hp j.unop F ≫ (e F).inv =
        colimit.ι (p.op ⋙ F) j :=
    by rw [← he F j, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hmap (F G : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} R) (a : F ⟶ G) :
      colim.map (p.op.whiskerLeft a) =
        (e F).hom ≫ Φ.presheafFiber.map a ≫ (e G).inv := by
    apply colimit.hom_ext
    intro j
    rw [colim_map, ι_colimMap, ← Category.assoc, he]
    rw [← Category.assoc,
      GrothendieckTopology.Point.toPresheafFiberOfIsCofiltered_naturality]
    rw [Category.assoc, hei]
    rfl
  change IsIso (colim.map (p.op.whiskerLeft (toSheafify (Scheme.ProEt.topology X) P)))
  rw [hmap]
  infer_instance

private theorem scalarStalkComparison
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (R S : Type (u + 1)) [Ring R] [Ring S]
    (E : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} S)
    [E.IsLeftAdjoint]
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) :
    let N := (presheafToSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} S)).obj (M.obj ⋙ E)
    ∃ c : E.obj (Scheme.proEtaleGeometricStalk x M) ≅ Scheme.proEtaleGeometricStalk x N,
      ∀ V : Scheme.ProEtaleGeometricNeighbourhood x,
        E.map (colimit.ι (Scheme.proEtaleGeometricStalkDiagram x M) (op V)) ≫ c.hom =
          (toSheafify (Scheme.ProEt.topology X) (M.obj ⋙ E)).app (op V.right) ≫
            colimit.ι (Scheme.proEtaleGeometricStalkDiagram x N) (op V) := by
  let p := Scheme.proEtaleGeometricNeighbourhoodForget x
  let D := Scheme.proEtaleGeometricStalkDiagram x M
  let α := Functor.whiskerLeft p.op (toSheafify (Scheme.ProEt.topology X) (M.obj ⋙ E))
  have : IsIso (colim.map α) := moduleSheafificationStalk_isIso x S (M.obj ⋙ E)
  refine ⟨preservesColimitIso E D ≪≫ asIso (colim.map α), ?_⟩
  intro V
  change E.map (colimit.ι D (op V)) ≫
    ((preservesColimitIso E D).hom ≫ colim.map α) = _
  rw [← Category.assoc, ι_preservesColimitIso_hom]
  exact ι_colimMap α (op V)

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
  let N := (presheafToSheaf (Scheme.ProEt.topology Q.puncturedResidual)
    (ModuleCat.{u + 1} S)).obj (M.obj ⋙ E)
  have hN := sncFiniteTame_scalarExtension Q k _hD R S φ E _adj M _hM
  have : E.IsLeftAdjoint := _adj.isLeftAdjoint
  obtain ⟨c, hc⟩ := scalarStalkComparison (z ≫ Q.towerMap) R S E M
  refine ⟨hN, c, hc, ?_⟩
  intro d
  let L := ModuleCat.restrictScalars.{u + 1} φ
  have hunit {X Y : ModuleCat.{u + 1} R} (f : X ⟶ Y) :
      f ≫ _adj.unit.app Y = _adj.unit.app X ≫ L.map (E.map f) :=
    _adj.unit.naturality f
  let η := Functor.whiskerLeft M.obj _adj.unit ≫
    Functor.whiskerRight
      (toSheafify (Scheme.ProEt.topology Q.puncturedResidual) (M.obj ⋙ E)) L
  let f : M ⟶ (sheafCompose (Scheme.ProEt.topology Q.puncturedResidual) L).obj N := ⟨η⟩
  let t := _adj.unit.app (Scheme.proEtaleGeometricStalk (z ≫ Q.towerMap) M) ≫ L.map c.hom
  have ht : ∀ V : Scheme.ProEtaleGeometricNeighbourhood (z ≫ Q.towerMap),
      colimit.ι (Scheme.proEtaleGeometricStalkDiagram (z ≫ Q.towerMap) M) (op V) ≫ t =
        f.hom.app (op V.right) ≫ L.map
          (colimit.ι (Scheme.proEtaleGeometricStalkDiagram (z ≫ Q.towerMap) N) (op V)) := by
    intro V
    let iM : M.obj.obj (op V.right) ⟶ Scheme.proEtaleGeometricStalk (z ≫ Q.towerMap) M :=
      colimit.ι (Scheme.proEtaleGeometricStalkDiagram (z ≫ Q.towerMap) M) (op V)
    let iN : N.obj.obj (op V.right) ⟶ Scheme.proEtaleGeometricStalk (z ≫ Q.towerMap) N :=
      colimit.ι (Scheme.proEtaleGeometricStalkDiagram (z ≫ Q.towerMap) N) (op V)
    let q := (toSheafify (Scheme.ProEt.topology Q.puncturedResidual) (M.obj ⋙ E)).app
      (op V.right)
    change iM ≫ (_adj.unit.app _ ≫ L.map c.hom) =
      (_adj.unit.app _ ≫ L.map q) ≫ L.map iN
    calc
      iM ≫ (_adj.unit.app _ ≫ L.map c.hom) =
          (iM ≫ _adj.unit.app _) ≫ L.map c.hom := (Category.assoc _ _ _).symm
      _ = (_adj.unit.app _ ≫ L.map (E.map iM)) ≫ L.map c.hom :=
        congrArg (fun b ↦ b ≫ L.map c.hom) (hunit iM)
      _ = _adj.unit.app _ ≫ L.map (E.map iM ≫ c.hom) := by
        rw [Category.assoc, ← L.map_comp]
      _ = _adj.unit.app _ ≫ L.map (q ≫ iN) :=
        congrArg (fun b ↦ _adj.unit.app _ ≫ L.map b) (hc V)
      _ = (_adj.unit.app _ ≫ L.map q) ≫ L.map iN := by
        rw [L.map_comp, Category.assoc]
  obtain ⟨A, B, hAB⟩ := sncFiniteModuleStalkAction_natural Q z d R S φ M N _hM hN f t ht
  refine ⟨A, B, ?_⟩
  intro g
  apply (_adj.homEquiv _ _).injective
  change _adj.unit.app _ ≫ L.map (E.map (A.action g) ≫ c.hom) =
    _adj.unit.app _ ≫ L.map (c.hom ≫ B.action g)
  rw [L.map_comp, L.map_comp, ← Category.assoc]
  rw [← hunit (A.action g)]
  exact (Category.assoc _ _ _).trans ((hAB g).trans (Category.assoc _ _ _))


end AlgebraicGeometry.ProEtale
