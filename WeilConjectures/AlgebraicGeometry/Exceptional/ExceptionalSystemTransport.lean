/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemInterfaces
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSiteOriginComparison
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalProperOpenOriginComparison
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalProOriginExactLinear
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalOriginAdjunctionEvaluation

/-! # Exceptional adjunction on strict pro-etale coefficient systems

The geometric existence theorem transports the actual etale adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace CategoryTheory
universe a b x y av bv xv yv
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
  {F : A ⥤ B} {G : B ⥤ A}
private def reverseHom (adj : F ⊣ G) (M : B) (Q : A)
    [IsIso (adj.counit.app M)] [IsIso (adj.unit.app Q)] :
    (G.obj M ⟶ Q) ≃ (M ⟶ F.obj Q) where
  toFun u := inv (adj.counit.app M) ≫ F.map u
  invFun k := G.map k ≫ inv (adj.unit.app Q)
  left_inv u := by
    have he : G.map (inv (adj.counit.app M)) = adj.unit.app (G.obj M) := by
      apply (cancel_mono (G.map (adj.counit.app M))).mp
      simp only [← Functor.map_comp, IsIso.inv_hom_id, Functor.map_id]
      exact (adj.right_triangle_components M).symm
    simp only [Functor.map_comp, he, Category.assoc]
    have hn := adj.unit.naturality u
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    rw [← Category.assoc, ← hn]
    simp
  right_inv k := by
    have he : F.map (inv (adj.unit.app Q)) = adj.counit.app (F.obj Q) := by
      apply (cancel_epi (F.map (adj.unit.app Q))).mp
      simp only [← Functor.map_comp, IsIso.hom_inv_id, Functor.map_id]
      exact (adj.left_triangle_components Q).symm
    simp only [Functor.map_comp, he]
    have hn := adj.counit.naturality k
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    rw [hn]
    simp

variable {X : Type x} [Category.{xv} X] {Y : Type y} [Category.{yv} Y]
  {CX : A ⥤ X} {VX : X ⥤ A} {CY : B ⥤ Y} {VY : Y ⥤ B}
  (adj : F ⊣ G) (adjX : CX ⊣ VX) (adjY : CY ⊣ VY)
  (FP : X ⥤ Y) (PX : ObjectProperty X) (PY : ObjectProperty Y)
  (kappa : VX ⋙ F ⋙ CY ⟶ FP)
  (hleft : ∀ M, PX M → PY (FP.obj M))
  (hright : ∀ N, PY N → PX ((VY ⋙ G ⋙ CX).obj N))
  (hk : ∀ M, PX M → IsIso (kappa.app M))
  (hc : ∀ M, PX M → IsIso (adjX.counit.app M))
  (hu : ∀ N, PY N → IsIso (adjX.unit.app (G.obj (VY.obj N))))

private def originEquiv (M : PX.FullSubcategory) (N : PY.FullSubcategory) :
    ((PY.lift (PX.ι ⋙ FP) (fun M ↦ hleft M.obj M.property)).obj M ⟶ N) ≃
      (M ⟶ (PX.lift (PY.ι ⋙ (VY ⋙ G ⋙ CX))
        (fun N ↦ hright N.obj N.property)).obj N) := by
  letI := hk M.obj M.property
  have := hc M.obj M.property
  letI := hu N.obj N.property
  exact PY.fullyFaithfulι.homEquiv.trans
    ((asIso (kappa.app M.obj)).symm.homFromEquiv.trans
      ((adjY.homEquiv _ _).trans ((adj.homEquiv _ _).trans
        ((reverseHom adjX M.obj (G.obj (VY.obj N.obj))).trans
          (PX.fullyFaithfulι.homEquiv (X := M)
            (Y := (PX.lift (PY.ι ⋙ (VY ⋙ G ⋙ CX))
              (fun N ↦ hright N.obj N.property)).obj N)).symm))))

private theorem originEquiv_left
    {M M' : PX.FullSubcategory} {N : PY.FullSubcategory} (f : M ⟶ M')
    (h : (PY.lift (PX.ι ⋙ FP) (fun M ↦ hleft M.obj M.property)).obj M' ⟶ N) :
    originEquiv adj adjX adjY FP PX PY kappa hleft hright hk hc hu M N
      ((PY.lift (PX.ι ⋙ FP) (fun M ↦ hleft M.obj M.property)).map f ≫ h) =
    f ≫ originEquiv adj adjX adjY FP PX PY kappa hleft hright hk hc hu M' N h := by
  have := hc M.obj M.property
  have := hc M'.obj M'.property
  apply ObjectProperty.hom_ext
  change inv (adjX.counit.app M.obj) ≫ CX.map
    (adj.homEquiv _ _ (adjY.homEquiv _ _
      (kappa.app M.obj ≫ FP.map f.hom ≫ h.hom))) = _
  have hn := kappa.naturality f.hom
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, ← hn, Category.assoc,
    adjY.homEquiv_naturality_left, adj.homEquiv_naturality_left, CX.map_comp]
  change inv (adjX.counit.app M.obj) ≫ CX.map (VX.map f.hom) ≫ _ = _
  have hn := adjX.counit.naturality f.hom
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  have hi : inv (adjX.counit.app M.obj) ≫ CX.map (VX.map f.hom) =
      f.hom ≫ inv (adjX.counit.app M'.obj) := by
    have := hc M.obj M.property
    have := hc M'.obj M'.property
    apply (cancel_mono (adjX.counit.app M'.obj)).mp
    simpa only [Category.assoc, IsIso.inv_hom_id_assoc, IsIso.inv_hom_id,
      Category.comp_id] using congrArg (inv (adjX.counit.app M.obj) ≫ ·) hn
  rw [← Category.assoc, hi, Category.assoc]
  rfl

private theorem originEquiv_right
    {M : PX.FullSubcategory} {N N' : PY.FullSubcategory}
    (h : (PY.lift (PX.ι ⋙ FP) (fun M ↦ hleft M.obj M.property)).obj M ⟶ N)
    (f : N ⟶ N') :
    originEquiv adj adjX adjY FP PX PY kappa hleft hright hk hc hu M N' (h ≫ f) =
    originEquiv adj adjX adjY FP PX PY kappa hleft hright hk hc hu M N h ≫
      (PX.lift (PY.ι ⋙ (VY ⋙ G ⋙ CX))
        (fun N ↦ hright N.obj N.property)).map f := by
  have := hc M.obj M.property
  apply ObjectProperty.hom_ext
  change inv (adjX.counit.app M.obj) ≫ CX.map
    (adj.homEquiv _ _ (adjY.homEquiv _ _ (kappa.app M.obj ≫ h.hom ≫ f.hom))) = _
  rw [← Category.assoc, adjY.homEquiv_naturality_right,
    adj.homEquiv_naturality_right, CX.map_comp, ← Category.assoc]
  rfl

private def originAdjunction :
    PY.lift (PX.ι ⋙ FP) (fun M ↦ hleft M.obj M.property) ⊣
      PX.lift (PY.ι ⋙ (VY ⋙ G ⋙ CX)) (fun N ↦ hright N.obj N.property) :=
  Adjunction.mkOfHomEquiv {
    homEquiv := originEquiv adj adjX adjY FP PX PY kappa hleft hright hk hc hu
    homEquiv_naturality_left_symm := by
      intro M' M N f h
      apply (originEquiv adj adjX adjY FP PX PY kappa hleft hright hk hc hu M' N).injective
      rw [Equiv.apply_symm_apply,
        originEquiv_left adj adjX adjY FP PX PY kappa hleft hright hk hc hu,
        Equiv.apply_symm_apply]
    homEquiv_naturality_right :=
      originEquiv_right adj adjX adjY FP PX PY kappa hleft hright hk hc hu }

private theorem originAdjunction_transpose (M : PX.FullSubcategory) (N : PY.FullSubcategory)
    (h : (PY.lift (PX.ι ⋙ FP) (fun M ↦ hleft M.obj M.property)).obj M ⟶ N) :
    CX.map (adj.homEquiv (VX.obj M.obj) (VY.obj N.obj)
      (adjY.unit.app (F.obj (VX.obj M.obj)) ≫ VY.map (kappa.app M.obj ≫ h.hom))) =
    adjX.counit.app M.obj ≫
      ((originAdjunction adj adjX adjY FP PX PY kappa hleft hright hk hc hu).homEquiv
        M N h).hom := by
  have := hc M.obj M.property
  simp only [originAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  change _ = adjX.counit.app M.obj ≫
    (originEquiv adj adjX adjY FP PX PY kappa hleft hright hk hc hu M N h).hom
  change _ = adjX.counit.app M.obj ≫ inv (adjX.counit.app M.obj) ≫ _
  rw [IsIso.hom_inv_id_assoc]
  rw [adjY.homEquiv_unit]
  rfl
private def makeOriginAdjunction :
    ExceptionalOriginAdjunction adj adjX adjY FP PX PY kappa where
  leftStable := hleft
  rightStable := hright
  adjunction := originAdjunction adj adjX adjY FP PX PY kappa hleft hright hk hc hu
  transpose := originAdjunction_transpose adj adjX adjY FP PX PY kappa hleft hright hk hc hu
end CategoryTheory

namespace AlgebraicGeometry
variable {O : Type (u + 1)} [CommRing O] {ell : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  {S : StrictEtaleCompactSupport O ell c}
  (G : StrictEtaleExceptionalAdjoint O ell c S)
  (CX : ExceptionalSystemSiteComparison O ell X S.PX)
  (CY : ExceptionalSystemSiteComparison O ell Y S.PY)

private theorem exceptionalSystemRight_lowerBound
    (hX : ExceptionalSystemSiteEquivalence CX)
    (hY : ExceptionalSystemSiteEquivalence CY) :
    ∃ c_f : ℕ, ∀ (a : ℤ) N, CY.origin N → N.IsGE a →
      ((exceptionalSystemRight G CX CY).obj N).IsGE (a - c_f) := by
  obtain ⟨d, hd⟩ := G.property.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨d, ?_⟩
  intro a N _hN ha
  exact hX.inverseBound (a - d) _ (hd a _ (hY.directBound a N ha))

private theorem exceptionalSystemRight_normalized
    (hX : ExceptionalSystemSiteEquivalence CX)
    (hY : ExceptionalSystemSiteEquivalence CY) (N) (hN : CY.origin N)
    (hn : IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
      O ell CY.proEvaluation N) :
    IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
      O ell CX.proEvaluation ((exceptionalSystemRight G CX CY).obj N) := by
  obtain ⟨a, ha⟩ := hN.1
  have hV := hY.directBound a N ha
  obtain ⟨hG, hnorm⟩ := G.property.2.2.2.2.2.2.2.2.2.2.2 _
    ⟨a, hV⟩ (hY.directNormalized N hN hn)
  intro m n h
  exact hX.inverseNormalized _ hG (fun {_ _} h ↦ hnorm h) h

/-- Transport the ordinary etale system adjunction through the actual comparison
adjunctions. All data, their finite operations, and their normalized maps are conclusions.
Source: Zheng, Propositions 2.23, 2.29, 3.16, Lemma 5.22 and Proposition 5.24;
blueprint exceptional inverse-image construction, system transport steps 8--9
(blueprint: lem-sf-exceptional-system-transport).

Proof:
1. Apply lem-pur-etale-system-brown-construction and
lem-pur-etale-coefficient-system-adjoint to obtain S and G on unbounded strict
systems. Their bound restricts G to bounded-below objects, without absolute
separatedness assumptions on X or Y.
2. Apply lem-pur-coefficient-system-derived-comparison at X, c.Z and Y.
The actual unit evaluates to the finite site unit (thm-weil-pbc-site-comparison),
so lem-pur-system-derived-evaluation detects its invertibility. The origin
counit is invertible by the system comparison. Exact inverse image and
lem-pur-exact-derived-adjunction-bounds preserve each lower bound. Derived
tensor compatibility identifies normalized transitions in both directions.
3. Construct the pullback square of strict systems from the canonical
levelwise inverse-image square (lem-weil-pbc-comparison-pullback) and its
ordinary evaluations; localize that square on complexes. Take the proper
adjunction mate, then the termwise open comparison
(lem-cbc-proetale-extension-zero-comparison). This defines J on systems.
4. Evaluation identifies this word with the finite canonical proper mate
and open comparison (lem-coef-semilinear-derived-sections). Properness gives
quasi-compactness and quasi-separatedness, so
lem-weil-pbc-comparison-direct-image-canonical-mate makes each finite word
invertible on bounded-below objects. Joint conservativity makes J invertible.
Compose with the actual source-site counit to obtain kappa on origin systems.
5. Compose the site Hom bijections, G.adjunction, and the inverse source-site
counit. The inverse sends k to the inverse site-unit followed by the etale
counit, then the target site counit and inverse kappa. Site triangle identities
and the etale triangle identities make these maps inverse. Naturality and
lem-weil-pbc-adjunction-of-natural-bijection give the whole-system adjunction.
6. Its unit is the forward image of identity and its counit is the inverse
image of identity. Evaluate these words using the actual comparison equations.
They are the finite transported adjunction unit and counit; no equality of
system maps is inferred from equality of evaluations.
7. The etale transition theorem lem-pur-etale-system-evaluation-bound expresses
the right transition as its finite counit-normalized quotient transpose followed
by G_n of the input transition. Apply exact C_X and its derived tensor comparison.
The scalar pullback cube (lem-sfb-etale-proetale-scalar-pullback-cube) and
lem-weil-pbc-mate-pasting give precisely the quotientTransition equation. The
transpose is formed on unbounded etale categories: no quotient flatness or
boundedness of the intermediate tensor is used.
8. Normalization follows successively for V_Y, G, C_X. Their bounds give
one c_f independent of n. Exact localization of j_! and the K-injective proper
right-derived functor make the left functor triangulated; the corresponding
exactness of C_X, G and V_Y makes the right functor triangulated, by
lem-sf-exact-functor-derived-triangulated and
lem-pc-right-derived-functor-triangulated. Constant scalar actions commute with
each operation, giving O-linearity on all Hom groups.
9. The residue exponent is retained as level zero. Identity compactification
reduces the formulas to site triangle identities. Empty source gives zero
functors with bound zero; empty target forces empty source. Only the chosen
proper factor needs qcqs; neither absolute separatedness nor faithful finite
evaluation of derived morphisms is used.
-/
theorem exceptionalSystemTransport
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    ∃ (S : StrictEtaleCompactSupport (Padic.coefficientExtensionIntegers l E)
        (Padic.coefficientExtensionUniformizer l E) c)
      (G : StrictEtaleExceptionalAdjoint _ _ c S)
      (CX : ExceptionalSystemSiteComparison _ _ X S.PX)
      (CY : ExceptionalSystemSiteComparison _ _ Y S.PY)
      (CZ : ExceptionalSystemSiteComparison _ _ c.Z S.PZ)
      (P : ExceptionalProCompactSupport _ _ c
        CX.proEvaluation CY.proEvaluation CZ.proEvaluation)
      (R : ExceptionalSystemCompactificationComparison S CX CY CZ P),
      Nonempty (ExceptionalSystemTransport G CX CY CZ P R) := by
  obtain ⟨S, ⟨G⟩⟩ := etaleCoefficientSystemAdjoint D l _hl E f c
  let O := Padic.coefficientExtensionIntegers l E
  let ell := Padic.coefficientExtensionUniformizer l E
  have hfinite (n : ℕ) : Finite (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  obtain ⟨CX, hX, heX, huX, hcX, hiX⟩ := exceptionalSiteOriginComparison O ell X S.PX
  obtain ⟨CY, hY, heY, _huY, _hcY, _hiY⟩ := exceptionalSiteOriginComparison O ell Y S.PY
  obtain ⟨CZ, hZ, _heZ, _huZ, _hcZ, _hiZ⟩ :=
    exceptionalSiteOriginComparison O ell c.Z S.PZ
  obtain ⟨P, R, hcomparison, hleft, hfiniteLeft, hfiniteComparison, hfiniteBound,
    hcomparisonEvaluation⟩ := exceptionalProperOpenOriginComparison G CX CY CZ hX hY hZ
  have horigin (M) (hM : CX.origin M) :
      IsIso ((exceptionalSystemOriginComparison R).app M) := by
    obtain ⟨a, ha⟩ := hM.1
    have := hcomparison (CX.image.system.direct.obj M) ⟨a, hX.directBound a M ha⟩
    have := hX.counit M hM
    let e := asIso ((exceptionalSystemComparison R).app
        (CX.image.system.direct.obj M)) ≪≫
      ((Functor.associator CX.image.system.direct CX.image.system.inverse
        (exceptionalProSupport P)).symm.app M) ≪≫
      asIso ((exceptionalProSupport P).map (CX.image.system.adjunction.counit.app M)) ≪≫
      (Functor.leftUnitor (exceptionalProSupport P)).app M
    change IsIso e.hom
    infer_instance
  have hright (N) (hN : CY.origin N) :
      CX.origin ((exceptionalSystemRight G CX CY).obj N) := by
    obtain ⟨a, ha⟩ := hN.1
    obtain ⟨d, hd⟩ := G.property.2.2.2.2.2.2.2.2.2.2.1
    exact hX.inverseOrigin _ ⟨a - d, hd a _ (hY.directBound a N ha)⟩
  let adj := makeOriginAdjunction G.adjunction
    CX.image.system.adjunction CY.image.system.adjunction
    (exceptionalProSupport P) CX.origin CY.origin (exceptionalSystemOriginComparison R)
    hleft hright horigin hX.counit (fun N hN ↦ by
      obtain ⟨a, ha⟩ := hN.1
      obtain ⟨d, hd⟩ := G.property.2.2.2.2.2.2.2.2.2.2.1
      exact hX.unit _ ⟨a - d, hd a _ (hY.directBound a N ha)⟩)
  let finiteAdj (n : ℕ) := makeOriginAdjunction (G.levelAdjunction n)
    (CX.image.level n).adjunction (CY.image.level n).adjunction
    (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct)
    (CX.levelOrigin n) (CY.levelOrigin n) (exceptionalSystemLevelOriginComparison R n)
    (hfiniteLeft n)
    (fun N hN ↦ hiX n _ (hfiniteBound n N hN))
    (hfiniteComparison n) (hcX n)
    (fun N hN ↦ huX n _ (hfiniteBound n N hN))
  obtain ⟨la, ra, ls, rs, sx, sy, hle, hre, hll, hrl⟩ :=
    exceptionalProOriginExactLinear G CX CY CZ P
  let record : ExceptionalSystemTransportData G CX CY CZ P R := {
    siteX := hX
    siteY := hY
    siteZ := hZ
    systemAdjunction := adj
    finiteAdjunction := finiteAdj
    evaluationOriginX := heX
    evaluationOriginY := heY
    leftAdditive := la
    rightAdditive := ra
    leftShift := ls
    rightShift := rs
    scalarX := sx
    scalarY := sy }
  obtain ⟨hunit, hcounit, hquotient⟩ :=
    exceptionalOriginAdjunctionEvaluation G CX CY CZ P R record hcX hcomparisonEvaluation
  refine ⟨S, G, CX, CY, CZ, P, R, ⟨⟨record, ?_⟩⟩⟩
  exact ⟨hcomparison, horigin, hcomparisonEvaluation, hunit, hcounit, hquotient,
    hle, hre, hll, hrl, exceptionalSystemRight_normalized G CX CY hX hY,
    exceptionalSystemRight_lowerBound G CX CY hX hY⟩

end AlgebraicGeometry
