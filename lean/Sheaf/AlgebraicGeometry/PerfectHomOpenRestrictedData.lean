/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectHomPushPullCocone
public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
import Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedDataExists

/-! # Unshifted restriction of a representing pullback Hom cocone

Source: Stacks Project, Cohomology, Tags 079W and 08FE; perfect.tex, Tag 09RE.
(blueprint: lem-pc-perfect-hom-open-restricted-data).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section

variable {S Y T : Scheme.{u}} (s : Y ⟶ S) (B : Y.Opens) (r : T ⟶ S)
  [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The cartesian map induced by the open inclusion, constructed by pullback.map.
Source: Stacks Tag 09RE (blueprint: lem-pc-perfect-hom-open-restricted-data). -/
def perfectHomOpenBaseChangeMap : pullback (B.ι ≫ s) r ⟶ pullback s r :=
  pullback.map (B.ι ≫ s) r s r B.ι (𝟙 T) (𝟙 S) (by simp) (by simp)

/-- The pullback comparison on the cartesian open square, fixed by the supplied
open pullback adjunction and the existing counit-pinned composition comparisons.
Source: Stacks Tags 079W and 09RE (blueprint: lem-pc-perfect-hom-open-restricted-data). -/
def perfectHomOpenPullbackComparison
    (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι) :
    derivedPullback (pullback.fst s r) ⋙ derivedPullback (perfectHomOpenBaseChangeMap s B r) ≅
      schemeMVDerivedRestriction Y B ⋙ derivedPullback (pullback.fst (B.ι ≫ s) r) := by
  let σ : schemeMVDerivedRestriction Y B ≅ derivedPullback B.ι :=
    (conjugateIsoEquiv a (schemeMVAdjunction Y B)).symm (Iso.refl _)
  have he : perfectHomOpenBaseChangeMap s B r ≫ pullback.fst s r =
      pullback.fst (B.ι ≫ s) r ≫ B.ι := by
    simp [perfectHomOpenBaseChangeMap, pullback.map]
  exact perfectHomComposition (perfectHomOpenBaseChangeMap s B r) (pullback.fst s r) ≪≫
    eqToIso (congrArg (fun f ↦ derivedPullback f) he) ≪≫
    (perfectHomComposition (pullback.fst (B.ι ≫ s) r) B.ι).symm ≪≫
    Functor.isoWhiskerRight σ.symm (derivedPullback (pullback.fst (B.ι ≫ s) r))

/-- Restrict a pullback Hom along the explicit cartesian map and conjugate it by
perfectHomOpenPullbackComparison. No existence witness is selected here.
Source: Stacks Tag 09RE (blueprint: lem-pc-perfect-hom-open-restricted-data). -/
def perfectHomOpenRestrictionMap
    (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    {M Q : schemeDerivedCategory Y}
    (f : (derivedPullback (pullback.fst s r)).obj M ⟶
      (derivedPullback (pullback.fst s r)).obj Q) :
    (derivedPullback (pullback.fst (B.ι ≫ s) r)).obj
        ((schemeMVDerivedRestriction Y B).obj M) ⟶
      (derivedPullback (pullback.fst (B.ι ≫ s) r)).obj
        ((schemeMVDerivedRestriction Y B).obj Q) :=
  (perfectHomOpenPullbackComparison s B r a).inv.app M ≫
    (derivedPullback (perfectHomOpenBaseChangeMap s B r)).map f ≫
    (perfectHomOpenPullbackComparison s B r a).hom.app Q

end

noncomputable section

/-- The restricted stage and limit equivalences are the explicit restriction maps.
The proof transports the original representing equivalences across the canonical
open restriction and pullback composition comparisons. Naturality of the
adjunction equivalences gives the stage equation, and the identical argument for
the cocone apex gives the limit equation. This is the mate calculation for the
comparison used in `perfectHomOpenRestrictionMap`.
(blueprint: lem-pc-perfect-hom-open-restricted-data-pinned). -/
theorem perfect_hom_open_restricted_data_pinned
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens) (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    (Q : schemeDerivedCategory Y) (F : Set.Ici i ⥤ schemeDerivedCategory Y)
    (d : Cocone F)
    (h : PerfectHomPushPullData R c s Q F d)
    (hB : PerfectHomPushPullData R c (B.ι ≫ s)
      ((schemeMVDerivedRestriction Y B).obj Q)
      (F ⋙ schemeMVDerivedRestriction Y B)
      ((schemeMVDerivedRestriction Y B).mapCocone d)) :
    (∀ (j : Set.Ici i) (M : schemeDerivedCategory Y) (f : M ⟶ F.obj j),
      hB.stageEquiv j ((schemeMVDerivedRestriction Y B).obj M)
          ((schemeMVDerivedRestriction Y B).map f) =
        perfectHomOpenRestrictionMap s B
          (Spec.map (R.map (homOfLE j.property))) a (h.stageEquiv j M f)) ∧
    (∀ (M : schemeDerivedCategory Y) (f : M ⟶ d.pt),
      hB.limitEquiv ((schemeMVDerivedRestriction Y B).obj M)
          ((schemeMVDerivedRestriction Y B).map f) =
        perfectHomOpenRestrictionMap s B (Spec.map (c.ι.app i)) a
          (h.limitEquiv M f)) := by sorry

/-- Exact open restriction carries a representing pullback Hom cocone to a representing
cocone for the restricted base scheme. There is no shift or outer open direct image
in this conclusion. The two additional equations tie its Hom equivalences on restricted
testing objects to the concrete perfectHomOpenRestrictionMap. These equations specify
which restriction of the original representing equivalences is used.

Source: Stacks Project, Cohomology, Tags 079W and 08FE; perfect.tex, Tag 09RE.
(blueprint: lem-pc-perfect-hom-open-restricted-data).

Proof: For the supplied adjunction a, set sigma =
(conjugateIsoEquiv a (schemeMVAdjunction Y B)).symm (Iso.refl _).
Thus sigma : L -> LB.ι* is the mate of the identity on the common right adjoint.
For any r : T -> Spec(R_i), let b_r be perfectHomOpenBaseChangeMap s B r,
p = pullback.fst s r and p' = pullback.fst (B.ι followed by s) r. Its fst equation
is b_r followed by p = p' followed by B.ι. The concrete comparison kappa_r is
perfectHomComposition b_r p, followed by eqToIso of that fst equation, followed
by (perfectHomComposition p' B.ι).symm, followed by sigma.symm whiskered by Lp'*.
The restriction of a Hom f is kappa_r(M).inv followed by Lb_r*(f), followed by
kappa_r(Q).hom: this is exactly perfectHomOpenRestrictionMap s B r a f.

Write L for restriction to B, pi_j for the original projection, A_j for
Lpi_j*, and J_j = Rpi_j* A_j Q. Choose the derived adjunction a_j of Tag 079W
compatible with the fixed pullback counit and direct-image unit. Its equivalence is
eta_j(M) : Hom(A_j M,A_j Q) -> Hom(M,J_j). Define
rho_j = eta_j(F_j)(h.stageEquiv j F_j (id)). Its inverse is
(h.stageEquiv j J_j).symm (eta_j(J_j).symm (id)). Naturality in M of eta_j and
h.stageEquiv proves eta_j(M)(h.stageEquiv j M f) = f followed by rho_j.
Applying this identity to rho_j and its proposed inverse proves both inverse laws.
Do the same at the apex, using h.limitEquiv and h.limitNatural.

Put U_j = pi_j inverse-image B and v_j = pi_j restricted to B. Restriction gives
L rho_j : L F_j -> L J_j. Compose it with the component of the explicitly
constructed schemeMVOpenRestrictionComparison pi_j B at A_j Q. This identifies
L J_j with Rv_j* (restriction to U_j of A_j Q). The cartesian square identifies
U_j.toScheme with the pullback of B.ι followed by s along the same ring map:
the forward map is pullback.lift of v_j and the restricted second projection;
the inverse is pullback.lift of the open inclusion and second projection, factored
through U_j. The two inverse laws follow by pullback.hom_ext and the open inclusion
monomorphism. Denote this isomorphism by k_j. The counit-pinned pullback composition
isomorphisms on the square give
restriction to U_j of A_j Q = Lk_j* (Lpi'_j* (L Q)), up to natural isomorphism.
Here restriction along an open inclusion is its exact derived pullback, by the
underived restriction/tensor-pullback adjunction and its derived universal property.
The inverse-image comparison is the composite of these two composition
isomorphisms and the equality of the square's morphisms, not an arbitrary iso.
Transport direct image across k_j using the right-derived composition comparison
and the identity comparison; k_j is an isomorphism, so its adjunction counit is
invertible. We obtain a representing isomorphism sigma_j : L F_j ->
Rpi'_j* (Lpi'_j* (L Q)). Repeat this construction at the apex to obtain sigma_inf.

For every M on B, define the new stage equivalence by postcomposition with sigma_j,
followed by the inverse Hom equivalence of the restricted projection adjunction.
Define its apex equivalence in the same way with sigma_inf. Adjunction naturality
and associativity prove the two testing-object naturality equations. Restriction
is exact and preserves quasi-coherent sheaves, hence stageQCoh and limitQCoh.

For j <= k, define the original representing transition J_j -> J_k by applying
eta_k(J_j) to perfectStageMap R s j.property hjk (eta_j(J_j).symm (id)).
The h.stageMap identity at id says F.map(j,k) followed by rho_k equals rho_j
followed by this transition. At the apex, the analogous formula using
perfectLimitMap gives the corresponding equation for the cocone leg.
Apply L to these equations. Naturality of the sectionwise restriction comparison,
and its determining right-derived unit equation, identify the resulting
transitions with the representing transitions for the restricted projections.
The pullback composition associativity equation identifies the square's two
pasted inverse-image comparisons; after applying the Hom adjunction, adjacent
comparison and inverse components cancel. The remaining composites are exactly
perfectStageMap R (B.ι followed by s) and perfectLimitMap R c (B.ι followed by s).
Thus postcomposition by L(F.map(j,k)) and L(d.ι.app j) satisfies the required
stageMap and limitMap fields for every M. For the additional two equations, the
original representing identity eta(M)(h.stageEquiv M f) = f followed by rho
is restricted to B. The mate identities for sigma and the restriction comparison
identify this restricted adjunction formula with kappa(M).inv followed by Lb*(f)
followed by kappa(Q).hom. This is the displayed equation with the specified
perfectHomOpenRestrictionMap, at a stage and at the apex. Package these fields
and equations. Since L has fully faithful right adjoint, its counit is invertible,
so every testing object on B is isomorphic to L of its open direct image; testing
object naturality extends these pinned equations to all objects on B.
The argument uses neither compactness nor perfectness. For the empty open every
Hom set is a singleton; for the full open the same comparison formulas apply.
For Q = 0, representability makes every representing object zero, so the
construction still works. No arbitrary existence witness is used in a definition. -/
theorem perfect_hom_open_restricted_data
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens)
    (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    (Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F)
    (h : PerfectHomPushPullData R c s Q F d) :
    let L := schemeMVDerivedRestriction Y B
    ∃ hB : PerfectHomPushPullData R c (B.ι ≫ s) (L.obj Q) (F ⋙ L) (L.mapCocone d),
      (∀ (j : Set.Ici i) (M : schemeDerivedCategory Y) (f : M ⟶ F.obj j),
        hB.stageEquiv j (L.obj M) (L.map f) =
          perfectHomOpenRestrictionMap s B (Spec.map (R.map (homOfLE j.property))) a
            (h.stageEquiv j M f)) ∧
      (∀ (M : schemeDerivedCategory Y) (f : M ⟶ d.pt),
        hB.limitEquiv (L.obj M) (L.map f) =
          perfectHomOpenRestrictionMap s B (Spec.map (c.ι.app i)) a (h.limitEquiv M f)) := by
  classical
  let L := schemeMVDerivedRestriction Y B
  obtain ⟨hB⟩ := perfect_hom_open_restricted_data_exists R c s B Q F d h
  exact ⟨hB, perfect_hom_open_restricted_data_pinned R c s B a Q F d h hB⟩

end
end AlgebraicGeometry
