/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapCompositeStageMap
import Sheaf.AlgebraicGeometry.PerfectOverlapCompositeCounitFactor
import Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionComponent
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare
import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons
import Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence

/-! # A component of composite overlap compatibility
Source: Stacks Project, Tags 08DW and 0D5S.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local irreducible] perfectHomComposition
attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
private theorem combineComponents {𝒟 : Type*} [Category 𝒟]
    {R P Q G H : 𝒟} (stage : R ⟶ G) (eta : R ⟶ Q) (t : P ≅ Q)
    (d : P ⟶ G) (chi : G ⟶ H) (w : Q ⟶ H)
    (hf : stage = eta ≫ t.inv ≫ d) (hp : d ≫ chi = t.hom ≫ w) :
    stage ≫ chi = eta ≫ w := by
  rw [hf]
  simp only [Category.assoc]
  rw [hp, Iso.inv_hom_id_assoc]

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

/-- The constructed cartesian stage map satisfies the projection comparison.
Source: Stacks Project, Tags 08DW and 0D5S, composition comparisons in Tag 09RE.

Proof: Replace the three supplied isomorphisms by their specified constructors
using their equalities. Treat each Boolean branch with its open L and object
M. Expand the branch of `perfectOverlapCompositeStageMap` into its four
constructed factors. Separate the first factor, the stage pullback of the
open-site counit.

For the remaining factors, express exact overlap restriction by the pinned
inclusion-pullback comparison. Naturality moves the two inclusion comparisons
to the outside, where inverse-forward pairs cancel. The restricted scheme
square commutes after cancellation of the larger open immersion. The
factorizations of the two cartesian inverse isomorphisms followed by the
restricted projections agree by `hmap`; the outer projection equation is
`baseChangeMap_fst`. Apply the component associativity law of the fixed
pullback-composition family to each of the six faces of this prism. Cancel
the common invertible composition factors. More explicitly, write rL for the
restricted gk over L, jX and jK for the nested inclusions, fL for f restricted
to L, and j for W into L. With eY and eK the cartesian isomorphisms and pX,pK
the first projections, use the triples
(eY.inv followed by jX, rL, fL), (eY.inv, jX, rL),
(eY.inv, r, jK), (m, eK.inv, jK),
(m, eK.inv followed by jK, fL), and (m, pK, j).
The first two change the source path, the middle two cross hmap, and the last
two change the target path using baseChangeMap_fst. Postcompose by the common
invertible projection-composition factor, use naturality to move the local
composition through the first inclusion factor, and apply these six
associativity equations in that order; adjacent inverse pairs cancel.
This identifies the remaining
composite, followed by the projection comparison, with
`perfectOverlapDerivedPullbackTransport` followed by pullback of the fixed
stage-object map at f.

Precompose this equality by the separated site counit. The component formula
`perfectOverlapNaturalComparisonOfSquare_hom_app` identifies the counit
followed by that derived transport with eta. Associativity gives the claimed
equality, and the constructor equalities return sigma', eta' and chi'. The
argument uses isomorphisms and naturality only, so it includes empty and equal
opens and arbitrary unbounded objects. The local object identifications are
needed only to give the common overlap source its original interface.
(blueprint: lem-pc-perfect-overlap-projection-composition-component). -/
theorem perfectOverlapProjectionCompositionComponent
    {X Y K C T S : Scheme.{u}}
    (f : K ⟶ Y) (gk : X ⟶ K) (g : X ⟶ Y) (hgf : gk ≫ f = g)
    (pX : X ⟶ C) (pK : K ⟶ T) (pY : Y ⟶ S)
    (b : C ⟶ S) (q : T ⟶ S)
    (hg : IsPullback g pX pY b) (hf : IsPullback f pK pY q)
    (l : Over.mk b ⟶ Over.mk q)
    (U V : Y.Opens)
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (E : schemeDerivedCategory X)
    (φU : (derivedPullback (g ∣_ U)).obj A ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ U)).mapDerivedCategory.obj E)
    (φV : (derivedPullback (g ∣_ V)).obj B ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ V)).mapDerivedCategory.obj E) :
  let W := U ⊓ V
  let s := W.ι ≫ pY
  let r := gk.resLE (f ⁻¹ᵁ W) (g ⁻¹ᵁ W)
    (by rw [← Scheme.Hom.comp_preimage, hgf])
  let m := baseChangeMap s l
  let eY := ((isPullback_morphismRestrict g W).paste_vert hg).isoPullback
  let eK := ((isPullback_morphismRestrict f W).paste_vert hf).isoPullback
  ∀ hmap : eY.inv ≫ r = m ≫ eK.inv,
  let data := transportDataOfComposite f gk g hgf U V A B E φU φV
  let F : Bool → schemeDerivedCategory (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V).toScheme := fun a ↦
    if a then
      (schemeOpenOverlapRestriction K
        (homOfLE (inf_le_right : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V))).mapDerivedCategory.obj
        ((derivedPullback (f ∣_ V)).obj B)
    else
      (schemeOpenOverlapRestriction K
        (homOfLE (inf_le_left : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U))).mapDerivedCategory.obj
        ((derivedPullback (f ∣_ U)).obj A)
  let apex := perfectOverlapApexEquivalence g pX pY b hg U V
  let η := perfectOverlapNaturalComparisonOfSquare g f pX pK pY b q hg hf U V r m hmap
  let σ : ∀ a : Bool,
      (perfectOverlapStageEquivalence f pK pY q hf U V).functor.obj (F a) ≅
        (derivedPullback (pullback.fst s q)).obj
          (if a then (derivedPullback (Y.homOfLE (inf_le_right : W ≤ V))).obj B
          else (derivedPullback (Y.homOfLE (inf_le_left : W ≤ U))).obj A) := fun a ↦
    Bool.casesOn a
      ((perfectOverlapStageObjectIso f pK pY q hf U V U inf_le_left).app A)
      ((perfectOverlapStageObjectIso f pK pY q hf U V V inf_le_right).app B)
  ∀ (σ' : ∀ a : Bool,
      (perfectOverlapStageEquivalence f pK pY q hf U V).functor.obj (F a) ≅
        (derivedPullback (pullback.fst s q)).obj
          (if a then (derivedPullback (Y.homOfLE (inf_le_right : W ≤ V))).obj B
          else (derivedPullback (Y.homOfLE (inf_le_left : W ≤ U))).obj A))
    (η' : data.d.toDiagram.HW ⋙ apex.functor ≅
      (perfectOverlapStageEquivalence f pK pY q hf U V).functor ⋙ derivedPullback m)
    (χ' : derivedPullback (pullback.fst s b) ≅
      derivedPullback (pullback.fst s q) ⋙ derivedPullback m),
    σ' = σ → η' = η → χ' = perfectHomComparison s l →
  ∀ a : Bool,
    perfectOverlapCompositeStageMap f gk g hgf pX pY b hg U V A B E φU φV a ≫
        χ'.hom.app
          (if a then (derivedPullback (Y.homOfLE (inf_le_right : W ≤ V))).obj B
          else (derivedPullback (Y.homOfLE (inf_le_left : W ≤ U))).obj A) =
      η'.hom.app (F a) ≫ (derivedPullback m).map (σ' a).hom := by
  intro W s r m eY eK hmap data F apex η σ σ' η' χ' hσ hη hχ a
  have hfactor := perfectOverlapCompositeCounitFactor f gk g hgf pX pK pY b q
    hg hf l U V A B E φU φV hmap a
  have hprojection := perfectOverlapTailProjectionComponent f gk g hgf pX pK pY b q
    hg hf l U V A B E φU φV hmap a
  dsimp only [η, r, m, s, W] at hη
  dsimp only [σ, s, W] at hσ
  dsimp only [s, W] at hχ
  erw [← hη] at hfactor
  erw [← hσ, ← hχ] at hprojection
  exact combineComponents _ _
    ((perfectOverlapStageTransport g f pX pK pY b q hg hf U V r m hmap).app (F a))
    _ _ _ hfactor hprojection

end AlgebraicGeometry
