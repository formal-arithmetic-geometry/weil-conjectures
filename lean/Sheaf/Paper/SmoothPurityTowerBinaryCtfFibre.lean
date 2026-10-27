/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q79
-/
module

public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.Paper.SmoothPurityTowerShriekLevels
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Sheaf.CategoryTheory.RingedToposBinaryDescentDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.Paper.SmoothPurityTowerFibreProjections
import Sheaf.Paper.ProEtaleBinaryCtfLocalModels

/-! # Binary open descent for constructible finite-Tor coefficient towers

Source: blueprint, sec-smooth-purity, det-sp-tower-gluing, Gluing and Uniformity;
its retained corrected fibre construction, step 8
(blueprint: lem-sp-tower-binary-ctf-fibre).

We use the published ordinary ringed sequence-site presentation `SpTowerShriek.D`.
`Base.realization` identifies its abelian category with `spCoefficientTowers`, fixing
all sections and quotient transitions. Thus these are ordinary derived towers, not
inverse systems in derived categories. The coefficient exponent at index n is n+1.
The open slice is the constant representable subterminal, as in
`sequenceSiteOpenExtension`; `Scheme.ProEt.sliceEquiv` identifies the localized site
with the small pro-etale site of the open subscheme. Its constant-section ring
identifications preserve the actual quotient maps. `Operations.geometry` retains
these canonical inverse images and direct images, including their adjunctions.

The level predicates below are precisely those of `sk-def-sp-normalized-towers`,
with the witnessing intervals displayed rather than existentially hidden. In
particular no normalization or constructibility of the middle direct images occurs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerBinaryCtfFibre

open SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : Base l E) (o : Operations l E b)

/-- Open restriction in the published ordinary derived tower category.
Source: blueprint, Gluing, j_D^* (blueprint: lem-sp-tower-binary-ctf-fibre). -/
abbrev restriction {Z : Scheme.{u}} (U : Z.Opens) := pull l E b (o.geometry U.ι)

/-- Restriction from an open V to a smaller open U.
Source: blueprint, Gluing, restriction to the overlap
(blueprint: lem-sp-tower-binary-ctf-fibre). -/
abbrev restrictionBetween {Z : Scheme.{u}} {U V : Z.Opens} (h : U ≤ V) :=
  pull l E b (o.geometry (Z.homOfLE h))

/-- The canonical composition comparison, localized from ordinary restriction.
Its equality transport is the equality of the actual open inclusion maps.
Source: blueprint, Gluing, iterated restrictions
(blueprint: lem-sp-tower-binary-ctf-fibre). -/
def restrictionComp {Z : Scheme.{u}} {U V : Z.Opens} (h : U ≤ V) :
    restriction l E b o U ≅ restriction l E b o V ⋙ restrictionBetween l E b o h :=
  (o.comp (Z.homOfLE h) V.ι ≪≫
    eqToIso (congrArg (fun f ↦ pull l E b (o.geometry f)) (Z.homOfLE_ι h))).symm

/-- Evaluation of a selected restriction isomorphism, using the canonical comparison.
This supplies the selected finite local model, including its action on morphisms;
it is not an independently chosen level isomorphism.
Source: blueprint, Gluing and Uniformity, evaluated local models
(blueprint: lem-sp-tower-binary-ctf-fibre). -/
def evaluatedRestrictionIso {Z : Scheme.{u}} (U : Z.Opens)
    {G : D l E Z} {P : D l E U.toScheme}
    (a : (restriction l E b o U).obj G ≅ P) (n : ℕ) :
    (proEtaleConstantRingDerivedPullback (R l E n) U.ι).obj ((Ev l E Z n).obj G) ≅
      (Ev l E U.toScheme n).obj P :=
  ((o.geometry U.ι).pullEvaluation n).symm.app G ≪≫ (Ev l E U.toScheme n).mapIso a

/-- Exact evaluation in the fixed-scalar coordinates of the recorded intrinsic
constructibility predicate. The inverse realization changes only the presentation
of the constant scalar action, not the coefficient ring or the module sheaf.
Source: blueprint, finite-level convention and intrinsic constructibility
(blueprint: lem-sp-tower-binary-ctf-fibre). -/
def fixedLevel (T : Scheme.{u}) (n : ℕ) :
    D l E T ⥤ DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))) :=
  Ev l E T n ⋙ (sfIntrinsicModuleEquivalence T (R l E n)).inverse.mapDerivedCategory

private theorem restriction_mate
    {D DU DW : Type*} [Category D] [Category DU] [Category DW]
    {rU : D ⥤ DU} {rW : D ⥤ DW} {rUW : DU ⥤ DW}
    {RU : DU ⥤ D} {RW : DW ⥤ D}
    (adjU : rU ⊣ RU) (adjW : rW ⊣ RW) (comp : rW ≅ rU ⋙ rUW)
    {G : D} {A : DU} (k : G ⟶ RU.obj A) :
    (adjW.homEquiv G (rUW.obj A))
        (comp.hom.app G ≫ rUW.map (rU.map k ≫ adjU.counit.app A)) =
      k ≫ restrictionAdjunctionMap adjU adjW comp A := by
  have hn := comp.hom.naturality k
  change rW.map k ≫ comp.hom.app _ =
    comp.hom.app G ≫ rUW.map (rU.map k) at hn
  rw [Functor.map_comp, ← Category.assoc, ← hn, Category.assoc]
  exact adjW.homEquiv_naturality_left k _

set_option backward.isDefEq.respectTransparency false in
private theorem fibre_compatibility
    {D DU DV DW : Type*} [Category D] [Category DU] [Category DV] [Category DW]
    [Preadditive D] [Preadditive DW] [HasBinaryBiproducts D]
    {rU : D ⥤ DU} {rV : D ⥤ DV} {rW : D ⥤ DW}
    {rUW : DU ⥤ DW} {rVW : DV ⥤ DW}
    {RU : DU ⥤ D} {RV : DV ⥤ D} {RW : DW ⥤ D}
    (adjU : rU ⊣ RU) (adjV : rV ⊣ RV) (adjW : rW ⊣ RW)
    (compU : rW ≅ rU ⋙ rUW) (compV : rW ≅ rV ⋙ rVW)
    {A : DU} {B : DV} (c : rUW.obj A ≅ rVW.obj B)
    {G : D} (f : G ⟶ RU.obj A ⊞ RV.obj B)
    (hz : f ≫ biprod.desc
      (restrictionAdjunctionMap adjU adjW compU A ≫ RW.map c.hom)
      (-restrictionAdjunctionMap adjV adjW compV B) = 0) :
    compU.hom.app G ≫
        rUW.map (rU.map (f ≫ biprod.fst) ≫ adjU.counit.app A) ≫ c.hom =
      compV.hom.app G ≫
        rVW.map (rV.map (f ≫ biprod.snd) ≫ adjV.counit.app B) := by
  apply (adjW.homEquiv G (rVW.obj B)).injective
  rw [← Category.assoc, adjW.homEquiv_naturality_right]
  erw [restriction_mate adjU adjW compU (f ≫ biprod.fst),
    restriction_mate adjV adjW compV (f ≫ biprod.snd)]
  have hd : biprod.desc
      (restrictionAdjunctionMap adjU adjW compU A ≫ RW.map c.hom)
      (-restrictionAdjunctionMap adjV adjW compV B) =
      biprod.fst ≫ (restrictionAdjunctionMap adjU adjW compU A ≫ RW.map c.hom) -
        biprod.snd ≫ restrictionAdjunctionMap adjV adjW compV B := by
    apply biprod.hom_ext'
    · simp
    · simp
  rw [hd, Preadditive.comp_sub, sub_eq_zero] at hz
  simpa only [Category.assoc] using hz

/-- Binary open fibre descent retains the same uniform cohomological and Tor intervals
and intrinsic constructibility, without requiring normalized towers.

Source: blueprint, det-sp-tower-gluing, corrected Gluing and Uniformity paragraphs,
retained nineteen-step proof, step 8 (blueprint: lem-sp-tower-binary-ctf-fibre).

Proof:
1. Apply lem-pur-sequence-site-open-extension to the three open inclusions. The
constant representable subterminals give the open slices of the sequence topos.
By lem-weil-proetale-weakly-etale-localization their base sites and constant rings
are the pro-etale sites and rings of the three opens. The ring identifications
are identity on constant sections, hence commute with every quotient map. By
det-sp-coefficient-towers-abelian these are exactly the strict semilinear towers.
The two subterminals cover the terminal object and intersect in the overlap.
2. Apply clause (1) of lem-sp-ringed-topos-binary-descent to P,Q,c in that ringed
topos. It gives G, the displayed distinguished fibre triangle, and restriction
isomorphisms satisfying the overlap equation. Its middle terms are ambient
right derived direct images; no constructibility of them is used. G is the first
vertex, not a shift of that vertex.
3. Restriction is exact by lem-pur-site-restriction-module-adjunction-exact and
evaluation is exact by det-sp-coefficient-towers-abelian. Both orders applied to
a tower complex have degree-i term (C_n^i)|_D and the same differential. Their
identity descends to the ordinary derived categories. Thus evaluation of a_U,a_V,
as explicitly constructed by evaluatedRestrictionIso, supplies the chosen finite
local models and the evaluated overlap equation. Exactness also identifies the
restrictions of each cohomology sheaf with cohomology of the restriction.
4. A module sheaf whose restrictions to U,V vanish is zero: on every test object
the two pullbacks form a cover, and sheaf separatedness detects zero sections.
Apply this to each H^i(G_n) outside [a,b]. The local models give its vanishing
with the same a,b for every n.
5. For every module sheaf M in degree zero, apply the tensor pullback comparison
lem-weil-pbc-ringed-topoi-derived-tensor-pullback to either open localization.
Its structural ring map is an isomorphism, so derived pullback is exact
restriction. The restricted tensors are P_n tensor^L M|_U and Q_n tensor^L M|_V.
Their cohomology vanishes outside [s,t] by def-weil-proetale-tor-amplitude. The
zero test of step 4 proves this globally, for every M and every n.
6. For each n,i take finite immersed constructible strata for H^i(P_n) on U and
H^i(Q_n) on V. Put C=Z\\U with reduced closed structure. Keep the U-strata and
intersect the V-strata with C by base change. They form a finite disjoint locally
closed partition of Z, constructible since Z is Noetherian. Base change the
pro-etale trivializing covers, using def-weil-proetale-inverse-image; the finite
constant module values pull back unchanged by
lem-sfb-geometric-inverse-image-constant-module. This witnesses intrinsic
constructibility as in def-weil-proetale-constructible-sheaf. For empty Z take
one empty stratum and the zero constant module.
7. Steps 4--6 give exactly the level predicates and common intervals defining
C_Z in sk-def-sp-normalized-towers. The selected isomorphisms are those of
steps 2--3. No reduction map is required to be invertible. -/
theorem binary_ctf_fibre
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] (_hlp : l ≠ p)
    (Z : Over (Spec (CommRingCat.of k)))
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (U V : Z.left.Opens) (_hcover : U ⊔ V = ⊤)
    (a₀ b₀ s t : ℤ) (_hab : a₀ ≤ b₀) (_hst : s ≤ t)
    (P : D l E U.toScheme) (Q : D l E V.toScheme)
    (_hP : ∀ n : ℕ,
      (∀ i : ℤ, IsConstructibleProEtaleFixedModuleSheaf U.toScheme
        (ULift.{u + 1} (R l E n))
        ((DerivedCategory.homologyFunctor _ i).obj ((fixedLevel l E b U.toScheme n).obj P))) ∧
      (∀ i : ℤ, i < a₀ ∨ b₀ < i → IsZero
        ((DerivedCategory.homologyFunctor _ i).obj ((Ev l E U.toScheme n).obj P))) ∧
      HasProEtaleTorAmplitude U.toScheme (R l E n) ((Ev l E U.toScheme n).obj P) s t)
    (_hQ : ∀ n : ℕ,
      (∀ i : ℤ, IsConstructibleProEtaleFixedModuleSheaf V.toScheme
        (ULift.{u + 1} (R l E n))
        ((DerivedCategory.homologyFunctor _ i).obj ((fixedLevel l E b V.toScheme n).obj Q))) ∧
      (∀ i : ℤ, i < a₀ ∨ b₀ < i → IsZero
        ((DerivedCategory.homologyFunctor _ i).obj ((Ev l E V.toScheme n).obj Q))) ∧
      HasProEtaleTorAmplitude V.toScheme (R l E n) ((Ev l E V.toScheme n).obj Q) s t)
    (c : (restrictionBetween l E b o (inf_le_left : U ⊓ V ≤ U)).obj P ≅
      (restrictionBetween l E b o (inf_le_right : U ⊓ V ≤ V)).obj Q) :
    ∃ (G : D l E Z.left)
      (f : G ⟶ (push l E b (o.geometry U.ι)).obj P ⊞
        (push l E b (o.geometry V.ι)).obj Q)
      (d : (push l E b (o.geometry U.ι)).obj P ⊞
        (push l E b (o.geometry V.ι)).obj Q ⟶
        (push l E b (o.geometry (U ⊓ V).ι)).obj
          ((restrictionBetween l E b o (inf_le_right : U ⊓ V ≤ V)).obj Q))
      (δ : (push l E b (o.geometry (U ⊓ V).ι)).obj
        ((restrictionBetween l E b o (inf_le_right : U ⊓ V ≤ V)).obj Q) ⟶
          (shiftFunctor _ (1 : ℤ)).obj G)
      (aU : (restriction l E b o U).obj G ≅ P)
      (aV : (restriction l E b o V).obj G ≅ Q),
      d = biprod.desc
        (restrictionAdjunctionMap (adjunction l E b (o.geometry U.ι))
          (adjunction l E b (o.geometry (U ⊓ V).ι))
          (restrictionComp l E b o (inf_le_left : U ⊓ V ≤ U)) P ≫
            (push l E b (o.geometry (U ⊓ V).ι)).map c.hom)
        (-restrictionAdjunctionMap (adjunction l E b (o.geometry V.ι))
          (adjunction l E b (o.geometry (U ⊓ V).ι))
          (restrictionComp l E b o (inf_le_right : U ⊓ V ≤ V)) Q) ∧
      Triangle.mk f d δ ∈ distTriang _ ∧
      aU.hom = (restriction l E b o U).map f ≫
        (restriction l E b o U).map biprod.fst ≫
          (adjunction l E b (o.geometry U.ι)).counit.app P ∧
      aV.hom = (restriction l E b o V).map f ≫
        (restriction l E b o V).map biprod.snd ≫
          (adjunction l E b (o.geometry V.ι)).counit.app Q ∧
      (restrictionComp l E b o (inf_le_left : U ⊓ V ≤ U)).hom.app G ≫
          (restrictionBetween l E b o (inf_le_left : U ⊓ V ≤ U)).map aU.hom ≫ c.hom =
        (restrictionComp l E b o (inf_le_right : U ⊓ V ≤ V)).hom.app G ≫
          (restrictionBetween l E b o (inf_le_right : U ⊓ V ≤ V)).map aV.hom ∧
      (∀ n : ℕ,
        (∀ i : ℤ, IsConstructibleProEtaleFixedModuleSheaf Z.left
          (ULift.{u + 1} (R l E n))
          ((DerivedCategory.homologyFunctor _ i).obj ((fixedLevel l E b Z.left n).obj G))) ∧
        (∀ i : ℤ, i < a₀ ∨ b₀ < i → IsZero
          ((DerivedCategory.homologyFunctor _ i).obj ((Ev l E Z.left n).obj G))) ∧
        HasProEtaleTorAmplitude Z.left (R l E n) ((Ev l E Z.left n).obj G) s t) := by
  let d := biprod.desc
    (restrictionAdjunctionMap (adjunction l E b (o.geometry U.ι))
      (adjunction l E b (o.geometry (U ⊓ V).ι))
      (restrictionComp l E b o (inf_le_left : U ⊓ V ≤ U)) P ≫
        (push l E b (o.geometry (U ⊓ V).ι)).map c.hom)
    (-restrictionAdjunctionMap (adjunction l E b (o.geometry V.ι))
      (adjunction l E b (o.geometry (U ⊓ V).ι))
      (restrictionComp l E b o (inf_le_right : U ⊓ V ≤ V)) Q)
  obtain ⟨G, f, δ, hT⟩ := distinguished_cocone_triangle₁ d
  obtain ⟨hU, hV⟩ := tower_fibre_projections l E b o Z.left U V P Q c G f δ hT
  let := hU
  let := hV
  let aU := asIso ((restriction l E b o U).map f ≫
    (restriction l E b o U).map biprod.fst ≫
      (adjunction l E b (o.geometry U.ι)).counit.app P)
  let aV := asIso ((restriction l E b o V).map f ≫
    (restriction l E b o V).map biprod.snd ≫
      (adjunction l E b (o.geometry V.ι)).counit.app Q)
  refine ⟨G, f, d, δ, aU, aV, rfl, hT, rfl, rfl, ?_, ?_⟩
  · have hz := comp_distTriang_mor_zero₁₂ _ hT
    simpa only [aU, aV, asIso_hom, Functor.map_comp, Category.assoc] using
      fibre_compatibility (adjunction l E b (o.geometry U.ι))
        (adjunction l E b (o.geometry V.ι))
        (adjunction l E b (o.geometry (U ⊓ V).ι))
        (restrictionComp l E b o (inf_le_left : U ⊓ V ≤ U))
        (restrictionComp l E b o (inf_le_right : U ⊓ V ≤ V)) c f hz
  · have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
    have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
    have : IsNoetherian Z.left := ⟨⟩
    intro n
    exact proEtale_binary_ctf_of_local_models Z.left U V _hcover (R l E n) a₀ b₀ s t
      ((Ev l E Z.left n).obj G) ((Ev l E U.toScheme n).obj P)
      ((Ev l E V.toScheme n).obj Q)
      (evaluatedRestrictionIso l E b o U aU n)
      (evaluatedRestrictionIso l E b o V aV n) (_hP n) (_hQ n)

end AlgebraicGeometry.ProEtale.SpTowerBinaryCtfFibre

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
