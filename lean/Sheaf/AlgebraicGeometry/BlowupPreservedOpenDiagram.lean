module

public import WeilConjectures.Blowup.FlatBaseChange
public import WeilConjectures.Compactification.FiniteTypeExtension
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
import WeilConjectures.Blowup.Complement

/-!
# Preserved opens and closed immersions in flat blowup base change

Source: Stacks Project, Divisors, Tags 0805 and 02OS (1); Schemes, Tags
01JU, 01JR and 01JX; Morphisms, Tag 01QR
(blueprint: lem-trf-blowup-base-change-preserved-open-diagram).

The auxiliary abbreviations only name the fibre products and projections of the
statement. All comparison isomorphisms in the theorem are characterized by their
projections. The upstream blowup comparison already puts the blowup factor first.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData.BlowupPreservedOpenDiagram

/-- The map `T = Z ×_X P → X` through `P`.
Source: Stacks Tag 01JX (blueprint: lem-trf-blowup-base-change-preserved-open-diagram). -/
noncomputable abbrev ambientMap {X Z : Scheme.{u}} (I : X.IdealSheafData) (i : Z ⟶ X) :=
  pullback.snd i I.blowupMap ≫ I.blowupMap

/-- The ambient scheme `T_W = T ×_X W`.
Source: Stacks Tag 01JX (blueprint: lem-trf-blowup-base-change-preserved-open-diagram). -/
noncomputable abbrev ambientBase {X Z W : Scheme.{u}} (I : X.IdealSheafData)
    (i : Z ⟶ X) (v : W ⟶ X) :=
  pullback (ambientMap I i) v

/-- The projection `p : T_W → P ×_X W`, using the canonical pullback pasting isomorphism.
Source: Stacks Tag 01JX (blueprint: lem-trf-blowup-base-change-preserved-open-diagram). -/
noncomputable abbrev ambientProjection {X Z W : Scheme.{u}} (I : X.IdealSheafData)
    (i : Z ⟶ X) (v : W ⟶ X) :=
  (pullbackRightPullbackFstIso I.blowupMap v (pullback.snd i I.blowupMap)).inv ≫
    pullback.snd (pullback.snd i I.blowupMap) (pullback.fst I.blowupMap v)

/-- The other ambient scheme `T̂ = Z_W ×_W Q`.
Source: Stacks Tag 01JX (blueprint: lem-trf-blowup-base-change-preserved-open-diagram). -/
noncomputable abbrev pulledAmbient {X Z W : Scheme.{u}} (I : X.IdealSheafData)
    (i : Z ⟶ X) (v : W ⟶ X) :=
  pullback (pullback.snd i v) (I.comap v).blowupMap

/-- The map `T̂ → W` through `Z_W`.
Source: Stacks Tag 01JX (blueprint: lem-trf-blowup-base-change-preserved-open-diagram). -/
noncomputable abbrev pulledAmbientMap {X Z W : Scheme.{u}} (I : X.IdealSheafData)
    (i : Z ⟶ X) (v : W ⟶ X) :=
  pullback.fst (pullback.snd i v) (I.comap v).blowupMap ≫ pullback.snd i v

/-- The open `T̂ ×_W U_W`.
Source: Stacks Tag 01JR (blueprint: lem-trf-blowup-base-change-preserved-open-diagram). -/
noncomputable abbrev sourceOpen {X Z W : Scheme.{u}} (I : X.IdealSheafData)
    (i : Z ⟶ X) (v : W ⟶ X) :=
  pullback (pulledAmbientMap I i v) (Scheme.Opens.ι (I.comap v).support.compl)

/-- The map `T ×_X U → X` through U.
Source: Stacks Tag 01JR (blueprint: lem-trf-blowup-base-change-preserved-open-diagram). -/
noncomputable abbrev restrictedAmbientMap {X Z : Scheme.{u}} (I : X.IdealSheafData)
    (i : Z ⟶ X) :=
  pullback.snd (ambientMap I i) (Scheme.Opens.ι I.support.compl) ≫
    Scheme.Opens.ι I.support.compl

/-- The open `(T ×_X U) ×_X W`, with its displayed fibre-product order.
Source: Stacks Tag 01JR (blueprint: lem-trf-blowup-base-change-preserved-open-diagram). -/
noncomputable abbrev targetOpen {X Z W : Scheme.{u}} (I : X.IdealSheafData)
    (i : Z ⟶ X) (v : W ⟶ X) :=
  pullback (restrictedAmbientMap I i) v

/-- The common open `Z_W ×_W U_W`.
Source: Stacks Tag 01JR (blueprint: lem-trf-blowup-base-change-preserved-open-diagram). -/
noncomputable abbrev commonOpen {X Z W : Scheme.{u}} (I : X.IdealSheafData)
    (i : Z ⟶ X) (v : W ⟶ X) :=
  pullback (pullback.snd i v) (Scheme.Opens.ι (I.comap v).support.compl)

private noncomputable def forgetRightIso {A B S U : Scheme.{u}}
    (f : A ⟶ S) (g : B ⟶ S) (u : U ⟶ S) [IsIso (pullback.snd g u)] :
    pullback (pullback.fst f g ≫ f) u ≅ pullback f u :=
  pullback.congrHom (pullback.condition (f := f) (g := g)) rfl ≪≫
    pullbackAssoc f g g u ≪≫
    asIso (pullback.map f (pullback.fst g u ≫ g) f u
      (𝟙 _) (pullback.snd g u) (𝟙 _) (by simp)
      (by simpa using (pullback.condition (f := g) (g := u))))

private lemma forgetRightIso_fst {A B S U : Scheme.{u}}
    (f : A ⟶ S) (g : B ⟶ S) (u : U ⟶ S) [IsIso (pullback.snd g u)] :
    (forgetRightIso f g u).hom ≫ pullback.fst f u =
      pullback.fst (pullback.fst f g ≫ f) u ≫ pullback.fst f g := by
  simp [forgetRightIso, Category.assoc]

private lemma forgetRightIso_snd {A B S U : Scheme.{u}}
    (f : A ⟶ S) (g : B ⟶ S) (u : U ⟶ S) [IsIso (pullback.snd g u)] :
    (forgetRightIso f g u).hom ≫ pullback.snd f u =
      pullback.snd (pullback.fst f g ≫ f) u := by
  simp [forgetRightIso, Category.assoc]

private noncomputable def ambientIso {X Z W P Q : Scheme.{u}}
    (i : Z ⟶ X) (a : P ⟶ X) (v : W ⟶ X) (b : Q ⟶ W)
    (c : Q ⟶ pullback a v) [IsIso c] (hc : c ≫ pullback.snd a v = b) :
    pullback (pullback.snd i v) b ≅ pullback (pullback.snd i a ≫ a) v :=
  asIso (pullback.map (pullback.snd i v) b (pullback.snd i v)
    (pullback.snd a v) (𝟙 _) c (𝟙 _) (by simp) (by simpa using hc.symm)) ≪≫
    pullbackLeftPullbackSndIso i v (pullback.snd a v) ≪≫
    pullback.congrHom rfl (pullback.condition (f := a) (g := v)).symm ≪≫
    (pullbackAssoc i a a v).symm

private lemma ambientIso_fst {X Z W P Q : Scheme.{u}}
    (i : Z ⟶ X) (a : P ⟶ X) (v : W ⟶ X) (b : Q ⟶ W)
    (c : Q ⟶ pullback a v) [IsIso c] (hc : c ≫ pullback.snd a v = b) :
    (ambientIso i a v b c hc).hom ≫
        pullback.fst (pullback.snd i a ≫ a) v ≫ pullback.fst i a =
      pullback.fst (pullback.snd i v) b ≫ pullback.fst i v := by
  simp [ambientIso, Category.assoc]

private lemma ambientIso_snd {X Z W P Q : Scheme.{u}}
    (i : Z ⟶ X) (a : P ⟶ X) (v : W ⟶ X) (b : Q ⟶ W)
    (c : Q ⟶ pullback a v) [IsIso c] (hc : c ≫ pullback.snd a v = b) :
    (ambientIso i a v b c hc).hom ≫ pullback.snd (pullback.snd i a ≫ a) v =
      pullback.fst (pullback.snd i v) b ≫ pullback.snd i v := by
  simp [ambientIso, Category.assoc, hc, pullback.condition]

private lemma ambientIso_blowup {X Z W P Q : Scheme.{u}}
    (i : Z ⟶ X) (a : P ⟶ X) (v : W ⟶ X) (b : Q ⟶ W)
    (c : Q ⟶ pullback a v) [IsIso c] (hc : c ≫ pullback.snd a v = b) :
    (ambientIso i a v b c hc).hom ≫
        pullback.fst (pullback.snd i a ≫ a) v ≫ pullback.snd i a =
      pullback.snd (pullback.snd i v) b ≫ c ≫ pullback.fst a v := by
  simp [ambientIso, Category.assoc]

private noncomputable def openBaseChangeIso {T X W U UW : Scheme.{u}}
    (t : T ⟶ X) (v : W ⟶ X) (u : U ⟶ X) (uw : UW ⟶ W)
    (e : UW ≅ pullback u v) (he : e.hom ≫ pullback.snd u v = uw) :
    pullback (pullback.snd t v) uw ≅ pullback (pullback.snd t u ≫ u) v :=
  pullbackLeftPullbackSndIso t v uw ≪≫
    asIso (pullback.map t (uw ≫ v) t (pullback.fst u v ≫ u)
      (𝟙 _) e.hom (𝟙 _) (by simp)
      (by rw [Category.comp_id, ← he, Category.assoc, pullback.condition])) ≪≫
    (pullbackAssoc t u u v).symm

private lemma openBaseChangeIso_fst {T X W U UW : Scheme.{u}}
    (t : T ⟶ X) (v : W ⟶ X) (u : U ⟶ X) (uw : UW ⟶ W)
    (e : UW ≅ pullback u v) (he : e.hom ≫ pullback.snd u v = uw) :
    (openBaseChangeIso t v u uw e he).hom ≫
        pullback.fst (pullback.snd t u ≫ u) v ≫ pullback.fst t u =
      pullback.fst (pullback.snd t v) uw ≫ pullback.fst t v := by
  simp [openBaseChangeIso, Category.assoc]

private lemma openBaseChangeIso_snd {T X W U UW : Scheme.{u}}
    (t : T ⟶ X) (v : W ⟶ X) (u : U ⟶ X) (uw : UW ⟶ W)
    (e : UW ≅ pullback u v) (he : e.hom ≫ pullback.snd u v = uw) :
    (openBaseChangeIso t v u uw e he).hom ≫ pullback.snd (pullback.snd t u ≫ u) v =
      pullback.snd (pullback.snd t v) uw ≫ uw := by
  simp [openBaseChangeIso, Category.assoc, he]

/-- Flat blowup base change identifies the preserved opens, their two projections,
and their ambient closed immersions. The projection equations characterize the
induced isomorphisms, so these are the restrictions of the specified comparison.

Source: Stacks Tags 0805, 02OS (1), 01JU, 01JR, 01JX and 01QR
(blueprint: lem-trf-blowup-base-change-preserved-open-diagram).

Proof:
1. On affine opens, the extended ideal is generated by the image of the original
ideal (`def-nagata-extended-ideal`, `lem-pc-ideal-sheaf-comap-affine-extension`).
A prime contains this ideal exactly when its contraction contains the original
ideal (`lem-weil-pbc-closed-immersion-image-zero-locus`, `def-weil-affine-spectrum`).
Taking complements and restricting structure sheaves identifies the two opens.
2. The specified comparison is invertible over W by
`thm-nagata-blowup-flat-base-change`. The complement maps are invertible by
`thm-nagata-global-blowup-complement`. Restrict and base change these maps using
`def-pc-fibre-product` and `lem-weil-pbc-open-preimage-fibre-product`; the restricted
comparison has the same U_W projection and commutes with the two structure maps.
3. On test schemes send (z,w,q) to ((z,pr_P(c(q))),w). The inverse uses
c inverse on (p,w). The equations over X follow from the two pullback squares;
the composites have identical projections and hence are identities by
`def-pc-fibre-product`. These are the asserted equations for theta.
4. Restrict these formulas to U_W. Pullback reassociation identifies the target
with (T ×_X U) ×_X W (`lem-weil-pbc-open-preimage-fibre-product`). Forgetting the
blowup coordinate identifies both opens with Z_W ×_W U_W; the inverse is given
by the inverse complement structure map from step 2. All projection equations,
including compatibility with theta, follow from these formulas and pullback uniqueness.
5. Pullback pasting identifies p with the base change of i to P_W, so it is closed
by `lem-weil-pbc-closed-immersion-base-change`. The other immersion is the iterated
base change of i. Finally p theta = c p-hat follows by checking the P and W
projections, using the formula from step 3 and `def-pc-fibre-product`. -/
theorem flat_baseChange_preserved_open_diagram
    {X Z W : Scheme.{u}} (I : X.IdealSheafData) (_hI : I.ofFiniteType)
    (i : Z ⟶ X) [IsClosedImmersion i] (v : W ⟶ X) [Flat v] :
    IsIso (I.blowupFlatBaseChange v) ∧
    I.blowupFlatBaseChange v ≫ pullback.snd I.blowupMap v = (I.comap v).blowupMap ∧
    (I.comap v).support.compl = v ⁻¹ᵁ I.support.compl ∧
    IsIso (pullback.snd I.blowupMap (Scheme.Opens.ι I.support.compl)) ∧
    IsIso (pullback.snd (I.comap v).blowupMap (Scheme.Opens.ι (I.comap v).support.compl)) ∧
    IsIso (pullback.snd (pullback.snd I.blowupMap v)
      (Scheme.Opens.ι (I.comap v).support.compl)) ∧
    (∃ δ : pullback (I.comap v).blowupMap (Scheme.Opens.ι (I.comap v).support.compl) ≅
        pullback (pullback.snd I.blowupMap v) (Scheme.Opens.ι (I.comap v).support.compl),
      δ.hom ≫ pullback.fst (pullback.snd I.blowupMap v)
          (Scheme.Opens.ι (I.comap v).support.compl) =
        pullback.fst (I.comap v).blowupMap (Scheme.Opens.ι (I.comap v).support.compl) ≫
          I.blowupFlatBaseChange v ∧
      δ.hom ≫ pullback.snd (pullback.snd I.blowupMap v)
          (Scheme.Opens.ι (I.comap v).support.compl) =
        pullback.snd (I.comap v).blowupMap (Scheme.Opens.ι (I.comap v).support.compl)) ∧
    IsClosedImmersion (ambientProjection I i v) ∧
    IsClosedImmersion (pullback.snd (pullback.snd i v) (I.comap v).blowupMap) ∧
    ∃ θ : pulledAmbient I i v ≅ ambientBase I i v,
      θ.hom ≫ pullback.fst (ambientMap I i) v ≫ pullback.fst i I.blowupMap =
        pullback.fst (pullback.snd i v) (I.comap v).blowupMap ≫ pullback.fst i v ∧
      θ.hom ≫ pullback.snd (ambientMap I i) v = pulledAmbientMap I i v ∧
      θ.hom ≫ ambientProjection I i v =
        pullback.snd (pullback.snd i v) (I.comap v).blowupMap ≫ I.blowupFlatBaseChange v ∧
      ∃ (ε : sourceOpen I i v ≅ targetOpen I i v)
        (ρhat : sourceOpen I i v ≅ commonOpen I i v)
        (ρ : targetOpen I i v ≅ commonOpen I i v),
        ε.hom ≫ pullback.fst (restrictedAmbientMap I i) v ≫
            pullback.fst (ambientMap I i) (Scheme.Opens.ι I.support.compl) =
          pullback.fst (pulledAmbientMap I i v) (Scheme.Opens.ι (I.comap v).support.compl) ≫
            θ.hom ≫ pullback.fst (ambientMap I i) v ∧
        ε.hom ≫ pullback.snd (restrictedAmbientMap I i) v =
          pullback.snd (pulledAmbientMap I i v) (Scheme.Opens.ι (I.comap v).support.compl) ≫
            Scheme.Opens.ι (I.comap v).support.compl ∧
        ε.hom ≫ ρ.hom = ρhat.hom ∧
        ρhat.hom ≫ pullback.fst (pullback.snd i v) (Scheme.Opens.ι (I.comap v).support.compl) =
          pullback.fst (pulledAmbientMap I i v) (Scheme.Opens.ι (I.comap v).support.compl) ≫
            pullback.fst (pullback.snd i v) (I.comap v).blowupMap ∧
        ρhat.hom ≫ pullback.snd (pullback.snd i v) (Scheme.Opens.ι (I.comap v).support.compl) =
          pullback.snd (pulledAmbientMap I i v) (Scheme.Opens.ι (I.comap v).support.compl) ∧
        ρ.hom ≫ pullback.fst (pullback.snd i v) (Scheme.Opens.ι (I.comap v).support.compl) ≫
            pullback.fst i v =
          pullback.fst (restrictedAmbientMap I i) v ≫
            pullback.fst (ambientMap I i) (Scheme.Opens.ι I.support.compl) ≫
              pullback.fst i I.blowupMap ∧
        ρ.hom ≫ pullback.fst (pullback.snd i v) (Scheme.Opens.ι (I.comap v).support.compl) ≫
            pullback.snd i v = pullback.snd (restrictedAmbientMap I i) v ∧
        ρ.hom ≫ pullback.snd (pullback.snd i v) (Scheme.Opens.ι (I.comap v).support.compl) ≫
            Scheme.Opens.ι (I.comap v).support.compl =
          pullback.snd (restrictedAmbientMap I i) v := by
  have hc : I.blowupFlatBaseChange v ≫ pullback.snd I.blowupMap v =
      (I.comap v).blowupMap := I.blowupFlatBaseChangeIso_hom_snd v
  have hU : (I.comap v).support.compl = v ⁻¹ᵁ I.support.compl := by
    rw [support_comap]
    rfl
  have : IsIso (I.blowupMap ∣_ I.support.compl) :=
    I.isIso_blowupMap_restrict_support_compl
  have : IsIso ((I.comap v).blowupMap ∣_ (I.comap v).support.compl) :=
    (I.comap v).isIso_blowupMap_restrict_support_compl
  have hP : IsIso (pullback.snd I.blowupMap (Scheme.Opens.ι I.support.compl)) := by
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
    infer_instance
  have hQ : IsIso (pullback.snd (I.comap v).blowupMap
      (Scheme.Opens.ι (I.comap v).support.compl)) := by
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
    infer_instance
  let δ := asIso (pullback.map (I.comap v).blowupMap
    (Scheme.Opens.ι (I.comap v).support.compl) (pullback.snd I.blowupMap v)
    (Scheme.Opens.ι (I.comap v).support.compl) (I.blowupFlatBaseChange v)
    (𝟙 _) (𝟙 _) (by simpa using hc.symm) (by simp))
  have hδfst : δ.hom ≫ pullback.fst (pullback.snd I.blowupMap v)
      (Scheme.Opens.ι (I.comap v).support.compl) =
      pullback.fst (I.comap v).blowupMap (Scheme.Opens.ι (I.comap v).support.compl) ≫
        I.blowupFlatBaseChange v := by simp [δ]
  have hδsnd : δ.hom ≫ pullback.snd (pullback.snd I.blowupMap v)
      (Scheme.Opens.ι (I.comap v).support.compl) =
      pullback.snd (I.comap v).blowupMap
        (Scheme.Opens.ι (I.comap v).support.compl) := by simp [δ]
  have hPW : IsIso (pullback.snd (pullback.snd I.blowupMap v)
      (Scheme.Opens.ι (I.comap v).support.compl)) := by
    have : IsIso (δ.hom ≫ pullback.snd (pullback.snd I.blowupMap v)
        (Scheme.Opens.ι (I.comap v).support.compl)) := by
      rw [hδsnd]
      infer_instance
    exact IsIso.of_isIso_comp_left δ.hom _
  let θ := ambientIso i I.blowupMap v (I.comap v).blowupMap
    (I.blowupFlatBaseChange v) hc
  have hθZ : θ.hom ≫ pullback.fst (ambientMap I i) v ≫ pullback.fst i I.blowupMap =
      pullback.fst (pullback.snd i v) (I.comap v).blowupMap ≫ pullback.fst i v :=
    ambientIso_fst i I.blowupMap v (I.comap v).blowupMap (I.blowupFlatBaseChange v) hc
  have hθW : θ.hom ≫ pullback.snd (ambientMap I i) v = pulledAmbientMap I i v :=
    ambientIso_snd i I.blowupMap v (I.comap v).blowupMap (I.blowupFlatBaseChange v) hc
  have hθP : θ.hom ≫ pullback.fst (ambientMap I i) v ≫ pullback.snd i I.blowupMap =
      pullback.snd (pullback.snd i v) (I.comap v).blowupMap ≫
        I.blowupFlatBaseChange v ≫ pullback.fst I.blowupMap v :=
    ambientIso_blowup i I.blowupMap v (I.comap v).blowupMap
      (I.blowupFlatBaseChange v) hc
  have hθambient : θ.hom ≫ ambientProjection I i v =
      pullback.snd (pullback.snd i v) (I.comap v).blowupMap ≫
        I.blowupFlatBaseChange v := by
    apply pullback.hom_ext
    · simpa only [ambientProjection, Category.assoc,
        pullbackRightPullbackFstIso_inv_snd_fst] using hθP
    · simp only [ambientProjection, Category.assoc,
        pullbackRightPullbackFstIso_inv_snd_snd, hc]
      rw [hθW]
      exact pullback.condition
  let eU : ((I.comap v).support.compl : Scheme.{u}) ≅
      pullback (Scheme.Opens.ι I.support.compl) v :=
    W.isoOfEq hU ≪≫ (pullbackRestrictIsoRestrict v I.support.compl).symm ≪≫
      pullbackSymmetry v (Scheme.Opens.ι I.support.compl)
  have heU : eU.hom ≫ pullback.snd (Scheme.Opens.ι I.support.compl) v =
      Scheme.Opens.ι (I.comap v).support.compl := by
    simp [eU, Category.assoc]
  let ε₀ := asIso (pullback.map (pulledAmbientMap I i v)
    (Scheme.Opens.ι (I.comap v).support.compl) (pullback.snd (ambientMap I i) v)
    (Scheme.Opens.ι (I.comap v).support.compl) θ.hom (𝟙 _) (𝟙 _)
    (by simpa using hθW.symm) (by simp))
  let ε := ε₀ ≪≫ openBaseChangeIso (ambientMap I i) v (Scheme.Opens.ι I.support.compl)
    (Scheme.Opens.ι (I.comap v).support.compl) eU heU
  have hεT : ε.hom ≫ pullback.fst (restrictedAmbientMap I i) v ≫
      pullback.fst (ambientMap I i) (Scheme.Opens.ι I.support.compl) =
      pullback.fst (pulledAmbientMap I i v) (Scheme.Opens.ι (I.comap v).support.compl) ≫
        θ.hom ≫ pullback.fst (ambientMap I i) v := by
    simp [ε, ε₀, restrictedAmbientMap, Category.assoc, openBaseChangeIso_fst]
  have hεW : ε.hom ≫ pullback.snd (restrictedAmbientMap I i) v =
      pullback.snd (pulledAmbientMap I i v) (Scheme.Opens.ι (I.comap v).support.compl) ≫
        Scheme.Opens.ι (I.comap v).support.compl := by
    simp [ε, ε₀, restrictedAmbientMap, Category.assoc, openBaseChangeIso_snd]
  let ρhat := forgetRightIso (pullback.snd i v) (I.comap v).blowupMap
    (Scheme.Opens.ι (I.comap v).support.compl)
  have hρhatZ : ρhat.hom ≫ pullback.fst (pullback.snd i v)
      (Scheme.Opens.ι (I.comap v).support.compl) =
      pullback.fst (pulledAmbientMap I i v) (Scheme.Opens.ι (I.comap v).support.compl) ≫
        pullback.fst (pullback.snd i v) (I.comap v).blowupMap :=
    forgetRightIso_fst _ _ _
  have hρhatU : ρhat.hom ≫ pullback.snd (pullback.snd i v)
      (Scheme.Opens.ι (I.comap v).support.compl) =
      pullback.snd (pulledAmbientMap I i v)
        (Scheme.Opens.ι (I.comap v).support.compl) :=
    forgetRightIso_snd _ _ _
  let ρ := ε.symm ≪≫ ρhat
  have hερ : ε.hom ≫ ρ.hom = ρhat.hom := by simp [ρ]
  refine ⟨inferInstance, hc, hU, hP, hQ, hPW, ⟨δ, hδfst, hδsnd⟩, ?_,
    inferInstance, θ, hθZ, hθW, hθambient, ε, ρhat, ρ, hεT, hεW, hερ,
    hρhatZ, hρhatU, ?_, ?_, ?_⟩
  · dsimp only [ambientProjection]
    infer_instance
  · apply (cancel_epi ε.hom).1
    calc
      ε.hom ≫ (ρ.hom ≫ pullback.fst (pullback.snd i v)
          (Scheme.Opens.ι (I.comap v).support.compl) ≫ pullback.fst i v) =
          ρhat.hom ≫ pullback.fst (pullback.snd i v)
            (Scheme.Opens.ι (I.comap v).support.compl) ≫ pullback.fst i v := by
        rw [reassoc_of% hερ]
      _ = pullback.fst (pulledAmbientMap I i v)
          (Scheme.Opens.ι (I.comap v).support.compl) ≫
          pullback.fst (pullback.snd i v) (I.comap v).blowupMap ≫ pullback.fst i v := by
        rw [reassoc_of% hρhatZ]
      _ = ε.hom ≫ pullback.fst (restrictedAmbientMap I i) v ≫
          pullback.fst (ambientMap I i) (Scheme.Opens.ι I.support.compl) ≫
            pullback.fst i I.blowupMap := by
        rw [reassoc_of% hεT, hθZ]
  · apply (cancel_epi ε.hom).1
    rw [reassoc_of% hερ, reassoc_of% hρhatZ, hεW]
    exact pullback.condition
  · apply (cancel_epi ε.hom).1
    rw [reassoc_of% hερ, reassoc_of% hρhatU, hεW]

end AlgebraicGeometry.Scheme.IdealSheafData.BlowupPreservedOpenDiagram
