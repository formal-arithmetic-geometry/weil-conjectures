/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap

/-! # Common-target diagram for composition of module cohomology maps

The statement concerns homology of section complexes before transport to derived
cohomology. Source: Stacks Project, Cohomology of Sheaves, Tags 01F8 and 01FB;
Derived Categories, Tags 013P and 013S.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- The section-complex homology maps for two successive scheme maps admit a common
comparison target. This is the diagram step, before cancellation or transport through
`isoRightDerivedObj`, of composition.
Source: Stacks Project, Cohomology of Sheaves, Tags 01F8 and 01FB; Derived Categories,
Tags 013P and 013S (blueprint: lem-weil-pbc-module-cohomology-fmap-comp-data).

Proof: Z.Modules has enough injectives. Replace k_*Ch.K by a nonnegative
termwise injective complex L with a quasi-isomorphism mu. Since Ch.K is termwise
injective, the canonical sections comparison followed by Gamma(mu) induces an
isomorphism s on homology (01EZ).
Lift k_*(desc id from Ck.I to Ch.J) followed by k_*(Ch.beta) and mu across
Ck.lambda to obtain e : Ck.K -> L up to homotopy. Lift (kh)_*(desc id from
Ccomp.I to Ch.I), followed by the inverse successive-pushforward comparison at
Ch.I, k_*(Ch.lambda), and mu across Ccomp.lambda to obtain
f : Ccomp.K -> L up to homotopy.
Precomposing the beta square with Ccomp.J's augmentation gives homotopic maps:
the two beta compatibility equations, the augmentation equation for identity
descent, and naturality of pushforwardComp identify both routes. Uniqueness of
lifts into L gives the beta homotopy (013S). Apply additive global sections and
homology to these three homotopies. Canonical sections comparisons commute with
identity descents and with successive pushforwards, by naturality of restrictions
and h inverse k inverse top = (h followed by k) inverse top. Their three resulting
identities are precisely the displayed squares. Take Q = H^p(Gamma(Z,L)),
qk = H^p(Gamma(e)), qc = H^p(Gamma(f)), and s as above. No identification with
derived cohomology and no cancellation of the three squares occurs in this lemma.
-/
theorem moduleCohomologyFMap_comp_data {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z)
    {H : Z.Modules} {G : Y.Modules} {F : X.Modules}
    (ψ : H ⟶ (pushforward k).obj G) (φ : G ⟶ (pushforward h).obj F)
    (Ck : ModuleCohomologyFMapData k H G ψ)
    (Ch : ModuleCohomologyFMapData h G F φ)
    (Cc : ModuleCohomologyFMapData (h ≫ k) H F
      (ψ ≫ (pushforward k).map φ ≫ (pushforwardComp h k).hom.app F)) (p : ℕ) :
    let HX := (RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)
    let HY := (RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)
    let HZ := (RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)
    let Hp := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p
    ∃ (Q : AddCommGrpCat.{u}) (qk : Hp.obj (HZ.obj Ck.K) ⟶ Q)
      (qc : Hp.obj (HZ.obj Cc.K) ⟶ Q) (s : Hp.obj (HY.obj Ch.K) ⟶ Q),
      IsIso s ∧
      Hp.map (HZ.map Cc.β) ≫ qc =
        Hp.map (HZ.map (InjectiveResolution.desc (𝟙 H) Ck.J Cc.J)) ≫
          Hp.map (HZ.map Ck.β) ≫ qk ∧
      Hp.map (Cc.a.hom ≫ HZ.map Cc.lambda) ≫ qc =
        Hp.map (HX.map (InjectiveResolution.desc (𝟙 F) Ch.I Cc.I)) ≫
          Hp.map (Ch.a.hom ≫ HY.map Ch.lambda) ≫ s ∧
      Hp.map (Ck.a.hom ≫ HZ.map Ck.lambda) ≫ qk =
        Hp.map (HY.map (InjectiveResolution.desc (𝟙 G) Ch.J Ck.I)) ≫
          Hp.map (HY.map Ch.β) ≫ s := by
  sorry

end AlgebraicGeometry.Scheme.Modules
