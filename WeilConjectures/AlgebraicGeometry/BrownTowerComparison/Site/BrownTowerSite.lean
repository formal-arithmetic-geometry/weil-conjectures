/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BrownTowerComparison.BrownTowerFiniteEvaluation

/-! # Strict system site comparison and compact support

Source: Zheng Construction 4.1 and Lemmas 4.10, 5.16, 5.22
(blueprint: def-pur-brown-system-site).

These are comparison data, without any existence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
namespace BrownTowerComparison
variable {O : Type (u + 1)} [CommRing O] {t : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}

/-- System site comparison along the prescribed inclusion `toProEt`, using the
ordinary and universal derived images of the dependency. The fixed-module realizations
identify the level inverse/direct images with the existing site functors.
Source: Zheng Construction 4.1, Lemma 4.10; Stacks 099R
(blueprint: def-pur-brown-system-site). -/
structure Site (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O] (t : O)
    (P : StrictEtaleEvaluation T O t) where
  proEvaluation : CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2}
    (J := Scheme.ProEt.topology T) (O := O) (ell := t)
  ordinary : CoefficientSystemOrdinaryImage
    (J := T.smallEtaleTopology) (K := Scheme.ProEt.topology T) O t
    (Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt T)
      (Type (u + 1)) T.smallEtaleTopology (Scheme.ProEt.topology T))
    ((Scheme.toProEt T).sheafPushforwardContinuous (Type (u + 1))
      T.smallEtaleTopology (Scheme.ProEt.topology T)) (Scheme.proEtaleSiteComparison T)
  comparison : CoefficientSystemUnboundedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
    (J := T.smallEtaleTopology) (K := Scheme.ProEt.topology T) O t _ _ _ ordinary P proEvaluation
  realization : ∀ n, Realization (Scheme.ProEt.topology T) O t n
  etaleRealization : ∀ n, Realization T.smallEtaleTopology O t n
  inverseLevel : ∀ n : ℕ, (comparison.evaluation.level n).inverse ⋙ (realization n).derived ≅
    (etaleRealization n).derived ⋙ FiniteCoefficientAdjoints.nu (Ring O t n) T
  directLevel : ∀ n, (comparison.evaluation.level n).direct ⋙ (etaleRealization n).derived ≅
    (realization n).derived ⋙ FiniteCoefficientAdjoints.rnu (Ring O t n) T
  level_counit : ∀ n M,
    (inverseLevel n).hom.app ((comparison.evaluation.level n).direct.obj M) ≫
      (FiniteCoefficientAdjoints.nu (Ring O t n) T).map ((directLevel n).hom.app M) ≫
      (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} (Ring O t n)) T).counit.app
        ((realization n).derived.obj M) =
    (realization n).derived.map ((comparison.evaluation.level n).adjunction.counit.app M)
  inverse_bound : ∀ K a, K.IsGE a → (comparison.evaluation.system.inverse.obj K).IsGE a
  direct_bound : ∀ K a, K.IsGE a → (comparison.evaluation.system.direct.obj K).IsGE a

/-- The prescribed system site inverse, with its concrete domain and codomain.
Source: Zheng Lemma 4.10 (blueprint: def-pur-brown-system-site). -/
def Site.inverse {T : Scheme.{u}} {P : StrictEtaleEvaluation T O t}
    (V : Site T O t P) : DerivedCategory (strictEtaleCoefficientSystem T O t) ⥤
      DerivedCategory (ProSystem T O t) :=
  V.comparison.evaluation.system.inverse

/-- The prescribed system site direct, with its concrete domain and codomain.
Source: Zheng Lemma 4.10 (blueprint: def-pur-brown-system-site). -/
def Site.direct {T : Scheme.{u}} {P : StrictEtaleEvaluation T O t}
    (V : Site T O t P) : DerivedCategory (ProSystem T O t) ⥤
      DerivedCategory (strictEtaleCoefficientSystem T O t) :=
  V.comparison.evaluation.system.direct

/-- The prescribed system site adjunction, with its concrete domain and codomain.
Source: Zheng Lemma 4.10 (blueprint: def-pur-brown-system-site). -/
def Site.adjunction {T : Scheme.{u}} {P : StrictEtaleEvaluation T O t}
    (V : Site T O t P) : V.inverse ⊣ V.direct :=
  V.comparison.evaluation.system.adjunction

/-- Levelwise etale origin with bounded-below witnesses, for the prescribed system
site inverse image. This does not require compatible choices of the witnesses.
Source: Stacks 099W; node proof Step 7
(blueprint: def-pur-brown-system-site). -/
def Site.Origin {T : Scheme.{u}} {P : StrictEtaleEvaluation T O t}
    (V : Site T O t P) (M : DerivedCategory (ProSystem T O t)) : Prop :=
  (∃ a : ℤ, M.IsGE a) ∧ ∀ n : ℕ, ∃ H : DerivedCategory (strictEtaleLevel T O t n),
    (∃ a : ℤ, H.IsGE a) ∧
      Nonempty ((V.comparison.evaluation.level n).inverse.obj H ≅
        (V.proEvaluation.evaluation n).obj M)

/-- The finite exceptional image transported by the actual site adjunction.
Source: node statement and proof Step 8; Zheng Lemma 5.22
(blueprint: def-pur-brown-system-site). -/
def finiteExceptional (S : StrictEtaleCompactSupport O t c)
    (G : EtaleTowerBrownAdjunction S) (H : FiniteEvaluation S G)
    (VX : Site X O t S.PX) (VY : Site Y O t S.PY) (n : ℕ) :=
  (VY.comparison.evaluation.level n).direct ⋙ H.right n ⋙ (VX.comparison.evaluation.level n).inverse

/-- The ordinary pro-etale proper/open system functor. The geometric lifts retain
sections and transitions, the derived images are universal, and open extension is
fixed by its adjunction and exact-complex factorization. Thus its data are canonical
up to the displayed universal identifications.
Source: node proof Step 10; Zheng Constructions 4.1 and 5.15
(blueprint: def-pur-brown-system-site). -/
structure ProCompact (S : StrictEtaleCompactSupport O t c)
    (VX : Site X O t S.PX) (VY : Site Y O t S.PY) where
  openImage : CoefficientSystemOrdinaryImage
    (J := Scheme.ProEt.topology c.Z) (K := Scheme.ProEt.topology X) O t
    (Scheme.proEtaleSheafInverseImage c.i (Type (u + 1)))
    (Scheme.proEtaleSheafDirectImage c.i (Type (u + 1)))
    (Scheme.proEtaleSheafAdjunction c.i (Type (u + 1)))
  properImage : CoefficientSystemOrdinaryImage
    (J := Scheme.ProEt.topology Y) (K := Scheme.ProEt.topology c.Z) O t
    (Scheme.proEtaleSheafInverseImage c.g (Type (u + 1)))
    (Scheme.proEtaleSheafDirectImage c.g (Type (u + 1)))
    (Scheme.proEtaleSheafAdjunction c.g (Type (u + 1)))
  openDerived : CoefficientDerivedImage openImage.inverse openImage.rightSystem
    openImage.systemAdj
  properDerived : CoefficientDerivedImage properImage.inverse properImage.rightSystem
    properImage.systemAdj
  openExtension : ProSystem X O t ⥤ ProSystem c.Z O t
  [openAdditive : openExtension.Additive]
  openExact : PreservesFiniteLimits openExtension ∧ PreservesFiniteColimits openExtension
  openAdjunction : openExtension ⊣ openImage.inverse
  derivedOpen : DerivedCategory (ProSystem X O t) ⥤ DerivedCategory (ProSystem c.Z O t)
  derivedOpenAdjunction : derivedOpen ⊣ openDerived.inverse
  openFactors : DerivedCategory.Q ⋙ derivedOpen ≅
    openExtension.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  openTranspose : ∀ P K
      (a : (openExtension.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
    derivedOpenAdjunction.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
      (openFactors.hom.app P ≫ DerivedCategory.Q.map a) =
    DerivedCategory.Q.map ((openAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P K a) ≫
      openDerived.inverseFactors.inv.app K

/-- Actual compact support, defined by the proper/open composite on pro-etale systems.
Source: node proof Step 10 (blueprint: def-pur-brown-system-site). -/
def ProCompact.functor {S : StrictEtaleCompactSupport O t c}
    {VX : Site X O t S.PX} {VY : Site Y O t S.PY} (F : ProCompact S VX VY) :=
  F.derivedOpen ⋙ F.properDerived.direct

end BrownTowerComparison
end AlgebraicGeometry
