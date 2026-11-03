/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCompactProjectionFormulaTheorem
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
public import Mathlib.CategoryTheory.HomCongr

/-! # Archived native compact structure comparison

Temporary compatibility archive requested by reviewer C-e6555. These `_legacy`
declarations preserve the existing native VerdierDual proofs until their independent
route switch. This archive is not imported by the current condensed exchange module.

## Historical construction

Source: blueprint latest, fix-cor-verdier-exchange.proof.md, Step 1, and
fix-lem-tensor-adjunction.proof.md, Step 1, second Hom bijection
(blueprint: lem-sf-weil-compact-structure-tensor-comparison).

The comparison is the actual projection isomorphism followed by inverse compact
composition. Its Hom bijection is precomposition by the inverse comparison.
All functors and arrows remain in the native bounded constructible full categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false

-- Use the identity structure morphism for the base over itself.
attribute [instance 1100] CategoryTheory.instOverClass

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.WeilComplex

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The tensor input on X, with the framework's actual module pullback.
Source: blueprint latest, fix-lem-tensor-adjunction.proof.md, Step 1
(blueprint: lem-sf-weil-compact-structure-tensor-comparison). -/
abbrev nativeStructureTensorInput_legacy :
    WeilComplex k₀ l X × WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X :=
  (𝟭 (WeilComplex k₀ l X)).prod (upperStar (k₀ := k₀) (l := l) f) ⋙
    nativeConstructibleTensor k₀ l X

/-- The structure pushforward of Rf! M tensor L.
Source: blueprint latest, fix-cor-verdier-exchange.proof.md, Step 1
(blueprint: lem-sf-weil-compact-structure-tensor-comparison). -/
abbrev nativeStructureTensorLeft_legacy :=
  nativeCompactProjectionLeft k₀ l f ⋙
    derivedLowerShriek k₀ l (Y ↘ Spec (CommRingCat.of k₀))

/-- The structure pushforward of M tensor f* L.
Source: blueprint latest, fix-cor-verdier-exchange.proof.md, Step 1
(blueprint: lem-sf-weil-compact-structure-tensor-comparison). -/
abbrev nativeStructureTensorRight_legacy :=
  nativeStructureTensorInput_legacy k₀ l f ⋙
    derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))

/-- The specified comparison, made from projection followed by inverse composition.
The inputs are comparison data, not choices from a bare existence assertion.
Source: blueprint latest, fix-cor-verdier-exchange.proof.md, Step 1, and
fix-lem-tensor-adjunction.proof.md, Step 1
(blueprint: lem-sf-weil-compact-structure-tensor-comparison). -/
def nativeStructureTensorIso_legacy
    (pi : nativeCompactProjectionLeft k₀ l f ≅ nativeCompactProjectionRight k₀ l f)
    (gamma : derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀)) ≅
      derivedLowerShriek k₀ l f ⋙
        derivedLowerShriek k₀ l (Y ↘ Spec (CommRingCat.of k₀))) :
    nativeStructureTensorLeft_legacy k₀ l f ≅ nativeStructureTensorRight_legacy k₀ l f :=
  Functor.isoWhiskerRight pi (derivedLowerShriek k₀ l (Y ↘ Spec (CommRingCat.of k₀))) ≪≫
    Functor.isoWhiskerLeft (nativeStructureTensorInput_legacy k₀ l f) gamma.symm

/-- The comparison's Hom bijection into the existing degree-zero coefficient unit.
It has the actual inverse of the comparison as its precomposition map.
Source: blueprint latest, fix-lem-tensor-adjunction.proof.md, Step 1, Hom chain
(blueprint: lem-sf-weil-compact-structure-tensor-comparison). -/
def nativeStructureTensorHomEquiv_legacy
    (pi : nativeCompactProjectionLeft k₀ l f ≅ nativeCompactProjectionRight k₀ l f)
    (gamma : derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀)) ≅
      derivedLowerShriek k₀ l f ⋙
        derivedLowerShriek k₀ l (Y ↘ Spec (CommRingCat.of k₀)))
    (M : WeilComplex k₀ l X) (L : WeilComplex k₀ l Y) :
    ((nativeStructureTensorLeft_legacy k₀ l f).obj (M, L) ⟶
        WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)))) ≃
      ((nativeStructureTensorRight_legacy k₀ l f).obj (M, L) ⟶
        WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)))) :=
  ((nativeStructureTensorIso_legacy k₀ l f pi gamma).app (M, L)).homCongr (Iso.refl _)

set_option maxHeartbeats 800000 in
-- Elaborating the normalized comparison data exceeds the default heartbeat budget.
/-- Compact structure comparison and its contravariantly natural Hom bijection.
The existential projection is pinned to exactly the same normalized native
compactification formula as native_compact_projection_formula. Composition is
in the native Weil categories, and its source is the actual structure morphism.

Source: blueprint latest, fix-cor-verdier-exchange.proof.md, Step 1, and
fix-lem-tensor-adjunction.proof.md, Step 1, second Hom bijection
(blueprint: lem-sf-weil-compact-structure-tensor-comparison).

Proof:
1. Finite type is quasi-compact and locally of finite type
(def-weil-finite-type-morphism). The separated structure maps and f therefore
satisfy all operation domains (def-weil-proper-morphism). Y is a finite union of
spectra of finitely generated k0-algebras, hence Noetherian, so its diagonal
inverse images of affine opens are quasi-compact; Spec k0 is a point. This also
gives the quasi-separated schemes needed for compact composition
(def-weil-quasi-separated-morphism).
2. Compact support preserves bounded constructible objects by
lem-sf-native-weil-shriek-triangulated, and f* does so by
lem-sf-native-weil-pullback-star-preservation. Tensor closure is
lem-sf-derived-weil-tensor-hom-adjunction, applied to (FM,L) and (M,f*L).
3. Take pi and its normalized compactification data from
lem-sf-derived-weil-compact-projection-formula. Apply
lem-sf-native-weil-shriek-composition to f and aY; comp_over identifies their
composite with aX. Thus gamma : AX ≅ F followed by AY. Define e by AY(pi)
followed by gamma inverse. Its inverse is gamma followed by AY(pi inverse).
Functoriality and the two inverse identities show that these cancel.
4. For u:M→M' and v:L→L', put p=Fu tensor v and q=u tensor f*v.
Naturality of pi says pi followed by Fq equals p followed by pi'. Naturality
of gamma then gives e followed by AX(q) equals AY(p) followed by e'. This is
already encoded in nativeStructureTensorIso_legacy as an isomorphism of functors.
5. For the coefficient unit of def-sf-derived-weil-category-and-operations,
put H(h)=e inverse followed by h, and J(h')=e followed by h'. The inverse
identities give JH=id and HJ=id. Inverting the naturality equation of Step 4
gives H(h' after AY(p))=H(h') after AX(q), the displayed contravariant square.
The inverse bijection has the corresponding square by the same equation. -/
theorem native_compact_structure_tensor_comparison_legacy :
    ∃ (C : ProEtaleWeilSheaf.NativeProjectionTensorComparison k₀ l
          (nativeProjectionCompactification k₀ f).g)
      (s : ProEtaleWeilSheaf.NativeOpenTensorData k₀ l
          (nativeProjectionCompactification k₀ f).i)
      (d : ProEtaleWeilSheaf.NativeOpenDerivedTensorData k₀ l
          (nativeProjectionCompactification k₀ f).i s)
      (c : OpenTensorPresentation (ProEtaleWeilSheaf k₀ l X)
          (ProEtaleWeilSheaf k₀ l (nativeProjectionCompactification k₀ f).Z))
      (pi : nativeCompactProjectionLeft k₀ l f ≅ nativeCompactProjectionRight k₀ l f)
      (gamma : derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀)) ≅
        derivedLowerShriek k₀ l f ⋙
          derivedLowerShriek k₀ l (Y ↘ Spec (CommRingCat.of k₀))),
      ProEtaleWeilSheaf.NativeOpenPresentationCompatibility k₀ l
          (nativeProjectionCompactification k₀ f).i s d c ∧
      (∀ (M : WeilComplex k₀ l X) (L : WeilComplex k₀ l Y),
        (pi.hom.app (M, L)).hom =
          ProEtaleWeilSheaf.nativeProjectionProperMate k₀ l
            (nativeProjectionCompactification k₀ f).g C
            ((ProEtaleWeilSheaf.nativeOpenExtension k₀ l
              (nativeProjectionCompactification k₀ f).i).obj M.obj) L.obj ≫
          (ProEtaleWeilSheaf.lowerStar k₀ l
            (nativeProjectionCompactification k₀ f).g).rightDerivedFunctor.map
            (d.gamma.hom.app (M.obj,
              (ProEtaleWeilSheaf.nativeOpenPull k₀ l
                (nativeProjectionCompactification k₀ f).g).obj L.obj)) ≫
          (ProEtaleWeilSheaf.lowerStar k₀ l
            (nativeProjectionCompactification k₀ f).g).rightDerivedFunctor.map
            ((ProEtaleWeilSheaf.nativeOpenExtension k₀ l
              (nativeProjectionCompactification k₀ f).i).map
              ((ProEtaleWeilSheaf.nativeDerivedTensor k₀ l X).map
                (Prod.mkHom (𝟙 M.obj) ((nativeProjectionPullComp k₀ l f).hom.app L.obj))))) ∧
      (∀ (M : WeilComplex k₀ l X) (L : WeilComplex k₀ l Y),
        (nativeStructureTensorIso_legacy k₀ l f pi gamma).hom.app (M, L) =
          (derivedLowerShriek k₀ l (Y ↘ Spec (CommRingCat.of k₀))).map
              (pi.hom.app (M, L)) ≫
            gamma.inv.app ((nativeStructureTensorInput_legacy k₀ l f).obj (M, L))) ∧
      (∀ (M : WeilComplex k₀ l X) (L : WeilComplex k₀ l Y)
        (h : (nativeStructureTensorLeft_legacy k₀ l f).obj (M, L) ⟶
          WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)))),
        nativeStructureTensorHomEquiv_legacy k₀ l f pi gamma M L h =
          (nativeStructureTensorIso_legacy k₀ l f pi gamma).inv.app (M, L) ≫ h) ∧
      (∀ (M : WeilComplex k₀ l X) (L : WeilComplex k₀ l Y)
        (h : (nativeStructureTensorRight_legacy k₀ l f).obj (M, L) ⟶
          WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)))),
        (nativeStructureTensorHomEquiv_legacy k₀ l f pi gamma M L).symm h =
          (nativeStructureTensorIso_legacy k₀ l f pi gamma).hom.app (M, L) ≫ h) ∧
      (∀ {M M' : WeilComplex k₀ l X} {L L' : WeilComplex k₀ l Y}
        (u : M ⟶ M') (v : L ⟶ L')
        (h : (nativeStructureTensorLeft_legacy k₀ l f).obj (M', L') ⟶
          WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)))),
        nativeStructureTensorHomEquiv_legacy k₀ l f pi gamma M L
            ((nativeStructureTensorLeft_legacy k₀ l f).map (Prod.mkHom u v) ≫ h) =
          (nativeStructureTensorRight_legacy k₀ l f).map (Prod.mkHom u v) ≫
            nativeStructureTensorHomEquiv_legacy k₀ l f pi gamma M' L' h) ∧
      (∀ {M M' : WeilComplex k₀ l X} {L L' : WeilComplex k₀ l Y}
        (u : M ⟶ M') (v : L ⟶ L')
        (h : (nativeStructureTensorRight_legacy k₀ l f).obj (M', L') ⟶
          WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)))),
        (nativeStructureTensorHomEquiv_legacy k₀ l f pi gamma M L).symm
            ((nativeStructureTensorRight_legacy k₀ l f).map (Prod.mkHom u v) ≫ h) =
          (nativeStructureTensorLeft_legacy k₀ l f).map (Prod.mkHom u v) ≫
            (nativeStructureTensorHomEquiv_legacy k₀ l f pi gamma M' L').symm h) := by
  obtain ⟨C, s, d, c, pi, hc, hpi⟩ := native_compact_projection_formula k₀ l f
  have hgamma : Nonempty (derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀)) ≅
      derivedLowerShriek k₀ l f ⋙
        derivedLowerShriek k₀ l (Y ↘ Spec (CommRingCat.of k₀))) := by
    simpa only [comp_over f (Spec (CommRingCat.of k₀))] using
      (nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) f
        (Y ↘ Spec (CommRingCat.of k₀)))
  obtain ⟨gamma⟩ := hgamma
  refine ⟨C, s, d, c, pi, gamma, hc, hpi, ?_, ?_, ?_, ?_, ?_⟩
  · intro M L
    rfl
  · intro M L h
    change (nativeStructureTensorIso_legacy k₀ l f pi gamma).inv.app (M, L) ≫
      (h ≫ 𝟙 _) = _
    rw [Category.comp_id]
  · intro M L h
    change (nativeStructureTensorIso_legacy k₀ l f pi gamma).hom.app (M, L) ≫
      (h ≫ 𝟙 _) = _
    rw [Category.comp_id]
  · intro M M' L L' u v h
    change (nativeStructureTensorIso_legacy k₀ l f pi gamma).inv.app (M, L) ≫
        (((nativeStructureTensorLeft_legacy k₀ l f).map (Prod.mkHom u v) ≫ h) ≫ 𝟙 _) =
      (nativeStructureTensorRight_legacy k₀ l f).map (Prod.mkHom u v) ≫
        (nativeStructureTensorIso_legacy k₀ l f pi gamma).inv.app (M', L') ≫ (h ≫ 𝟙 _)
    simp only [Category.comp_id]
    rw [← Category.assoc, ← (nativeStructureTensorIso_legacy k₀ l f pi gamma).inv.naturality,
      Category.assoc]
  · intro M M' L L' u v h
    change (nativeStructureTensorIso_legacy k₀ l f pi gamma).hom.app (M, L) ≫
        (((nativeStructureTensorRight_legacy k₀ l f).map (Prod.mkHom u v) ≫ h) ≫ 𝟙 _) =
      (nativeStructureTensorLeft_legacy k₀ l f).map (Prod.mkHom u v) ≫
        (nativeStructureTensorIso_legacy k₀ l f pi gamma).hom.app (M', L') ≫ (h ≫ 𝟙 _)
    simp only [Category.comp_id]
    rw [← Category.assoc, ← (nativeStructureTensorIso_legacy k₀ l f pi gamma).hom.naturality,
      Category.assoc]

end AlgebraicGeometry.WeilComplex
