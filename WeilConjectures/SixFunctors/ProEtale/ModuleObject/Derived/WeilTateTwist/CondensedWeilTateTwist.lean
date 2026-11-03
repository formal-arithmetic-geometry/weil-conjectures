/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralTateBasis
public import WeilConjectures.AlgebraicGeometry.Native.NativeSignedLine
public import WeilConjectures.CategoryTheory.Endofunctor.FixedPairEquivalenceTransport
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeLineTensorFiniteness

/-! # Tate twists of ordinary condensed Weil pairs

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-weights-deligne-theorem/sec-wdef-weights/sk-r-real-linear/def-wf-tate-twist.md
(blueprint: def-wf-tate-twist).

All coefficient lines and their root-normalized structures are the published ones.
The functors assemble them by the existing transport of invertible endofunctor algebras.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.WeilTateTwist

open PurityTransport StrictWeilCondensed

variable (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
  {T : Scheme.{u}} (g : T ≅ T) [∀ x : T, Invertible (ell : T.residueField x)]

private noncomputable def pullExtendIso
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] :
    (ProEtale.upperStar Ab.{u + 1} f).mapMod R ⋙
        Mod.extendScalars ((ProEtale.upperStar Ab.{u + 1} f).map a) ≅
      Mod.extendScalars a ⋙ (ProEtale.upperStar Ab.{u + 1} f).mapMod S := by
  let adj := ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f
  exact Adjunction.pullIsoOfComapIso
    (Mod.extendRestrictAdjunction ((ProEtale.upperStar Ab.{u + 1} f).map a))
    (Mod.extendRestrictAdjunction a)
    (adj.mapModAdjunction R) (adj.mapModAdjunction S)
    (Mod.comapMapModComapIso (ProEtale.lowerStar Ab.{u + 1} f)
      ((ProEtale.upperStar Ab.{u + 1} f).map a) a
      (adj.unitAlgHom R) (adj.unitAlgHom S) (adj.unit.naturality a))

private theorem firstLine_trivial :
    ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage T, ∀ i : 𝒰.I₀,
      Nonempty (((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapMod
        (condensedRingObj (c.obj ell) T)).obj (c.firstLine ell T) ≅ 𝟙_ _) := by
  have hInv : IsUnit (ell : Γ(T, ⊤)) := by
    apply T.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    change IsUnit ((T.presheaf.germ ⊤ x hx).hom (ell : Γ(T, ⊤)))
    rw [map_natCast]
    apply (isUnit_map_iff (IsLocalRing.residue (T.presheaf.stalk x)) _).mp
    simpa only [map_natCast] using isUnit_of_invertible (ell : T.residueField x)
  obtain ⟨𝒰, h𝒰⟩ := tateModule_locally_trivial T ell hInv
  refine ⟨𝒰, fun i ↦ ?_⟩
  let F := ProEtale.upperStar Ab.{u + 1} (𝒰.f i)
  exact ⟨(pullExtendIso (𝒰.f i) (coefficientMap (c.integralMap ell) T)).symm.app
      (tateModule T ell) ≪≫
    (Mod.extendScalars (F.map (coefficientMap (c.integralMap ell) T))).mapIso
      (h𝒰 i).some ≪≫
    Mod.extendScalarsObjRegularIso (F.map (coefficientMap (c.integralMap ell) T))⟩

private theorem signedLine_locallyFree (m : ℤ) :
    IsLocallyFree (condensedRingObj (c.obj ell) T) (tateLine ell c T m) := by
  have hs := nativeSignedLine (condensedRingObj (c.obj ell) T) (c.firstLine ell T)
    (firstLine_trivial ell c (T := T))
  exact (hs.2.1 m).of_iso
    (tateLine_identification ell c T m ≪≫ presentationSignedIso ell c T m).symm

private theorem signedLine_cancels (m : ℤ) :
    Nonempty (tateLine ell c T m ⊗ tateLine ell c T (-m) ≅ 𝟙_ _) := by
  have hs := nativeSignedLine (condensedRingObj (c.obj ell) T) (c.firstLine ell T)
    (firstLine_trivial ell c (T := T))
  exact ⟨tensorIso
    (tateLine_identification ell c T m ≪≫ presentationSignedIso ell c T m)
    (tateLine_identification ell c T (-m) ≪≫ presentationSignedIso ell c T (-m)) ≪≫
      (hs.2.2.2.2 m).some⟩

/-- Tensor with the signed Tate module. The structure uses the inverse tensorator
and the root-normalized Tate structure; maps tensor with the identity.
Source: def-wf-tate-twist.md, displayed tensor Weil map and morphism formula
(blueprint: def-wf-tate-twist). -/
def moduleTwist (m : ℤ) : WeilModule (c.obj ell) g ⥤ WeilModule (c.obj ell) g :=
  CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    ((Functor.Monoidal.commTensorRight (upperStar (c.obj ell) g.hom)
        (tateLine ell c T m)).symm ≪≫
      Functor.isoWhiskerLeft (upperStar (c.obj ell) g.hom)
        ((tensoringRight _).mapIso (tatePull ell c g m)))

/-- Derived tensor with the actual Tate line in degree zero, with the two Weil
structures composed after the inverse derived tensorator.
Source: def-wf-tate-twist.md, K(m) and the displayed Weil map
(blueprint: def-wf-tate-twist). -/
def ambientTwist (m : ℤ) :
    CategoryTheory.Endofunctor.IsoAlgebra (action (c.obj ell) g) ⥤
      CategoryTheory.Endofunctor.IsoAlgebra (action (c.obj ell) g) :=
  CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    ((Functor.Monoidal.commTensorRight (action (c.obj ell) g)
        (derivedTateLine ell c T m)).symm ≪≫
      Functor.isoWhiskerLeft (action (c.obj ell) g)
        ((tensoringRight _).mapIso (tateDatum ell c g m)))

/-- Tate tensor preserves constructibility and is exact on Weil modules.
Source: def-wf-tate-twist.md, final sentence (blueprint: def-wf-tate-twist).
Proof: the common root cover trivializes the signed Tate line, including its
negative powers by duality. On this cover, tensor by the line is isomorphic to
the identity on module carriers, so preserves constructibility, kernels and
cokernels. These properties descend. Weil-module kernels and cokernels are
computed on carriers with the induced tensor structure. Hence the functor
preserves finite limits and colimits. -/
theorem moduleTwist_properties (m : ℤ) :
    (∀ M : WeilModule (c.obj ell) g,
      IsConstructibleModuleObject (condensedRingObj (c.obj ell) T) M.carrier →
      IsConstructibleModuleObject (condensedRingObj (c.obj ell) T)
        (((moduleTwist ell c g m).obj M).carrier)) ∧
    PreservesFiniteLimits (moduleTwist ell c g m) ∧
    PreservesFiniteColimits (moduleTwist ell c g m) := by
  have hL := signedLine_locallyFree ell c (T := T) m
  let := hL.flat.tensorRight.preservesFiniteLimits
  let := hL.flat.tensorRight.preservesFiniteColimits
  refine ⟨?_, ?_, ?_⟩
  · intro M hM
    exact (hL.isConstructibleModuleObject_tensorObj hM).of_iso (β_ _ _)
  · unfold moduleTwist
    infer_instance
  · unfold moduleTwist
    infer_instance

/-- Derived Tate tensor preserves bounded constructibility and cohomological bounds.
Source: def-wf-tate-twist.md, preservation and t-exactness clause
(blueprint: def-wf-tate-twist).
Proof: a locally free line is flat, so derived tensor by its single complex is
ordinary exact tensor on complexes. Its cohomology is the input cohomology
tensored with the same line, in the same degree. This preserves both bounds,
and constructibility is preserved locally on the common root cover. The Weil
structure equips these carriers with the specified tensor isomorphism. -/
theorem ambientTwist_properties (m : ℤ)
    (K : CategoryTheory.Endofunctor.IsoAlgebra (action (c.obj ell) g)) :
    (boundedConstructible (condensedRingObj (c.obj ell) T) K.carrier →
      boundedConstructible (condensedRingObj (c.obj ell) T)
        (((ambientTwist ell c g m).obj K).carrier)) ∧
    (∀ n : ℤ, K.carrier.IsGE n → (((ambientTwist ell c g m).obj K).carrier).IsGE n) ∧
    (∀ n : ℤ, K.carrier.IsLE n → (((ambientTwist ell c g m).obj K).carrier).IsLE n) := by
  have hL := signedLine_locallyFree ell c (T := T) m
  have h := nativeLineTensor_finiteness (tateLine ell c T m) hL
  refine ⟨h.2.2.2.1 K.carrier, ?_, ?_⟩
  · intro n hn
    apply (DerivedCategory.isGE_iff _ n).2
    intro i hi
    exact ((tensorLeft _).map_isZero ((DerivedCategory.isGE_iff _ n).1 hn i hi)).of_iso
      (h.1 K.carrier i).some
  · intro n hn
    apply (DerivedCategory.isLE_iff _ n).2
    intro i hi
    exact ((tensorLeft _).map_isZero ((DerivedCategory.isLE_iff _ n).1 hn i hi)).of_iso
      (h.1 K.carrier i).some

/-- The restriction to constructible Weil sheaves retains the ambient tensor maps.
Source: def-wf-tate-twist.md, constructible Weil heart
(blueprint: def-wf-tate-twist). -/
def heartTwist (m : ℤ) :
    WeilConjectures.condensedConstructibleWeilSheaves (c.obj ell) g.hom ⥤
      WeilConjectures.condensedConstructibleWeilSheaves (c.obj ell) g.hom :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ moduleTwist ell c g m)
    (fun M ↦ (moduleTwist_properties ell c g m).1 M.obj M.property)

/-- Tate twisting in the bounded constructible strict-pair category.
Source: def-wf-tate-twist.md, twist of a Weil complex
(blueprint: def-wf-tate-twist). -/
def strictTwist (m : ℤ) :
    WeilConjectures.condensedStrictWeilComplex (c.obj ell) g.hom ⥤
      WeilConjectures.condensedStrictWeilComplex (c.obj ell) g.hom :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ ambientTwist ell c g m)
    (fun K ↦ (ambientTwist_properties ell c g m K.obj).1 K.property)

/-- The restriction of Tate tensor is exact on the constructible Weil heart.
Source: def-wf-tate-twist.md, final sentence (blueprint: def-wf-tate-twist).
Proof: constructible Weil sheaves form an abelian full subcategory with kernels
and cokernels computed on carriers. The ambient exactness and preservation of
constructibility in moduleTwist_properties therefore restrict to this heart. -/
theorem heartTwist_exact (m : ℤ) :
    PreservesFiniteLimits (heartTwist ell c g m) ∧
    PreservesFiniteColimits (heartTwist ell c g m) := by
  -- Use opposite-line cancellation to restrict the Weil-pair tensor equivalence.
  let L := tateLine ell c T m
  let N := tateLine ell c T (-m)
  let e : L ⊗ N ≅ 𝟙_ _ := (signedLine_cancels ell c (T := T) m).some
  let E := tensorRightEquivalenceOfTensorIso e (β_ N L ≪≫ e)
  let a :=
    (Functor.Monoidal.commTensorRight (upperStar (c.obj ell) g.hom) L).symm ≪≫
      Functor.isoWhiskerLeft (upperStar (c.obj ell) g.hom)
        ((tensoringRight _).mapIso (tatePull ell c g m))
  let : (moduleTwist ell c g m).IsEquivalence :=
    (CategoryTheory.Endofunctor.IsoAlgebra.fixedPair_equivalence_transport
      (upperStar (c.obj ell) g.hom) (upperStar (c.obj ell) g.hom) E a.symm).1
  let P : ObjectProperty (WeilModule (c.obj ell) g) := fun M ↦
    IsConstructibleModuleObject (condensedRingObj (c.obj ell) T) M.carrier
  let : P.IsClosedUnderIsomorphisms := ⟨fun i hi ↦ hi.of_iso
    ((CategoryTheory.Endofunctor.IsoAlgebra.forget _).mapIso i)⟩
  have hp : P.inverseImage (moduleTwist ell c g m) = P := by
    funext M
    apply propext
    constructor
    · intro h
      have hc :=
        (signedLine_locallyFree ell c (T := T) (-m)).isConstructibleModuleObject_tensorObj h
      exact (hc.of_iso (β_ _ _)).of_iso
        (α_ M.carrier L N ≪≫ whiskerLeftIso M.carrier e ≪≫ ρ_ M.carrier)
    · exact (moduleTwist_properties ell c g m).1 M
  let E' := (moduleTwist ell c g m).asEquivalence.congrFullSubcategory hp
  let : (heartTwist ell c g m).IsEquivalence := inferInstanceAs E'.functor.IsEquivalence
  exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.ProEtale.CondensedRing.WeilTateTwist
