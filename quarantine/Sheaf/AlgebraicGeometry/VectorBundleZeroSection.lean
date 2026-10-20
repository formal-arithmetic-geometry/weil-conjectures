/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore
public import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraAffine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sheaves.Functors
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# The vector bundle Spec Sym(F), its augmentation and zero section

Source: blueprint, `sec-smooth-purity/sk-prop-an`, order 1968;
Stacks Project, Constructions, Tags 01M2, 01LW and 01LX
(blueprint: def-asd-vector-bundle-zero-section).

The relative-spectrum anti-equivalence is the one characterized by its structure-algebra
functor in `affine_morphism_relative_spec`. Its inverse determines the bundle up to the
unique algebra-compatible isomorphism. The augmentation is chosen from a unique extension
of the zero linear map, and the zero section is its fully faithful inverse image.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.VectorBundleZeroSection

/-- The relative-spectrum anti-equivalence characterized on objects and morphisms in
Stacks Tags 01LW and 01LX (blueprint: def-asd-vector-bundle-zero-section). -/
def antiEquivalence (S : Scheme.{u}) :
    (ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom))ᵒᵖ ≌
      ObjectProperty.FullSubcategory
        (fun A : S.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent) :=
  (affine_morphism_relative_spec S).2.choose

/-- The base itself as an affine scheme over itself, Stacks Tag 01LX
(blueprint: def-asd-vector-bundle-zero-section). -/
def baseObject (S : Scheme.{u}) :
    ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom) :=
  ⟨Over.mk (𝟙 S), inferInstanceAs (IsAffineHom (𝟙 S))⟩

/-- The constructed symmetric algebra, with the quasi-coherence provided by the affine
comparison. Source: Stacks Tag 01CL (blueprint: def-asd-vector-bundle-zero-section). -/
def algebraObject (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] :
    ObjectProperty.FullSubcategory
      (fun A : S.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent) := by
  letI := SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree F d
  exact ⟨SymmetricAlgebraSheaf.algebra F,
    (quasiCoherentSymmetricAlgebra_affine_comparison S F).1⟩

/-- The relative affine scheme Spec_S Sym(F) as an object over S.
Source: Stacks Tag 01M2 (blueprint: def-asd-vector-bundle-zero-section). -/
def over (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] :
    ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom) :=
  ((antiEquivalence S).inverse.obj (algebraObject S d F)).unop

/-- The total space of the vector bundle of constant rank d.
Source: Stacks Tag 01M2 (blueprint: def-asd-vector-bundle-zero-section). -/
def scheme (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] : Scheme.{u} :=
  (over S d F).obj.left

/-- The structural projection of Spec_S Sym(F).
Source: Stacks Tag 01M2 (blueprint: def-asd-vector-bundle-zero-section). -/
def π (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] : scheme S d F ⟶ S :=
  (over S d F).obj.hom

/-- The unique algebra morphism to O_S killing the degree-one generators.
Source: Stacks Tag 01M2 (blueprint: def-asd-vector-bundle-zero-section). -/
def augmentation (S : Scheme.{u}) (F : S.Modules) :
    SymmetricAlgebraSheaf.algebra F ⟶ Under.mk (𝟙 S.sheaf) :=
  (exists_quasiCoherentSymmetricAlgebra_core S F (Under.mk (𝟙 S.sheaf)) 0).exists.choose

/-- The same zero-generator extension into the structure algebra of the identity S-scheme.
This is the augmentation transported to the anti-equivalence's chosen base object.
Source: Stacks Tags 01M2 and 01LX (blueprint: def-asd-vector-bundle-zero-section). -/
def augmentationToBase (S : Scheme.{u}) (F : S.Modules) :
    SymmetricAlgebraSheaf.algebra F ⟶
      ((antiEquivalence S).functor.obj (op (baseObject S))).obj :=
  (exists_quasiCoherentSymmetricAlgebra_core S F
    ((antiEquivalence S).functor.obj (op (baseObject S))).obj 0).exists.choose

/-- The zero section: the fully faithful inverse image of the augmentation, after the
counit identifies the bundle's structure algebra with Sym(F).
Source: Stacks Tag 01M2 (blueprint: def-asd-vector-bundle-zero-section). -/
def zero (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] : S ⟶ scheme S d F :=
  ((antiEquivalence S).functor.preimage
    (((antiEquivalence S).counitIso.app (algebraObject S d F)).hom ≫
    (ObjectProperty.homMk (augmentationToBase S F)))).unop.hom.left

/-- The canonical symmetric-algebra identification with the direct-image structure algebra.
Source: Stacks Tag 01LX (blueprint: def-asd-vector-bundle-zero-section). -/
def algebraIso (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] :
    SymmetricAlgebraSheaf.algebra F ≅
      Under.mk (⟨(π S d F).c⟩ : S.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} (π S d F).base).obj
          (scheme S d F).sheaf) :=
  ((ObjectProperty.ι (fun A : S.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent)).mapIso
    ((antiEquivalence S).counitIso.app (algebraObject S d F))).symm ≪≫
      eqToIso ((affine_morphism_relative_spec S).2.choose_spec.choose (over S d F))

/-- The chart over an affine open is induced by the sheafification unit and the
symmetric-algebra identification. Source: Stacks Tag 01LX
(blueprint: def-asd-vector-bundle-zero-section). -/
def affineChart (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] (U : S.affineOpens) :
    ((π S d F) ⁻¹ᵁ U.1).toScheme ⟶
      Spec (.of (SymmetricAlgebraSheaf.sections F (op U.1))) :=
  ((π S d F) ⁻¹ᵁ U.1).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom
      (((algebraIso S d F).hom.right.hom.app (op U.1)).hom.comp
        (SymmetricAlgebraSheaf.sectionMap F (op U.1))))

/-- The augmentation is the unique map killing every degree-one section, and on sectionwise
symmetric algebras is the identity on scalars and zero on generators.
Source: Stacks Tag 01M2 (blueprint: def-asd-vector-bundle-zero-section).
Proof: the core symmetric-algebra universal property with the zero linear map gives
existence and uniqueness. Before sheafification the map is SymmetricAlgebra.algebraMapInv;
uniqueness on scalars and generators identifies the composite with the sheafification unit.
The under-category compatibility supplies the identity on scalars. -/
theorem augmentation_spec (S : Scheme.{u}) (F : S.Modules) :
    (∀ (U : S.Opens) (x : F.val.obj (op U)),
      (augmentation S F).right.hom.app (op U)
        ((SymmetricAlgebraSheaf.inclusion F).val.app (op U) x) = 0) ∧
    (∀ t : SymmetricAlgebraSheaf.algebra F ⟶ Under.mk (𝟙 S.sheaf),
      (∀ (U : S.Opens) (x : F.val.obj (op U)),
        t.right.hom.app (op U) ((SymmetricAlgebraSheaf.inclusion F).val.app (op U) x) = 0) →
      t = augmentation S F) ∧
    (∀ (U : S.Opens) (a : SymmetricAlgebraSheaf.sections F (op U)),
      (augmentation S F).right.hom.app (op U) (SymmetricAlgebraSheaf.sectionMap F (op U) a) =
        SymmetricAlgebra.algebraMapInv a) := by
  have h := (exists_quasiCoherentSymmetricAlgebra_core S F (Under.mk (𝟙 S.sheaf))
    0).exists.choose_spec
  have hz : ∀ (U : S.Opens) (x : F.val.obj (op U)),
      (augmentation S F).right.hom.app (op U)
        ((SymmetricAlgebraSheaf.inclusion F).val.app (op U) x) = 0 := by
    intro U x
    exact h U x
  refine ⟨hz, ?_, ?_⟩
  · intro t ht
    exact ExistsUnique.unique
      (exists_quasiCoherentSymmetricAlgebra_core S F (Under.mk (𝟙 S.sheaf)) 0) ht hz
  · intro U a
    induction a using SymmetricAlgebra.induction with
    | algebraMap r =>
        rw [AlgHom.commutes]
        exact congrArg (fun q ↦ q.hom.app (op U) r) (Under.w (augmentation S F))
    | ι x =>
        exact (hz U x).trans (SymmetricAlgebra.algebraMapInv_ι x).symm
    | mul a b ha hb => simp only [map_mul, ha, hb]
    | add a b ha hb => simp only [map_add, ha, hb]

/-- The zero section is a section and a closed immersion.
Source: Stacks Tag 01M2 (blueprint: def-asd-vector-bundle-zero-section).
Proof: the augmentation is an O_S-algebra map, so its spectrum lies over S, giving the
section identity. On each relative-spectrum affine chart it is induced by the
augmentation Sym_R(F(U)) → R, which is surjective because it fixes scalars. It is therefore
the quotient closed subscheme for the augmentation kernel, by the affine closed-immersion
criterion. These charts cover the total space, so the morphism is a closed immersion. -/
theorem zero_spec (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] :
    zero S d F ≫ π S d F = 𝟙 S ∧ IsClosedImmersion (zero S d F) := by
  have hs : zero S d F ≫ π S d F = 𝟙 S := by
    exact Over.w
      (((antiEquivalence S).functor.preimage
        (((antiEquivalence S).counitIso.app (algebraObject S d F)).hom ≫
          ObjectProperty.homMk (augmentationToBase S F))).unop.hom)
  have : IsAffineHom (π S d F) := (over S d F).property
  have : IsClosedImmersion (zero S d F ≫ π S d F) := hs ▸ inferInstance
  exact ⟨hs, IsClosedImmersion.of_comp (zero S d F) (π S d F)⟩

/-- Restriction of the zero section to an open of the base.
Source: Stacks Tag 01M2 (blueprint: def-asd-vector-bundle-zero-section). -/
def zeroRestricted (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens) :
    V.toScheme ⟶ ((π S d F) ⁻¹ᵁ V).toScheme :=
  (zero S d F).resLE ((π S d F) ⁻¹ᵁ V) V
    (by rw [← Scheme.Hom.comp_preimage, (zero_spec S d F).1]; simp)

/-- The affine charts are isomorphisms over the corresponding base affine opens, and the
zero section in these charts is exactly the spectrum of the augmentation.
Source: Stacks Tags 01LX and 01M2 (blueprint: def-asd-vector-bundle-zero-section).
Proof: quasiCoherentSymmetricAlgebra_affine_comparison identifies affine algebra sections
with Sym_R(F(U)). Apply the counit chart characterization in affine_morphism_relative_spec
and compose with the spectrum of that ring isomorphism. The counit is an O_S-algebra map,
which gives the equation with the structural projection. The zero map was defined as the
fully faithful inverse image of the unique zero-generator extension. The morphism-chart
clause of affine_morphism_relative_spec thus identifies its restriction with the spectrum
of SymmetricAlgebra.algebraMapInv, using augmentation_spec. -/
theorem affineChart_spec (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] (U : S.affineOpens) :
    IsIso (affineChart S d F U) ∧
    (affineChart S d F U ≫
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.obj (op U.1))
        (SymmetricAlgebraSheaf.sections F (op U.1)))) ≫ U.2.isoSpec.inv = (π S d F) ∣_ U.1) ∧
    (zeroRestricted S d F U.1 ≫ affineChart S d F U =
      U.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (SymmetricAlgebra.algebraMapInv (R := S.presheaf.obj (op U.1))
          (M := F.val.obj (op U.1))).toRingHom)) := by
  sorry

/-- On an inclusion of affine opens, the chart change is the spectrum of the
symmetric-algebra restriction, so these are exactly the affine pieces glued in the node.
Source: Stacks Tag 01LX (blueprint: def-asd-vector-bundle-zero-section).
Proof: naturality of the counit algebra isomorphism and of the sheafification unit
identifies the maps on section rings with SymmetricAlgebraSheaf.restriction. Apply
naturality of toSpecΓ and contravariant functoriality of Spec. -/
theorem affineChart_naturality (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] (U V : S.affineOpens) (h : U.1 ≤ V.1) :
    Scheme.Hom.resLE (𝟙 (scheme S d F)) ((π S d F) ⁻¹ᵁ V.1) ((π S d F) ⁻¹ᵁ U.1)
        ((π S d F).preimage_mono h) ≫ affineChart S d F V =
      affineChart S d F U ≫
        Spec.map (CommRingCat.ofHom (SymmetricAlgebraSheaf.restriction F (homOfLE h).op)) := by
  simp only [Scheme.Hom.resLE_id, affineChart, Category.assoc]
  rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc]
  simp only [← Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  have hA := (algebraIso S d F).hom.right.hom.naturality (homOfLE h).op
  have hθ := (toSheafify (Opens.grothendieckTopology S)
    (SymmetricAlgebraSheaf.presheaf F)).naturality (homOfLE h).op
  exact (CategoryTheory.congr_fun hA
    (SymmetricAlgebraSheaf.sectionMap F (op V.1) a)).symm.trans
      (congrArg ((algebraIso S d F).hom.right.hom.app (op U.1))
        (CategoryTheory.congr_fun hθ a).symm)

/-- A Zariski trivialization is a frame of the given module, not an arbitrary isomorphism
of schemes. Source: blueprint order 1968 (blueprint: def-asd-vector-bundle-zero-section). -/
def Trivialization (S : Scheme.{u}) (d : ℕ) (F : S.Modules) (V : S.Opens) :=
  F.restrict V.ι ≅ SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin d))

/-- The i-th frame section over V, obtained by the inverse frame map on its standard basis.
Source: blueprint order 1968 (blueprint: def-asd-vector-bundle-zero-section). -/
def frameSection (S : Scheme.{u}) (d : ℕ) (F : S.Modules) (V : S.Opens)
    (e : Trivialization S d F V) (i : Fin d) : F.val.obj (op V) :=
  F.presheaf.map (eqToHom V.ι_image_top.symm).op
    ((F.restrictAppIso V.ι ⊤).hom
      (e.inv.val.app (op ⊤) ((SheafOfModules.ιFree (R := V.toScheme.ringCatSheaf)
        (ULift.up i)).val.app (op ⊤)
          (1 : V.toScheme.ringCatSheaf.obj.obj (op ⊤)))))

/-- The coordinate x_i = j(e_i), transported to the restricted total space's global ring.
Source: blueprint order 1968 (blueprint: def-asd-vector-bundle-zero-section). -/
def coordinate (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens) (e : Trivialization S d F V) (i : Fin d) :
    Γ(((π S d F) ⁻¹ᵁ V).toScheme, ⊤) :=
  ((π S d F) ⁻¹ᵁ V).topIso.inv
    ((algebraIso S d F).hom.right.hom.app (op V)
      ((SymmetricAlgebraSheaf.inclusion F).val.app (op V) (frameSection S d F V e i)))

/-- The map to affine space induced by a module frame and its degree-one coordinates.
Source: Stacks Tag 01M2 (blueprint: def-asd-vector-bundle-zero-section). -/
def trivializationMap (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens) (e : Trivialization S d F V) :
    ((π S d F) ⁻¹ᵁ V).toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) V.toScheme :=
  AffineSpace.homOfVector ((π S d F) ∣_ V) (fun i ↦ coordinate S d F V e i.down)

/-- The frame induces an affine-space isomorphism over V with the zero section at the origin.
Source: blueprint order 1968 and Stacks Tag 01M2
(blueprint: def-asd-vector-bundle-zero-section).
Proof: on every affine open inside V the frame gives a module basis. The basis-preserving
isomorphism SymmetricAlgebra.equivMvPolynomial identifies its symmetric algebra with the
polynomial algebra and its generators with the variables. The affine relative-spectrum
charts therefore identify trivializationMap with an isomorphism over V. These maps agree
on overlaps because their coordinates are the restrictions of j(e_i), so they glue.
The augmentation kills each e_i, hence all coordinates of the zero section vanish;
AffineSpace.homOfVector identifies this with the standard affine-space zero section. -/
theorem trivializationMap_spec (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens) (e : Trivialization S d F V) :
    IsIso (trivializationMap S d F V e) ∧
    (trivializationMap S d F V e ≫
      AffineSpace (ULift.{u} (Fin d)) V.toScheme ↘ V.toScheme = (π S d F) ∣_ V) ∧
    (zeroRestricted S d F V ≫ trivializationMap S d F V e =
      AffineSpace.zeroSection (ULift.{u} (Fin d)) V.toScheme) := by
  sorry

/-- Two frames on an overlap differ by an invertible matrix of regular functions, and the
same matrix changes their degree-one coordinates (with no transpose or dual convention).
Source: blueprint order 1968 (blueprint: def-asd-vector-bundle-zero-section).
Proof: the composite of the two frame isomorphisms is an automorphism of the finite free
module sheaf. Its values on the standard global basis have global coefficient sections,
giving G. The inverse automorphism gives H. Applying their composites to each basis
vector proves GH = HG = I. These coefficients give the displayed equation for frame
sections on W, whether or not W is affine. The degree-one map j is O_S-linear; applying
it and the algebra isomorphism to that equation gives the coordinate equation, with
coefficients pulled back along the restricted projection. For d = 0 all sums are empty
and the unique empty matrices are mutual inverses. -/
theorem transition_spec (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] (W : S.Opens) (e e' : Trivialization S d F W) :
    ∃ G H : Matrix (Fin d) (Fin d) (S.presheaf.obj (op W)),
      G * H = 1 ∧ H * G = 1 ∧
      (∀ j : Fin d,
        frameSection S d F W e' j = ∑ i : Fin d, G i j • frameSection S d F W e i) ∧
      (∀ j : Fin d,
        coordinate S d F W e' j = ∑ i : Fin d,
          ((π S d F) ∣_ W).appTop (W.topIso.inv (G i j)) * coordinate S d F W e i) := by
  sorry

end AlgebraicGeometry.VectorBundleZeroSection
