/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
import Sheaf.Algebra.Homology.DerivedInternalHom
import Sheaf.Algebra.Homology.DerivedChangeOfRings
import Sheaf.Algebra.Homology.KFlatTensorQuasiIso
import Sheaf.Algebra.Homology.KFlatResolution
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.FinitePresentation

/-! # The RHom scalar-extension comparison on perfect representatives

Source: Stacks Project, more-algebra.tex, equation-base-change-RHom and
lemma-base-change-RHom, clause (1) (blueprint: def-pc-perfect-rhom-base-change-map).

The scalar-extension functor is specified on objects and maps and by its left-derived
universal property. The Hom-complex map is specified on pure tensors and every product
projection. In particular, neither the functor nor the comparison is an arbitrary choice.
-/

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory

/-- Modules on the one-object bottom-topology site with ring `A`. Source: Stacks,
more-algebra.tex, equation-base-change-RHom
(blueprint: def-pc-perfect-rhom-base-change-map). -/
abbrev RingSiteModules (A : Type u) [CommRing A] :=
  SheafOfModules.{u} ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (CochainComplex.onePointRingSheaf A))

/-- The map of constant ring sheaves induced by the given ring homomorphism. Source:
Stacks, equation-base-change-RHom (blueprint: def-pc-perfect-rhom-base-change-map). -/
def ringSiteMap {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    CochainComplex.onePointRingSheaf A ⟶ CochainComplex.onePointRingSheaf B :=
  ⟨(Functor.const _).map (CommRingCat.ofHom φ)⟩

/-- The already established Grothendieck structure for the one-object site. Source:
Stacks, Modules on Sites, 03DA (blueprint: def-pc-perfect-rhom-base-change-map). -/
instance ringSiteModulesGrothendieck (A : Type u) [CommRing A] :
    IsGrothendieckAbelian.{u} (RingSiteModules A) :=
  SheafOfModules.isGrothendieckAbelian _

/-- The projections of the shared Hom complex, taken from exactly the witness used in
`homComplexFunctor`, rather than from another product. Source: Stacks, sites-cohomology.tex,
0A8X (blueprint: def-pc-perfect-rhom-base-change-map). -/
noncomputable def ringHomComplexProjection {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ) (n p : ℤ) :
    (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n ⟶
      SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A)
        (P.X p) (Q.X (p + n)) :=
  (homComplex_exists (R := CochainComplex.onePointRingSheaf A)).choose_spec.choose
    P Q n p (p + n) rfl

/-- Evaluate a product coordinate of the shared Hom complex on the unique object's slice.
Source: Stacks, 0A8X (blueprint: def-pc-perfect-rhom-base-change-map). -/
noncomputable def ringHomEvaluate {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ) (n p : ℤ)
    (U : (Discrete PUnit.{u + 1})ᵒᵖ)
    (f : (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n |>.val.obj U)
    (x : (P.X p).val.obj U) : (Q.X (p + n)).val.obj U :=
  (((ringHomComplexProjection P Q n p).val.app U f).app (op (Over.mk (𝟙 U.unop)))) x

/-- Termwise extension on complexes using the specified additive structure. Source:
Stacks, 06YY (blueprint: def-pc-perfect-rhom-base-change-map). -/
noncomputable def ringExtensionComplex {A B : Type u} [CommRing A] [CommRing B]
    (F : RingSiteModules A ⥤ RingSiteModules B) (hF : F.Additive) :
    CochainComplex (RingSiteModules A) ℤ ⥤ CochainComplex (RingSiteModules B) ℤ := by
  letI := hF
  exact F.mapHomologicalComplex (.up ℤ)

/-- Termwise extension on the homotopy category. Source: Stacks, 06YY
(blueprint: def-pc-perfect-rhom-base-change-map). -/
noncomputable def ringExtensionHomotopy {A B : Type u} [CommRing A] [CommRing B]
    (F : RingSiteModules A ⥤ RingSiteModules B) (hF : F.Additive) :
    HomotopyCategory (RingSiteModules A) (.up ℤ) ⥤
      HomotopyCategory (RingSiteModules B) (.up ℤ) :=
  @Functor.mapHomotopyCategory _ _ _ _ _ _ _ F hF (.up ℤ)

/-- The pure tensor, followed by the shared sheafification unit and the specified object
identification for extension. Source: Stacks, 03EK
(blueprint: def-pc-perfect-rhom-base-change-map). -/
noncomputable def ringExtensionPure {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (F : RingSiteModules A ⥤ RingSiteModules B)
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (M : RingSiteModules A) (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b : B) (x : M.val.obj U) :
    (F.obj M).val.obj U :=
  (eqToHom (h M).symm).val.app U
    ((toSheafify ⊥
      (SheafOfModules.changeOfRingsPresheaf (ringSiteMap φ) M).presheaf).app U
        (b ⊗ₜ[A, φ] x))

/-- Extension and its derived functor, with a Hom-complex map specified in every product
coordinate by `b ⊗ f ↦ (c ⊗ x ↦ bc ⊗ f(x))`. Source: Stacks, equation-base-change-RHom
(blueprint: def-pc-perfect-rhom-base-change-map). -/
structure RingRHomBaseChangeData {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (RingSiteModules A)]
    [HasDerivedCategory.{w} (RingSiteModules B)] (φ : A →+* B) where
  extension : RingSiteModules A ⥤ RingSiteModules B
  objects : ∀ M, extension.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M
  maps : ∀ {M N} (f : M ⟶ N), extension.map f = eqToHom (objects M) ≫
    SheafOfModules.changeOfRingsHom (ringSiteMap φ) M f ≫ eqToHom (objects N).symm
  additive : extension.Additive
  derived : DerivedCategory (RingSiteModules A) ⥤ DerivedCategory (RingSiteModules B)
  counit : DerivedCategory.Qh ⋙ derived ⟶
    ringExtensionHomotopy extension additive ⋙ DerivedCategory.Qh
  isDerived : derived.IsLeftDerivedFunctor counit
    (HomotopyCategory.quasiIso (RingSiteModules A) (.up ℤ))
  counit_kFlat : ∀ P : CochainComplex (RingSiteModules A) ℤ, P.IsKFlat →
    IsIso (counit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
  homMap : ∀ P Q : CochainComplex (RingSiteModules A) ℤ,
    (ringExtensionComplex extension additive).obj
      (homComplex (R := CochainComplex.onePointRingSheaf A) P Q) ⟶
    homComplex (R := CochainComplex.onePointRingSheaf B)
      ((ringExtensionComplex extension additive).obj P)
      ((ringExtensionComplex extension additive).obj Q)
  homMap_pure : ∀ (P Q : CochainComplex (RingSiteModules A) ℤ) (n p : ℤ)
    (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b c : B)
    (f : (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n |>.val.obj U)
    (x : (P.X p).val.obj U),
    ringHomEvaluate ((ringExtensionComplex extension additive).obj P)
      ((ringExtensionComplex extension additive).obj Q) n p U
      (((homMap P Q).f n).val.app U
        (ringExtensionPure φ extension objects _ U b f))
      (ringExtensionPure φ extension objects (P.X p) U c x) =
    ringExtensionPure φ extension objects (Q.X (p + n)) U (b * c)
      (ringHomEvaluate P Q n p U f x)

/-- Existence of the scalar-extension data and the normalized Hom-complex map. Source:
Stacks, more-algebra.tex, equation-base-change-RHom
(blueprint: def-pc-perfect-rhom-base-change-map).

Proof: use `SheafOfModules.derivedChangeOfRings` for the additive extension functor,
its everywhere-defined left derived functor and the counit on K-flat complexes.
For the Hom-complex map, tensor its product projections with `B`, and apply the ordinary
scalar-extension Hom map in each coordinate. Its action is `b ⊗ f ↦ (c ⊗ x ↦ bc ⊗ f(x))`.
The balanced relations and restriction compatibility give module maps; the product
universal property gives the degree maps. The tensor-Hom formula commutes with both terms
of `d_Q f - (-1)^n f d_P`, hence these maps form a chain map. Sheafification supplies the
same maps and the displayed unit formula. No perfectness or flatness of `B/A` is needed. -/
theorem ringRHomBaseChangeData_exists {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (RingSiteModules A)]
    [HasDerivedCategory.{w} (RingSiteModules B)] (φ : A →+* B) :
    Nonempty (RingRHomBaseChangeData φ) := by
  sorry

/-- A bounded complex of finite projectives computes RHom without replacing the source.
Source: Stacks, more-algebra.tex, lemma-base-change-RHom, clause (1)
(blueprint: def-pc-perfect-rhom-base-change-map).

Proof: bounded projective complexes are K-projective. The cone of the functorial
K-injective resolution map is acyclic, so applying the Hom complex from `P` gives an
acyclic cone, and hence a quasi-isomorphism. Finite generation is not needed here. -/
theorem ringHomReplacement_quasiIso {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hp : ∀ n : ℤ, Module.Projective A ((P.X n).val.obj (op ⟨PUnit.unit⟩))) :
    QuasiIso (((homComplexFunctor (R := CochainComplex.onePointRingSheaf A)).obj (op P)).map
      ((CochainComplex.toKInjectiveResolution.{u} (RingSiteModules A)).app Q)) := by
  sorry

/-- The canonical Hom-model isomorphism, obtained from the localization factorization and
inverse of the Hom map induced by the functorial K-injective resolution. Source: Stacks,
0A6A (blueprint: def-pc-perfect-rhom-base-change-map). -/
noncomputable def ringRHomModelIso {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (RingSiteModules A)]
    (P Q : CochainComplex (RingSiteModules A) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hp : ∀ n : ℤ, Module.Projective A ((P.X n).val.obj (op ⟨PUnit.unit⟩))) :
    (derivedInternalHom ⊥ (CochainComplex.onePointRingSheaf A)).obj
      (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj Q) ≅
      DerivedCategory.Q.obj (homComplex (R := CochainComplex.onePointRingSheaf A) P Q) := by
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} (RingSiteModules A)
  let η := CochainComplex.toKInjectiveResolution.{u} (RingSiteModules A)
  let F := (𝟭 _).prod I ⋙
    Functor.uncurry.obj (homComplexFunctor (R := CochainComplex.onePointRingSheaf A)) ⋙
      DerivedCategory.Q
  have hF := derivedInternalHom_inverts ⊥ (CochainComplex.onePointRingSheaf A) I η
    (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ M).2,
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} _ M⟩)
  have h := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    (ringHomReplacement_quasiIso P Q hb hp)
  exact (Localization.fac F hF (DerivedCategory.Q.op.prod DerivedCategory.Q)).app (op P, Q)
    ≪≫ (asIso (DerivedCategory.Q.map
      (((homComplexFunctor (R := CochainComplex.onePointRingSheaf A)).obj (op P)).map
        (η.app Q)))).symm

/-- The canonical derived counit on a complex, including the quotient-factorization
isomorphisms. Source: Stacks, 06YY (blueprint: def-pc-perfect-rhom-base-change-map). -/
noncomputable def ringDerivedExtensionCounit {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (RingSiteModules A)]
    [HasDerivedCategory.{w} (RingSiteModules B)] {φ : A →+* B}
    (d : RingRHomBaseChangeData φ) (P : CochainComplex (RingSiteModules A) ℤ) :
    d.derived.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((ringExtensionComplex d.extension d.additive).obj P) := by
  letI := d.additive
  exact d.derived.map ((DerivedCategory.quotientCompQhIso _).app P).inv ≫
    d.counit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map ((d.extension.mapHomotopyCategoryFactors (.up ℤ)).app P).hom ≫
    ((DerivedCategory.quotientCompQhIso _).app
      ((ringExtensionComplex d.extension d.additive).obj P)).hom

/-- Representatives for the perfect-source comparison, with precisely the properties
needed to invert the model-identification maps. Source: Stacks, 0A6A clause (1)
(blueprint: def-pc-perfect-rhom-base-change-map). -/
structure PerfectRHomBaseChangeModel {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (RingSiteModules A)]
    [HasDerivedCategory.{w} (RingSiteModules B)] {φ : A →+* B}
    (d : RingRHomBaseChangeData φ) (E K : DerivedCategory (RingSiteModules A)) where
  source : CochainComplex (RingSiteModules A) ℤ
  target : CochainComplex (RingSiteModules A) ℤ
  bounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (source.X n)
  projective : ∀ n : ℤ, Module.Projective A ((source.X n).val.obj (op ⟨PUnit.unit⟩))
  finite : ∀ n : ℤ, Module.Finite A ((source.X n).val.obj (op ⟨PUnit.unit⟩))
  sourceIso : DerivedCategory.Q.obj source ≅ E
  targetIso : DerivedCategory.Q.obj target ≅ K
  target_kFlat : target.IsKFlat
  extended_bounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n →
    IsZero (((ringExtensionComplex d.extension d.additive).obj source).X n)
  extended_projective : ∀ n : ℤ, Module.Projective B
    ((((ringExtensionComplex d.extension d.additive).obj source).X n).val.obj
      (op ⟨PUnit.unit⟩))
  source_counit : IsIso (ringDerivedExtensionCounit d source)
  target_counit : IsIso (ringDerivedExtensionCounit d target)

/-- Existence of the representative data for every perfect `E` and arbitrary `K`.
Source: Stacks, more-algebra.tex, 0A6A clause (1)
(blueprint: def-pc-perfect-rhom-base-change-map).

Proof: choose the bounded finite-projective representative of `E` in the hypothesis.
Take a K-flat resolution of a representative of `K` using `exists_isKFlatResolution`
(lem-pc-kflat-resolution), and invert its image under `Q` to obtain `targetIso`.
Bounded projective complexes are K-flat (lem-pc-module-bounded-flat-kflat), so the
scalar-extension counits are isomorphisms on both representatives by
lem-pur-derived-change-of-rings. A finite projective module is a summand of a finite free
module; scalar extension preserves this splitting. Thus the extended source is still
bounded finite projective, including the zero terms. These are all the fields of the
model; no invertibility of the Hom comparison is used. -/
theorem perfectRHomBaseChangeModel_exists {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (RingSiteModules A)]
    [HasDerivedCategory.{w} (RingSiteModules B)] {φ : A →+* B}
    (d : RingRHomBaseChangeData φ) (E K : DerivedCategory (RingSiteModules A))
    (hE : ∃ P : CochainComplex (RingSiteModules A) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
      (∀ n : ℤ, Module.Finite A ((P.X n).val.obj (op ⟨PUnit.unit⟩))) ∧
      (∀ n : ℤ, Module.Projective A ((P.X n).val.obj (op ⟨PUnit.unit⟩))) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ E)) :
    Nonempty (PerfectRHomBaseChangeModel d E K) := by
  sorry

/-- The canonical base-change map for given extension data `d` and given perfect and K-flat
representatives `m`. The two RHom identifications use the shared functorial K-injective
replacement and the actual localization factorization. The middle arrow is the normalized
pure-tensor Hom-complex map. Nothing is chosen: `d` is pinned by its object, map, derived and
pure-tensor fields, and `ringRHomBaseChangeData_exists` and `perfectRHomBaseChangeModel_exists`
show that both arguments exist when `E` is perfect. Source: Stacks,
equation-base-change-RHom and 0A6A clause (1)
(blueprint: def-pc-perfect-rhom-base-change-map). -/
noncomputable def perfectRHomBaseChangeMap {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (RingSiteModules A)]
    [HasDerivedCategory.{w} (RingSiteModules B)] {φ : A →+* B}
    (d : RingRHomBaseChangeData φ) {E K : DerivedCategory (RingSiteModules A)}
    (m : PerfectRHomBaseChangeModel d E K) :
    d.derived.obj
      ((derivedInternalHom ⊥ (CochainComplex.onePointRingSheaf A)).obj (op E, K)) ⟶
    (derivedInternalHom ⊥ (CochainComplex.onePointRingSheaf B)).obj
      (op (d.derived.obj E), d.derived.obj K) := by
  let FP := (ringExtensionComplex d.extension d.additive).obj m.source
  let FQ := (ringExtensionComplex d.extension d.additive).obj m.target
  haveI := m.source_counit
  haveI := m.target_counit
  let eP := d.derived.mapIso m.sourceIso.symm ≪≫ asIso (ringDerivedExtensionCounit d m.source)
  let eQ := d.derived.mapIso m.targetIso.symm ≪≫ asIso (ringDerivedExtensionCounit d m.target)
  exact d.derived.map
      ((derivedInternalHom ⊥ (CochainComplex.onePointRingSheaf A)).map
        (m.sourceIso.op.hom, m.targetIso.symm.hom)) ≫
    d.derived.map (ringRHomModelIso m.source m.target m.bounded m.projective).hom ≫
    ringDerivedExtensionCounit d
      (homComplex (R := CochainComplex.onePointRingSheaf A) m.source m.target) ≫
    DerivedCategory.Q.map (d.homMap m.source m.target) ≫
    (ringRHomModelIso FP FQ m.extended_bounded m.extended_projective).inv ≫
    (derivedInternalHom ⊥ (CochainComplex.onePointRingSheaf B)).map
      (eP.op.hom, eQ.symm.hom)

end CategoryTheory
