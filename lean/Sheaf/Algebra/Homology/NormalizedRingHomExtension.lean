/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1, SHEAF group T3
-/
module

public import Sheaf.Algebra.Homology.HomComplex
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.Algebra.Homology.KFlatTensorQuasiIso

/-! # Scalar extension of the shared Hom complex

Source: Stacks Project, more-algebra.tex, equation-base-change-RHom, and
sites-cohomology.tex, section-hom-complexes (Tag 0A8X).
(blueprint: lem-pc-normalized-ring-hom-extension)

This is a chain-level construction. It requires neither derived categories nor
perfectness, and supplies only the normalized Hom map, not derived extension data.
-/

@[expose] public section

universe u

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

/-- Scalar extension gives a map of the shared Hom complexes with the normalized
pure-tensor evaluation formula at every product coordinate.
Source: Stacks, more-algebra.tex, equation-base-change-RHom; sites-cohomology.tex,
section-hom-complexes (Tag 0A8X).
(blueprint: lem-pc-normalized-ring-hom-extension)

Proof: write each Hom term as its specified product of internal Homs, using the limit
witness of `homComplex_exists`. For each coordinate, extend a linear map by scalars:
`b ⊗ f` acts on `c ⊗ x` as `bc ⊗ f(x)`. This is additive in each argument. The balanced
relation in the first tensor follows from A-linearity of f, and in the second tensor
from that same linearity and the identity `φ(a)bc = bφ(a)c`. Thus the tensor universal
property gives a B-linear map into the internal Hom of the extended modules. On the
one-object site the slice restrictions are identities up to the unique isomorphisms;
this construction commutes with them. Sheafify, using the sheafification units, and
transport along the given object equalities. Apply this to every product projection;
the target product's universal property gives the degree map, without claiming tensor
commutes with infinite products. For the differential, compose with each target product
projection and evaluate on pure tensors. The two terms are respectively
`bc ⊗ d_Q(f(x))` and `(-1)^n bc ⊗ f(d_P(x))` on both sides, since the given functor maps
are exactly scalar extension of maps. Their difference is therefore equal. Pure tensors
span the extended modules, and the product projections are jointly monic, proving the
chain-map identity. In degrees not adjacent the differentials are zero. This constructs
the map and proves its normalization, with no boundedness or flatness assumption. -/
theorem normalizedRingHomExtension_exists {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (F : RingSiteModules A ⥤ RingSiteModules B)
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (hm : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (h M) ≫
      SheafOfModules.changeOfRingsHom (ringSiteMap φ) M f ≫ eqToHom (h N).symm)
    (hF : F.Additive) (P Q : CochainComplex (RingSiteModules A) ℤ) :
    ∃ χ : (ringExtensionComplex F hF).obj
        (homComplex (R := CochainComplex.onePointRingSheaf A) P Q) ⟶
      homComplex (R := CochainComplex.onePointRingSheaf B)
        ((ringExtensionComplex F hF).obj P) ((ringExtensionComplex F hF).obj Q),
      ∀ (n p : ℤ) (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b c : B)
        (f : (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n |>.val.obj U)
        (x : (P.X p).val.obj U),
        ringHomEvaluate ((ringExtensionComplex F hF).obj P)
          ((ringExtensionComplex F hF).obj Q) n p U
          (((χ.f n).val.app U) (ringExtensionPure φ F h _ U b f))
          (ringExtensionPure φ F h (P.X p) U c x) =
        ringExtensionPure φ F h (Q.X (p + n)) U (b * c)
          (ringHomEvaluate P Q n p U f x) := by
  sorry

end CategoryTheory
