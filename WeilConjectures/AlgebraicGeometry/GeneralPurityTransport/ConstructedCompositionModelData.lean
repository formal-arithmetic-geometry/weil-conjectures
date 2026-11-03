/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralPurityTransport.ConstructedCompositionTrace
public import WeilConjectures.AlgebraicGeometry.PurityTransport.FieldCompositionScalarData

/-! # Actual functors for scalar transport of the constructed counits

Source: sk-prop-sp-composition.proof.md, coefficient passage
(blueprint: def-pur-general-composition-model-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.GeneralPurityTransport

variable (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] (hk : Finite k ∨ IsAlgClosed k)
  (hEll : IsUnit (ell : k))

/-- Restrict the selected family's source, retaining its literal objects and maps.
Source: the normalized trace equation (blueprint: def-pur-general-composition-model-data). -/
abbrev modelSource (c : Coefficient ell) (s : SmoothDatum k) :
    c.ctf ell s.Y.left ⥤ c.ctf ell s.X.left :=
  source ell c s.map s.dim
    (constructionFamily ell k hk hEll c s).source_closed

/-- Restrict the selected family's support functor.
Source: the normalized trace equation (blueprint: def-pur-general-composition-model-data). -/
abbrev modelSupport (c : Coefficient ell) (s : SmoothDatum k) :
    c.ctf ell s.X.left ⥤ c.ctf ell s.Y.left :=
  support ell c s.compactification
    (constructionFamily ell k hk hEll c s).support_closed

/-- Restriction of the actual scalar extension with an explicit membership certificate.
Source: scalar-six Dctf preservation (blueprint: def-pur-general-composition-model-data). -/
abbrev modelChange {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (T : Over (Spec (.of k)))
    (h : ∀ K : c.ctf ell T.left,
      property ell c' T.left ((scalarSixChange a T.left).obj K.obj)) :
    c.ctf ell T.left ⥤ c'.ctf ell T.left :=
  (property ell c' T.left).lift
    ((property ell c T.left).ι ⋙ scalarSixChange a T.left) h

variable (s : SmoothDatum k) (Z : Over (Spec (.of k)))
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  (g : s.Y.left ⟶ Z.left) [g.IsOver (Spec (.of k))]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (e : ℕ) [SmoothOfRelativeDimension e g]

/-- The second smooth map with its specified compactification.
Source: the composition indices (blueprint: def-pur-general-composition-model-data). -/
def modelSecond (cg : Compactification g) : SmoothDatum k :=
  { X := s.Y, Y := Z, map := g, dim := e, compactification := cg }

/-- The composite smooth map with an arbitrary specified compactification.
Source: the composition indices (blueprint: def-pur-general-composition-model-data). -/
def modelTotal (ch : Compactification (s.map ≫ g)) : SmoothDatum k :=
  { X := s.X, Y := Z, map := s.map ≫ g, dim := s.dim + e, compactification := ch }

/-- Base-field invertibility on the source, used only to form the Tate compositor.
Source: the standing coefficient setting (blueprint: def-pur-general-composition-model-data). -/
@[instance_reducible] def modelInvertible (T : Over (Spec (.of k))) (x : T.left) :
    Invertible (ell : T.left.residueField x) :=
  (show IsUnit (ell : T.left.residueField x) from by
    simpa only [map_natCast] using
      hEll.map ((T.left ↘ Spec (.of k)).residueFieldAlgebraMap x)).invertible

/-- The natural source compositor with its specified root-normalized components.
Source: the source word (blueprint: def-pur-general-composition-model-data). -/
def modelSourceIso (c : Coefficient ell) (cg : Compactification g)
    (ch : Compactification (s.map ≫ g)) (p : LinePullCoordinates ell c s.map) :
    modelSource ell k hk hEll c (modelTotal k s Z g e ch) ≅
      modelSource ell k hk hEll c (modelSecond k s Z g e cg) ⋙
        modelSource ell k hk hEll c s := by
  letI := modelInvertible ell k hEll s.X
  exact NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _ (sourceComp ell c s.map g s.dim e p K.obj))
    (fun v ↦ ObjectProperty.hom_ext _
      (fieldCompSourceNaturality ell c s.map g s.dim e p v.hom))

/-- The support compositor restricted to the actual constructed adjunctions.
Source: the proper/open compositor (blueprint: def-pur-general-composition-model-data). -/
def modelSupportIso (c : Coefficient ell) (cg : Compactification g)
    (ch : Compactification (s.map ≫ g))
    (H : CompactSupportComposition.CoherentData (c.obj.{u} ell) k) :
    modelSupport ell k hk hEll c s ⋙
      modelSupport ell k hk hEll c (modelSecond k s Z g e cg) ≅
        modelSupport ell k hk hEll c (modelTotal k s Z g e ch) :=
  let f₀ := SepFinType.homMk (X := s.X) (Y := s.Y)
    (Over.homMk s.map (comp_over s.map (Spec (.of k))))
  let g₀ := SepFinType.homMk (X := s.Y) (Y := Z)
    (Over.homMk g (comp_over g (Spec (.of k))))
  let alpha := H.comp f₀ g₀ s.compactification cg ch
  NatIso.ofComponents (fun K ↦
    { hom := ⟨alpha.hom.app ((inclusion ell c s.X.left).obj K)⟩
      inv := ⟨alpha.inv.app ((inclusion ell c s.X.left).obj K)⟩
      hom_inv_id := by ext; exact alpha.hom_inv_id_app _
      inv_hom_id := by ext; exact alpha.inv_hom_id_app _ })
    (by intro K L a; ext; exact alpha.hom.naturality ((inclusion ell c s.X.left).map a))

end AlgebraicGeometry.ProEtale.GeneralPurityTransport
