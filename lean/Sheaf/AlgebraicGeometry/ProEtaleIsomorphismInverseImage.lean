/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Sheaf.AlgebraicGeometry.ProEtaleOperations

/-! # Inverse image along an isomorphism of schemes

Source: Stacks Project, Tags 09A5 and 00WX
(blueprint: lem-weil-proetale-isomorphism-inverse-image).

## Main statements

- `proEtaleIsoPostcompose_equivalence`: the covering-preserving site equivalence.
- `existsUnique_proEtaleIsoInverseImageIdentification`: its normalized section identification.
- `proEtaleIsoInverseImage_equivalence`: equivalence and preservation of limits and colimits.
- `proEtaleIso_inverseLimitComparison`: the canonical inverse-limit comparison.
- `proEtaleIso_constantComparison`: invertible constant comparison and naturality.
- `proEtaleIso_constantModuleEquivalence`: the same equivalence for module sheaves.
- `proEtaleIso_constantRingModuleEquivalence`: module sheaves over any constant ring.
-/

@[expose] public section

set_option autoImplicit false

universe u v w w'

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Change only the structure map of an object of the pro-etale site.
Source: Stacks Project, Tag 09A5
(blueprint: lem-weil-proetale-isomorphism-inverse-image). -/
def proEtaleIsoPostcompose {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : X.ProEt ⥤ Y.ProEt :=
  MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)

/-- The site equivalence and its specified inverse preserve covering families.
Source: Stacks Project, Tag 09A5
(blueprint: lem-weil-proetale-isomorphism-inverse-image).
Proof: compose structure maps with `f` or its inverse; the composites identify naturally
with the identity, with the identity on underlying schemes. These functors preserve weak
etaleness and coverings since the underlying schemes and covering arrows are unchanged. -/
theorem proEtaleIsoPostcompose_equivalence {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    (proEtaleIsoPostcompose f).IsEquivalence ∧
      Nonempty (proEtaleIsoPostcompose f ⋙ proEtaleIsoPostcompose (inv f) ≅ 𝟭 X.ProEt) ∧
      Nonempty (proEtaleIsoPostcompose (inv f) ⋙ proEtaleIsoPostcompose f ≅ 𝟭 Y.ProEt) ∧
      Nonempty (CoverPreserving (ProEt.topology X) (ProEt.topology Y)
        (proEtaleIsoPostcompose f)) ∧
      Nonempty (CoverPreserving (ProEt.topology Y) (ProEt.topology X)
        (proEtaleIsoPostcompose (inv f))) := by
  sorry

/-- The distinguished comma-category arrow `(u,id)` from the map/pullback adjunction.
Source: Stacks Project, Tags 09A5 and 00WX
(blueprint: lem-weil-proetale-isomorphism-inverse-image). -/
noncomputable def proEtaleIsoCommaArrow {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (U : X.ProEt) : U ⟶ (proEtaleBaseChange f).obj ((proEtaleIsoPostcompose f).obj U) :=
  (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ f
    (inferInstance : WeaklyEtale f) trivial).unit.app U

/-- The canonical identification is uniquely fixed by the coprojection at `(u,id)`.
Source: Stacks Project, Tags 09A5 and 00WX
(blueprint: lem-weil-proetale-isomorphism-inverse-image).
Proof: the distinguished comma object is initial before taking opposites, hence terminal
in the colimit index. Its coprojection is invertible. The inverse evaluates each
coprojection by the unique arrow into that terminal object. The resulting presheaf is
already a sheaf because the site equivalence preserves covers and overlap schemes;
sheafification leaves it unchanged. The construction is natural in objects and sheaves.
The prescribed inverse determines the natural isomorphism uniquely. -/
theorem existsUnique_proEtaleIsoInverseImageIdentification {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] (D : Type v) [Category.{u + 1} D]
    [HasColimitsOfSize.{u + 1, u + 1} D] [HasWeakSheafify (ProEt.topology X) D] :
    ∃! e : proEtaleSheafInverseImage f D ⋙ sheafToPresheaf (ProEt.topology X) D ≅
        sheafToPresheaf (ProEt.topology Y) D ⋙
          (Functor.whiskeringLeft _ _ D).obj (proEtaleIsoPostcompose f).op,
      ∀ (F : Sheaf (ProEt.topology Y) D) (U : X.ProEt),
        (e.inv.app F).app (op U) =
          ((proEtaleSheafAdjunction f D).unit.app F).hom.app
              (op ((proEtaleIsoPostcompose f).obj U)) ≫
            ((proEtaleSheafInverseImage f D).obj F).obj.map
              (proEtaleIsoCommaArrow f U).op := by
  sorry

/-- The canonical section identification, natural both in the sheaf and in the site object.
Source: Stacks Project, Tags 09A5 and 00WX
(blueprint: lem-weil-proetale-isomorphism-inverse-image). -/
noncomputable def proEtaleIsoInverseImageIdentification {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] (D : Type v) [Category.{u + 1} D]
    [HasColimitsOfSize.{u + 1, u + 1} D] [HasWeakSheafify (ProEt.topology X) D] :
    proEtaleSheafInverseImage f D ⋙ sheafToPresheaf (ProEt.topology X) D ≅
      sheafToPresheaf (ProEt.topology Y) D ⋙
        (Functor.whiskeringLeft _ _ D).obj (proEtaleIsoPostcompose f).op :=
  (existsUnique_proEtaleIsoInverseImageIdentification f D).exists.choose

/-- The recorded adjunction is an equivalence, so its quasi-inverse is the recorded direct
image. Its inverse image preserves arbitrary limits and colimits, and is exact in the
abelian case by preservation of finite limits and colimits.
Source: Stacks Project, Tags 09A5 and 00WX
(blueprint: lem-weil-proetale-isomorphism-inverse-image).
Proof: both site functors are inverse equivalences preserving covers; the section
identification identifies inverse image with transport of sheaves. Thus the unit and
counit are isomorphisms, and an equivalence preserves every existing limit and colimit. -/
theorem proEtaleIsoInverseImage_equivalence {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (ProEt.topology X) D] :
    (proEtaleSheafInverseImage f D).IsEquivalence ∧
      IsIso (proEtaleSheafAdjunction f D).unit ∧
      IsIso (proEtaleSheafAdjunction f D).counit ∧
      PreservesLimitsOfSize.{w', w} (proEtaleSheafInverseImage f D) ∧
      PreservesColimitsOfSize.{w', w} (proEtaleSheafInverseImage f D) := by
  sorry

/-- The canonical comparison induced by the inverse images of all tower projections.
The indexing natural number `r` denotes the original positive index `r+1`.
Source: Stacks Project, Tags 09A5 and 00WX
(blueprint: lem-weil-proetale-isomorphism-inverse-image).
Proof: the equivalence preserves the limit cone; its comparison `limit.post` is therefore
invertible. By its universal property its composites with the projections are exactly
the inverse images of the original projections. -/
theorem proEtaleIso_inverseLimitComparison {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (ProEt.topology X) D]
    (F : ℕᵒᵖ ⥤ Sheaf (ProEt.topology Y) D) [HasLimit F]
    [HasLimit (F ⋙ proEtaleSheafInverseImage f D)] :
    IsIso (limit.post F (proEtaleSheafInverseImage f D)) := by
  sorry

/-- Constant coefficient comparisons are isomorphisms and natural in the coefficient
object; in particular this asserts the ring-sheaf statement for every commutative ring.
Source: Stacks Project, Tags 09A5, 00WX and 0H7J
(blueprint: lem-weil-proetale-isomorphism-inverse-image).
Proof: under the canonical section identification the constant-presheaf map is the
identity. Sheafification preserves this identification. Naturality follows from the
naturality of the constant-presheaf map and the inverse-image adjunction counit. -/
theorem proEtaleIso_constantComparison {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (ProEt.topology X) D] [HasWeakSheafify (ProEt.topology Y) D] :
    (∀ A : D, IsIso (proEtaleConstantInverseImageMap f D A)) ∧
      ∀ (A B : D) (a : A ⟶ B),
        proEtaleConstantInverseImageMap f D A ≫
            (constantSheaf (ProEt.topology X) D).map a =
          (proEtaleSheafInverseImage f D).map
              ((constantSheaf (ProEt.topology Y) D).map a) ≫
            proEtaleConstantInverseImageMap f D B := by
  sorry

/-- The canonical ring-coefficient identification, with the recorded structure map as hom.
Source: Stacks Project, Tags 09A5 and 0H7J
(blueprint: lem-weil-proetale-isomorphism-inverse-image). -/
noncomputable def proEtaleIsoConstantRingComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] (A : CommRingCat.{u + 1}) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj A) ≅
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A :=
  @asIso _ _ _ _ (proEtaleConstantInverseImageMap f CommRingCat.{u + 1} A)
    ((proEtaleIso_constantComparison f CommRingCat.{u + 1}).1 A)

/-- For modules over any constant commutative ring, the specified tensor pullback and
sectionwise direct image are inverse equivalences. The unit and counit below specify the
quasi-inverse; the pullback already includes its canonical coefficient extension.
Source: Stacks Project, Tags 09A5, 00WX and 03D2
(blueprint: lem-weil-proetale-isomorphism-inverse-image).
Proof: the site equivalence transports module actions sectionwise, and the constant-ring
comparison is invertible. Tensor extension along it undoes restriction of scalars.
The two composites are the identity by the tensor unit isomorphisms and site equivalence. -/
theorem proEtaleIso_constantModuleEquivalence {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (A : CommRingCat.{u + 1}) :
    (proEtaleRingModulePullback f
      ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj A)
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A)
      (proEtaleIsoConstantRingComparison f A)).IsEquivalence ∧
    Nonempty (𝟭 _ ≅
      proEtaleRingModulePullback f
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj A)
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A)
        (proEtaleIsoConstantRingComparison f A) ⋙
      proEtaleRingModuleDirectImage f
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj A)
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A)
        (proEtaleIsoConstantRingComparison f A)) ∧
    Nonempty (proEtaleRingModuleDirectImage f
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj A)
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A)
        (proEtaleIsoConstantRingComparison f A) ⋙
      proEtaleRingModulePullback f
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj A)
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A)
        (proEtaleIsoConstantRingComparison f A) ≅ 𝟭 _) := by
  sorry

/-- Module sheaves over an arbitrary constant ring are transported equivalently, with
the actual sectionwise direct image as inverse. No commutativity of the ring is needed.
Source: Stacks Project, Tags 09A5, 00YV, 0H7J and 03D2
(blueprint: lem-weil-proetale-isomorphism-inverse-image).
Proof: postcomposition with `f` and its inverse gives inverse covering-preserving site
equivalences. Transport a module action along these equivalences. The constant-ring
identifications preserve every constant section, so the transported restriction maps are
semilinear and the resulting module maps are linear. Both composites are naturally the
identity, sectionwise by the identity on the underlying schemes. Direct image is exactly
precomposition by base change with scalars restricted along the recorded constant-section
map. Therefore it is the inverse functor of this equivalence; the forward functor is its
inverse-image left adjoint, determined up to the unique adjunction isomorphism. -/
theorem proEtaleIso_constantRingModuleEquivalence {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] (A : RingCat.{u + 1}) :
    ∃ e : ringedSiteModules.{u + 1}
          ((constantSheaf (ProEt.topology Y) RingCat.{u + 1}).obj A) ≌
        ringedSiteModules.{u + 1}
          ((constantSheaf (ProEt.topology X) RingCat.{u + 1}).obj A),
      e.inverse = SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
        (J := ProEt.topology Y) (K := ProEt.topology X)
        (proEtaleConstantDirectImageMap f RingCat.{u + 1} A) := by
  sorry

end AlgebraicGeometry.Scheme
