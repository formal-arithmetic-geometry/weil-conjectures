module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSetStalk
public import Sheaf.AlgebraicGeometry.AtlasEtaleRestriction
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Geometric points of the small étale topos of an algebraic space

Source: Stacks Project, Properties of Spaces, Tags 04K0, 04K2(4), 04K5
(blueprint: lem-sfb-space-geometric-points-conservative).

The existing pointed scheme neighbourhood category is used literally. Set coefficients
live in `Type (max (u + 1) w)`, so its colimits exist in the chosen ambient universe.
The inverse-image comparison is specified on germs of the adjunction unit. Its finite
product formula includes all algebraic operations, including mixed scalar actions.
The structural-map clause uses the actual regular functions, lifted by `ULift` only
for size, and specifies the resulting map on their geometric stalks.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The canonical small étale geometric morphism is the one with the published
base-change direct image. Its adjunction determines the inverse image up to its
unique adjunction-compatible isomorphism.
Source: Stacks, Tag 03G2(3), used in Tag 04K2
(blueprint: lem-sfb-space-geometric-points-conservative). -/
def smallEtaleMorphism {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    GeometricMorphism (Sheaf X.etaleTopology (Type (max (u + 1) w)))
      (Sheaf Y.etaleTopology (Type (max (u + 1) w))) :=
  (enlargedSmallDirectImage_geometric f).choose

/-- Pull a direct-image section back along a commuting pair of scheme charts.
This uses restriction on the enlarged site and the published restriction counit.
Source: Stacks, Tags 03G2(3), 03G8 and 04K2
(blueprint: lem-sfb-space-geometric-points-conservative). -/
def smallDirectImageChartSection {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (G : Sheaf X.etaleTopology (Type (max (u + 1) w)))
    (U : X.EtaleSite) (V : Y.EtaleSite) (a : U.obj.left ⟶ V.obj.left)
    (ha : yoneda.map a ≫ V.obj.hom = U.obj.hom ≫ f.hom.hom) :
    ((enlargedSmallDirectImage f).obj G).obj.obj (op V) ⟶ G.obj.obj (op U) :=
  ((enlargedSetEquivalence X).inverse.obj G).obj.map
      (enlargedChartLift f U V a ha).op ≫
    ((enlargedSetEquivalence X).counitIso.hom.app G).hom.app (op U)

/-- The local section of inverse image supplied by the unit on a target chart.
Source: Stacks, Tag 04K2(4), the displayed double-colimit proof
(blueprint: lem-sfb-space-geometric-points-conservative). -/
def inverseImageChartSection {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (F : Sheaf Y.etaleTopology (Type (max (u + 1) w)))
    (U : X.EtaleSite) (V : Y.EtaleSite) (a : U.obj.left ⟶ V.obj.left)
    (ha : yoneda.map a ≫ V.obj.hom = U.obj.hom ≫ f.hom.hom) :
    F.obj.obj (op V) ⟶ ((smallEtaleMorphism f).inverse.obj F).obj.obj (op U) :=
  ((smallEtaleMorphism f).adj.unit.app F).hom.app (op V) ≫
    (eqToHom (congrArg
      (fun D ↦ (D.obj ((smallEtaleMorphism f).inverse.obj F)).obj.obj (op V))
      (enlargedSmallDirectImage_geometric f).choose_spec)) ≫
    smallDirectImageChartSection f _ U V a ha

/-- A comparison is canonical when it sends each germ of the local adjunction unit
to the original target germ. Both chart and lift triangles are required.
Source: Stacks, Tag 04K2(4)
(blueprint: lem-sfb-space-geometric-points-conservative). -/
def IsGeometricStalkComparison {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {P : Over S} (x : yoneda.obj P ⟶ X.obj.obj)
    (e : (smallEtaleMorphism f).inverse ⋙ X.pointedSetStalk x ≅
      Y.pointedSetStalk (x ≫ f.hom.hom)) : Prop :=
  ∀ (F : Sheaf Y.etaleTopology (Type (max (u + 1) w)))
    (U : X.PointedEtale x) (V : Y.PointedEtale (x ≫ f.hom.hom))
    (a : U.right.obj.left ⟶ V.right.obj.left)
    (ha : yoneda.map a ≫ V.right.obj.hom = U.right.obj.hom ≫ f.hom.hom),
    U.hom.left ≫ a = V.hom.left →
      inverseImageChartSection f F U.right V.right a ha ≫
        X.pointedSetGerm x U ((smallEtaleMorphism f).inverse.obj F) ≫ e.hom.app F =
      Y.pointedSetGerm (x ≫ f.hom.hom) V F

/-- Lifting the underlying regular functions to the ambient universe preserves their
sheaf condition. Source: Stacks, Tags 03G7 and 04K2
(blueprint: lem-sfb-space-geometric-points-conservative).
Proof: a covering family is a jointly surjective étale family of schemes. Regular
functions satisfy its equalizer gluing condition. Forget ring structure, and apply
ULift.up and ULift.down to matching families and their unique amalgamations. This
proves the sheaf condition for the generating coverings and hence their topology.
The coefficient lift changes no sections or algebraic operations. -/
theorem geometricStructureSets_isSheaf (X : AlgebraicSpace S) :
    Presheaf.IsSheaf X.etaleTopology
      (X.structurePresheaf ⋙ forget RingCat.{u} ⋙ uliftFunctor.{max (u + 1) w, u}) := by
  sorry

/-- Regular functions as a sheaf of sets in the ambient universe. ULift preserves
all the original ring operations and sections; it is only coefficient-size transport.
Source: Stacks, Tags 03G7, 04K2 and the size convention
(blueprint: lem-sfb-space-geometric-points-conservative). -/
def geometricStructureSets (X : AlgebraicSpace S) :
    Sheaf X.etaleTopology (Type (max (u + 1) w)) :=
  ⟨X.structurePresheaf ⋙ forget RingCat.{u} ⋙ uliftFunctor.{max (u + 1) w, u},
    geometricStructureSets_isSheaf X⟩

/-- The structural map is prescribed on every commuting pair of scheme charts by
ordinary pullback of regular functions. This specifies the inverse-image ring map.
Source: Stacks, Tags 03G8 and 04K2(4)
(blueprint: lem-sfb-space-geometric-points-conservative). -/
def IsGeometricStructuralMap {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (σ : (smallEtaleMorphism.{u, w} f).inverse.obj (geometricStructureSets.{u, w} Y) ⟶
      (geometricStructureSets.{u, w} X)) : Prop :=
  ∀ (U : X.EtaleSite) (V : Y.EtaleSite) (a : U.obj.left ⟶ V.obj.left)
    (ha : yoneda.map a ≫ V.obj.hom = U.obj.hom ≫ f.hom.hom)
    (r : Y.structureSheaf.obj.obj (op V)),
    σ.hom.app (op U)
      (inverseImageChartSection f (geometricStructureSets.{u, w} Y) U V a ha (ULift.up r)) =
        ULift.up ((Scheme.Γ.map a.left.op) r)

/-- The geometric stalk is the inverse image of a topos point.
Source: Stacks, Tags 04K0, 00Y8 and 00YA
(blueprint: lem-sfb-space-geometric-points-conservative).
Proof: for A set, put P_A(U) = Map(Hom_X(Spec Ω,U), A), restrictions by precomposition.
A cover lifts every geometric point with its original field (03PR). Matching
functions glue independently of the chosen lift because two lifts meet in the scheme
fibre product. This also treats an empty lift set. The bijection between stalk maps
and maps F → P_A sends b to s ↦ (l ↦ b([U,l,s])); naturality makes its inverse
well-defined on colimit relations. These recipes are inverse and natural. Filtered
pointed-neighbourhood colimits commute with finite limits, giving left exactness. -/
theorem pointedSetStalk_isPoint (X : AlgebraicSpace S) (Ω : Type u)
    [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk b) ⟶ X.obj.obj) :
    (∃ D : Type (max (u + 1) w) ⥤ Sheaf X.etaleTopology (Type (max (u + 1) w)),
      Nonempty (X.pointedSetStalk x ⊣ D)) ∧
    PreservesFiniteLimits (X.pointedSetStalk.{u, w} x) := by
  sorry

/-- Geometric stalks detect monomorphisms, epimorphisms and isomorphisms.
Epimorphism means local surjectivity of sheaves, not surjectivity on all sections.
Source: Stacks, Tag 04K5
(blueprint: lem-sfb-space-geometric-points-conservative).
Proof: use lem-sfb-space-etale-conservative-geometric-points, with the identical
pointed-neighbourhood colimit. Alternatively choose a surjective étale scheme atlas;
restriction to it detects mono and epi, and the scheme stalk theorem gives the tests.
A map that is both mono and epi in a sheaf topos is an isomorphism. For the empty
space the sheaf category is terminal up to equivalence, so the empty point family
still detects all three properties. -/
theorem geometricStalk_mono_epi_iso_iff (X : AlgebraicSpace S)
    {F G : Sheaf X.etaleTopology (Type (max (u + 1) w))} (α : F ⟶ G) :
    (Mono α ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (b : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk b) ⟶ X.obj.obj),
      Function.Injective ((X.pointedSetStalk x).map α)) ∧
    (Epi α ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (b : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk b) ⟶ X.obj.obj),
      Function.Surjective ((X.pointedSetStalk x).map α)) ∧
    (IsIso α ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (b : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk b) ⟶ X.obj.obj),
      Function.Bijective ((X.pointedSetStalk x).map α)) := by
  sorry

/-- The canonical natural comparison of stalks commutes with every finite product.
Consequently naturality with any operation from a finite product, including a mixed
product of different sorts, says that the comparison preserves that operation.
Source: Stacks, Tag 04K2(4)
(blueprint: lem-sfb-space-geometric-points-conservative).
Proof: apply lem-sfb-space-etale-pullback-chart-comparison after changing base to
Spec Z with lem-sfb-space-change-base-to-integers. The latter identifies small sites,
coverings, structure sheaves and base-change functors, so the comparison applies over
arbitrary S. Equivalently compute the stalk of the inverse-image sheafification by
its double colimit: a pointed chart and a map to a pulled-back target chart give
exactly a target pointed chart. This sends germs of the unit to the original germs,
so gives the specified unique isomorphism, naturally in F. Naturality with projections
identifies its finite-product component with the product of its components, including
the empty product for constants. Naturality with each operation then proves the
algebraic compatibility asserted in the node. -/
theorem geometricStalk_inverseImage {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk b) ⟶ X.obj.obj) :
    ∃! e : (smallEtaleMorphism.{u, w} f).inverse ⋙ X.pointedSetStalk x ≅
        Y.pointedSetStalk (x ≫ f.hom.hom),
      IsGeometricStalkComparison f x e ∧
      ∀ (n : ℕ) (F : Fin n → Sheaf Y.etaleTopology (Type (max (u + 1) w))),
        e.hom.app (∏ᶜ F) ≫ piComparison (Y.pointedSetStalk (x ≫ f.hom.hom)) F =
          piComparison ((smallEtaleMorphism f).inverse ⋙ X.pointedSetStalk x) F ≫
            Limits.Pi.map (fun i ↦ e.hom.app (F i)) := by
  sorry

/-- The structural ring map is canonical, and the point comparison gives its actual
map on stalk rings, characterized on germs by pullback of regular functions.
Together with finite-product compatibility above, this respects 0, 1, + and ×.
Source: Stacks, Tags 03G8 and 04K2(4)
(blueprint: lem-sfb-space-geometric-points-conservative).
Proof: transpose the enlarged-site structural map and transport it through the small
site equivalences. Its chart formula is precisely IsGeometricStructuralMap. Atlas
restriction and the adjunction unit show uniqueness. For a compatible pair of pointed
charts, the inverse comparison sends the target germ of r to the source germ of
its unit section. Apply the structural map and its chart formula; the result is
the germ of the ordinary pullback of r. This is the colimit description of the
canonical stalk-ring map. Finite-product compatibility and naturality with the ring
operations show it is a ring map. The same argument treats all algebraic operations
and scalar actions on sheaves; no choice of an unrelated stalk isomorphism is made. -/
theorem geometricStalk_structureMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ∃! σ : (smallEtaleMorphism.{u, w} f).inverse.obj (geometricStructureSets.{u, w} Y) ⟶
        (geometricStructureSets.{u, w} X),
      IsGeometricStructuralMap f σ ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ S)
        (x : yoneda.obj (Over.mk b) ⟶ X.obj.obj)
        (e : (smallEtaleMorphism f).inverse ⋙ X.pointedSetStalk x ≅
          Y.pointedSetStalk (x ≫ f.hom.hom)),
        IsGeometricStalkComparison f x e →
        ∀ (U : X.PointedEtale x) (V : Y.PointedEtale (x ≫ f.hom.hom))
          (a : U.right.obj.left ⟶ V.right.obj.left)
          (ha : yoneda.map a ≫ V.right.obj.hom = U.right.obj.hom ≫ f.hom.hom),
          U.hom.left ≫ a = V.hom.left →
          ∀ r : Y.structureSheaf.obj.obj (op V.right),
            (X.pointedSetStalk x).map σ
              (e.inv.app (geometricStructureSets.{u, w} Y)
                (Y.pointedSetGerm (x ≫ f.hom.hom) V (geometricStructureSets.{u, w} Y)
                  (ULift.up r))) =
              X.pointedSetGerm x U (geometricStructureSets.{u, w} X)
                (ULift.up ((Scheme.Γ.map a.left.op) r)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
