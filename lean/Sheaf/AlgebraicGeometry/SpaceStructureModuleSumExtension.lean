module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceGeometricStalkModels
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceCommAlgebraSheaf
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbelianStalk
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.DirectSum.Module

/-! # Structure-module étale sum extension and its germ coordinates

Source: Stacks Project, spaces-perfect.tex, Tag 08GU, equations stalk-restriction
and stalk-j-shriek; sites-modules.tex, Tag 0710, including its germ construction
(blueprint: def-sfb-space-structure-module-sum-extension).

Lift indices are sections of the represented point functor. Yoneda identifies these
with the actual scheme maps, while keeping the original section universe. Stalks are
exactly the existing normalized pointed-affine colimits. Germs on arbitrary scheme
charts are characterized by restriction to that cofinal basis.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S}

/-- Scheme-valued lifts, written as sections through Yoneda to retain their size.
Source: Stacks 0710 (blueprint: def-sfb-space-structure-module-sum-extension). -/
def SumLift (j : Z ⟶ X) {T : Over S} (t : yoneda.obj T ⟶ X.obj.obj) :=
  {a : Z.obj.obj.obj (op T) // j.hom.hom.app (op T) a = yonedaEquiv t}

/-- A section lift gives the actual commuting triangle of scheme-valued points.
Source: Stacks 0710 (blueprint: def-sfb-space-structure-module-sum-extension).
Proof: Yoneda identifies composition with evaluation of the natural transformation;
the required equality is the defining equality of the subtype. -/
theorem sumLift_over (j : Z ⟶ X) {T : Over S} (t : yoneda.obj T ⟶ X.obj.obj)
    (a : SumLift j t) : yonedaEquiv.symm a.val ≫ j.hom.hom = t := by
  sorry

/-- A lift between étale objects is étale, including without separation or compactness.
Source: Stacks 03FV and 0710 (blueprint: def-sfb-space-structure-module-sum-extension).
Proof: both the scheme chart and Z are étale over X. Base change to a scheme atlas
and use cancellation of étale scheme maps, as in
lem-trf-space-chartwise-etale-permanence. Descent gives the representable étale lift. -/
theorem sumLift_isEtale (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    (W : X.EtaleSite) (a : SumLift j W.obj.hom) :
    IsEtale (yonedaEquiv.symm a.val) := by
  sorry

/-- The chart of Z specified by a lift of a scheme chart of X.
Source: Stacks 0710 (blueprint: def-sfb-space-structure-module-sum-extension). -/
def sumLiftChart (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    (W : X.EtaleSite) (a : SumLift j W.obj.hom) : Z.EtaleSite :=
  ⟨CostructuredArrow.mk (yonedaEquiv.symm a.val), sumLift_isEtale j hj W a⟩

/-- Restricting a lift section still lies over the restricted chart.
Source: Stacks 0710 (blueprint: def-sfb-space-structure-module-sum-extension).
Proof: naturality of j moves its component past the restriction; the lift equation
and the commuting triangle of the chart arrow give the asserted equality. -/
theorem sumLift_restrict_over (j : Z ⟶ X) {V W : X.EtaleSite} (r : V ⟶ W)
    (a : SumLift j W.obj.hom) :
    j.hom.hom.app (op V.obj.left) (Z.obj.obj.map r.hom.left.op a.val) =
      yonedaEquiv V.obj.hom := by
  sorry

/-- Pullback of lift labels along a scheme-chart arrow.
Source: Stacks 0710 (blueprint: def-sfb-space-structure-module-sum-extension). -/
def sumLiftRestrict (j : Z ⟶ X) {V W : X.EtaleSite} (r : V ⟶ W)
    (a : SumLift j W.obj.hom) : SumLift j V.obj.hom :=
  ⟨Z.obj.obj.map r.hom.left.op a.val, sumLift_restrict_over j r a⟩

/-- The restriction triangle for the lifted charts commutes.
Source: Stacks 0710 (blueprint: def-sfb-space-structure-module-sum-extension).
Proof: Yoneda turns restriction of a section into precomposition of its represented
map. Apply the Yoneda naturality identity to the actual underlying scheme arrow. -/
theorem sumLiftChart_w (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    {V W : X.EtaleSite} (r : V ⟶ W) (a : SumLift j W.obj.hom) :
    yoneda.map r.hom.left ≫ (sumLiftChart j hj W a).obj.hom =
      (sumLiftChart j hj V (sumLiftRestrict j r a)).obj.hom := by
  sorry

/-- The underlying scheme arrow between restricted lift charts.
Source: Stacks 0710 (blueprint: def-sfb-space-structure-module-sum-extension). -/
def sumLiftChartMap (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    {V W : X.EtaleSite} (r : V ⟶ W) (a : SumLift j W.obj.hom) :
    sumLiftChart j hj V (sumLiftRestrict j r a) ⟶ sumLiftChart j hj W a :=
  ObjectProperty.homMk (CostructuredArrow.homMk r.hom.left (sumLiftChart_w j hj r a))

/-- The actual sectionwise direct sum, with the regular-functions action on each copy.
Source: Stacks 0710 (blueprint: def-sfb-space-structure-module-sum-extension). -/
def spaceSumSection (j : Z ⟶ X) (hj : IsEtale j.hom.hom) (M : Z.Modules)
    (W : X.EtaleSite) : ModuleCat.{u} (X.structurePresheaf.obj (op W)) :=
  ModuleCat.of _ (DirectSum (SumLift j W.obj.hom)
    (fun a ↦ M.val.obj (op (sumLiftChart j hj W a))))

open Classical in
/-- Restriction relabels and adds summands, even when distinct lifts merge.
Source: Stacks 0710 (blueprint: def-sfb-space-structure-module-sum-extension). -/
def spaceSumRestrict (j : Z ⟶ X) (hj : IsEtale j.hom.hom) (M : Z.Modules)
    {V W : X.EtaleSite} (r : V ⟶ W) :
    spaceSumSection j hj M W →+ spaceSumSection j hj M V :=
  DirectSum.toAddMonoid (fun a ↦
    (DirectSum.of (fun b ↦ M.val.obj (op (sumLiftChart j hj V b)))
      (sumLiftRestrict j r a)).comp
        (M.val.map (sumLiftChartMap j hj r a).op).hom.toAddMonoidHom)

/-- Semilinearity and the two presheaf identities for the direct-sum restrictions.
Source: Stacks 0710 (blueprint: def-sfb-space-structure-module-sum-extension).
Proof: test each equality on a single direct-sum injection. Semilinearity is that of
M on its lifted chart. Identity and composition are the corresponding identities
of M and restriction of lift sections. Direct-sum induction extends the equations
to all finite sums; no injectivity of the relabelling is used. -/
theorem spaceSumRestrict_laws (j : Z ⟶ X) (hj : IsEtale j.hom.hom) (M : Z.Modules) :
    (∀ (V W : X.EtaleSite) (r : V ⟶ W) (b : X.structurePresheaf.obj (op W))
      (m : spaceSumSection j hj M W),
      spaceSumRestrict j hj M r (b • m) =
        X.structurePresheaf.map r.op b • spaceSumRestrict j hj M r m) ∧
    (∀ (W : X.EtaleSite) (m : spaceSumSection j hj M W),
      spaceSumRestrict j hj M (𝟙 W) m = m) ∧
    (∀ (U V W : X.EtaleSite) (r : U ⟶ V) (s : V ⟶ W)
      (m : spaceSumSection j hj M W),
      spaceSumRestrict j hj M (r ≫ s) m =
        spaceSumRestrict j hj M r (spaceSumRestrict j hj M s m)) := by
  sorry

/-- Underlying additive direct-sum presheaf with literal section and restriction data.
Source: Stacks 0710 (blueprint: def-sfb-space-structure-module-sum-extension). -/
def spaceSumAbPresheaf (j : Z ⟶ X) (hj : IsEtale j.hom.hom) (M : Z.Modules) :
    X.EtaleSiteᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj W := AddCommGrpCat.of (spaceSumSection j hj M W.unop)
  map r := AddCommGrpCat.ofHom (spaceSumRestrict j hj M r.unop)
  map_id W := AddCommGrpCat.hom_ext (AddMonoidHom.ext
    ((spaceSumRestrict_laws j hj M).2.1 W.unop))
  map_comp r s := AddCommGrpCat.hom_ext (AddMonoidHom.ext
    ((spaceSumRestrict_laws j hj M).2.2 _ _ _ s.unop r.unop))

/-- The inherited scalar action on the explicit additive sum presheaf.
Source: Stacks 0710 (blueprint: def-sfb-space-structure-module-sum-extension). -/
instance spaceSumAbPresheaf_module (j : Z ⟶ X) (hj : IsEtale j.hom.hom) (M : Z.Modules)
    (W : X.EtaleSiteᵒᵖ) :
    Module (X.structurePresheaf.obj W) ((spaceSumAbPresheaf j hj M).obj W) :=
  (spaceSumSection j hj M W.unop).isModule

/-- The presheaf of structure modules in the statement; only laws are postponed.
Source: Stacks 0710 (blueprint: def-sfb-space-structure-module-sum-extension). -/
def spaceSumPresheaf (j : Z ⟶ X) (hj : IsEtale j.hom.hom) (M : Z.Modules) :
    PresheafOfModules.{u} X.structurePresheaf :=
  PresheafOfModules.ofPresheaf (spaceSumAbPresheaf j hj M)
    (fun _ _ r b m ↦ (spaceSumRestrict_laws j hj M).1 _ _ r.unop b m)

/-- Sum extension is exactly module sheafification of the specified presheaf.
Source: Stacks 0710 and 08GU
(blueprint: def-sfb-space-structure-module-sum-extension). -/
def spaceSumExtension (j : Z ⟶ X) (hj : IsEtale j.hom.hom) (M : Z.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.structureSheaf.obj)).obj (spaceSumPresheaf j hj M)



/-- The section map of a morphism on the sum presheaf, applied to each summand.
Source: Stacks 0710 (blueprint: def-sfb-space-structure-module-sum-extension). -/
def spaceSumSectionHom (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    {M N : Z.Modules} (f : M ⟶ N) (W : X.EtaleSite) :
    spaceSumSection j hj M W ⟶ spaceSumSection j hj N W :=
  ModuleCat.ofHom (DirectSum.lmap (fun a ↦ (f.val.app (op (sumLiftChart j hj W a))).hom))

/-- Sectionwise maps commute with the specified sum restrictions.
Source: Stacks 0710 (blueprint: def-sfb-space-structure-module-sum-extension).
Proof: on the a-summand, this is naturality of f on the lifted chart arrow. Both
sides are additive, so direct-sum induction gives the result for all sections. -/
theorem spaceSumSectionHom_naturality (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    {M N : Z.Modules} (f : M ⟶ N) {V W : X.EtaleSite} (r : V ⟶ W)
    (m : spaceSumSection j hj M W) :
    spaceSumRestrict j hj N r (spaceSumSectionHom j hj f W m) =
      spaceSumSectionHom j hj f V (spaceSumRestrict j hj M r m) := by
  sorry

/-- The actual morphism of presheaves induced by a module-sheaf morphism.
Source: Stacks 0710 (blueprint: def-sfb-space-structure-module-sum-extension). -/
def spaceSumPresheafHom (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    {M N : Z.Modules} (f : M ⟶ N) : spaceSumPresheaf j hj M ⟶ spaceSumPresheaf j hj N :=
  PresheafOfModules.homMk
    { app W := AddCommGrpCat.ofHom (spaceSumSectionHom j hj f W.unop).hom.toAddMonoidHom
      naturality _ _ r := AddCommGrpCat.hom_ext (AddMonoidHom.ext
        (fun m ↦ (spaceSumSectionHom_naturality j hj f r.unop m).symm)) }
    (fun W b m ↦ (spaceSumSectionHom j hj f W.unop).hom.map_smul b m)

/-- The induced morphism of sum extensions is module sheafification of that map.
Source: Stacks 0710 (blueprint: def-sfb-space-structure-module-sum-extension). -/
def spaceSumExtensionHom (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    {M N : Z.Modules} (f : M ⟶ N) : spaceSumExtension j hj M ⟶ spaceSumExtension j hj N :=
  (PresheafOfModules.sheafification (𝟙 X.structureSheaf.obj)).map
    (spaceSumPresheafHom j hj f)

open Classical in
/-- Include a section in its lift summand and then apply the sheafification unit.
Source: Stacks 0710 (blueprint: def-sfb-space-structure-module-sum-extension). -/
def spaceSumGenerator (j : Z ⟶ X) (hj : IsEtale j.hom.hom) (M : Z.Modules)
    (W : X.EtaleSite) (a : SumLift j W.obj.hom)
    (m : M.val.obj (op (sumLiftChart j hj W a))) :
    (spaceSumExtension j hj M).val.obj (op W) :=
  (toSheafify X.etaleTopology (spaceSumPresheaf j hj M).presheaf).app (op W)
    (DirectSum.of (fun a ↦ M.val.obj (op (sumLiftChart j hj W a))) a m)

/-- The usual germ on every scheme chart is uniquely determined on the affine basis.
Source: Stacks 04JY and 0710 (blueprint: def-sfb-space-structure-module-sum-extension).
Proof: refine the pointed chart by an affine open containing its geometric point,
then by the chosen small affine basis. Send its restricted section to its colimit
germ. Any two refinements admit a common pointed refinement, so this is independent
of choices and additive. The same comparison with one refinement proves uniqueness.
It agrees with every pointed scheme-neighbourhood colimit cocone by cofinality. -/
theorem spaceChartGerm_existsUnique {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj)
    (M : X.Modules) (W : X.PointedEtale x) :
    ∃! g : M.val.obj (op W.right) →+ (SingleComplex.stalkModel s x).modules.obj M,
      ∀ (V : SingleComplex.Neighbourhood (Over.mk s) x)
        (r : (SingleComplex.neighbourhoodChart (x := x)).obj V ⟶ W.right),
        V.hom.left ≫ r.hom.left = W.hom.left →
        ∀ m : M.val.obj (op W.right),
          g m = ((SingleComplex.stalkModel s x).germs M).app (op V) (M.val.map r.op m) := by
  sorry

/-- Germ on an arbitrary pointed scheme chart, fixed by its affine-refinement equation.
Source: Stacks 04JY and 0710 (blueprint: def-sfb-space-structure-module-sum-extension). -/
def spaceChartGerm {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj)
    (M : X.Modules) (W : X.PointedEtale x) :=
  Classical.choose (spaceChartGerm_existsUnique s x M W)

/-- The structural map at a lift, with the target point equality transported explicitly.
Source: Stacks 08GU, stalk-restriction
(blueprint: def-sfb-space-structure-module-sum-extension). -/
def spaceSumStalkScalar (j : Z ⟶ X) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) (a : SumLift j x) :
    SingleComplex.stalkRing s x →+* SingleComplex.stalkRing s (yonedaEquiv.symm a.val) :=
  (SingleComplex.stalkMap j s (yonedaEquiv.symm a.val)).comp
    (CommRingCat.Hom.hom (eqToHom (congrArg (SingleComplex.stalkRing s)
      (sumLift_over j x a).symm)))

/-- The source module stalk regarded over the target local ring by its structural map.
Source: Stacks 08GU and 0710
(blueprint: def-sfb-space-structure-module-sum-extension). -/
def spaceSumStalkPiece (j : Z ⟶ X) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj)
    (M : Z.Modules) (a : SumLift j x) : ModuleCat.{u} (SingleComplex.stalkRing s x) :=
  (ModuleCat.restrictScalars (spaceSumStalkScalar j s x a)).obj
    ((SingleComplex.stalkModel s (yonedaEquiv.symm a.val)).modules.obj M)

/-- A lift evaluated at the pointed chart lies over the given geometric point.
Source: Stacks 0710 (blueprint: def-sfb-space-structure-module-sum-extension).
Proof: naturality of j and the pointed-chart triangle identify its image with x.
This is exactly the map (W,w,a) to a w in the source's proof. -/
theorem spaceSumPointLift_over (j : Z ⟶ X) {P : Over S}
    (x : yoneda.obj P ⟶ X.obj.obj) (W : X.PointedEtale x)
    (a : SumLift j W.right.obj.hom) :
    j.hom.hom.app (op P) (Z.obj.obj.map W.hom.left.op a.val) = yonedaEquiv x := by
  sorry

/-- The label a w of the destination summand.
Source: Stacks 0710 (blueprint: def-sfb-space-structure-module-sum-extension). -/
def spaceSumPointLift (j : Z ⟶ X) {P : Over S}
    (x : yoneda.obj P ⟶ X.obj.obj) (W : X.PointedEtale x)
    (a : SumLift j W.right.obj.hom) : SumLift j x :=
  ⟨Z.obj.obj.map W.hom.left.op a.val, spaceSumPointLift_over j x W a⟩

/-- The lifted chart with its original pointing is over the evaluated lift a w.
Source: Stacks 0710 (blueprint: def-sfb-space-structure-module-sum-extension).
Proof: the Yoneda naturality formula identifies the composite of w and a with
the natural transformation represented by the restricted section defining a w. -/
theorem spaceSumLiftPointed_w (j : Z ⟶ X) (hj : IsEtale j.hom.hom) {P : Over S}
    (x : yoneda.obj P ⟶ X.obj.obj) (W : X.PointedEtale x)
    (a : SumLift j W.right.obj.hom) :
    yoneda.map W.hom.left ≫ (sumLiftChart j hj W.right a).obj.hom =
      yonedaEquiv.symm (spaceSumPointLift j x W a).val := by
  sorry

/-- The pointed scheme neighbourhood of the source lift supplied by (W,w,a).
Source: Stacks 0710 (blueprint: def-sfb-space-structure-module-sum-extension). -/
def spaceSumLiftPointed (j : Z ⟶ X) (hj : IsEtale j.hom.hom) {P : Over S}
    (x : yoneda.obj P ⟶ X.obj.obj) (W : X.PointedEtale x)
    (a : SumLift j W.right.obj.hom) :
    Z.PointedEtale (yonedaEquiv.symm (spaceSumPointLift j x W a).val) :=
  StructuredArrow.mk (Y := sumLiftChart j hj W.right a)
    (CostructuredArrow.homMk W.hom.left (spaceSumLiftPointed_w j hj x W a))

end AlgebraicGeometry.AlgebraicSpace
