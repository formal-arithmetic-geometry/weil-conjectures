/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import Mathlib.CategoryTheory.Subfunctor.Image

/-!
# Scheme-test presentations for a line module and its graded sections

Source: Stacks Project, Properties of Spaces, Tag 03G7; Divisors on Spaces, Tag 0D2Z;
and Constructions, Tag 01O9 (blueprint: def-trf-space-line-module-proj-input).

A cartesian family specifies the actual tensor pullbacks to schemes. Its identification
on the small etale site identifies the family with the given line module, rather than
introducing an unrelated line bundle. Graded maps are specified on homogeneous sections
on affine opens of the base, with scalar, product, unit, and restriction equations.

## Main definitions

* `EtaleLinePresentation` and `lineTestFamily` realize the given small-etale line module.
* `GradedLineMap` specifies the homogeneous algebra map on the actual scheme pullbacks.
* `GradedLineMap.IsGenerationOpen` specifies its positive-degree generation open.
* `GradedLineMap.IsCanonicalMap` specifies the usual local relative-Proj construction.
* `GradedLineMap.IsBaseChange` specifies the coefficientwise pulled-back graded map.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Schemes mapping to a presheaf, with commuting triangles as morphisms.
Source: Stacks, Tag 0D2Z (blueprint: def-trf-space-line-module-proj-input). -/
abbrev SchemeTests (F : (Over S)ᵒᵖ ⥤ Type u) := CostructuredArrow yoneda F

/-- The structural map of a scheme test to the scheme base.
Source: Stacks, Tag 0D2Z (blueprint: def-trf-space-line-module-proj-input). -/
noncomputable def testToBase {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    (f : F ⟶ yoneda.obj T) (W : SchemeTests F) : W.left ⟶ T :=
  yoneda.preimage (W.hom ≫ f)

/-- A family of invertible modules with specified tensor-pullback identifications.
Coherence and identification with the small-etale module are imposed below.
Source: Stacks, Tags 03G7 and 0D2Z
(blueprint: def-trf-space-line-module-proj-input). -/
structure TestLineFamily (F : (Over S)ᵒᵖ ⥤ Type u) where
  module (W : SchemeTests F) : W.left.left.Modules
  invertible (W : SchemeTests F) : (module W).IsInvertible
  pullbackIso {W V : SchemeTests F} (j : W ⟶ V) :
    (Scheme.Modules.tensorPullback j.left.left).obj (module V) ≅ module W

attribute [instance] TestLineFamily.invertible

/-- Pullback of a global section, using the tensor-formula adjunction normalized by
`1 ⊗ eta(s)`, followed by the specified cartesian identification.
Source: Stacks, Tags 0095, 0096 and 0D2Z
(blueprint: def-trf-space-line-module-proj-input). -/
noncomputable def TestLineFamily.sectionMap {F : (Over S)ᵒᵖ ⥤ Type u}
    (L : TestLineFamily F) {W V : SchemeTests F} (j : W ⟶ V)
    (s : Γ(L.module V, ⊤)) : Γ(L.module W, ⊤) :=
  (L.pullbackIso j).hom.app ⊤
    (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j.left.left)).unit.app
      (L.module V)).val.app (op ⊤) s)

/-- The same pullback on tensor powers, using the existing monoidal comparisons.
Source: Stacks, Tags 01CD and 0D2Z
(blueprint: def-trf-space-line-module-proj-input). -/
noncomputable def TestLineFamily.powerMap {F : (Over S)ᵒᵖ ⥤ Type u}
    (L : TestLineFamily F) {W V : SchemeTests F} (j : W ⟶ V) (n : ℕ)
    (s : Γ((L.module V).tensorPow n, ⊤)) : Γ((L.module W).tensorPow n, ⊤) :=
  (Scheme.Modules.boundaryPullbackPowIso j.left.left (L.module V) n ≪≫
    Scheme.Modules.boundaryTensorPowIso (L.pullbackIso j) n).hom.app ⊤
    (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j.left.left)).unit.app
      ((L.module V).tensorPow n)).val.app (op ⊤) s)

/-- The full identity and composition equations of the cartesian pullback isomorphisms.
These are equations of sheaf isomorphisms, so they include every local section.
Source: Stacks, Tags 03G7 and 0097
(blueprint: def-trf-space-line-module-proj-input). -/
def TestLineFamily.IsCoherent {F : (Over S)ᵒᵖ ⥤ Type u} (L : TestLineFamily F) : Prop :=
  (∀ W : SchemeTests F, L.pullbackIso (𝟙 W) =
    (Scheme.Modules.boundaryPullbackComparison (𝟙 W.left.left)).app (L.module W) ≪≫
      (Scheme.Modules.pullbackId W.left.left).app (L.module W)) ∧
    ∀ (W V Z : SchemeTests F) (j : W ⟶ V) (k : V ⟶ Z),
      L.pullbackIso (j ≫ k) =
        (Scheme.Modules.tensorPullbackCompositionIso j.left.left k.left.left
          (j ≫ k).left.left rfl).app (L.module Z) ≪≫
        (Scheme.Modules.tensorPullback j.left.left).mapIso (L.pullbackIso k) ≪≫
        L.pullbackIso j

/-- Restricting a cartesian family along a map of presheaves is its scheme-test pullback.
There are no choices of objects or morphisms in this construction.
Source: Stacks, Tag 0D2Z(3) (blueprint: def-trf-space-line-module-proj-input). -/
noncomputable def TestLineFamily.pullback {F G : (Over S)ᵒᵖ ⥤ Type u}
    (L : TestLineFamily F) (g : G ⟶ F) : TestLineFamily G where
  module W := L.module ((CostructuredArrow.map g).obj W)
  invertible W := L.invertible ((CostructuredArrow.map g).obj W)
  pullbackIso j := L.pullbackIso ((CostructuredArrow.map g).map j)

/-- A cartesian scheme-test presentation of the given small-etale line module.
The additive equivalences are linear over regular functions, and commute with every
small-etale restriction map. Thus the family is the pullback of `line`, not arbitrary
extra line modules on the test schemes.
Source: Stacks, Tags 03G7 and 0D2Z
(blueprint: def-trf-space-line-module-proj-input). -/
structure EtaleLinePresentation (X : AlgebraicSpace S) extends TestLineFamily X.obj.obj where
  coherent : toTestLineFamily.IsCoherent
  line : X.Modules
  isLine : X.IsLineModule line
  etaleSections (T : X.EtaleSite) : Γ(module T.obj, ⊤) ≃+ line.val.obj (op T)
  etaleSections_smul (T : X.EtaleSite) (r : Γ(T.obj.left.left, ⊤))
      (s : Γ(module T.obj, ⊤)) : etaleSections T (r • s) = r • etaleSections T s
  etaleSections_naturality {T U : X.EtaleSite} (j : T ⟶ U)
      (s : Γ(module U.obj, ⊤)) :
    etaleSections T (toTestLineFamily.sectionMap j.hom s) =
      line.val.map j.op (etaleSections U s)

/-- Cartesian isomorphisms of the actual pullback modules on scheme tests.
Source: Stacks, Tags 03G7 and 0D2Z
(blueprint: def-trf-space-line-module-proj-input). -/
structure TestLineIso {F : (Over S)ᵒᵖ ⥤ Type u} (P Q : TestLineFamily F) where
  app (W : SchemeTests F) : P.module W ≅ Q.module W
  naturality {W V : SchemeTests F} (j : W ⟶ V) :
    (P.pullbackIso j).hom ≫ (app W).hom =
      (Scheme.Modules.tensorPullback j.left.left).map (app V).hom ≫ (Q.pullbackIso j).hom

/-- Compatibility with the prescribed small-etale module, rather than only an abstract
isomorphism of the test families. `HEq` uses the fixed equality of the underlying line
modules when applying this predicate to two realizations of the same module.
Source: Stacks, Tags 03G7 and 0D2Z
(blueprint: def-trf-space-line-module-proj-input). -/
def TestLineIso.IsEtaleCompatible {X : AlgebraicSpace S} (P Q : EtaleLinePresentation X)
    (e : TestLineIso P.toTestLineFamily Q.toTestLineFamily) : Prop :=
  ∀ (T : X.EtaleSite) (s : Γ(P.module T.obj, ⊤)),
    HEq (Q.etaleSections T ((e.app T.obj).hom.app ⊤ s)) (P.etaleSections T s)

/-- Every small-etale line module has its cartesian scheme-test realization, uniquely
up to the unique isomorphism inducing the identity of that small-etale module. This
universal property determines all the objects used in the construction up to the
specified equality, namely cartesian isomorphism preserving the etale identification.
Source: Stacks, Tags 03G7 and 0D2Z, descent of invertible modules
(blueprint: def-trf-space-line-module-proj-input).
Proof: trivialize the given line module on an etale scheme atlas. For each scheme
mapping to X, pull back that atlas; representability of the diagonal makes its terms
and double intersections schemes. Pull back the trivial line bundles and their unit
transition functions. Effective etale descent of invertible modules glues them to an
invertible module on the test scheme. Uniqueness of descent gives the tensor-pullback
identifications for all test maps and their identity and composition equations. On
etale tests the descended sections are exactly the sections of the given small-etale
module. Conversely those etale identifications fix the transition functions. Two
realizations therefore have exactly one compatible isomorphism on every test; the
isomorphisms commute with pullback by uniqueness of descent. The empty scheme has the
unique module and unique descent datum, so the argument also covers empty tests. -/
theorem exists_linePresentation (X : AlgebraicSpace S) (L : X.Modules)
    (hL : X.IsLineModule L) :
    ∃ P : EtaleLinePresentation X, P.line = L ∧
      ∀ Q : EtaleLinePresentation X, Q.line = L →
        ∃! e : TestLineIso P.toTestLineFamily Q.toTestLineFamily,
          e.IsEtaleCompatible P Q := by
  sorry

/-- The cartesian realization selected by its preceding universal property. It is
uniquely determined up to the unique isomorphism preserving the original line module.
Source: Stacks, Tag 0D2Z (blueprint: def-trf-space-line-module-proj-input). -/
noncomputable def linePresentation (X : AlgebraicSpace S) (L : X.Modules)
    (hL : X.IsLineModule L) : EtaleLinePresentation X :=
  (exists_linePresentation X L hL).choose

/-- The actual family of scheme pullbacks of the given line module.
Source: Stacks, Tag 0D2Z (blueprint: def-trf-space-line-module-proj-input). -/
noncomputable def lineTestFamily (X : AlgebraicSpace S) (L : X.Modules)
    (hL : X.IsLineModule L) : TestLineFamily X.obj.obj :=
  (linePresentation X L hL).toTestLineFamily

/-- A graded algebra map to tensor powers of the line module, written on homogeneous
sections of affine base charts. The linearity and naturality equations are the adjoint
form of a map from tensor pullback of the graded algebra sheaf.
Source: Stacks, Tags 0D2Z and 01O9
(blueprint: def-trf-space-line-module-proj-input). -/
structure GradedLineMap {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    (f : F ⟶ yoneda.obj T) (A : T.left.GradedAlgebraData) (L : TestLineFamily F) where
  component (W : SchemeTests F) (V : T.left.affineOpens)
      (h : (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V.1) (n : ℕ) :
    A.grading V n →+ Γ((L.module W).tensorPow n, ⊤)
  smul (W : SchemeTests F) (V : T.left.affineOpens)
      (h : (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V.1)
      (n : ℕ) (r : Γ(T.left, V.1)) (a : A.grading V n) :
    component W V h n (r • a) =
      ((testToBase f W).left.appLE V.1 ⊤ h r) • component W V h n a
  one (W : SchemeTests F) (V : T.left.affineOpens)
      (h : (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V.1) :
    component W V h 0 ⟨1, SetLike.one_mem_graded (A.grading V)⟩ =
      Scheme.Modules.unitSectionsEquiv ⊤ 1
  mul (W : SchemeTests F) (V : T.left.affineOpens)
      (h : (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V.1)
      (m n : ℕ) (a : A.grading V m) (b : A.grading V n) :
    component W V h (m + n) ⟨a * b, SetLike.mul_mem_graded a.property b.property⟩ =
      ((L.module W).tensorPowAddIso m n).inv.app ⊤
        (Scheme.Modules.tmulSection (component W V h m a) (component W V h n b))
  naturality {W W' : SchemeTests F} (j : W ⟶ W') (V : T.left.affineOpens)
      (h : (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V.1)
      (h' : (⊤ : W'.left.left.Opens) ≤ (testToBase f W').left ⁻¹ᵁ V.1)
      (n : ℕ) (a : A.grading V n) :
    component W V h n a = L.powerMap j n (component W' V h' n a)
  restriction (W : SchemeTests F) (V V' : T.left.affineOpens) (j : V ≤ V')
      (h : (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V.1)
      (h' : (⊤ : W.left.left.Opens) ≤ (testToBase f W).left ⁻¹ᵁ V'.1)
      (n : ℕ) (a : A.grading V' n) :
    component W V h n ⟨A.res j a, (A.res j).map_mem a.property⟩ =
      component W V' h' n a

/-- A point is in the generation locus if, on some open neighbourhood over an affine
base chart, a positive-degree homogeneous image is a free generator. Allowing every
open scheme test is precisely the union of the surjectivity loci of the degree maps.
Source: Stacks, Tag 0D2Z, opening construction
(blueprint: def-trf-space-line-module-proj-input). -/
def GradedLineMap.generationSet {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    {f : F ⟶ yoneda.obj T} {A : T.left.GradedAlgebraData} {L : TestLineFamily F}
    (ψ : GradedLineMap f A L) (W : SchemeTests F) : Set W.left.left :=
  {x | ∃ (B : SchemeTests F) (j : B ⟶ W), IsOpenImmersion j.left.left ∧
    ∃ (y : B.left.left), j.left.left y = x ∧
      ∃ (V : T.left.affineOpens)
        (h : (⊤ : B.left.left.Opens) ≤ (testToBase f B).left ⁻¹ᵁ V.1)
        (n : ℕ) (_hn : 0 < n) (a : A.grading V n),
        Scheme.Modules.IsFreeGenerator (ψ.component B V h n a)}

/-- The functor-of-points specification of the generation open; no finite generation,
nonemptiness, or degree-one generation is required.
Source: Stacks, Tag 0D2Z (blueprint: def-trf-space-line-module-proj-input). -/
def GradedLineMap.IsGenerationOpen {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    {f : F ⟶ yoneda.obj T} {A : T.left.GradedAlgebraData} {L : TestLineFamily F}
    (ψ : GradedLineMap f A L) (U : Subfunctor F) : Prop :=
  ∀ (W : Over S) (a : F.obj (op W)),
    a ∈ U.obj (op W) ↔
      ψ.generationSet (CostructuredArrow.mk (yonedaEquiv.symm a)) = Set.univ

/-- Tensor powers of a chosen trivialization, including the prescribed degree-zero unit.
Source: Stacks, Tag 01O9 (blueprint: def-trf-space-line-module-proj-input). -/
noncomputable def trivializedPower {W : Scheme.{u}} {L : W.Modules}
    (e : L ≅ SheafOfModules.unit W.ringCatSheaf) :
    (n : ℕ) → L.tensorPow n ≅ SheafOfModules.unit W.ringCatSheaf
  | 0 => Iso.refl _
  | n + 1 => (e ⊗ᵢ trivializedPower e n) ≪≫ λ_ _

/-- The relative Proj as an object over `S`, using its actual structural map.
Source: Stacks, Tags 01LH and 0D2Z
(blueprint: def-trf-space-line-module-proj-input). -/
noncomputable def projOver (T : Over S) (A : T.left.GradedAlgebraData) : Over S :=
  Over.mk (A.relProjHom ≫ T.hom)

/-- The canonical Proj map is characterized on all trivializing scheme charts by the
usual homogeneous-fraction construction. The ring homomorphism is required to agree
on every homogeneous section; consequently it is completely specified by `ψ` and `e`.
Source: Stacks, Tags 0D2Z(2) and 01O9
(blueprint: def-trf-space-line-module-proj-input). -/
def GradedLineMap.IsCanonicalMap {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    {f : F ⟶ yoneda.obj T} {A : T.left.GradedAlgebraData} {L : TestLineFamily F}
    (ψ : GradedLineMap f A L) (U : Subfunctor F)
    (r : U.toFunctor ⟶ yoneda.obj (projOver T A)) : Prop :=
  (∀ (W : Over S) (a : U.toFunctor.obj (op W)),
    (r.app (op W) a).left ≫ A.relProjHom =
      (testToBase f (CostructuredArrow.mk (yonedaEquiv.symm a.val))).left) ∧
    ∀ (W : Over S) (a : U.toFunctor.obj (op W)) (V : T.left.affineOpens)
      (h : (⊤ : W.left.Opens) ≤
        (testToBase f (CostructuredArrow.mk (yonedaEquiv.symm a.val))).left ⁻¹ᵁ V.1)
      (e : L.module (CostructuredArrow.mk (yonedaEquiv.symm a.val)) ≅
        SheafOfModules.unit W.left.ringCatSheaf) (α : A.obj V →+* Γ(W.left, ⊤)),
      (∀ (n : ℕ) (b : A.grading V n), α b =
        (Scheme.Modules.unitSectionsEquiv ⊤).symm
          ((trivializedPower e n).hom.app ⊤
            (ψ.component (CostructuredArrow.mk (yonedaEquiv.symm a.val)) V h n b))) →
      ∀ hα : Ideal.map α (HomogeneousIdeal.irrelevant (A.grading V)).toIdeal = ⊤,
        (r.app (op W) a).left =
          Proj.fromOfGlobalSections (A.grading V) α hα ≫ A.relProjι V

/-- A graded homomorphism is the coefficientwise base change of `ψ` when its homogeneous
images agree after the specified coefficientwise pullback maps. These maps generate
each pulled-back piece, so this condition determines the pulled-back homomorphism.
Source: Stacks, Tag 0D2Z(3) (blueprint: def-trf-space-line-module-proj-input). -/
def GradedLineMap.IsBaseChange {F G : (Over S)ᵒᵖ ⥤ Type u} {T T' : Over S}
    {f : F ⟶ yoneda.obj T} {f' : G ⟶ yoneda.obj T'}
    {A : T.left.GradedAlgebraData} {A' : T'.left.GradedAlgebraData}
    {L : TestLineFamily F} (ψ : GradedLineMap f A L) (k : G ⟶ F)
    (g : T' ⟶ T) (D : Scheme.GradedAlgebraData.PullbackData g.left A A')
    (ψ' : GradedLineMap f' A' (L.pullback k)) : Prop :=
  ∀ (W : SchemeTests G) (V : T.left.affineOpens) (V' : T'.left.affineOpens)
    (hVV' : V'.1 ≤ g.left ⁻¹ᵁ V.1)
    (h : (⊤ : W.left.left.Opens) ≤
      (testToBase f ((CostructuredArrow.map k).obj W)).left ⁻¹ᵁ V.1)
    (h' : (⊤ : W.left.left.Opens) ≤ (testToBase f' W).left ⁻¹ᵁ V'.1)
    (n : ℕ) (a : A.grading V n),
    ψ'.component W V' h' n ⟨D.map hVV' a, (D.map hVV').map_mem a.property⟩ =
      ψ.component ((CostructuredArrow.map k).obj W) V h n a

end AlgebraicGeometry.AlgebraicSpace
