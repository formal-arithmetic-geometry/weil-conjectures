# ProjectiveBundleQuotientGeometry data-module interface

## Reason

The assigned theorem must import its stated dependencies SymmetricProjTautologicalCharts
and LineQuotientChartInversePullback. Both currently publicly import the theorem's module
only to refer to its definitions. Keeping those imports produces a cycle. Extract all
seven existing data declarations unchanged into ProjectiveBundleQuotientData and publicly
reexport that module from the original module. Adapt only the single import line in each
of the two held dependency modules (J2 and G3 respectively).

There is no mathematical definition or statement change, no binder or universe change,
no new choice of data, and no target meaning change. The original public import surface is
retained transitively through the data module. Every definition body below is byte-for-byte
identical; all seven names retain their namespaces and visibility. Consequently consumers
need no proof adaptation. This is an import-graph repair required by the assigned proof.

Original compilation with each held module restored in the final sandbox fails, respectively:

```
the modules import one another in a cycle: Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry, Sheaf.AlgebraicGeometry.SymmetricProjTautologicalCharts

the modules import one another in a cycle: Sheaf.AlgebraicGeometry.LineQuotientChartInversePullback, Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
```

The adapted files and all sandbox files compile on the server.

## Old

In lean/Sheaf/AlgebraicGeometry/ProjectiveBundleQuotientGeometry.lean, in namespace
AlgebraicGeometry.ProjectiveBundleQuotientGeometry with the existing S,E,IsQuasicoherent
variables:

```lean
structure TautologicalQuotient where
  line : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Modules
  quotient : (Scheme.Modules.tensorPullback
    (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).obj E ⟶ line
  invertible : line.IsInvertible
  surjective : Epi quotient
  chart (U : S.affineOpens) :
    (Scheme.Modules.tensorPullback
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U)).obj line ≅
      Proj.twist ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U) 1
  generator (U : S.affineOpens) (m : E.val.obj (op U.1))
      (hm : SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) m ∈
        (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U 1) :
    (chart U).hom.app
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
        (Scheme.Modules.tensorPullbackSection
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U) line
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)
          (((Scheme.Modules.tensorPullbackSectionAdjunction
            (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).homEquiv E line
              quotient).app U.1 m)) =
      Scheme.Modules.Hom.app (Proj.unitToTwist
        (𝒜 := (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U) hm)
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
        (1 : Γ(Proj ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U),
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)))

variable {E}

/-- The actual pullback quotient along an S-morphism, using the section-normalized
composition comparison of tensor pullbacks.
Source: Stacks, Tag 01OA (blueprint: lem-trf-projective-bundle-quotient-geometry). -/
noncomputable def pulledQuotient (D : TautologicalQuotient E) {T : Scheme.{u}}
    (h : T ⟶ S) (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (ha : a ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h) :
    (Scheme.Modules.tensorPullback h).obj E ⟶
      (Scheme.Modules.tensorPullback a).obj D.line :=
  (eqToIso (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj E) ha)).inv ≫
    (Scheme.Modules.tensorPullbackSectionComp a
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom.app E ≫
    (Scheme.Modules.tensorPullback a).map D.quotient

/-- A quotient pair corresponds to a exactly when the pullback of the universal
quotient is isomorphic to that pair, with the quotient map preserved.
Source: Stacks, Tag 01OA (blueprint: lem-trf-projective-bundle-quotient-geometry). -/
def Classifies (D : TautologicalQuotient E) {T : Scheme.{u}} (h : T ⟶ S)
    (L : T.Modules) (q : (Scheme.Modules.tensorPullback h).obj E ⟶ L)
    (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj) : Prop :=
  ∃ ha : a ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h,
    ∃ v : (Scheme.Modules.tensorPullback a).obj D.line ≅ L,
      pulledQuotient D h a ha ≫ v.hom = q

/-- The scheme specialization of the canonical map of Tag 01O9. A frame of L turns
q into coefficients. The unique ring map fixing scalars and those coefficients is
Sym(E) to the tensor powers of L in that frame. The displayed map is precisely the
usual homogeneous-fraction construction, also used in GradedLineMap.IsCanonicalMap.
The ring map and its irrelevant-ideal condition are asserted to exist, not assumed.
Source: Stacks, Tags 01O9, 01OA; def-trf-space-line-module-proj-input
(blueprint: lem-trf-projective-bundle-quotient-geometry). -/
def IsCanonicalMap {T : Scheme.{u}} (h : T ⟶ S) (L : T.Modules)
    (q : (Scheme.Modules.tensorPullback h).obj E ⟶ L)
    (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj) : Prop :=
  ∀ (V : S.affineOpens) (W : T.affineOpens) (hWV : W.1 ≤ h ⁻¹ᵁ V.1)
    (e : (Scheme.Modules.tensorPullback W.1.ι).obj L ≅
      SheafOfModules.unit W.1.toScheme.ringCatSheaf),
    ∃ α : (SymmetricAlgebraSheaf.gradedAlgebraData E).obj V →+*
        Γ(W.1.toScheme, ⊤),
      (∀ r : Γ(S, V.1), α (algebraMap Γ(S, V.1)
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).obj V) r) =
          W.1.ι.appLE W.1 ⊤ (by simp) (h.appLE V.1 W.1 hWV r)) ∧
      (∀ m : E.val.obj (op V.1),
        α (SymmetricAlgebra.ι Γ(S, V.1) (E.val.obj (op V.1)) m) =
          (Scheme.Modules.unitSectionsEquiv ⊤).symm
            (e.hom.app ⊤
              (((Scheme.Modules.tensorPullback W.1.ι).obj L).presheaf.map
                (homOfLE (show (⊤ : W.1.toScheme.Opens) ≤ W.1.ι ⁻¹ᵁ W.1 by simp)).op
                (Scheme.Modules.tensorPullbackSection W.1.ι L W.1
                  (L.presheaf.map (homOfLE hWV).op
                    (q.app (h ⁻¹ᵁ V.1)
                      (Scheme.Modules.tensorPullbackSection h E V.1 m))))))) ∧
      ∃ hα : Ideal.map α
          (HomogeneousIdeal.irrelevant
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V)).toIdeal = ⊤,
        W.1.ι ≫ a = Proj.fromOfGlobalSections
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) α hα ≫
            (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι V

/-- Restricting the canonical projective bundle to an arbitrary open of its base.
The map exhibits the fibre product and the line isomorphism preserves the quotient.
Source: Stacks, Tags 01NQ, 01NR, 01OA
(blueprint: lem-trf-projective-bundle-quotient-geometry). -/
def HasOpenCompatibility (D : TautologicalQuotient E) : Prop :=
  ∀ V : S.Opens,
    ∃ hE : ((Scheme.Modules.tensorPullback V.ι).obj E).IsQuasicoherent,
      ∃ DV : @TautologicalQuotient V.toScheme
          ((Scheme.Modules.tensorPullback V.ι).obj E) hE,
        ∃ j : (@SymmetricAlgebraSheaf.gradedAlgebraData V.toScheme
            ((Scheme.Modules.tensorPullback V.ι).obj E) hE).relProj ⟶
              (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj,
          ∃ hj : IsPullback j
            (@SymmetricAlgebraSheaf.gradedAlgebraData V.toScheme
              ((Scheme.Modules.tensorPullback V.ι).obj E) hE).relProjHom
            (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom V.ι,
          ∃ w : (Scheme.Modules.tensorPullback j).obj D.line ≅ DV.line,
            (Scheme.Modules.tensorPullbackSectionComp j
              (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom.app E ≫
              (Scheme.Modules.tensorPullback j).map D.quotient ≫ w.hom =
            (eqToIso (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj E)
              hj.w)).hom ≫
            (Scheme.Modules.tensorPullbackSectionComp
              (@SymmetricAlgebraSheaf.gradedAlgebraData V.toScheme
                ((Scheme.Modules.tensorPullback V.ι).obj E) hE).relProjHom V.ι).hom.app E ≫
              DV.quotient


/-- Over an affine base chart, the ordered basis gives exactly the standard graded
polynomial algebra. Both projective-space identifications use these polynomial charts,
and the degree-one twists correspond by a section-preserving isomorphism.
The local instance is only the specified Mathlib polynomial grading inside this definition.
Source: Stacks, Tags 01OE, 01OB, 01MN
(blueprint: lem-trf-projective-bundle-quotient-geometry). -/
def AffineFreeComparison (r : ℕ) (b : RelativeProjectiveSpace.freeModule S r ≅ E)
    (eRel : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
      RelativeProjectiveSpace.scheme S r) (V : S.affineOpens) : Prop := by
  letI := MvPolynomial.gradedAlgebra (σ := ULift.{u} (Fin (r + 1))) (R := Γ(S, V.1))
  exact ∃ β : MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) Γ(S, V.1) →+*ᵍ
      (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V,
    Function.Bijective β ∧
    (∀ x : Γ(S, V.1), β (MvPolynomial.C x) = algebraMap Γ(S, V.1)
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).obj V) x) ∧
    (∀ i : ULift.{u} (Fin (r + 1)), β (MvPolynomial.X i) =
      SymmetricAlgebra.ι Γ(S, V.1) (E.val.obj (op V.1))
        (b.hom.app V.1 ((SheafOfModules.ιFree
          (R := S.ringCatSheaf) i).val.app (op V.1) (1 : Γ(S, V.1))))) ∧
    ∃ (hβ : HomogeneousIdeal.irrelevant
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) ≤
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) Γ(S, V.1))).map β)
      (eC : Proj ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) ≅
        Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (r + 1))) Γ(S, V.1)),
      eC.hom = Proj.map β hβ ∧
      (∃ t : (Scheme.Modules.tensorPullback eC.hom).obj
          (Proj.twist (MvPolynomial.homogeneousSubmodule
            (ULift.{u} (Fin (r + 1))) Γ(S, V.1)) 1) ≅
          Proj.twist ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) 1,
        ∀ (s : MvPolynomial (ULift.{u} (Fin (r + 1))) Γ(S, V.1))
          (hs : s ∈ MvPolynomial.homogeneousSubmodule
            (ULift.{u} (Fin (r + 1))) Γ(S, V.1) 1),
          (Scheme.Modules.tensorPullback eC.hom).map (Proj.unitToTwist
            (𝒜 := MvPolynomial.homogeneousSubmodule
              (ULift.{u} (Fin (r + 1))) Γ(S, V.1)) hs) ≫ t.hom =
          ((Scheme.Modules.boundaryPullbackComparison eC.hom).app
              (Scheme.Modules.unit _) ≪≫ Scheme.Modules.pullbackObjUnitIso eC.hom).hom ≫
            Proj.unitToTwist
              (𝒜 := (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V)
              (β.map_mem hs)) ∧
      ∃ (γ : MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) Γ(S, V.1) →+*ᵍ
            (RelativeProjectiveSpace.algebra S r).sectionGrade V)
        (hγ : HomogeneousIdeal.irrelevant
            ((RelativeProjectiveSpace.algebra S r).sectionGrade V) ≤
          (HomogeneousIdeal.irrelevant
            (MvPolynomial.homogeneousSubmodule
              (ULift.{u} (Fin (r + 1))) Γ(S, V.1))).map γ)
        (eR : (RelativeProjectiveSpace.algebra S r).localProj V ≅
          Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (r + 1))) Γ(S, V.1)),
        (∀ x, γ x = RelativeProjectiveSpace.affinePolynomialEquiv S r V
          (MvPolynomial.rename (fun i : ULift.{u} (Fin (r + 1)) ↦ i.down) x)) ∧
        eR.hom = Proj.map γ hγ ∧
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι V ≫ eRel.hom =
          eC.hom ≫ eR.inv ≫ ((RelativeProjectiveSpace.construction S r).restrictionIso V).inv ≫
            (RelativeProjectiveSpace.π S r ⁻¹ᵁ V.1).ι

/-- The finite free case, with its ordered coordinate quotients and affine polynomial
models. ULift changes only the index universe, retaining all r+1 basis elements.
Source: Stacks, Tag 01OE; ProjectiveSpace.twist and its coordinate sections
(blueprint: lem-trf-projective-bundle-quotient-geometry). -/
def HasFreeCompatibility (D : TautologicalQuotient E) : Prop :=
  ∀ (r : ℕ) (b : RelativeProjectiveSpace.freeModule S r ≅ E),
    ∃ (eRel : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
        RelativeProjectiveSpace.scheme S r)
      (eStd : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
        ℙ(ULift.{u} (Fin (r + 1)); S))
      (t : (Scheme.Modules.tensorPullback eStd.hom).obj
        (ProjectiveSpace.twist (ULift.{u} (Fin (r + 1))) S 1) ≅ D.line),
      eRel.hom ≫ RelativeProjectiveSpace.π S r =
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ∧
      eStd.hom ≫ (ℙ(ULift.{u} (Fin (r + 1)); S) ↘ S) =
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ∧
      (∀ i : ULift.{u} (Fin (r + 1)),
        (Scheme.Modules.tensorPullback
            (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).map
          (SheafOfModules.ιFree (R := S.ringCatSheaf) i ≫ b.hom) ≫ D.quotient =
        ((Scheme.Modules.boundaryPullbackComparison
            (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).app
              (Scheme.Modules.unit S) ≪≫
          Scheme.Modules.pullbackObjUnitIso
            (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom ≫
        ((Scheme.Modules.boundaryPullbackComparison eStd.hom).app
            (Scheme.Modules.unit _) ≪≫ Scheme.Modules.pullbackObjUnitIso eStd.hom).inv ≫
        (Scheme.Modules.tensorPullback eStd.hom).map
          (ProjectiveSpace.coordinateSection (ULift.{u} (Fin (r + 1))) S i) ≫ t.hom) ∧
      ∀ V : S.affineOpens, AffineFreeComparison r b eRel V
```

Both dependent modules import:

```lean
public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
```

## New

In lean/Sheaf/AlgebraicGeometry/ProjectiveBundleQuotientData.lean, with exactly the same
namespace, universe, variables, options, visibility and definitions:

```lean
structure TautologicalQuotient where
  line : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Modules
  quotient : (Scheme.Modules.tensorPullback
    (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).obj E ⟶ line
  invertible : line.IsInvertible
  surjective : Epi quotient
  chart (U : S.affineOpens) :
    (Scheme.Modules.tensorPullback
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U)).obj line ≅
      Proj.twist ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U) 1
  generator (U : S.affineOpens) (m : E.val.obj (op U.1))
      (hm : SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) m ∈
        (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U 1) :
    (chart U).hom.app
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
        (Scheme.Modules.tensorPullbackSection
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U) line
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)
          (((Scheme.Modules.tensorPullbackSectionAdjunction
            (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).homEquiv E line
              quotient).app U.1 m)) =
      Scheme.Modules.Hom.app (Proj.unitToTwist
        (𝒜 := (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U) hm)
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
        (1 : Γ(Proj ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U),
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)))

variable {E}

/-- The actual pullback quotient along an S-morphism, using the section-normalized
composition comparison of tensor pullbacks.
Source: Stacks, Tag 01OA (blueprint: lem-trf-projective-bundle-quotient-geometry). -/
noncomputable def pulledQuotient (D : TautologicalQuotient E) {T : Scheme.{u}}
    (h : T ⟶ S) (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (ha : a ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h) :
    (Scheme.Modules.tensorPullback h).obj E ⟶
      (Scheme.Modules.tensorPullback a).obj D.line :=
  (eqToIso (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj E) ha)).inv ≫
    (Scheme.Modules.tensorPullbackSectionComp a
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom.app E ≫
    (Scheme.Modules.tensorPullback a).map D.quotient

/-- A quotient pair corresponds to a exactly when the pullback of the universal
quotient is isomorphic to that pair, with the quotient map preserved.
Source: Stacks, Tag 01OA (blueprint: lem-trf-projective-bundle-quotient-geometry). -/
def Classifies (D : TautologicalQuotient E) {T : Scheme.{u}} (h : T ⟶ S)
    (L : T.Modules) (q : (Scheme.Modules.tensorPullback h).obj E ⟶ L)
    (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj) : Prop :=
  ∃ ha : a ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h,
    ∃ v : (Scheme.Modules.tensorPullback a).obj D.line ≅ L,
      pulledQuotient D h a ha ≫ v.hom = q

/-- The scheme specialization of the canonical map of Tag 01O9. A frame of L turns
q into coefficients. The unique ring map fixing scalars and those coefficients is
Sym(E) to the tensor powers of L in that frame. The displayed map is precisely the
usual homogeneous-fraction construction, also used in GradedLineMap.IsCanonicalMap.
The ring map and its irrelevant-ideal condition are asserted to exist, not assumed.
Source: Stacks, Tags 01O9, 01OA; def-trf-space-line-module-proj-input
(blueprint: lem-trf-projective-bundle-quotient-geometry). -/
def IsCanonicalMap {T : Scheme.{u}} (h : T ⟶ S) (L : T.Modules)
    (q : (Scheme.Modules.tensorPullback h).obj E ⟶ L)
    (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj) : Prop :=
  ∀ (V : S.affineOpens) (W : T.affineOpens) (hWV : W.1 ≤ h ⁻¹ᵁ V.1)
    (e : (Scheme.Modules.tensorPullback W.1.ι).obj L ≅
      SheafOfModules.unit W.1.toScheme.ringCatSheaf),
    ∃ α : (SymmetricAlgebraSheaf.gradedAlgebraData E).obj V →+*
        Γ(W.1.toScheme, ⊤),
      (∀ r : Γ(S, V.1), α (algebraMap Γ(S, V.1)
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).obj V) r) =
          W.1.ι.appLE W.1 ⊤ (by simp) (h.appLE V.1 W.1 hWV r)) ∧
      (∀ m : E.val.obj (op V.1),
        α (SymmetricAlgebra.ι Γ(S, V.1) (E.val.obj (op V.1)) m) =
          (Scheme.Modules.unitSectionsEquiv ⊤).symm
            (e.hom.app ⊤
              (((Scheme.Modules.tensorPullback W.1.ι).obj L).presheaf.map
                (homOfLE (show (⊤ : W.1.toScheme.Opens) ≤ W.1.ι ⁻¹ᵁ W.1 by simp)).op
                (Scheme.Modules.tensorPullbackSection W.1.ι L W.1
                  (L.presheaf.map (homOfLE hWV).op
                    (q.app (h ⁻¹ᵁ V.1)
                      (Scheme.Modules.tensorPullbackSection h E V.1 m))))))) ∧
      ∃ hα : Ideal.map α
          (HomogeneousIdeal.irrelevant
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V)).toIdeal = ⊤,
        W.1.ι ≫ a = Proj.fromOfGlobalSections
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) α hα ≫
            (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι V

/-- Restricting the canonical projective bundle to an arbitrary open of its base.
The map exhibits the fibre product and the line isomorphism preserves the quotient.
Source: Stacks, Tags 01NQ, 01NR, 01OA
(blueprint: lem-trf-projective-bundle-quotient-geometry). -/
def HasOpenCompatibility (D : TautologicalQuotient E) : Prop :=
  ∀ V : S.Opens,
    ∃ hE : ((Scheme.Modules.tensorPullback V.ι).obj E).IsQuasicoherent,
      ∃ DV : @TautologicalQuotient V.toScheme
          ((Scheme.Modules.tensorPullback V.ι).obj E) hE,
        ∃ j : (@SymmetricAlgebraSheaf.gradedAlgebraData V.toScheme
            ((Scheme.Modules.tensorPullback V.ι).obj E) hE).relProj ⟶
              (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj,
          ∃ hj : IsPullback j
            (@SymmetricAlgebraSheaf.gradedAlgebraData V.toScheme
              ((Scheme.Modules.tensorPullback V.ι).obj E) hE).relProjHom
            (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom V.ι,
          ∃ w : (Scheme.Modules.tensorPullback j).obj D.line ≅ DV.line,
            (Scheme.Modules.tensorPullbackSectionComp j
              (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom.app E ≫
              (Scheme.Modules.tensorPullback j).map D.quotient ≫ w.hom =
            (eqToIso (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj E)
              hj.w)).hom ≫
            (Scheme.Modules.tensorPullbackSectionComp
              (@SymmetricAlgebraSheaf.gradedAlgebraData V.toScheme
                ((Scheme.Modules.tensorPullback V.ι).obj E) hE).relProjHom V.ι).hom.app E ≫
              DV.quotient


/-- Over an affine base chart, the ordered basis gives exactly the standard graded
polynomial algebra. Both projective-space identifications use these polynomial charts,
and the degree-one twists correspond by a section-preserving isomorphism.
The local instance is only the specified Mathlib polynomial grading inside this definition.
Source: Stacks, Tags 01OE, 01OB, 01MN
(blueprint: lem-trf-projective-bundle-quotient-geometry). -/
def AffineFreeComparison (r : ℕ) (b : RelativeProjectiveSpace.freeModule S r ≅ E)
    (eRel : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
      RelativeProjectiveSpace.scheme S r) (V : S.affineOpens) : Prop := by
  letI := MvPolynomial.gradedAlgebra (σ := ULift.{u} (Fin (r + 1))) (R := Γ(S, V.1))
  exact ∃ β : MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) Γ(S, V.1) →+*ᵍ
      (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V,
    Function.Bijective β ∧
    (∀ x : Γ(S, V.1), β (MvPolynomial.C x) = algebraMap Γ(S, V.1)
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).obj V) x) ∧
    (∀ i : ULift.{u} (Fin (r + 1)), β (MvPolynomial.X i) =
      SymmetricAlgebra.ι Γ(S, V.1) (E.val.obj (op V.1))
        (b.hom.app V.1 ((SheafOfModules.ιFree
          (R := S.ringCatSheaf) i).val.app (op V.1) (1 : Γ(S, V.1))))) ∧
    ∃ (hβ : HomogeneousIdeal.irrelevant
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) ≤
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) Γ(S, V.1))).map β)
      (eC : Proj ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) ≅
        Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (r + 1))) Γ(S, V.1)),
      eC.hom = Proj.map β hβ ∧
      (∃ t : (Scheme.Modules.tensorPullback eC.hom).obj
          (Proj.twist (MvPolynomial.homogeneousSubmodule
            (ULift.{u} (Fin (r + 1))) Γ(S, V.1)) 1) ≅
          Proj.twist ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) 1,
        ∀ (s : MvPolynomial (ULift.{u} (Fin (r + 1))) Γ(S, V.1))
          (hs : s ∈ MvPolynomial.homogeneousSubmodule
            (ULift.{u} (Fin (r + 1))) Γ(S, V.1) 1),
          (Scheme.Modules.tensorPullback eC.hom).map (Proj.unitToTwist
            (𝒜 := MvPolynomial.homogeneousSubmodule
              (ULift.{u} (Fin (r + 1))) Γ(S, V.1)) hs) ≫ t.hom =
          ((Scheme.Modules.boundaryPullbackComparison eC.hom).app
              (Scheme.Modules.unit _) ≪≫ Scheme.Modules.pullbackObjUnitIso eC.hom).hom ≫
            Proj.unitToTwist
              (𝒜 := (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V)
              (β.map_mem hs)) ∧
      ∃ (γ : MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) Γ(S, V.1) →+*ᵍ
            (RelativeProjectiveSpace.algebra S r).sectionGrade V)
        (hγ : HomogeneousIdeal.irrelevant
            ((RelativeProjectiveSpace.algebra S r).sectionGrade V) ≤
          (HomogeneousIdeal.irrelevant
            (MvPolynomial.homogeneousSubmodule
              (ULift.{u} (Fin (r + 1))) Γ(S, V.1))).map γ)
        (eR : (RelativeProjectiveSpace.algebra S r).localProj V ≅
          Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (r + 1))) Γ(S, V.1)),
        (∀ x, γ x = RelativeProjectiveSpace.affinePolynomialEquiv S r V
          (MvPolynomial.rename (fun i : ULift.{u} (Fin (r + 1)) ↦ i.down) x)) ∧
        eR.hom = Proj.map γ hγ ∧
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι V ≫ eRel.hom =
          eC.hom ≫ eR.inv ≫ ((RelativeProjectiveSpace.construction S r).restrictionIso V).inv ≫
            (RelativeProjectiveSpace.π S r ⁻¹ᵁ V.1).ι

/-- The finite free case, with its ordered coordinate quotients and affine polynomial
models. ULift changes only the index universe, retaining all r+1 basis elements.
Source: Stacks, Tag 01OE; ProjectiveSpace.twist and its coordinate sections
(blueprint: lem-trf-projective-bundle-quotient-geometry). -/
def HasFreeCompatibility (D : TautologicalQuotient E) : Prop :=
  ∀ (r : ℕ) (b : RelativeProjectiveSpace.freeModule S r ≅ E),
    ∃ (eRel : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
        RelativeProjectiveSpace.scheme S r)
      (eStd : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
        ℙ(ULift.{u} (Fin (r + 1)); S))
      (t : (Scheme.Modules.tensorPullback eStd.hom).obj
        (ProjectiveSpace.twist (ULift.{u} (Fin (r + 1))) S 1) ≅ D.line),
      eRel.hom ≫ RelativeProjectiveSpace.π S r =
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ∧
      eStd.hom ≫ (ℙ(ULift.{u} (Fin (r + 1)); S) ↘ S) =
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ∧
      (∀ i : ULift.{u} (Fin (r + 1)),
        (Scheme.Modules.tensorPullback
            (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).map
          (SheafOfModules.ιFree (R := S.ringCatSheaf) i ≫ b.hom) ≫ D.quotient =
        ((Scheme.Modules.boundaryPullbackComparison
            (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).app
              (Scheme.Modules.unit S) ≪≫
          Scheme.Modules.pullbackObjUnitIso
            (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom ≫
        ((Scheme.Modules.boundaryPullbackComparison eStd.hom).app
            (Scheme.Modules.unit _) ≪≫ Scheme.Modules.pullbackObjUnitIso eStd.hom).inv ≫
        (Scheme.Modules.tensorPullback eStd.hom).map
          (ProjectiveSpace.coordinateSection (ULift.{u} (Fin (r + 1))) S i) ≫ t.hom) ∧
      ∀ V : S.affineOpens, AffineFreeComparison r b eRel V
```

The original module publicly imports ProjectiveBundleQuotientData. Both dependent modules
now import:

```lean
public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData
```

## Users

The following table covers every downstream module returned by tools/downstream.py,
including all textual --uses hits for the seven moved declarations. Some IsCanonicalMap
textual hits concern another namespace; they are included conservatively. No target
signature is edited, and all meanings are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CommonMarkedNodalModel | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.CompleteFlagBundle | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.ElementaryContractionEvaluation | unclaimed | Uses TautologicalQuotient, Classifies; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.KnudsenPointedForgetfulUniversalCurve | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.LineQuotientChartInversePullback | G3 | Forced one-line public import substitution to the data module; every declaration unchanged. |
| Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction | unclaimed | Uses IsCanonicalMap; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.NodalLogDualizingPullback | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.NoetherianFibreAmpleNeighbourhood | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleBaseChange | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleCoordinateGeometry | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleCoordinateSubschemes | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry | X5 | The seven definitions move verbatim; theorem signature stays identical. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleRelativeAmple | unclaimed | Uses pulledQuotient; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.ProperFibrewiseAmpleProjective | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.ProperRelativeAmpleProjectiveBundle | X7 | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.RelativeAmpleVeryAmple | unclaimed | Uses IsCanonicalMap; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.RelativelyVeryAmple | unclaimed | Uses TautologicalQuotient; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.SectionIdealProjExpansion | unclaimed | Uses TautologicalQuotient, Classifies; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.SemistableLogPluricanonicalLattices | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.SymmetricProjTautologicalCharts | J2 | Forced one-line public import substitution to the data module; every declaration unchanged. |
| Sheaf.AlgebraicGeometry.TenCanonicalHilbertParameter | unclaimed | Uses TautologicalQuotient, Classifies; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.VectorProjectiveCompletion | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.VectorProjectivePresentation | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.AlgebraicGeometry.VeryAmpleFiniteTypeRealization | unclaimed | Uses TautologicalQuotient; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.Paper.LineZeroGeometry | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.Paper.NearbyCycleSheafFiniteness | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.Paper.PsiGoodOrientedCohomologyStrata | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.Paper.VectorFrameIntegrationSiteDescent | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.TraceFormula.AmpleNeighbourhood | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | Transitive consumer; Unchanged signature and body; original module publicly reexports the data. |

## Status

landed 20261023T152134-L-454072 2026-10-23 (merge of deliver/X5/Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry)
