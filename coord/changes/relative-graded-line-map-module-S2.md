# RelativeGradedLineMap

## Reason

The affine-chart comparison must import the graded-map definitions without importing
its consumer, the ampleness criterion. Move the existing structure and predicates to
an independent module. Their names, signatures, visibility, and bodies stay verbatim.
The original module publicly re-exports the new module. This is an ownership/import
repair, not a mathematical definition change. No target meaning changes.

## Old

In `Sheaf.TraceFormula.GradedImmersionAmpleCriterion`:

```lean
/-- A graded algebra map on affine base opens into tensor powers of an invertible module.
Source: Stacks Project, Constructions, Tag 01O9 (blueprint:
lem-trf-graded-immersion-ample-criterion). -/
structure RelativeGradedLineMap {Z S : Scheme.{u}} (h : Z ⟶ S)
    (A : S.GradedAlgebraData) (L : Z.Modules) where
  component (V : S.affineOpens) (n : ℕ) :
    A.grading V n →+ Γ(L.tensorPow n, h ⁻¹ᵁ V.1)
  smul (V : S.affineOpens) (n : ℕ) (r : Γ(S, V.1)) (a : A.grading V n) :
    component V n (r • a) = h.app V.1 r • component V n a
  one (V : S.affineOpens) :
    component V 0 ⟨1, SetLike.one_mem_graded (A.grading V)⟩ =
      unitSectionsEquiv (h ⁻¹ᵁ V.1) 1
  mul (V : S.affineOpens) (m n : ℕ) (a : A.grading V m) (b : A.grading V n) :
    component V (m + n) ⟨a * b, SetLike.mul_mem_graded a.property b.property⟩ =
      (L.tensorPowAddIso m n).inv.app (h ⁻¹ᵁ V.1)
        (tmulSection (component V m a) (component V n b))
  restriction {V W : S.affineOpens} (q : V ≤ W) (n : ℕ) (a : A.grading W n) :
    component V n ⟨A.res q a, (A.res q).map_mem a.property⟩ =
      (L.tensorPow n).val.map (homOfLE (h.preimage_mono q)).op (component W n a)

/-- Pull the component of a graded line map to a scheme chart.
Source: Stacks Project, Constructions, Tag 01O9 (blueprint:
lem-trf-graded-immersion-ample-criterion). -/
noncomputable def RelativeGradedLineMap.evaluate
    {Z S : Scheme.{u}} {h : Z ⟶ S} {A : S.GradedAlgebraData} {L : Z.Modules}
    (ψ : RelativeGradedLineMap h A L) {W : Scheme.{u}} (j : W ⟶ Z)
    (V : S.affineOpens) (q : (⊤ : W.Opens) ≤ j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
    (n : ℕ) (a : A.grading V n) :
    Γ(((tensorPullback j).obj L).tensorPow n, ⊤) :=
  (boundaryPullbackPowIso j L n).hom.app ⊤
    (((tensorPullback j).obj (L.tensorPow n)).val.map (homOfLE q).op
      (((tensorPullbackSectionAdjunction j).unit.app (L.tensorPow n)).app (h ⁻¹ᵁ V.1)
        (ψ.component V n a)))

/-- Positive-degree images generate the line module everywhere.
Source: Stacks Project, Constructions, Tag 01O9 (blueprint:
lem-trf-graded-immersion-ample-criterion). -/
def RelativeGradedLineMap.GeneratesEverywhere
    {Z S : Scheme.{u}} {h : Z ⟶ S} {A : S.GradedAlgebraData} {L : Z.Modules}
    (ψ : RelativeGradedLineMap h A L) : Prop :=
  ∀ x : Z, ∃ (V : S.affineOpens) (hx : x ∈ h ⁻¹ᵁ V.1) (n : ℕ), 0 < n ∧
    ∃ a : A.grading V n,
      (TopCat.Presheaf.germ (L.tensorPow n).val.presheaf (h ⁻¹ᵁ V.1) x hx)
          (ψ.component V n a) ∉
        (IsLocalRing.maximalIdeal (Z.presheaf.stalk x)) •
          (⊤ : Submodule (Z.presheaf.stalk x)
            ↑(TopCat.Presheaf.stalk (L.tensorPow n).val.presheaf x))

/-- The usual homogeneous-fraction characterization of the canonical map to relative Proj.
Source: Stacks Project, Constructions, Tag 01O9 (blueprint:
lem-trf-graded-immersion-ample-criterion). -/
def RelativeGradedLineMap.IsCanonicalMap
    {Z S : Scheme.{u}} {h : Z ⟶ S} {A : S.GradedAlgebraData} {L : Z.Modules}
    (ψ : RelativeGradedLineMap h A L) (r : Z ⟶ A.relProj) : Prop :=
  r ≫ A.relProjHom = h ∧
    ∀ (W : Scheme.{u}) (j : W ⟶ Z), IsOpenImmersion j →
      ∀ (V : S.affineOpens)
        (q : (⊤ : W.Opens) ≤ j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
        (e : (tensorPullback j).obj L ≅ SheafOfModules.unit W.ringCatSheaf)
        (α : A.obj V →+* Γ(W, ⊤)),
        (∀ (n : ℕ) (a : A.grading V n), α a =
          (unitSectionsEquiv ⊤).symm
            ((AlgebraicSpace.trivializedPower e n).hom.app ⊤
              (ψ.evaluate j V q n a))) →
        ∀ hα : Ideal.map α (HomogeneousIdeal.irrelevant (A.grading V)).toIdeal = ⊤,
          j ≫ r = Proj.fromOfGlobalSections (A.grading V) α hα ≫ A.relProjι V
```

## New

The exact declarations above, unchanged, in
`Sheaf.TraceFormula.RelativeGradedLineMap`. The original module contains:

```lean
public import Sheaf.TraceFormula.RelativeGradedLineMap
```

## Users

`tools/downstream.py Sheaf.TraceFormula.GradedImmersionAmpleCriterion --uses
RelativeGradedLineMap` and the preflight's constant-usage scan list the following
textual and inferred predicate users. The four users found by the delivery preflight
were added after its first refusal, before retrying. All other downstream modules
retain the same exported constants. No consumer requires an adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjectiveBundleRelativeAmple | unclaimed | Uses the unchanged immersion criterion through its original import; no source adaptation. |
| Sheaf.TraceFormula.GradedImmersionAmpleCriterion | S2 | Definitions moved verbatim and publicly re-exported; theorem now has a complete assembly proof. |
| Sheaf.TraceFormula.LineQuotientHomogeneousFractionMap | N2 | Original source compiles unchanged against the extracted definitions. |
| Sheaf.AlgebraicGeometry.LineQuotientChartInversePullback | G3 | Original source compiles unchanged against the extracted definitions. |
| Sheaf.AlgebraicGeometry.LineQuotientTrivializedCoefficients | unclaimed | Uses the same re-exported structure and evaluation constants through LineQuotientHomogeneousFractionMap; no source adaptation. |
| Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction | unclaimed | Its relative-section-algebra canonical-map predicate still uses the same re-exported IsCanonicalMap; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry | unclaimed | The existing hcanonical.2 application uses the identical canonical-map predicate; no source adaptation. |
| Sheaf.AlgebraicGeometry.RelativeAmpleVeryAmple | unclaimed | Existing section-algebra predicate and use of the immersion criterion are unchanged; no source adaptation. |

All three direct importers were compiled unchanged as well:
`ProjectiveBundleRelativeAmple`, `RelativeAmpleVeryAmple`, and
`LineQuotientHomogeneousFractionMap`. The expanded check also compiled unchanged
`LineQuotientChartInversePullback`, `LineQuotientTrivializedCoefficients`,
`NodalLogCanonicalReconstruction`, and `ProjectiveBundleQuotientGeometry`.
The temporary consumer copies are excluded from the delivery. The imported theorem signatures remain identical.

## Status

landed 20261024T191003-L-203224 2026-10-24 (merge of deliver/S2/Sheaf.TraceFormula.GradedImmersionAmpleCriterion)
