# completedDirectImageRlim_roos and unused comparison declarations

## Reason

Prune the unused older Roos/completion interface from
`Sheaf.Paper.CompletedTowerDirectImage`. Whole-library whole-word searches, followed
by `tools/downstream.py ... --uses` for every removed name, find no reference outside
this module. The four removed holed theorems have no consumers even inside it.
The eight removed definitions are used only by these obsolete statements or by each
other. No module, target, definition used by a target, or retained statement is weakened.

The blueprint node `prop-weil-pbc-direct-image-limits` is attached to the newer
`Sheaf.Paper.CompletedDirectImageLimits` interface. Its declarations
`AdicCoefficientDatum.directImageRlim_roos`, `towerProjection_properties`,
`towerProjection_isIso` and `push_complete` retain the actual Roos, strict reduction
and completion obligations. They remain in place with the same statements and proofs.
This change does not claim to have proved those obligations or to have pruned the node.
In particular, evaluation equations are not being substituted for an equality of
strict derived-tower morphisms. The current node explicitly uses the latter route.

The finite projection-formula property in the assigned module is retained because
`FourArrows.finiteProjection_isIso` uses it. All completed module, derived module,
finite module and tower direct-image functors are retained, as are their normalized
restriction comparisons. No adaptation of another module is needed.

## Old

The following are the verbatim old declarations, including their defining bodies.
Four have `sorry`; their removal is pruning and is not counted as proof.

```lean
/-- The canonical Rf_* Rlim ≅ Rlim Rf_*^Tow comparison obtained by deriving the
projection-induced ordinary limit comparison, with universal derived units retained.
Source: Stacks Tag 099N (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedDirectImageRlimIso :
    completedTowerRlim d X ⋙ completedDerivedDirectImage f d ≅
      completedTowerDirectImage f d ⋙ completedTowerRlim d Y :=
  (Functor.rightDerivedFunctorCompIso
    (lim : pbcTowers X (pbcAdicCompletion X d) ⥤
      pbcModules X (pbcAdicCompletion X d)) (completedModuleDirectImage f d)).symm ≪≫
  Functor.rightDerivedFunctorNatIso (completedDirectImageLimitIso f d) ≪≫
  Functor.rightDerivedFunctorCompIso (completedTowerModuleDirectImage f d)
    (lim : pbcTowers Y (pbcAdicCompletion Y d) ⥤
      pbcModules Y (pbcAdicCompletion Y d))
```

```lean
/-- The ordinary limit projection as a natural transformation to evaluation.
Source: blueprint order 1276, proof steps 3--5
(blueprint: prop-weil-pbc-direct-image-limits). -/
def completedLimitEvaluation (T : Scheme.{u}) (n : ℕ) :
    (lim : pbcTowers T (pbcAdicCompletion T d) ⥤ pbcModules T (pbcAdicCompletion T d)) ⟶
      (CategoryTheory.evaluation ℕᵒᵖ (pbcModules T (pbcAdicCompletion T d))).obj (op n) :=
  { app M := limit.π M (op n)
    naturality _ _ h := limMap_π h (op n) }
```

```lean
/-- The derived limit projection, obtained from the ordinary projection and derived units.
Source: blueprint order 1276, proof steps 3--5
(blueprint: prop-weil-pbc-direct-image-limits). -/
def completedRlimEvaluation (T : Scheme.{u}) (n : ℕ) :
    completedTowerRlim d T ⟶ pbcTowerEvaluation T (pbcAdicCompletion T d) n :=
  Functor.rightDerivedFunctorNatTrans (completedLimitEvaluation d T n) ≫
    ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules T (pbcAdicCompletion T d))).obj
      (op n)).rightDerivedFunctorIsoMapDerivedCategory.hom
```

```lean
/-- The canonical map from the derived limit to the product of its evaluations.
Source: blueprint order 1276, proof steps 3--5
(blueprint: prop-weil-pbc-direct-image-limits). -/
def completedRlimProductMap (T : Scheme.{u})
    (M : DerivedCategory (pbcTowers T (pbcAdicCompletion T d)))
    [HasProduct (completedTowerDerivedSequence T d M)] :
    (completedTowerRlim d T).obj M ⟶ ∏ᶜ (completedTowerDerivedSequence T d M) :=
  Pi.lift (fun n ↦ (completedRlimEvaluation d T n).app M)
```

```lean
/-- The product comparison has exactly the direct images of the source projections,
transported by the canonical evaluation comparisons.
Source: blueprint order 1276, proof step 3 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedDirectImageProductMap
    (M : DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
    [HasProduct (completedTowerDerivedSequence X d M)]
    [HasProduct (completedTowerDerivedSequence Y d ((completedTowerDirectImage f d).obj M))] :
    (completedDerivedDirectImage f d).obj (∏ᶜ (completedTowerDerivedSequence X d M)) ⟶
      ∏ᶜ (completedTowerDerivedSequence Y d ((completedTowerDirectImage f d).obj M)) :=
  Pi.lift (fun n ↦ (completedDerivedDirectImage f d).map
    (Pi.π (completedTowerDerivedSequence X d M) n) ≫
      (completedDerivedDirectImageEvaluationIso f d n).inv.app M)
```

```lean
/-- The fixed inverse-limit comparison is induced by the canonical product comparison
and commutes with both canonical Roos triangles, including their connecting arrows.
Source: blueprint order 1276, proof steps 3--5; Stacks Tag 099N
(blueprint: prop-weil-pbc-direct-image-limits).
Proof: resolve M by a K-injective strict tower J. Exact evaluation makes each J_n
K-injective. Products and the mapping fiber of 1-shift are K-injective. The ordinary
right-adjoint product comparison is fixed by its projections; these projections show
that it commutes with shift and hence 1-shift. Direct image commutes with the finite
sum and matrix defining the mapping fiber. The resulting isomorphism of fiber complexes
is the derived ordinary-limit comparison already defined above. Localizing its cone
triangle gives both displayed squares, with the derived functor's shift comparison. -/
theorem completedDirectImageRlim_roos
    (M : DerivedCategory (pbcTowers X (pbcAdicCompletion X d))) :
    ∃ (_ : HasProduct (completedTowerDerivedSequence X d M))
      (_ : HasProduct (completedTowerDerivedSequence Y d
        ((completedTowerDirectImage f d).obj M))),
      IsIso (completedDirectImageProductMap f d M) ∧
      (completedDerivedDirectImage f d).map
          (towerTransitionEndomorphism (completedTowerDerivedStep X d M)) ≫
        completedDirectImageProductMap f d M =
      completedDirectImageProductMap f d M ≫ towerTransitionEndomorphism
        (completedTowerDerivedStep Y d ((completedTowerDirectImage f d).obj M)) ∧
      ∃ (δX : ∏ᶜ (completedTowerDerivedSequence X d M) ⟶
          ((completedTowerRlim d X).obj M)⟦(1 : ℤ)⟧)
        (δY : ∏ᶜ (completedTowerDerivedSequence Y d
          ((completedTowerDirectImage f d).obj M)) ⟶
            ((completedTowerRlim d Y).obj ((completedTowerDirectImage f d).obj M))⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle (completedTowerDerivedStep X d M)
          ((completedTowerRlim d X).obj M) (completedRlimProductMap d X M) δX ∧
        IsDerivedLimitTriangle
          (completedTowerDerivedStep Y d ((completedTowerDirectImage f d).obj M))
          ((completedTowerRlim d Y).obj ((completedTowerDirectImage f d).obj M))
          (completedRlimProductMap d Y ((completedTowerDirectImage f d).obj M)) δY ∧
        (completedDirectImageRlimIso f d).hom.app M ≫
            completedRlimProductMap d Y ((completedTowerDirectImage f d).obj M) =
          (completedDerivedDirectImage f d).map (completedRlimProductMap d X M) ≫
            completedDirectImageProductMap f d M ∧
        (completedDerivedDirectImage f d).map δX ≫
            ((completedDerivedDirectImage f d).commShiftIso (1 : ℤ)).hom.app
              ((completedTowerRlim d X).obj M) ≫
            (shiftFunctor _ (1 : ℤ)).map ((completedDirectImageRlimIso f d).hom.app M) =
          completedDirectImageProductMap f d M ≫ δY := by
  sorry
```

```lean
/-- The actual completed-linear transition between two reductions of K.
Source: blueprint order 1276, proof step 6 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedReductionStep (T : Scheme.{u})
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d)))
    (b a : ℕ) (hab : a ≤ b) :
    (pbcDerivedRestrict (pbcAdicProjection T d b)).obj
        ((pbcDerivedExtend (pbcAdicProjection T d b)).obj K) ⟶
      (pbcDerivedRestrict (pbcAdicProjection T d a)).obj
        ((pbcDerivedExtend (pbcAdicProjection T d a)).obj K) :=
  (pbcDerivedRestrict (pbcAdicProjection T d b)).map
      (pbcReductionTransition (pbcAdicProjection T d b) (pbcAdicQuotient T d b a hab)
        (pbcAdicProjection T d a) (pbcAdicProjection_comp T d b a hab) K) ≫
    (pbcDerivedRestrictComp (pbcAdicProjection T d b) (pbcAdicQuotient T d b a hab)
      (pbcAdicProjection T d a) (pbcAdicProjection_comp T d b a hab)).hom.app _
```

```lean
/-- The finite projection formula after restriction to the completed coefficient rings.
Source: blueprint order 1276, proof step 6 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedRestrictedProjectionFormula (n : ℕ)
    (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) :
    (pbcDerivedRestrict (pbcAdicProjection Y d n)).obj
        ((pbcDerivedExtend (pbcAdicProjection Y d n)).obj
          ((completedDerivedDirectImage f d).obj K)) ⟶
      (completedDerivedDirectImage f d).obj
        ((pbcDerivedRestrict (pbcAdicProjection X d n)).obj
          ((pbcDerivedExtend (pbcAdicProjection X d n)).obj K)) :=
  (pbcDerivedRestrict (pbcAdicProjection Y d n)).map
      (completedDirectImageProjectionFormula f d n K) ≫
    (completedDerivedRestrictionDirectImageIso f d n).inv.app
      ((pbcDerivedExtend (pbcAdicProjection X d n)).obj K)
```

```lean
/-- Projection formula respects every quotient transition and the reductions from K.
Source: blueprint order 1276, proof step 6 (blueprint: prop-weil-pbc-direct-image-limits).
Proof: the projection formula is the scalar-adjunction mate of direct image of the
reduction unit. Quotient balancing takes 1 tensor x to 1 tensor x. Thus both quotient
paths have the same adjunct, namely direct image of the same reduction unit followed
by the lower quotient. The normalized restriction/direct-image comparisons are identity
on sections and retain these equalities after deriving. Apply the Hom bijection for
scalar extension; it gives the quotient square and the equation for the unit from K. -/
theorem completedDirectImageProjectionFormula_quotients
    (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) :
    (∀ (b a : ℕ) (hab : a ≤ b),
      completedReductionStep d Y ((completedDerivedDirectImage f d).obj K) b a hab ≫
          completedRestrictedProjectionFormula f d a K =
        completedRestrictedProjectionFormula f d b K ≫
          (completedDerivedDirectImage f d).map (completedReductionStep d X K b a hab)) ∧
    ∀ n : ℕ,
      (pbcDerivedScalarAdjunction (pbcAdicProjection Y d n)).unit.app
          ((completedDerivedDirectImage f d).obj K) ≫
        completedRestrictedProjectionFormula f d n K =
      (completedDerivedDirectImage f d).map
        ((pbcDerivedScalarAdjunction (pbcAdicProjection X d n)).unit.app K) := by
  sorry
```

```lean
/-- The canonical quotient-tower completion map, induced by the strict reduction unit.
Source: blueprint order 1276, proof step 6 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedQuotientCompletionUnit (T : Scheme.{u})
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d))) :
    K ⟶ (completedTowerRlim d T).obj ((completedReductionTower T d).obj K) :=
  (completedConstantRlimUnit d T).app K ≫
    (completedTowerRlim d T).map ((completedReductionTowerUnit d T).app K)
```

```lean
/-- The output completion unit is precisely direct image of the input completion unit
followed by the fixed inverse-limit comparison and the finite projection-formula comparison.
The comparisons with intrinsic Koszul completion retain their unit normalization.
Source: blueprint order 1276, proof step 6; Stacks Tag 099N
(blueprint: prop-weil-pbc-direct-image-limits).
Proof: Koszul reconstruction identifies intrinsic completion with the quotient-tower
limit and identifies their units. Perfect projection formula at each quotient is an
isomorphism; the preceding quotient and unit equations make these an isomorphism of
the reduction towers with their maps from Rf_*K. Apply derived inverse limit and its
canonical direct-image comparison. The resulting composite is the output completion
map. The input completion map is invertible by the hypothesis, hence so is its direct
image and the displayed composite; this also proves output completeness. On complete
inputs the composite out of Rf_*K is invertible, so its unit equation determines the
last comparison uniquely. -/
theorem completedDirectImage_completionUnit (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
    (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
    (e : DerivedCategory.Q.obj C ≅ K)
    (_hK : IsDerivedCompleteIntrinsic X d r a ha K C e)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ (completedDerivedDirectImage f d).obj K) :
    ∃ (κX : intrinsicCompletion X d r a ha K C e ≅
        (completedTowerRlim d X).obj ((completedReductionTower X d).obj K))
      (κY : intrinsicCompletion Y d r a ha ((completedDerivedDirectImage f d).obj K)
        P eP ≅ (completedTowerRlim d Y).obj ((completedReductionTower Y d).obj
          ((completedDerivedDirectImage f d).obj K))),
      intrinsicCompletionUnit X d r a ha K C e ≫ κX.hom =
        completedQuotientCompletionUnit d X K ∧
      intrinsicCompletionUnit Y d r a ha ((completedDerivedDirectImage f d).obj K)
          P eP ≫ κY.hom =
        completedQuotientCompletionUnit d Y ((completedDerivedDirectImage f d).obj K) ∧
      ∃! β : (completedTowerRlim d Y).obj ((completedTowerDirectImage f d).obj
          ((completedReductionTower X d).obj K)) ≅
        (completedTowerRlim d Y).obj ((completedReductionTower Y d).obj
          ((completedDerivedDirectImage f d).obj K)),
        (completedDerivedDirectImage f d).map
            (completedQuotientCompletionUnit d X K) ≫
          (completedDirectImageRlimIso f d).hom.app
            ((completedReductionTower X d).obj K) ≫ β.hom =
        completedQuotientCompletionUnit d Y
          ((completedDerivedDirectImage f d).obj K) := by
  sorry
```

```lean
/-- Completed direct image preserves intrinsic derived completeness.
Source: Stacks Tag 099N, clauses (1),(3),(4)
(blueprint: prop-weil-pbc-direct-image-limits).
Proof: the constant/completed comparison identifies intrinsic completion with the
finite-reduction derived limit. Perfect projection formula identifies the reductions
of Rf_*K with Rf_* of the reductions. Apply completedDirectImageRlimIso to the
input completion unit; the output unit is the stated composite and is invertible. -/
theorem completedDirectImage_complete (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
    (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
    (e : DerivedCategory.Q.obj C ≅ K)
    (_hK : IsDerivedCompleteIntrinsic X d r a ha K C e)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ (completedDerivedDirectImage f d).obj K) :
    IsDerivedCompleteIntrinsic Y d r a ha
      ((completedDerivedDirectImage f d).obj K) P eP := by
  sorry
```

## New

All twelve declarations above are removed. No replacement declaration is added.
All other existing signatures and definitions remain unchanged.

## Users

`tools/downstream.py Sheaf.Paper.CompletedTowerDirectImage --uses` was run with
all twelve names together. For each name its only hit is the assigned module itself.
There are 1,432 transitive importing modules; none refers to any removed declaration.
A separate whole-library search also finds no external occurrence, including imports
that are not in that transitive set. Only the assigned module is changed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompletedTowerDirectImage | A3 | Remove four unused holed theorems and eight definitions used only by them; retain every used declaration and its signature. |

The module's direct importers `PbcScalarExtension`, `PbcCompletedPullbackActual`,
`FourArrows`, `IntegralCompactSupportUniformRestriction`, `PreservationConstructible`
and `TowerPreservation` use none of these declarations. Their files, holders and
signatures are unchanged. `FiniteEtaleAdicCohomology` uses the retained limit-preservation
instance. All other downstream users continue to see the retained public interface.

## Status

landed 20261019T192643-L-1851237 2026-10-19 (merge of deliver/A3/Sheaf.Paper.CompletedTowerDirectImage)
