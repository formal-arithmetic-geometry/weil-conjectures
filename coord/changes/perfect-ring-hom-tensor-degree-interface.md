# CategoryTheory.PerfectRingHomTensorDegreeCondition

## Reason

The degreewise theorem is decomposed into existence of a normalized morphism and its
invertibility. Both new theorem modules need the normalization interface, so keeping
its definitions in the original theorem module would produce an import cycle.
Extract the three definitions into a publicly imported interface module.
Names, universes, signatures, and visibility are identical. Two defining bodies are
unchanged; the evaluator uses the existing typed projection and canonical degree
transport to avoid slow elaboration of the raw chosen witness.
The original public import of PerfectRingDualTermFlat is retained.

## Old

In `Sheaf.Algebra.Homology.PerfectRingHomTensorDegrees`:

```lean
/-- Evaluate the degree `r` dual at a vector of degree `-r`, using the projection
of the shared Hom complex and the canonical degree-zero single-complex isomorphism.
Source: Stacks, Tag 0A6A (1), chain-level evaluation.
(blueprint: lem-pc-perfect-ring-hom-tensor-degrees) -/
noncomputable def perfectRingDualEvaluate {A : Type u} [CommRing A]
    (P : CochainComplex (RingSiteModules A) ℤ) (r : ℤ)
    (U : (Discrete PUnit.{u + 1})ᵒᵖ)
    (lam : ((perfectRingDual P).X r).val.obj U) (x : (P.X (-r)).val.obj U) : A := by
  let M := SheafOfModules.unit ((sheafCompose ⊥
    (forget₂ CommRingCat.{u} RingCat.{u})).obj (CochainComplex.onePointRingSheaf A))
  let S := (CochainComplex.singleFunctor (RingSiteModules A) 0).obj M
  let π := (homComplex_exists (R := CochainComplex.onePointRingSheaf A)).choose_spec.choose
    P S r (-r) 0 (by omega)
  let y := ((π.val.app U lam).app (op (Over.mk (𝟙 U.unop)))) x
  exact (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom.val.app U y

/-- The canonical map from the sectionwise tensor to the sheaf tensor, formed
from the sheafification unit and its specified tensor comparison.
Source: Stacks, Modules on Sites, Section 03EK.
(blueprint: lem-pc-perfect-ring-hom-tensor-degrees) -/
noncomputable def perfectRingTensorSectionMap {A : Type u} [CommRing A]
    (M N : RingSiteModules A) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    M.val ⊗ N.val ⟶ (M ⊗ N).val := by
  let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  exact (PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app (M.val ⊗ N.val) ≫
    (SheafOfModules.tensorObjIsoSheafification
      (R := CochainComplex.onePointRingSheaf A) M N).inv.val

/-- Normalization of evaluation: the `(r,s)` tensor summand contributes only to
Hom coordinate `-r`, with sign `(-1)^(r*s)`. The equation is before sheafification.
Source: Stacks, Tags 0A6A (1), 0ATK (1), expanded finite-projective argument.
(blueprint: lem-pc-perfect-ring-hom-tensor-degrees) -/
def PerfectRingHomTensorDegreeCondition {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    ((CochainComplex.mapBifunctor (perfectRingDual P) Q (curriedTensor _)).X n ⟶
      (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n) → Prop := by
  let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  intro a
  exact (∀ (r s : ℤ) (h : r + s = n) (p : ℤ), p ≠ -r →
    CochainComplex.ιMapBifunctor (perfectRingDual P) Q (curriedTensor _)
      r s n h ≫ a ≫ ringHomComplexProjection P Q n p = 0) ∧
    (∀ (r s : ℤ) (h : r + s = n) (U : (Discrete PUnit.{u + 1})ᵒᵖ)
      (lam : ((perfectRingDual P).X r).val.obj U) (y : (Q.X s).val.obj U)
      (x : (P.X (-r)).val.obj U),
      ringHomEvaluate P Q n (-r) U
        (a.val.app U ((CochainComplex.ιMapBifunctor (perfectRingDual P) Q
          (curriedTensor _) r s n h).val.app U
            ((perfectRingTensorSectionMap ((perfectRingDual P).X r) (Q.X s)).app U
              (lam ⊗ₜ[A] y)))) x =
        (eqToHom (congrArg Q.X (show s = -r + n by omega))).val.app U
          ((r * s).negOnePow • (perfectRingDualEvaluate P r U lam x • y)))

```

## New

The definitions and a proved private transport lemma are now in
`Sheaf.Algebra.Homology.PerfectRingHomTensorDegreeCondition`; the original module
publicly imports it. The new definitions are:

```lean
private lemma single_projection_evaluation {A : Type u} [CommRing A]
    (P : CochainComplex (RingSiteModules A) ℤ) (M Z : RingSiteModules A)
    (n p j : ℤ) (h : p + n = j)
    (π : ∀ (q : ℤ) (_h : p + n = q), Z ⟶
      SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) (P.X p)
        (((CochainComplex.singleFunctor (RingSiteModules A) j).obj M).X q))
    (U : (Discrete PUnit.{u + 1})ᵒᵖ) (lam : Z.val.obj U) (x : (P.X p).val.obj U) :
    (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) j M (p + n) h).hom.val.app U
      (((π (p + n) rfl).val.app U lam).app (op (Over.mk (𝟙 U.unop))) x) =
    (HomologicalComplex.singleObjXSelf (.up ℤ) j M).hom.val.app U
      (((π j h).val.app U lam).app (op (Over.mk (𝟙 U.unop))) x) := by
  subst j
  rfl

/-- Evaluate the degree `r` dual at a vector of degree `-r`, using the projection
of the shared Hom complex and the canonical degree-zero single-complex isomorphism.
Source: Stacks, Tag 0A6A (1), chain-level evaluation.
(blueprint: lem-pc-perfect-ring-hom-tensor-degrees) -/
noncomputable def perfectRingDualEvaluate {A : Type u} [CommRing A]
    (P : CochainComplex (RingSiteModules A) ℤ) (r : ℤ)
    (U : (Discrete PUnit.{u + 1})ᵒᵖ)
    (lam : ((perfectRingDual P).X r).val.obj U) (x : (P.X (-r)).val.obj U) : A := by
  let M := SheafOfModules.unit ((sheafCompose ⊥
    (forget₂ CommRingCat.{u} RingCat.{u})).obj (CochainComplex.onePointRingSheaf A))
  let S := (CochainComplex.singleFunctor (RingSiteModules A) 0).obj M
  let π := ringHomComplexProjection P S r (-r)
  let y := ((π.val.app U lam).app (op (Over.mk (𝟙 U.unop)))) x
  exact (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 M (-r + r)
    (by omega)).hom.val.app U y

/-- The canonical map from the sectionwise tensor to the sheaf tensor, formed
from the sheafification unit and its specified tensor comparison.
Source: Stacks, Modules on Sites, Section 03EK.
(blueprint: lem-pc-perfect-ring-hom-tensor-degrees) -/
noncomputable def perfectRingTensorSectionMap {A : Type u} [CommRing A]
    (M N : RingSiteModules A) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    M.val ⊗ N.val ⟶ (M ⊗ N).val := by
  let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  exact (PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app (M.val ⊗ N.val) ≫
    (SheafOfModules.tensorObjIsoSheafification
      (R := CochainComplex.onePointRingSheaf A) M N).inv.val

/-- Normalization of evaluation: the `(r,s)` tensor summand contributes only to
Hom coordinate `-r`, with sign `(-1)^(r*s)`. The equation is before sheafification.
Source: Stacks, Tags 0A6A (1), 0ATK (1), expanded finite-projective argument.
(blueprint: lem-pc-perfect-ring-hom-tensor-degrees) -/
def PerfectRingHomTensorDegreeCondition {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    ((CochainComplex.mapBifunctor (perfectRingDual P) Q (curriedTensor _)).X n ⟶
      (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n) → Prop := by
  let := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
  intro a
  exact (∀ (r s : ℤ) (h : r + s = n) (p : ℤ), p ≠ -r →
    CochainComplex.ιMapBifunctor (perfectRingDual P) Q (curriedTensor _)
      r s n h ≫ a ≫ ringHomComplexProjection P Q n p = 0) ∧
    (∀ (r s : ℤ) (h : r + s = n) (U : (Discrete PUnit.{u + 1})ᵒᵖ)
      (lam : ((perfectRingDual P).X r).val.obj U) (y : (Q.X s).val.obj U)
      (x : (P.X (-r)).val.obj U),
      ringHomEvaluate P Q n (-r) U
        (a.val.app U ((CochainComplex.ιMapBifunctor (perfectRingDual P) Q
          (curriedTensor _) r s n h).val.app U
            ((perfectRingTensorSectionMap ((perfectRingDual P).X r) (Q.X s)).app U
              (lam ⊗ₜ[A] y)))) x =
        (eqToHom (congrArg Q.X (show s = -r + n by omega))).val.app U
          ((r * s).negOnePow • (perfectRingDualEvaluate P r U lam x • y)))

```

The evaluator now projects to A[0]^(-r+r) with `ringHomComplexProjection` and
uses `singleObjXIsoOfEq` to transport to A[0]^0. The old version projected to
A[0]^0 directly and used `singleObjXSelf`. They are equal: apply the proved
`single_projection_evaluation` to the same family of projections chosen by
`homComplex_exists`. Substituting the target degree equality reduces the identity
to `rfl`; proof irrelevance identifies the equality witnesses. The helper is
proved for an arbitrary projection family so its elaboration does not unfold the
large Hom-complex choice. No ring dual or Hom object is replaced.

This refactor fixes a slow definition: the original direct chosen-projection
expression took 47 seconds initially and later exceeded the 60-second limit;
a diagnostic isolated it from the tensor-section map (4.6 seconds). Using the typed
projection interface reduced the entire definition module to 8.5 seconds before
adding the generic transport lemma. This is a change to the expression inside the
definition, not a split to evade the limit.

Every downstream importer sees the same exported constants and evaluation function.
The original theorem's signature is unchanged, and the new proof imports are
private to its module. No target statement changes meaning: the evaluation refactor
has the equality above, and the other two definitions are copied verbatim.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.PerfectRingHomTensorDegrees | Q2 | Definitions supplied by the new public import; theorem unchanged. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorDifferential | S1 | Predicate still supplied by the existing public import; no edit needed. |

The `downstream.py --uses` searches report only these declaration users.
There are 338 transitive downstream modules; their statements continue to use the
same exported constants. No target meaning changes and no forced adaptations occur.

## Status

landed 20261013T115432-L-3359892 2026-10-13 (merge of deliver/Q2/Sheaf.Algebra.Homology.PerfectRingHomTensorDegrees)
