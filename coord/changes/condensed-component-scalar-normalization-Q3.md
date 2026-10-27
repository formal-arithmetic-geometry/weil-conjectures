# AlgebraicGeometry.ProEtale.CondensedRing.componentComparisons

## Reason

The projective-calculus theorem requires its scalar homomorphism to have a specified
underlying function. The component comparison exposed a section-ring isomorphism and
scalar-realization comparison, but no equation relating that isomorphism to point scalars.
HRS (3.2), Remark 3.2 and Proposition 4.3(3), especially the coefficient identity and
(4.2) preceding its last square, use the canonical section identification, compatible
with constants. The existing proof step already says “including constants”; its Lean
interface omitted this requirement.

Add that scalar equation to componentComparisons. The explicit section construction
moves verbatim (generalizing the bundled ring parameter to its underlying commutative
ring object) from projectiveCalculusScalarSection to affineScalarSection in the shared
model module. The old name becomes a definitional alias. No data is chosen from a
new theorem. There is no new theorem hole. The existing component-compatibility theorem
still has its original named sorry, now with the scalar-normalization obligation recorded
in its node and docstring. This is an interface repair, not a proof of that dependency.

## Old

```lean
def componentComparisons
    (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ T)) : Prop :=
  (∃ (_ : (componentDerived Λ T α).CommShift ℤ),
    (componentDerived Λ T α).IsTriangulated) ∧
  componentSymmetric Λ T α ∧
  Nonempty ((componentDerived Λ T α).obj
      (𝟙_ (Evaluation.D ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
        (profiniteCoefficient Λ (affineComponentSpace T)))) ≅
    𝟙_ (Evaluation.D (Scheme.ProEt.topology T) (condensedRingObj Λ T))) ∧
  (∃ e : (Evaluation.lisse
      ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      (profiniteCoefficient Λ (affineComponentSpace T))).FullSubcategory ≌
      (Evaluation.lisse (Scheme.ProEt.topology T) (condensedRingObj Λ T)).FullSubcategory,
    Nonempty (e.functor ⋙ (Evaluation.lisse (Scheme.ProEt.topology T)
        (condensedRingObj Λ T)).ι ≅
      (Evaluation.lisse ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
        (profiniteCoefficient Λ (affineComponentSpace T))).ι ⋙ componentDerived Λ T α)) ∧
  ∃ a : Evaluation.A ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      (profiniteCoefficient Λ (affineComponentSpace T)) (Over.mk (𝟙 (affineComponentSpace T))) ≅
      Evaluation.A (Scheme.ProEt.topology T) (condensedRingObj Λ T) (Scheme.ProEt.mk (𝟙 T)),
    Nonempty (Evaluation.F ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
        (profiniteCoefficient Λ (affineComponentSpace T))
        (Over.mk (𝟙 (affineComponentSpace T))) Over.mkIdTerminal ⋙ componentDerived Λ T α ≅
      RingDerivedScalarExtension.moduleDerivedExtension a.hom.hom ⋙
        Evaluation.F (Scheme.ProEt.topology T) (condensedRingObj Λ T)
          (Scheme.ProEt.mk (𝟙 T)) (MorphismProperty.Over.mkIdTerminal
            @AlgebraicGeometry.WeaklyEtale T)) ∧
    Nonempty (profiniteScalarRealization Λ (affineComponentSpace T) ⋙ componentDerived Λ T α ≅
      condensedScalarRealization Λ T) ∧
    Nonempty (condensedScalarRealization Λ T ≅
      RingDerivedScalarExtension.moduleDerivedExtension
          (a.hom.hom.comp (profiniteScalarMap Λ (affineComponentSpace T))) ⋙
        Evaluation.F (Scheme.ProEt.topology T) (condensedRingObj Λ T)
          (Scheme.ProEt.mk (𝟙 T))
          (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale T))

def projectiveCalculusScalarSection (r : condensedScalarRing Λ.X) :
    Evaluation.A (Scheme.ProEt.topology T) (condensedRingObj Λ.X T)
      (Scheme.ProEt.mk (𝟙 T)) :=
  let rmap : 𝟙_ Ab.{u + 1} ⟶ Λ.X.obj.obj (op (⊤_ Profinite.{u})) :=
    AddCommGrpCat.ofHom
      (((AddMonoidHom.mulRight r).comp (Int.castAddHom (condensedScalarRing Λ.X))).comp
        AddEquiv.ulift.toAddMonoidHom)
  let s : 𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ.X :=
    ((constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
      terminalIsTerminal).homEquiv (𝟙_ Ab.{u + 1}) Λ.X).symm rmap
  let t : 𝟙_ (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) ⟶ condensedRingObj Λ.X T :=
    Functor.LaxMonoidal.ε (upperStarFromPoint T) ≫ (upperStarFromPoint T).map s
  (t.hom.app (op (Scheme.ProEt.mk (𝟙 T))))
    ((toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (𝟙_ Ab.{u + 1}))).app
        (op (Scheme.ProEt.mk (𝟙 T))) (ULift.up 1))
```

## New

```lean
def componentComparisons
    (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ T)) : Prop :=
  (∃ (_ : (componentDerived Λ T α).CommShift ℤ),
    (componentDerived Λ T α).IsTriangulated) ∧
  componentSymmetric Λ T α ∧
  Nonempty ((componentDerived Λ T α).obj
      (𝟙_ (Evaluation.D ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
        (profiniteCoefficient Λ (affineComponentSpace T)))) ≅
    𝟙_ (Evaluation.D (Scheme.ProEt.topology T) (condensedRingObj Λ T))) ∧
  (∃ e : (Evaluation.lisse
      ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      (profiniteCoefficient Λ (affineComponentSpace T))).FullSubcategory ≌
      (Evaluation.lisse (Scheme.ProEt.topology T) (condensedRingObj Λ T)).FullSubcategory,
    Nonempty (e.functor ⋙ (Evaluation.lisse (Scheme.ProEt.topology T)
        (condensedRingObj Λ T)).ι ≅
      (Evaluation.lisse ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
        (profiniteCoefficient Λ (affineComponentSpace T))).ι ⋙ componentDerived Λ T α)) ∧
  ∃ a : Evaluation.A ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      (profiniteCoefficient Λ (affineComponentSpace T)) (Over.mk (𝟙 (affineComponentSpace T))) ≅
      Evaluation.A (Scheme.ProEt.topology T) (condensedRingObj Λ T) (Scheme.ProEt.mk (𝟙 T)),
    (∀ r : condensedScalarRing Λ,
      a.hom.hom (profiniteScalarMap Λ (affineComponentSpace T) r) =
        affineScalarSection Λ T r) ∧
    Nonempty (Evaluation.F ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
        (profiniteCoefficient Λ (affineComponentSpace T))
        (Over.mk (𝟙 (affineComponentSpace T))) Over.mkIdTerminal ⋙ componentDerived Λ T α ≅
      RingDerivedScalarExtension.moduleDerivedExtension a.hom.hom ⋙
        Evaluation.F (Scheme.ProEt.topology T) (condensedRingObj Λ T)
          (Scheme.ProEt.mk (𝟙 T)) (MorphismProperty.Over.mkIdTerminal
            @AlgebraicGeometry.WeaklyEtale T)) ∧
    Nonempty (profiniteScalarRealization Λ (affineComponentSpace T) ⋙ componentDerived Λ T α ≅
      condensedScalarRealization Λ T) ∧
    Nonempty (condensedScalarRealization Λ T ≅
      RingDerivedScalarExtension.moduleDerivedExtension
          (a.hom.hom.comp (profiniteScalarMap Λ (affineComponentSpace T))) ⋙
        Evaluation.F (Scheme.ProEt.topology T) (condensedRingObj Λ T)
          (Scheme.ProEt.mk (𝟙 T))
          (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale T))

def affineScalarSection (T : Scheme.{u}) (r : condensedScalarRing Λ) :
    Evaluation.A (Scheme.ProEt.topology T) (condensedRingObj Λ T)
      (Scheme.ProEt.mk (𝟙 T)) :=
  let rmap : 𝟙_ Ab.{u + 1} ⟶ Λ.obj.obj (op (⊤_ Profinite.{u})) :=
    AddCommGrpCat.ofHom
      (((AddMonoidHom.mulRight r).comp (Int.castAddHom (condensedScalarRing Λ))).comp
        AddEquiv.ulift.toAddMonoidHom)
  let s : 𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ :=
    ((constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
      terminalIsTerminal).homEquiv (𝟙_ Ab.{u + 1}) Λ).symm rmap
  let t : 𝟙_ (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) ⟶ condensedRingObj Λ T :=
    Functor.LaxMonoidal.ε (upperStarFromPoint T) ≫ (upperStarFromPoint T).map s
  (t.hom.app (op (Scheme.ProEt.mk (𝟙 T))))
    ((toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (𝟙_ Ab.{u + 1}))).app
        (op (Scheme.ProEt.mk (𝟙 T))) (ULift.up 1))

def projectiveCalculusScalarSection (r : condensedScalarRing Λ.X) :
    Evaluation.A (Scheme.ProEt.topology T) (condensedRingObj Λ.X T)
      (Scheme.ProEt.mk (𝟙 T)) :=
  affineScalarSection Λ.X T r
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel | unclaimed | Owns the repaired predicate and the moved explicit section constructor. |
| Sheaf.AlgebraicGeometry.CondensedComponentPullbackCompatibility | unclaimed | Statement uses the strengthened predicate; its existing named hole is retained and its proof docstring and node record normalization. |
| Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation | unclaimed | Passes the component theorem through unchanged; original source compiles against the repaired model. |
| Sheaf.AlgebraicGeometry.CondensedWContractibleProjectiveCalculus | Q3 | Uses normalization in its completed scalar clause; original scalar section name is definitionally unchanged. |

`tools/downstream.py ... --uses componentComparisons componentClause` lists exactly
the first three modules as direct textual users of the repaired predicates; the item
adds the new explicit use. There are 73 transitive downstream modules, but none of the
others mentions or destructures either predicate. Searching quarantined Sheaf modules
finds no additional use. F, G, lisse, perfect, coefficient rings, derived tensors, and
all scalar realization functors keep their definitions. No Challenge declaration
signature changes. The target statement review is unaffected: the change strengthens
a proposition asserting canonical comparison data, without changing its underlying
categories or mathematical notions.

## Status

landed 20261024T015546-L-2418254 2026-10-24 (merge of deliver/Q3/Sheaf.AlgebraicGeometry.CondensedWContractibleProjectiveCalculus)
