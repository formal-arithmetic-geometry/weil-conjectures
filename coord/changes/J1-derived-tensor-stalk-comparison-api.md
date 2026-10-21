# AlgebraicGeometry.Etale.exists_derivedTensor_stalk_iso

## Reason

The expanded concrete statement repeatedly exceeded the normal 60-second per-file limit.
A baseline with an unproved body spent 23--47 seconds checking the statement alone; the
complete generic transport proof compiled independently in 6--12 seconds. A direct
specialization of that proof, and attempts to align braidings and coproduct instances,
still exceeded 60 seconds. The named-proposition version compiled completely in 15 seconds
without changing the limit, splitting the file, adding a hypothesis, or dropping a clause.

`ExactFunctorTensorComparison` is a real definition of a proposition: exactly the original
existence, two-variable naturality and homotopy-localization counit equation. It contains no
chosen data or proof hole. The stalk theorem has the same ring, scheme and geometric point
parameters and asserts this proposition for exactly the original stalk functor.
`derivedTensor` is definitionally `curriedTensor`; all underlying category and monoidal
structures, universes, maps and normalization terms are preserved. The proved
`exactFunctorTensorComparison_iff` exposes the complete formula, while
`ExactFunctorTensorComparison.exists_iso` exposes the part used by current consumers.
The public generic comparison, its pointwise accessor and the geometric-stalk flat-preservation
instance are fully proved. The minimal public class import exposes `Functor.PreservesFlat`
in their signatures. The generic comparison uses the source library's derived tensor
comparison and exact-functor comparison, and specializes after proving flat preservation.
This is neither a weaker theorem nor a transfer of its hole into a new declaration.

No adopted-source file, target statement, existing definition or instance is changed.
The only consumer changes are forced proof adaptations. No target acquires a changed
mathematical meaning. The original statements of all adapted consumers stay verbatim.

## Old

```lean
theorem exists_derivedTensor_stalk_iso
    (A : Type (u + 1)) [CommRing A] {T : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    ∃ e : ∀ K L : DerivedCategoryModule A T,
      (pointSmallEtale t).sheafFiber.mapDerivedCategory.obj
          (((derivedTensor (ModuleCat.{u + 1} A) T).obj K).obj L) ≅
        (pointSmallEtale t).sheafFiber.mapDerivedCategory.obj K ⊗
          (pointSmallEtale t).sheafFiber.mapDerivedCategory.obj L,
      (∀ (K K' L L' : DerivedCategoryModule A T) (f : K ⟶ K') (g : L ⟶ L'),
        (pointSmallEtale t).sheafFiber.mapDerivedCategory.map
            (((derivedTensor (ModuleCat.{u + 1} A) T).map f).app L ≫
              ((derivedTensor (ModuleCat.{u + 1} A) T).obj K').map g) ≫
            (e K' L').hom =
          (e K L).hom ≫
            ((pointSmallEtale t).sheafFiber.mapDerivedCategory.map f ⊗ₘ
              (pointSmallEtale t).sheafFiber.mapDerivedCategory.map g)) ∧
      ∀ P Q : HomotopyCategory
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ),
        (e (_root_.DerivedCategory.Qh.obj P) (_root_.DerivedCategory.Qh.obj Q)).hom ≫
          ((pointSmallEtale t).sheafFiber.mapDerivedCategoryFactorsh.hom.app P ⊗ₘ
            (pointSmallEtale t).sheafFiber.mapDerivedCategoryFactorsh.hom.app Q) ≫
          Functor.LaxMonoidal.μ (_root_.DerivedCategory.Qh (C := ModuleCat.{u + 1} A))
            (((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A) |>.mapHomotopyCategory
              (ComplexShape.up ℤ)).obj P)
            (((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A) |>.mapHomotopyCategory
              (ComplexShape.up ℤ)).obj Q) =
        (pointSmallEtale t).sheafFiber.mapDerivedCategory.map
          (Functor.LaxMonoidal.μ (_root_.DerivedCategory.Qh
            (C := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) P Q) ≫
          (pointSmallEtale t).sheafFiber.mapDerivedCategoryFactorsh.hom.app (P ⊗ Q) ≫
          (_root_.DerivedCategory.Qh (C := ModuleCat.{u + 1} A)).map
            (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ)
              ((pointSmallEtale t).sheafFiber)).app P).app Q)
```

## New

```lean
theorem exists_derivedTensor_stalk_iso
    (A : Type (u + 1)) [CommRing A] {T : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    ExactFunctorTensorComparison
      ((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A))
```

Its proposition is defined, in the same module, by:

```lean
@[irreducible]
def ExactFunctorTensorComparison
    {C : Type uC} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type uD} [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.IsLeftAdjoint] [F.Monoidal] : Prop :=
    ∃ e : ∀ K L : _root_.DerivedCategory C,
      F.mapDerivedCategory.obj (((curriedTensor (_root_.DerivedCategory C)).obj K).obj L) ≅
        F.mapDerivedCategory.obj K ⊗ F.mapDerivedCategory.obj L,
      (∀ (K K' L L' : _root_.DerivedCategory C) (f : K ⟶ K') (g : L ⟶ L'),
        F.mapDerivedCategory.map (((curriedTensor (_root_.DerivedCategory C)).map f).app L ≫
          ((curriedTensor (_root_.DerivedCategory C)).obj K').map g) ≫
          (e K' L').hom =
          (e K L).hom ≫ (F.mapDerivedCategory.map f ⊗ₘ F.mapDerivedCategory.map g)) ∧
      ∀ P Q : HomotopyCategory C (.up ℤ),
        (e (_root_.DerivedCategory.Qh.obj P) (_root_.DerivedCategory.Qh.obj Q)).hom ≫
          (F.mapDerivedCategoryFactorsh.hom.app P ⊗ₘ F.mapDerivedCategoryFactorsh.hom.app Q) ≫
          Functor.LaxMonoidal.μ (_root_.DerivedCategory.Qh (C := D))
            ((F.mapHomotopyCategory (.up ℤ)).obj P)
            ((F.mapHomotopyCategory (.up ℤ)).obj Q) =
        F.mapDerivedCategory.map
          (Functor.LaxMonoidal.μ (_root_.DerivedCategory.Qh (C := C)) P Q) ≫
          F.mapDerivedCategoryFactorsh.hom.app (P ⊗ Q) ≫
          (_root_.DerivedCategory.Qh (C := D)).map
            (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app P).app Q)
```

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.EtaleDerivedTensorStalk
--uses exists_derivedTensor_stalk_iso` lists twelve downstream modules and the four direct
occurrences including this module. The direct consumers only use the objectwise
isomorphisms; their comparison-construction blocks call the proved generic accessor and explicitly
bridge `derivedTensor` to `curriedTensor` at the functor level. Original consumer compiles
against the changed dependency failed at those lines with `Tactic rcases failed: ... is not
an inductive datatype`. Holder records were read from module and DAG-node claims.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleDerivedTensorStalk | J1 | Equivalent proposition API; complete proof; auxiliary instances unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | unclaimed | No use of the changed theorem; signatures, definitions and proofs unchanged. |
| Sheaf.AlgebraicGeometry.EtaleStalkTorTest | Q18 | Replace existential unpacking and bridge the tensor functors in the comparison construction; all signatures, visibility, imports and subsequent arguments unchanged. |
| Sheaf.AlgebraicGeometry.SmoothStratificationFiniteTor | unclaimed | No use of the changed theorem; signatures, definitions and proofs unchanged. |
| Sheaf.Paper.CoefficientChangeDualizing | unclaimed | No use of the changed theorem; signatures, definitions and proofs unchanged. |
| Sheaf.Paper.CtfHomCoefficientComparison | unclaimed | No use of the changed theorem; signatures, definitions and proofs unchanged. |
| Sheaf.Paper.HomUniversalCoefficients | unclaimed | No use of the changed theorem; signatures, definitions and proofs unchanged. |
| Sheaf.Paper.OpenTorBoundArbitraryField | unclaimed | No use of the changed theorem; signatures, definitions and proofs unchanged. |
| Sheaf.Paper.OpenTorBoundStalkFilteredExtension | unclaimed | Replace existential unpacking and bridge the tensor functors in the comparison construction; all signatures, visibility, imports and subsequent arguments unchanged. |
| Sheaf.SixFunctors.AdmissibleDirectImage | Q59 | No use of the changed theorem; signatures, definitions and proofs unchanged. |
| Sheaf.SixFunctors.ConnectedEtalePerfectConstant | unclaimed | No use of the changed theorem; signatures, definitions and proofs unchanged. |
| Sheaf.SixFunctors.EtaleStratifiedStalkIdentification | unclaimed | No use of the changed theorem; signatures, definitions and proofs unchanged. |
| Sheaf.SixFunctors.GeometricStalkTensorConstantSingle | unclaimed | Replace existential unpacking and bridge the tensor functors in the comparison construction; all signatures, visibility, imports and subsequent arguments unchanged. |

## Status

landed 20261021T111206-L-52924 2026-10-21 (merge of deliver/J1/Sheaf.AlgebraicGeometry.EtaleDerivedTensorStalk)
