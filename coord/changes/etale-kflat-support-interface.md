# AlgebraicGeometry.Etale.KFlatSupportComparison.etale_kflat_support_comparison

## Reason

Repeated elaboration of the expanded tensor rows and their projections unfolds competing
but definitionally equal sheaf/cochain instances and the chosen derived localization.
The original naturality clause alone can exceed the single-file compile limit.
The row-family interface packages the same object and arrow assignments, using the
supplied tensor-left functor. HEq relates maps with definitionally equal endpoints.
No extra hypothesis or mathematical condition is added or dropped.

The proved support_rightMap_iff identifies equality to OpenSupport.rightMap with the
original IsRightMap condition. For the middle component, HEq and equality are equivalent
because both endpoints are Q tensor I and F(Q tensor I). Naturality unfolds to the original
quantification over all I', f and characterized m'. The normalized middle and quotient
equations use eta and the canonical right map directly; the two component identifications
make these equations equivalent to those for m. No target or adopted-source declaration
or existing data definition changes.

## Old

```lean
theorem etale_kflat_support_comparison [Finite A] [Finite B]
    (φ : A →+* B) (i : Z ⟶ P) [IsClosedImmersion i]
    (j : U ⟶ P) [IsOpenImmersion j] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (L : _root_.DerivedCategory.Plus (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hTL : ∃ n : ℤ, ((scalarExtension φ P).obj L.obj).IsGE n)
    (_hRTL : ∃ n : ℤ, ((R(lowerStar (ModuleCat.{u + 1} B) j)).obj
      ((D(upperStar (ModuleCat.{u + 1} B) j)).obj
        ((scalarExtension φ P).obj L.obj))).IsGE n)
    (_hRL : ∃ n : ℤ, ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj
      ((D(upperStar (ModuleCat.{u + 1} A) j)).obj L.obj)).IsGE n)
    (_hTRL : ∃ n : ℤ, ((scalarExtension φ P).obj
      ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj
        ((D(upperStar (ModuleCat.{u + 1} A) j)).obj L.obj))).IsGE n)
    (I : Complex A P) [I.IsKInjective] [∀ n : ℤ, Injective (I.X n)]
    (e : (localize A P).obj I ≅ L.obj)
    (Q : Complex A P)
    (π : Q ⟶ (CochainComplex.singleFunctor
      (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj (scalarCoefficientSheaf φ P))
    [QuasiIso π] (hQ : (HomologicalComplex.quasiIso
      (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)).kFlat Q)
    (_hQf : ∀ n : ℤ, ObjectProperty.flat (Q.X n))
    (F : Complex A P ⥤ Complex A P) (η : 𝟭 _ ⟶ F)
    [∀ K : Complex A P, (F.obj K).IsKInjective]
    [∀ (K : Complex A P) (n : ℤ), Injective ((F.obj K).X n)]
    [∀ K : Complex A P, QuasiIso (η.app K)] :
    let N := Q ⊗ I
    let J := F.obj N
    let a := η.app N
    let S := totalTensorSequence Q (etaleSupportSequence A i j hij I)
    let S' := etaleSupportSequence A i j hij J
    ∃ (hI : CochainComplex.IsKInjective
        ((pullComplex A j).obj I))
      (hJ : CochainComplex.IsKInjective
        ((pullComplex A j).obj J))
      (hTop : S.ShortExact)
      (hBottom : S'.ShortExact)
      (m : S ⟶ S'),
      m.τ₂ = a ∧
      IsRightMap j Q I J a m.τ₃ ∧
      (∀ m' : S ⟶ S',
        m'.τ₂ = a →
        IsRightMap j Q I J a m'.τ₃ → m' = m) ∧
      _root_.DerivedCategory.triangleOfSES hTop ∈ distTriang _ ∧
      _root_.DerivedCategory.triangleOfSES hBottom ∈ distTriang _ ∧
      _root_.DerivedCategory.triangleOfSESδ hTop ≫
          ((localize A P).map m.τ₁)⟦1⟧' =
        (localize A P).map m.τ₃ ≫ _root_.DerivedCategory.triangleOfSESδ hBottom ∧
      (tensorModel φ Q π hQ I L.obj e).inv ≫ (localize A P).map m.τ₂ ≫
          (replacementIso a (tensorModel φ Q π hQ I L.obj e)).hom =
        𝟙 _ ∧
      (localize A P).map m.τ₃ ≫
          (targetThirdModel φ j J L.obj
            (replacementIso a (tensorModel φ Q π hQ I L.obj e)) hJ).hom =
        (sourceThirdModel φ j Q π hQ I L.obj e hI).hom ≫ restrictedProjection φ j L.obj ∧
      (IsIso ((localize A P).map m.τ₃) → IsIso ((localize A P).map m.τ₁)) ∧
      (∀ (I' : Complex A P) (f : I ⟶ I'),
        let N' := Q ⊗ I'
        let J' := F.obj N'
        let a' := η.app N'
        let S₁ := totalTensorSequence Q (etaleSupportSequence A i j hij I')
        let S₂ := etaleSupportSequence A i j hij J'
        let s : S ⟶ S₁ := totalTensorSequenceMap Q (etaleSupportSequenceMap A i j hij f)
        let t : S' ⟶ S₂ := etaleSupportSequenceMap A i j hij (F.map ((tensorLeft Q).map f))
        ∀ m' : S₁ ⟶ S₂, m'.τ₂ = a' → IsRightMap j Q I' J' a' m'.τ₃ →
          s ≫ m' = m ≫ t)
```

## New

```lean
theorem etale_kflat_support_comparison [Finite A] [Finite B]
    (φ : A →+* B) (i : Z ⟶ P) [IsClosedImmersion i]
    (j : U ⟶ P) [IsOpenImmersion j] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (L : _root_.DerivedCategory.Plus (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hTL : ∃ n : ℤ, ((scalarExtension φ P).obj L.obj).IsGE n)
    (_hRTL : ∃ n : ℤ, ((R(lowerStar (ModuleCat.{u + 1} B) j)).obj
      ((D(upperStar (ModuleCat.{u + 1} B) j)).obj
        ((scalarExtension φ P).obj L.obj))).IsGE n)
    (_hRL : ∃ n : ℤ, ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj
      ((D(upperStar (ModuleCat.{u + 1} A) j)).obj L.obj)).IsGE n)
    (_hTRL : ∃ n : ℤ, ((scalarExtension φ P).obj
      ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj
        ((D(upperStar (ModuleCat.{u + 1} A) j)).obj L.obj))).IsGE n)
    (I : Complex A P) [I.IsKInjective] [∀ n : ℤ, Injective (I.X n)]
    (e : (localize A P).obj I ≅ L.obj)
    (Q : Complex A P)
    (π : Q ⟶ (CochainComplex.singleFunctor
      (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj (scalarCoefficientSheaf φ P))
    [QuasiIso π] (hQ : (HomologicalComplex.quasiIso
      (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)).kFlat Q)
    (_hQf : ∀ n : ℤ, ObjectProperty.flat (Q.X n))
    (F : Complex A P ⥤ Complex A P) (η : 𝟭 _ ⟶ F)
    [∀ K : Complex A P, (F.obj K).IsKInjective]
    [∀ (K : Complex A P) (n : ℤ), Injective ((F.obj K).X n)]
    [∀ K : Complex A P, QuasiIso (η.app K)] :
    let S := (topSequenceFamily A i j hij Q).obj I
    let N := Q ⊗ I
    let _J := F.obj N
    let a := η.app N
    let S' := (bottomSequenceFamily A i j hij Q F).obj I
    let v := OpenSupport.rightMap
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j)
      Q I (F.obj (Q ⊗ I)) (η.app (Q ⊗ I))
    ∃ (hI : CochainComplex.IsKInjective
        ((pullComplex A j).obj I))
      (hJ : CochainComplex.IsKInjective
        ((pullComplex A j).obj (F.obj (Q ⊗ I))))
      (hTop : S.ShortExact)
      (hBottom : S'.ShortExact)
      (m : S ⟶ S'),
      HEq m.τ₂ a ∧
      HEq m.τ₃ v ∧
      (∀ m' : S ⟶ S',
        HEq m'.τ₂ a →
        HEq m'.τ₃ v → m' = m) ∧
      _root_.DerivedCategory.triangleOfSES hTop ∈ distTriang _ ∧
      _root_.DerivedCategory.triangleOfSES hBottom ∈ distTriang _ ∧
      _root_.DerivedCategory.triangleOfSESδ hTop ≫
          ((localize A P).map m.τ₁)⟦1⟧' =
        (localize A P).map m.τ₃ ≫ _root_.DerivedCategory.triangleOfSESδ hBottom ∧
      (tensorModel φ Q π hQ I L.obj e).inv ≫ (localize A P).map (η.app (Q ⊗ I)) ≫
          (replacementIso (η.app (Q ⊗ I)) (tensorModel φ Q π hQ I L.obj e)).hom =
        𝟙 _ ∧
      (localize A P).map v ≫
          (targetThirdModel φ j (F.obj (Q ⊗ I)) L.obj
            (replacementIso (η.app (Q ⊗ I)) (tensorModel φ Q π hQ I L.obj e)) hJ).hom =
        (sourceThirdModel φ j Q π hQ I L.obj e hI).hom ≫ restrictedProjection φ j L.obj ∧
      (IsIso ((localize A P).map m.τ₃) → IsIso ((localize A P).map m.τ₁)) ∧
      DiagramNatural (topSequenceFamily A i j hij Q)
        (bottomSequenceFamily A i j hij Q F)
        (IsComparison A i j hij Q F η) I m
```

## Users

The downstream/uses scan lists only the declaration's own module; there are no Lean
consumers to adapt. The DAG parent lem-pur-finite-coefficient-adjoint-comparisons Step 6
continues to require exactly the same support diagram and normalized derived maps.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleKFlatSupportComparison | X9 | Equivalent compact statement and assembly proof |

## Status

landed 20261025T124418-L-2006284 2026-10-25 (merge of deliver/X9/Sheaf.AlgebraicGeometry.EtaleKFlatSupportComparison)
