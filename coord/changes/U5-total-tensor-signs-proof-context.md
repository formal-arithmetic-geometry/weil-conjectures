# SheafOfModules.TotalTensorSigns.totalTensorHomotopyConeSigns

## Reason

The theorem specializes the existing generic bifunctor API. Keeping the canonical
tensor and total functors as named definitions, with their existing properties exposed
as instances, avoids repeatedly expanding their data during elaboration and kernel
checking. This record covers those two abbreviation-to-definition changes, eight proved
instance declarations, private proved helpers, local proof settings and proof imports.
No hypothesis is added, no conclusion is weakened, and the mathematical data are retained.

## Old

The module had the same theorem statement with one `by sorry` proof. `tensor` and
`total` were abbreviations with exactly the bodies below. Its private imports included
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed` and
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.

The unchanged public signature is:

```lean
theorem totalTensorHomotopyConeSigns :
    (∀ A : CochainComplex (Modules R) ℤ,
      ((total R).obj A).Additive ∧ ((total R).flip.obj A).Additive ∧
      (((homotopyTensor R).obj ((HomotopyCategory.quotient _ _).obj A)).Additive ∧
        ((homotopyTensor R).flip.obj ((HomotopyCategory.quotient _ _).obj A)).Additive) ∧
      (((homotopyTensor R).obj ((HomotopyCategory.quotient _ _).obj A)).IsTriangulated ∧
        ((homotopyTensor R).flip.obj ((HomotopyCategory.quotient _ _).obj A)).IsTriangulated) ∧
      (NatTrans.CommShift ((tensor R).quotientCompBifunctorMapHomotopyObjIso
        (.up ℤ) (.up ℤ) (.up ℤ) A).hom ℤ ∧
        NatTrans.CommShift ((tensor R).quotientCompBifunctorMapHomotopyFlipObjIso
          (.up ℤ) (.up ℤ) (.up ℤ) A).hom ℤ)) ∧
    (∀ (A X Y : CochainComplex (Modules R) ℤ) (f g : X ⟶ Y) (h : Homotopy f g)
        (p q n : ℤ) (hpq : p + q = n),
      (ι R A X p q n hpq ≫
        (homotopyLeft R A h).hom n (n - 1) =
        p.negOnePow • (A.X p ◁ h.hom q (q - 1) ≫
          ι R A Y p (q - 1) (n - 1) (by omega))) ∧
      (ι R X A q p n (by omega) ≫
        (homotopyRight R A h).hom n (n - 1) =
        h.hom q (q - 1) ▷ A.X p ≫
          ι R Y A (q - 1) p (n - 1) (by omega))) ∧
    (∀ (A X Y : CochainComplex (Modules R) ℤ) (f : X ⟶ Y),
      (((total R).obj A).map (mappingCone.inr f) ≫ (coneLeft R A f).hom =
        mappingCone.inr (((total R).obj A).map f)) ∧
      (((total R).flip.obj A).map (mappingCone.inr f) ≫ (coneRight R A f).hom =
        mappingCone.inr (((total R).flip.obj A).map f)) ∧
      (∀ (p q n : ℤ) (hpq : p + q = n),
        (A.X p ◁ (mappingCone.inl f).v (q + 1) q (by omega) ≫
            ι R A (mappingCone f) p q n hpq ≫
            (coneLeft R A f).hom.f n =
          p.negOnePow • (ι R A X
            p (q + 1) (n + 1) (by omega) ≫
              (mappingCone.inl (((total R).obj A).map f)).v (n + 1) n (by omega))) ∧
        ((mappingCone.inl f).v (q + 1) q (by omega) ▷ A.X p ≫
            ι R (mappingCone f) A q p n (by omega) ≫
            (coneRight R A f).hom.f n =
          ι R X A (q + 1) p (n + 1) (by omega) ≫
            (mappingCone.inl (((total R).flip.obj A).map f)).v (n + 1) n (by omega))) ∧
      ((coneLeft R A f).hom ≫ (-(mappingCone.triangle (((total R).obj A).map f)).mor₃) =
        ((total R).obj A).map (-(mappingCone.triangle f).mor₃) ≫
          (shiftLeft R A X 1).hom) ∧
      ((coneRight R A f).hom ≫ (-(mappingCone.triangle (((total R).flip.obj A).map f)).mor₃) =
        ((total R).flip.obj A).map (-(mappingCone.triangle f).mor₃) ≫
          (shiftRight R A X 1).hom) ∧
      ((coneLeft R A f).hom ≫ (mappingCone.triangle (((total R).obj A).map f)).mor₃ =
        ((total R).obj A).map (mappingCone.triangle f).mor₃ ≫
          (shiftLeft R A X 1).hom) ∧
      ((coneRight R A f).hom ≫ (mappingCone.triangle (((total R).flip.obj A).map f)).mor₃ =
        ((total R).flip.obj A).map (mappingCone.triangle f).mor₃ ≫
          (shiftRight R A X 1).hom)) ∧
    (∀ (A X Y X' Y' : CochainComplex (Modules R) ℤ) (f : X ⟶ Y) (f' : X' ⟶ Y')
        (a : X ⟶ X') (b : Y ⟶ Y') (comm : f ≫ b = a ≫ f'),
      (((total R).obj A).map (mappingCone.map f f' a b comm) ≫ (coneLeft R A f').hom =
        (coneLeft R A f).hom ≫ mappingCone.map (((total R).obj A).map f) (((total R).obj A).map f')
          (((total R).obj A).map a) (((total R).obj A).map b)
          (by rw [← Functor.map_comp, comm, Functor.map_comp])) ∧
      (((total R).flip.obj A).map (mappingCone.map f f' a b comm) ≫ (coneRight R A f').hom =
        (coneRight R A f).hom ≫
          mappingCone.map (((total R).flip.obj A).map f) (((total R).flip.obj A).map f')
          (((total R).flip.obj A).map a) (((total R).flip.obj A).map b)
          (by rw [← Functor.map_comp, comm, Functor.map_comp]))) ∧
    (∀ (A B : CochainComplex (Modules R) ℤ),
      (swap R B A).inv = (swap R A B).hom ∧
      ∀ (i j n : ℤ) (hij : i + j = n),
        ι R B A i j n hij ≫
            (swap R B A).hom.f n =
          (i * j).negOnePow • ((β_ (B.X i) (A.X j)).hom ≫
            ι R A B j i n (by omega))) ∧
    (∀ (A A' B B' : CochainComplex (Modules R) ℤ) (a : A ⟶ A') (b : B ⟶ B'),
      HomologicalComplex.mapBifunctorMap b a (tensor R) (.up ℤ) ≫
          (swap R B' A').hom =
        (swap R B A).hom ≫
          HomologicalComplex.mapBifunctorMap a b (tensor R) (.up ℤ)) ∧
    (∀ (A : CochainComplex (Modules R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients A →
        (∀ (X Y : CochainComplex (Modules R) ℤ) (f : X ⟶ Y),
          QuasiIso f → QuasiIso (((total R).obj A).map f) ∧
            QuasiIso (((total R).flip.obj A).map f)) ∧
        ∀ n : ℤ, CochainComplex.IsKFlatIndependentCoefficients (A⟦n⟧)) ∧
    (∀ (A : CochainComplex (Modules R) ℤ),
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (A.X i)) →
        ∀ n i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) ((A⟦n⟧).X i))
```

## New

The theorem has a complete proof using proved private helpers for a symmetric monoidal
preadditive category. The cone and homotopy component formulas, signed interchange,
cone naturality and third-arrow identities are proved from the existing APIs. The
K-flat argument uses the acyclic-cone criterion, signed symmetry and shift comparison.

The two functor definitions have exactly the old bodies:

```lean
def tensor := curriedTensor (Modules R)
def total := (tensor R).map₂CochainComplex
```

The carrier remains the original `abbrev Modules`. The existing `homotopyTensor`,
cone, signed swap, inclusion, homotopy and shift construction bodies are unchanged.
Five exported instances expose the regular definitions' existing properties:
`tensorAdditive`, `tensorObjAdditive`, `totalExists`, `totalObjAdditive` and
`totalFlipObjAdditive`. Their proofs unfold the definitions and use the native
instances or the generic totalization existence lemma.

Three public named local instances share native constructions. `coefficientCompose`
transports sheaf composition from the small model in the coefficient universe.
`Generic.genericTotalExists` supplies countable totalization in an abstract category.
`modulesAbelian` retains the native finite-product, kernel, cokernel and normality
fields and explicitly names the same pointwise preadditive field. These are real
constructions, with no postponed data fields. Public signatures and public definition
bodies use public names; private helpers occur only in proofs.

Local irreducibility of `SheafOfModules.monoidalCategory` prevents expansion of the
localization construction. The component proofs locally expose
`CategoryTheory.Functor.map₂HomologicalComplex` and use declaration-local backward
transparency options. Higher local priorities select the pointwise preadditive
instances for sheaves, complexes and functor categories, the complex linear instance,
preservation of zero morphisms from additivity, and the existing coefficient-universe
sheafification and locally-bijective instances. These settings end with this module.
No timeout or heartbeat limit is increased; no linter is disabled.

The two obsolete private imports are removed and the private proof import
`WeilConjectures.FromJoel.Algebra.Homology.Bifunctor` is added for the additive instances.

## Users

The only changed Lean module is this item, held by U5. Its current direct consumer
`Sheaf.Paper.NormalizedErrorTowerData` compiles unchanged against the new definitions
and instance interface. No forced adaptation is needed. No target meaning changes.

The node's statement, statement dependencies and unit route are unchanged. Its proof
route no longer needs the tensor-closed and presheaf-sheafification nodes directly;
the underlying tensor construction and its dependencies are retained.

## Status

landed 20261022T013442-L-3584909 2026-10-22 (merge of deliver/U5/Sheaf.Algebra.Homology.TotalTensorHomotopyConeSigns)
