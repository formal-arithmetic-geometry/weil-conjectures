# AlgebraicGeometry.Etale.VectorTraceScalar canonical data

## Reason

Split the unfinished scalar-descent argument into projective, affine and frame substeps without
creating import cycles. Move the eleven canonical helper definitions into
`Sheaf.Paper.VectorTraceScalarData`; the item publicly imports that module. Their fully qualified
names, universes, binders, definition terms and attributes are identical. No statement, coefficient
object or chosen comparison map changes. The theorem's fivefold conjunction is byte-for-byte
unchanged. The new definition node records seven maps formerly attached only to the theorem node;
the existing coefficient-data node follows its four unchanged definitions.

## Old

In `Sheaf.Paper.VectorTraceScalarDescent`:

```lean
@[irreducible]
def balancing (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    ∀ r : ℕ, (purityScalarSheaf φ T).obj (Scheme.finiteEtaleTateTwist T N A hA r) ≅
      Scheme.finiteEtaleTateTwist T N B hB r :=
  Classical.choose ((finite_tate_scalar_source_normalization φ N hN hA hB T
    (fun x ↦ by
      simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ x trivial).hom)).2.exists)

/-- The degree-one balancing from the uniquely generator-normalized Tate theorem,
shifted using its actual scalar/single comparison. This is l_{T,1}.
Source: blueprint paragraph 2, normalized coefficient identifications
(blueprint: lem-pur-vector-trace-scalar-descent). -/
def line (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    (scalarExtension φ T).obj ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) ⟶
      (ordinaryFiniteLine B N hB T)⟦(2 : ℤ)⟧ :=
  finiteTateScalarLineMap φ N hA hB T 1 (balancing φ N hN hA hB T hT 1)

/-- Multiplication on the constant coefficient complex, with the published single/unit
identifications. Source: blueprint paragraph 2, u_T
(blueprint: lem-pur-vector-trace-scalar-descent). -/
abbrev unit (φ : A →+* B) (T : Scheme.{u}) :
    (scalarExtension φ T).obj (ordinaryFiniteUnit A T) ⟶ ordinaryFiniteUnit B T :=
  purityScalarUnitMap φ T

/-- The tensor powers of shifted balanced lines, starting with multiplication at rank
zero. This is l in the ordered shifted-Tate presentation already used by integration;
no orientation or new Tate object is chosen.
Source: blueprint paragraph 2, l_{T,d}
(blueprint: lem-pur-vector-trace-scalar-descent). -/
def base (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    ∀ d : ℕ, (scalarExtension φ T).obj (affineLinearBaseCoefficient A N hA T d) ⟶
      affineLinearBaseCoefficient B N hB T d
  | 0 => unit φ T
  | d + 1 =>
    (ExceptionalCoefficients.tensorIso φ T).hom.app
      (affineLinearBaseCoefficient A N hA T d, (ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) ≫
    ((ordinaryFiniteTensor B T).map (base φ N hN hA hB T hT d)).app
      ((scalarExtension φ T).obj ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)) ≫
    ((ordinaryFiniteTensor B T).obj (affineLinearBaseCoefficient B N hB T d)).map
      (line φ N hN hA hB T hT)

/-- The normalized scalar map on the pullback of an ordered Tate coefficient. The
inverse scalar/pullback comparison has source Q_X f^* and target f'^* Q_Y.
Source: blueprint paragraph 2, pullback compatibility of l
(blueprint: lem-pur-vector-trace-scalar-descent). -/
def pullBase (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X T : Scheme.{u}} (f : X ⟶ T) (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) :
    (scalarExtension φ X).obj
        ((ordinaryFinitePullback A f).obj (affineLinearBaseCoefficient A N hA T d)) ⟶
      (ordinaryFinitePullback B f).obj (affineLinearBaseCoefficient B N hB T d) :=
  (scalarPullbackIso φ f).inv.app (affineLinearBaseCoefficient A N hA T d) ≫
    (ordinaryFinitePullback B f).map (base φ N hN hA hB T hT d)

/-- The actual proper scalar mate followed by the degree-one normalized balancing.
Source: blueprint paragraph 2, tilde q_p
(blueprint: lem-pur-vector-trace-scalar-descent). -/
def projective (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    (scalarExtension φ S).obj
        ((ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)) ⟶
      (ordinaryFinitePushforward B (ProjectiveLine S ↘ S)).obj
        ((ordinaryFiniteLine B N hB (ProjectiveLine S))⟦(2 : ℤ)⟧) :=
  (scalarMate φ (ProjectiveLine S ↘ S)).app
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
    (ordinaryFinitePushforward B (ProjectiveLine S ↘ S)).map
      (line φ N hN hA hB (ProjectiveLine S) (ordinaryFiniteP1_isUnit N S hS))

/-- The comparison d_S is assembled from its two projections l_{S,1} and u_S.
Source: blueprint paragraph 2, projective-line decomposition
(blueprint: lem-pur-vector-trace-scalar-descent). -/
def sum (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    (scalarExtension φ S).obj
        ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ⟶
      ((ordinaryFiniteLine B N hB S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit B S) :=
  biprod.lift ((scalarExtension φ S).map biprod.fst ≫ line φ N hN hA hB S hS)
    ((scalarExtension φ S).map biprod.snd ≫ unit φ S)

/-- Normalized balancing on the coordinate tower's actual right-adjoint input,
transported by the existing coefficient-descent isomorphisms.
Source: blueprint paragraph 2, affine-space composition
(blueprint: lem-pur-vector-trace-scalar-descent). -/
def affineCoefficient (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (scalarExtension φ (affineTraceTower S d)).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ⟶
      (affineTraceRight B N hB S d).obj (ordinaryFiniteUnit B S) :=
  (scalarExtension φ (affineTraceTower S d)).map
      (affineLinearCoefficientDescent A N hA (projectiveLineTraceTransport N hN A hA)
        S hS d).hom ≫
    pullBase φ N hN hA hB (affineTraceProjection S d) hS d ≫
    (affineLinearCoefficientDescent B N hB (projectiveLineTraceTransport N hN B hB)
      S hS d).inv

/-- The actual coordinate-tower counit, on the specified compact-support source.
Source: blueprint paragraph 2, t_{p_d}
(blueprint: lem-pur-vector-trace-scalar-descent). -/
def affineTrace (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ⟶
      ordinaryFiniteUnit A S :=
  (affineLinearCompactComparison N hN A hA S hS d).inv ≫
    affineTraceCounit A N hA (projectiveLineTraceTransport N hN A hA)
      (projectiveLineTraceDatum N hN A hA) S hS d

/-- The specified compactification scalar map followed by the tower's Tate balancing.
Source: blueprint paragraph 2, affine tilde q
(blueprint: lem-pur-vector-trace-scalar-descent). -/
def affine (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (scalarExtension φ S).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).obj
          ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))) ⟶
      (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (affineTraceProjection S d)).obj
        ((affineTraceRight B N hB S d).obj (ordinaryFiniteUnit B S)) :=
  (compactScalarChosenMap φ (affineTraceProjection S d)).app
      ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (affineTraceProjection S d)).map
      (affineCoefficient φ N hN hA hB S hS d)

/-- The specified compact-support comparison for the bundle followed by its actual
pullback/Tate balancing. Geometry instances are furnished by the recorded construction.
Source: blueprint paragraph 2, tilde q_pi
(blueprint: lem-pur-vector-trace-scalar-descent). -/
def vector (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    (scalarExtension φ S).obj (vectorIntegrationSource A N hA S d F) ⟶
      vectorIntegrationSource B N hB S d F :=
  letI := (vectorIntegration_geometry S d F).1
  letI := (vectorIntegration_geometry S d F).2.1
  (compactScalarChosenMap φ (VectorBundleZeroSection.π S d F)).app
      (vectorIntegrationCoefficient A N hA S d F) ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (VectorBundleZeroSection.π S d F)).map
      (pullBase φ N hN hA hB (VectorBundleZeroSection.π S d F) hS d)
```

## New

In `Sheaf.Paper.VectorTraceScalarData`, publicly re-exported by the original module:

```lean
@[irreducible]
def balancing (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    ∀ r : ℕ, (purityScalarSheaf φ T).obj (Scheme.finiteEtaleTateTwist T N A hA r) ≅
      Scheme.finiteEtaleTateTwist T N B hB r :=
  Classical.choose ((finite_tate_scalar_source_normalization φ N hN hA hB T
    (fun x ↦ by
      simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ x trivial).hom)).2.exists)

/-- The degree-one balancing from the uniquely generator-normalized Tate theorem,
shifted using its actual scalar/single comparison. This is l_{T,1}.
Source: blueprint paragraph 2, normalized coefficient identifications
(blueprint: def-pur-vector-trace-scalar-coefficient-data). -/
def line (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    (scalarExtension φ T).obj ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) ⟶
      (ordinaryFiniteLine B N hB T)⟦(2 : ℤ)⟧ :=
  finiteTateScalarLineMap φ N hA hB T 1 (balancing φ N hN hA hB T hT 1)

/-- Multiplication on the constant coefficient complex, with the published single/unit
identifications. Source: blueprint paragraph 2, u_T
(blueprint: def-pur-vector-trace-scalar-coefficient-data). -/
abbrev unit (φ : A →+* B) (T : Scheme.{u}) :
    (scalarExtension φ T).obj (ordinaryFiniteUnit A T) ⟶ ordinaryFiniteUnit B T :=
  purityScalarUnitMap φ T

/-- The tensor powers of shifted balanced lines, starting with multiplication at rank
zero. This is l in the ordered shifted-Tate presentation already used by integration;
no orientation or new Tate object is chosen.
Source: blueprint paragraph 2, l_{T,d}
(blueprint: def-pur-vector-trace-scalar-coefficient-data). -/
def base (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    ∀ d : ℕ, (scalarExtension φ T).obj (affineLinearBaseCoefficient A N hA T d) ⟶
      affineLinearBaseCoefficient B N hB T d
  | 0 => unit φ T
  | d + 1 =>
    (ExceptionalCoefficients.tensorIso φ T).hom.app
      (affineLinearBaseCoefficient A N hA T d, (ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) ≫
    ((ordinaryFiniteTensor B T).map (base φ N hN hA hB T hT d)).app
      ((scalarExtension φ T).obj ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)) ≫
    ((ordinaryFiniteTensor B T).obj (affineLinearBaseCoefficient B N hB T d)).map
      (line φ N hN hA hB T hT)

/-- The normalized scalar map on the pullback of an ordered Tate coefficient. The
inverse scalar/pullback comparison has source Q_X f^* and target f'^* Q_Y.
Source: blueprint paragraph 2, pullback compatibility of l
(blueprint: def-pur-vector-trace-scalar-map-data). -/
def pullBase (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X T : Scheme.{u}} (f : X ⟶ T) (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) :
    (scalarExtension φ X).obj
        ((ordinaryFinitePullback A f).obj (affineLinearBaseCoefficient A N hA T d)) ⟶
      (ordinaryFinitePullback B f).obj (affineLinearBaseCoefficient B N hB T d) :=
  (scalarPullbackIso φ f).inv.app (affineLinearBaseCoefficient A N hA T d) ≫
    (ordinaryFinitePullback B f).map (base φ N hN hA hB T hT d)

/-- The actual proper scalar mate followed by the degree-one normalized balancing.
Source: blueprint paragraph 2, tilde q_p
(blueprint: def-pur-vector-trace-scalar-map-data). -/
def projective (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    (scalarExtension φ S).obj
        ((ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)) ⟶
      (ordinaryFinitePushforward B (ProjectiveLine S ↘ S)).obj
        ((ordinaryFiniteLine B N hB (ProjectiveLine S))⟦(2 : ℤ)⟧) :=
  (scalarMate φ (ProjectiveLine S ↘ S)).app
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
    (ordinaryFinitePushforward B (ProjectiveLine S ↘ S)).map
      (line φ N hN hA hB (ProjectiveLine S) (ordinaryFiniteP1_isUnit N S hS))

/-- The comparison d_S is assembled from its two projections l_{S,1} and u_S.
Source: blueprint paragraph 2, projective-line decomposition
(blueprint: def-pur-vector-trace-scalar-map-data). -/
def sum (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    (scalarExtension φ S).obj
        ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ⟶
      ((ordinaryFiniteLine B N hB S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit B S) :=
  biprod.lift ((scalarExtension φ S).map biprod.fst ≫ line φ N hN hA hB S hS)
    ((scalarExtension φ S).map biprod.snd ≫ unit φ S)

/-- Normalized balancing on the coordinate tower's actual right-adjoint input,
transported by the existing coefficient-descent isomorphisms.
Source: blueprint paragraph 2, affine-space composition
(blueprint: def-pur-vector-trace-scalar-map-data). -/
def affineCoefficient (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (scalarExtension φ (affineTraceTower S d)).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ⟶
      (affineTraceRight B N hB S d).obj (ordinaryFiniteUnit B S) :=
  (scalarExtension φ (affineTraceTower S d)).map
      (affineLinearCoefficientDescent A N hA (projectiveLineTraceTransport N hN A hA)
        S hS d).hom ≫
    pullBase φ N hN hA hB (affineTraceProjection S d) hS d ≫
    (affineLinearCoefficientDescent B N hB (projectiveLineTraceTransport N hN B hB)
      S hS d).inv

/-- The actual coordinate-tower counit, on the specified compact-support source.
Source: blueprint paragraph 2, t_{p_d}
(blueprint: def-pur-vector-trace-scalar-map-data). -/
def affineTrace (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ⟶
      ordinaryFiniteUnit A S :=
  (affineLinearCompactComparison N hN A hA S hS d).inv ≫
    affineTraceCounit A N hA (projectiveLineTraceTransport N hN A hA)
      (projectiveLineTraceDatum N hN A hA) S hS d

/-- The specified compactification scalar map followed by the tower's Tate balancing.
Source: blueprint paragraph 2, affine tilde q
(blueprint: def-pur-vector-trace-scalar-map-data). -/
def affine (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (scalarExtension φ S).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).obj
          ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))) ⟶
      (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (affineTraceProjection S d)).obj
        ((affineTraceRight B N hB S d).obj (ordinaryFiniteUnit B S)) :=
  (compactScalarChosenMap φ (affineTraceProjection S d)).app
      ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (affineTraceProjection S d)).map
      (affineCoefficient φ N hN hA hB S hS d)

/-- The specified compact-support comparison for the bundle followed by its actual
pullback/Tate balancing. Geometry instances are furnished by the recorded construction.
Source: blueprint paragraph 2, tilde q_pi
(blueprint: def-pur-vector-trace-scalar-map-data). -/
def vector (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    (scalarExtension φ S).obj (vectorIntegrationSource A N hA S d F) ⟶
      vectorIntegrationSource B N hB S d F :=
  letI := (vectorIntegration_geometry S d F).1
  letI := (vectorIntegration_geometry S d F).2.1
  (compactScalarChosenMap φ (VectorBundleZeroSection.π S d F)).app
      (vectorIntegrationCoefficient A N hA S d F) ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (VectorBundleZeroSection.π S d F)).map
      (pullBase φ N hN hA hB (VectorBundleZeroSection.π S d F) hS d)
```

The only differences in the displayed blocks are the docstring node identifiers. All eight old
public imports remain public imports of the data module and are re-exported transitively. The
original proof-only imports are reduced to those used by the complete combining proof; the three
new proof lemmas import only the data module. Definitions and their attributes are not modified.

## Users

This conservative table lists all downstream modules, hence includes every textual `--uses`
match (including false positives for short names such as `base`, `sum`, `unit` and `vector`).
Holders are from the shared claim snapshot. None of these modules is adapted; the four direct
importers are checked against the relocated definitions and the original public import surface.
No target statement or definition meaning changes, so semantic target review is not reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedOpenCounitTensorAction | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorMaps | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineLineTensorCounit | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineProjectionReassociation | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineTensorActions | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineTowerTensorCounit | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1TensorAction | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AdicActualSystemsNormalized | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AdicNormalizedPuritySystems | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AdicPuritySourceFiniteness | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AdicPuritySourceNormalization | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AdicPuritySourceTransitionSquare | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AffineCounitScalar | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AffineIntegrationExponentTransition | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AffineOrderedCounitDescentComparison | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AffineOrderedCounitSuccessor | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AffineOrderedCounitZero | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.CentredDiagonalSourcePasting | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ChartCounitScalarTransport | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ChartDiagonalAssemblyData | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ChartDiagonalSourceSquare | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ChartDncNaturality | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ChartDncSquare | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ChartDncVectorFactorData | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ChartDncVectorFactors | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ChartEpsilonPasting | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ChartExceptionalCounitEquation | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ChartExceptionalMateCoherence | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ChartIntegrationAdjoints | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ChartNormalIntegrationSquare | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.CochainLocalizationTensorIso | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.CommonStageSmoothOperationCore | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.CommonStageSmoothOperationShift | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.CompositeProjectionCoefficients | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.CompositionComparisons | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.CompositionIteratedMateExpansion | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.CompositionModelOrientationDefinitions | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.CompositionSingleMatePresentation | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.CondensedIntegralEndpoints | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.CondensedTateIntegralTower | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.CondensedTateIntegralTowerData | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.DiagonalDncAssemblyGlobal | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.DiagonalDncChartNormalization | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.DiagonalOrientationCharts | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralMaps | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldExtensionCompletedStrictLimit | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldExtensionComposition | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldExtensionIntegralComparisons | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldExtensionIntegralCoordinates | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldExtensionIntegralDescent | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldExtensionIntegralModels | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldExtensionLimitEquations | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldExtensionRationalComparisons | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldExtensionRationalDescent | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldExtensionRationalModels | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldExtensionReductionDescent | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldExtensionReductionLimits | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldExtensionStrictLimits | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldExtensionSystemCoordinates | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldExtensionTowers | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldOrientationSystemComparison | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldOrientationSystemComparisonData | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldOrientationSystemCoordinates | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldOrientationSystemFiniteOrientation | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldOrientationSystemHeart | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldOrientationSystemNormalizations | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldOrientationSystemRigidity | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldOrientedExchangeSquares | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldPuritySystemTranspose | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldPuritySystemTransposeBase | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldPuritySystemTransposeCompatibility | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldPurityTransposeArrows | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FieldPurityTransposeLevelWords | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteBundleSectionAdjointScalar | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteCoefficientTensorFactorization | unclaimed in shared snapshot | Direct importer; copied unchanged for compile check, not delivered. |
| Sheaf.Paper.FiniteDiagonalBaseChangeReduction | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteDiagonalDncReduction | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteDiagonalOrientationAssembly | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteDiagonalVectorReduction | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteFirstRootChart | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteGammaEvaluationIsIso | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteGeometricOrientationExchange | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteGeometricPurityCoordinates | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteGeometricPurityFactors | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteGeometricPurityMate | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteGeometricTensorExchange | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteNormalizedOrientationScalar | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteOrientationReduction | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteOrientationScalarPresentation | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FinitePositiveChartFrameExt | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FinitePositiveChartRecursion | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FinitePositiveRootChartPower | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FinitePositiveRootCharts | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteProductReductionComparisons | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FinitePublishedRootChartPower | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FinitePurityCounitSystem | unclaimed in shared snapshot | Direct importer; copied unchanged for compile check, not delivered. |
| Sheaf.Paper.FinitePuritySourceUnitReduction | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteReductionBaseChangeSource | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteReductionExceptionalFiniteModel | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteReductionLineChartScalars | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteReductionLineInputConstructible | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteReductionPositiveLineComparison | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteReductionReassociation | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteReductionShiftedPullbackCube | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteReductionSourceChartIndependence | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteReductionTensorFactors | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteReductionTensorPurity | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteReductionTensorSource | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteReductionThetaFactor | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteRootLinePowerTransition | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteRootTensorPresentation | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteScalarCochainComparisonIso | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteScalarMonoidalRepresentative | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteScalarRepresentativeIso | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteScalarTensorData | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteScalarTensorSource | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteScalarUnitNormalization | unclaimed in shared snapshot | Direct importer; copied unchanged for compile check, not delivered. |
| Sheaf.Paper.FiniteSectionIntegratedScalar | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteSignedTwistProducts | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteSourceChartPowerTransition | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteSourceChartScalarTransition | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteSupportedReductionEquation | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteTateSourceMap | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteTateSourceStructuralCoherence | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteTensorComparisonEquations | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteTensorFixedComparisons | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteTensorLineChartReduction | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteTensorLineDerivedExistence | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteTensorLineDerivedExistenceWitness | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteTensorPresentationReduction | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteTensorProductFrameExt | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteTensorProductMap | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteTensorProductMapIsIso | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteTensorPullbackCompositionReduction | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteTensorPullbackTensorReduction | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteTensorReductionData | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteTensorSemilinearReduction | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteTensorShiftCoherence | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteTensorShiftFirst | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteTensorShiftSecond | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteTensorSignedReduction | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteTensorSymmetryCoherence | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FiniteVectorIntegrationScalar | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.FixedPresentationUniformizerReductions | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.GeneralChartComparisons | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.GeometricSmoothReconstructionSetup | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.IntegralAdjunctionBijection | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.IntegralAdjunctionReconstruction | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.IntegralAdjunctionSourceComparison | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.IntegralCoefficientModelComparison | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.IntegralCompositorLimitRealization | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.IntegralEquivarianceMate | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.IntegralEquivarianceNaturality | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.IntegralGeometricComparisonData | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.IntegralGeometricComparisonRealization | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.IntegralGeometricPurityRealization | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.IntegralGeometricReindexingRealization | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.IntegralGeometricSupportRealization | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.IntegralGeometricTransposeIdentity | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.IntegralOrientationReductionInjectivity | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.IntegralOrientationShiftedSheafModels | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.IntegralOrientedExchangeSquares | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.IntegralPurityComparisonCocycles | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.IntegralPurityCounitReduction | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.IntegralReconstructionComparisonData | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.IntegralReconstructionComparisons | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.IntegralSmoothAdjunctionPresentation | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.IteratedPurityScalarPasting | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.IteratedTateSourceComposite | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ModelAffineIntegrationOrientation | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ModelChartOrientationAssembly | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ModelOrientationChartDescent | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ModelOrientationSourceNaturality | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ModelOrientationTateDetection | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.NormalModelSectionOrientation | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.NormalSectionIntegrationBaseChange | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.NormalSectionIntegrationData | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.NormalSectionIntegrationOrientation | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.NormalizedFieldPurityTrace | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.NormalizedFieldPurityTraceCommonStage | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.NormalizedIntegralTraceData | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.NormalizedSmoothOrientationUnits | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.NormalizedTateTensorTower | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.NormalizedTateTensorTowerCore | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.NormalizedTateTensorTowerProperties | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.NormalizedTateTensorTowerZero | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.OrderedLineLevelBounds | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.OrientationGroundFieldRetagging | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.OrientationScalarPropagation | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.OrientationScalarTowerTransport | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.P1CounitScalar | unclaimed in shared snapshot | Direct importer; copied unchanged for compile check, not delivered. |
| Sheaf.Paper.PoincareDualityConventions | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ProjectionPurityAgreement | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ProjectionTensorIntegration | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.ProjectionUnitPresentationNormalization | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.PulledOrderedLineSingle | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.PurityCompactSupportTransport | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.PurityConjugatesTowerReduction | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.PurityFiniteReductionTransport | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.PurityFiniteTateSourceComparisonCalculus | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.PurityKappaStages | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.PurityPullbackLevelBounds | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.PurityPullbackReductionTransport | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.PurityTateDatum | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.PurityTowerReductionComparisons | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.QuotientInverseOrientation | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.RationalPurityExchangeEndpointData | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.RationalPurityExchangeEndpoints | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.RationalPurityLocalizedFamilyData | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.RationalizationOrientedExchangeSquare | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.RawChartScalarCounitPasting | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.RetaggingCoordinateOrientations | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.SectionDncIntegrationSquare | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.SectionEtaleOpenCancellation | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.SmoothExchangeScalarCompatibility | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.SmoothOrientationCoefficientFamily | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.SmoothOrientationPuritySquares | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.SmoothOrientationStageExchange | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.SmoothOrientedExchangeComparisons | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.SmoothPurityBaseChangeData | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.SmoothPurityBaseChangeFactors | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.SmoothPurityCompositionFactors | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.SmoothPurityTowerGamma | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.SpecifiedIntegralUnitOrientation | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.SpecifiedTowerAdjunctionCharts | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.StrictTateTensorTowerLift | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TateTensorNormalizedSquare | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TateTensorQuotientBalancing | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TowerFactorOrientation | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TowerFactorTensor | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TowerGeometricPurityAssembly | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TowerGeometricPurityData | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TowerGeometricPurityMate | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TowerIsomorphismPullback | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TowerMuEvaluation | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TowerPurityAdjointTransport | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TowerPurityPresentationRetagging | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TowerPurityRealizedData | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TowerPurityRealizedNormalization | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TowerSemilinearPurityFactors | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TowerTateSplitNormalized | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TowerTensorAdjointDomains | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TowerTensorPresentationRetagging | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TowerTraceCanonicalIntegral | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TowerTraceNormalizedPresentations | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TowerTraceOrientationUniqueness | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TowerTracePurityComparison | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TowerTracePurityComparisonData | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TowerTraceScalarCounit | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TransportCondensedStageRealization | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TransportIntegralBaseChangeRealization | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TransportIntegralChartRealization | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TransportIntegralCompositionRealization | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TransportIntegralCounitData | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TransportIntegralCounitRealization | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TransportIntegralStageConstruction | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.UniformTowerTensorClosure | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.VectorIntegrationChartComparison | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.VectorIntegrationChartCoordinates | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.VectorIntegrationChartTranspose | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.VectorIntegrationIdentityAdjunct | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.VectorIntegrationUnitTranspose | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.VectorModelChartDescent | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.WeilEquivarianceOfPurityAndTrace | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Paper.WeilPurityEquivarianceData | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.SecSmoothPurity.NestedAffineChartFormulas | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.SecSmoothPurity.NestedAffineFormulaData | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.SecSmoothPurity.NestedAffineIntegrationRegrouping | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.SecSmoothPurity.NestedAffineNormalizedInputs | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.SecSmoothPurity.NestedAffineOrientation | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.SecSmoothPurity.NestedAffineOrientationCoordinates | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.SecSmoothPurity.ReductionOrientation | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.SixFunctors.AffineDualizingCoefficient | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.SixFunctors.KappaCoefficientCoherence | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.SixFunctors.KappaGeometricComparisons | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.SixFunctors.KappaMixedCoherence | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Targets.PoincareUncurry | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| TargetsCheck | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| WeilConjectures | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| WeilConjectures.SmoothPurity.Defs | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| WeilConjectures.TraceFormula.BorelMoore | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| WeilConjectures.TraceFormula.Dualizing | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |
| WeilConjectures.TraceFormula.LocalTerm | unclaimed in shared snapshot | Unchanged: original module publicly re-exports the identical definitions. |

## Status

landed 20261027T210210-L-1670181 2026-10-27 (merge of deliver/R1/Sheaf.Paper.VectorTraceScalarDescent)
