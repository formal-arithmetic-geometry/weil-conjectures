# DiagonalTowerSystem interface extraction

## Reason

The existence proof needs a shared interface without importing its own theorem module.
The original module publicly re-exports the extracted interface. Names and signatures
of the existing declarations are retained. The cycle predicate is expressed through
`normalizedBoundaryTarget`; `normalizedBoundarySystem_iff_target` proves its equivalence
to the original existential Ext-class form, with the full finite class equation and
both normalization conditions. Finite class equality is expressed as heterogeneous
equality between definitionally identical endpoints.

The named sheaf Abelian structures explicitly use the sectionwise full-subcategory
preadditive structure. The inherited Abelian operations supply the remaining fields;
this avoids costly elaboration through the sheaf equivalence without changing their
mathematical meaning. Local irreducibility attributes keep derived and Cartier
constructions folded during elaboration. Generic boundary-transport definitions use
the same Ext operations as before. No public transparency attribute is exported.

The original source geometry proofs have explicit finite, flat and finite-presentation
witnesses after unused proof imports were removed. The extraction is needed for the
proof-component imports; files and proofs were not split for compilation speed.

Final validation is recorded in report.md. Definition review remains required.

## Old

The following declarations were defined in `Sheaf.Paper.DiagonalTowerSystem`.

```lean
/-- Integral sheaves. Source: blueprint clause 1
(blueprint: det-prop-diagonal-tower-system). -/
abbrev DiagonalAb (W : Scheme.{u}) := Sheaf (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1}

/-- Discrete constant Z_l-module sheaves, not continuous-function coefficient sheaves.
Source: blueprint tower category (blueprint: det-prop-diagonal-tower-system). -/
abbrev DiagonalMod (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :=
  Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ]))

/-- Strict inverse systems. Source: blueprint tower category
(blueprint: det-prop-diagonal-tower-system). -/
abbrev DiagonalSystems (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :=
  ℕᵒᵖ ⥤ DiagonalMod ℓ W

/-- The canonical abelian structure, named once to share all its sheafification
witnesses throughout the strict-system specification. This is the existing Mathlib
structure, with no choice of a replacement category.
Source: blueprint coefficient conventions (blueprint: det-prop-diagonal-tower-system). -/
instance (priority := 2000) diagonalModuleSheafAbelian
    (A : Type (u + 1)) [CommRing A] (W : Scheme.{u}) :
    Abelian (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} A)) := inferInstance

/-- The canonical abelian-sheaf structure, with its witnesses shared by name.
Source: blueprint coefficient conventions (blueprint: det-prop-diagonal-tower-system). -/
instance (priority := 2000) diagonalAbSheafAbelian (W : Scheme.{u}) :
    Abelian (DiagonalAb W) := inferInstance

/-- Ordinary extension from abelian groups to Z_l, before reduction, sheafified
sectionwise. Source: blueprint clause 2 (blueprint: det-prop-diagonal-tower-system). -/
def diagonalScalarExtension (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    DiagonalAb W ⥤ DiagonalMod ℓ W :=
  sheafToPresheaf (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringRight W.ProEtᵒᵖ AddCommGrpCat.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ]))).obj
        ((forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
          ModuleCat.extendScalars (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ]))) ⋙
    presheafToSheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ]))

/-- Forget scalars through the unique integer action.
Source: blueprint clause 2 (blueprint: det-prop-diagonal-tower-system). -/
def diagonalForget (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    DiagonalMod ℓ W ⥤ DiagonalAb W :=
  sheafCompose (Scheme.ProEt.topology W)
    (ModuleCat.restrictScalars (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ])) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1})

/-- The usual insertion-of-one scalar adjunction, lifted to sheaves.
Source: blueprint clause 2 (blueprint: det-prop-diagonal-tower-system). -/
def diagonalScalarAdjunction (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    diagonalScalarExtension ℓ W ⊣ diagonalForget ℓ W :=
  Sheaf.adjunction (Scheme.ProEt.topology W)
    ((forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).asEquivalence.symm.toAdjunction.comp
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
        (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ]))))

/-- Forgetting constant scalars is exact.
Source: blueprint clause 2 (blueprint: det-prop-diagonal-tower-system).
Proof: kernels are sectionwise; cokernels are sheafifications of the same additive
quotients. The unique integer action changes neither construction. -/
theorem diagonalForget_exact (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteLimits (diagonalForget ℓ W) ∧
      PreservesFiniteColimits (diagonalForget ℓ W) := by
  constructor
  · have := (diagonalScalarAdjunction ℓ W).rightAdjoint_preservesLimits
    infer_instance
  · let G := ModuleCat.restrictScalars
        (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ])) ⋙
        forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
    have : (ModuleCat.restrictScalars.{u + 1}
        (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ]))).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, 0, u + 1}
        (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ]))).isLeftAdjoint
    have : G.IsLeftAdjoint := inferInstance
    let J := Scheme.ProEt.topology W
    let e : Sheaf.composeAndSheafify J G ≅ sheafCompose J G :=
      Functor.isoWhiskerLeft (sheafCompose J G)
        (sheafificationNatIso J AddCommGrpCat.{u + 1}).symm ≪≫
        Functor.rightUnitor (sheafCompose J G)
    have : (Sheaf.composeAndSheafify J G).IsLeftAdjoint := inferInstance
    have : (sheafCompose J G).IsLeftAdjoint := Functor.isLeftAdjoint_of_iso e
    exact inferInstanceAs (PreservesFiniteColimits (sheafCompose J G))

/-- Exact scalar forgetting, limits. Source: blueprint clause 2
(blueprint: det-prop-diagonal-tower-system). -/
instance diagonalForgetLimits (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteLimits (diagonalForget ℓ W) := (diagonalForget_exact ℓ W).1

/-- Exact scalar forgetting, colimits. Source: blueprint clause 2
(blueprint: det-prop-diagonal-tower-system). -/
instance diagonalForgetColimits (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteColimits (diagonalForget ℓ W) := (diagonalForget_exact ℓ W).2

/-- Additivity of scalar forgetting. Source: blueprint clause 2
(blueprint: det-prop-diagonal-tower-system).
Proof: the underlying section maps add pointwise and forgetting retains them. -/
theorem diagonalForget_additive (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    (diagonalForget ℓ W).Additive := by
  dsimp only [diagonalForget, sheafCompose]
  infer_instance

attribute [instance] diagonalForget_additive

/-- A strict ordinary reduction functor, characterized by its quotient universal
properties and quotient transitions. With L=extension to Z_l this is tensor with the
whole coefficient system; with L=identity this is its integral version.
Source: blueprint clause 2 (blueprint: det-prop-diagonal-tower-system). -/
structure DiagonalReductionPresentation
    (ℓ : ℕ) {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] (L : A ⥤ B) where
  /-- One functor into the strict system category. -/
  E : A ⥤ (ℕᵒᵖ ⥤ B)
  /-- Termwise tensor is additive. -/
  [additive : E.Additive]
  /-- Quotient of extension by the positive prime power. -/
  π : ∀ n : ℕ, L ⟶ E ⋙ (evaluation ℕᵒᵖ B).obj (op n)
  /-- Its kernel relation. -/
  zero : ∀ (n : ℕ) (M : A),
    (ℓ ^ (n + 1) • 𝟙 (L.obj M)) ≫ (π n).app M = 0
  /-- The quotient is a cokernel, fixing its scalar action and maps. -/
  quotient : ∀ (n : ℕ) (M : A),
    IsColimit (CokernelCofork.ofπ ((π n).app M) (zero n M))
  /-- The transitions are the coefficient quotient maps, not independent level maps. -/
  transition : ∀ (n : ℕ) (M : A),
    (π (n + 1)).app M ≫ (E.obj M).map (homOfLE (Nat.le_succ n)).op = (π n).app M

attribute [instance] DiagonalReductionPresentation.additive

/-- The everywhere-defined left derived functor of a strict reduction presentation.
The universal counit and pointwise condition retain functoriality on all unbounded
complexes. Source: blueprint clause 2 (blueprint: det-prop-diagonal-tower-system). -/
structure DiagonalDerivedReduction
    (ℓ : ℕ) {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] (L : A ⥤ B)
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wS} (ℕᵒᵖ ⥤ B)] where
  /-- The ordinary simultaneous reduction. -/
  ordinary : DiagonalReductionPresentation ℓ L
  /-- Its left derived functor, valued in the derived category of strict systems. -/
  T : DerivedCategory A ⥤ DerivedCategory (ℕᵒᵖ ⥤ B)
  /-- Universal comparison with termwise scalar tensor. -/
  ε : DerivedCategory.Q ⋙ T ⟶ ordinary.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  /-- The left derived universal property determines T. -/
  universal : T.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ))
  /-- It exists pointwise at every complex. -/
  pointwise :
    (ordinary.E.mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q).HasPointwiseLeftDerivedFunctor (HomologicalComplex.quasiIso A (.up ℤ))
  /-- Exactness, including its shift comparison. -/
  triangulated : ∃ (_ : T.CommShift ℤ), T.IsTriangulated

/-- The source identification is the universal derived counit on a degree-zero
flat supported constant, with the standard single-complex comparisons.
Source: blueprint clause 3 (blueprint: det-prop-diagonal-tower-system). -/
def diagonalDerivedSingleCounit
    (ℓ : ℕ) {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] (L : A ⥤ B)
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wS} (ℕᵒᵖ ⥤ B)]
    (D : DiagonalDerivedReduction ℓ L) (M : A) :
    D.T.obj ((DerivedCategory.singleFunctor A 0).obj M) ⟶
      (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj (D.ordinary.E.obj M) :=
  D.T.map ((DerivedCategory.singleFunctorIsoCompQ A 0).hom.app M) ≫
    D.ε.app ((HomologicalComplex.single A (.up ℤ) 0).obj M) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex D.ordinary.E (.up ℤ) 0).hom.app M) ≫
    (DerivedCategory.singleFunctorIsoCompQ (ℕᵒᵖ ⥤ B) 0).inv.app (D.ordinary.E.obj M)

/-- The positive-exponent finite coefficient ring, lifted to the sheaf universe.
Source: blueprint clauses 3--4 (blueprint: det-prop-diagonal-tower-system). -/
abbrev diagonalResidue (ℓ n : ℕ) := cartierResidueRing.{u} ℓ (n + 1)

/-- The coefficient projection from Z_l to the lifted finite ring.
Source: blueprint clauses 2--4 (blueprint: det-prop-diagonal-tower-system). -/
def diagonalResidueProjection (ℓ n : ℕ) [Fact ℓ.Prime] :
    ULift.{u + 1} ℤ_[ℓ] →+* diagonalResidue.{u} ℓ n :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((PadicInt.toZModPow (n + 1)).comp ULift.ringEquiv.toRingHom)

/-- A finite-coefficient module, read as a Z_l-module through the specified projection.
Source: blueprint clause 4 (blueprint: det-prop-diagonal-tower-system). -/
def diagonalFiniteToPadic (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)) ⥤
      DiagonalMod ℓ W :=
  sheafCompose (Scheme.ProEt.topology W)
    (ModuleCat.restrictScalars (diagonalResidueProjection.{u} ℓ n))

/-- Finite coefficient restriction is exact and additive.
Source: blueprint clause 4 (blueprint: det-prop-diagonal-tower-system).
Proof: the underlying abelian kernels and sheafified cokernels are unchanged;
restriction retains every additive section map. -/
theorem diagonalFiniteToPadic_exact (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteLimits (diagonalFiniteToPadic ℓ n W) ∧
    PreservesFiniteColimits (diagonalFiniteToPadic ℓ n W) ∧
    (diagonalFiniteToPadic ℓ n W).Additive := by
  constructor
  · have := (Sheaf.adjunction (Scheme.ProEt.topology W)
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
        (diagonalResidueProjection.{u} ℓ n))).rightAdjoint_preservesLimits
    exact inferInstanceAs (PreservesFiniteLimits
      (sheafCompose (Scheme.ProEt.topology W)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          (diagonalResidueProjection.{u} ℓ n))))
  constructor
  · let q := diagonalResidueProjection.{u} ℓ n
    have hadj := ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} q
    have : PreservesLimitsOfSize.{u, u + 1}
        (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} q) :=
      hadj.rightAdjoint_preservesLimits
    have : (Scheme.ProEt.topology W).HasSheafCompose
        (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} q) :=
      hasSheafCompose_of_preservesLimitsOfSize _
    have := (Sheaf.adjunction (Scheme.ProEt.topology W) hadj).isLeftAdjoint
    let J := Scheme.ProEt.topology W
    let G := ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q
    let e : Sheaf.composeAndSheafify J G ≅ sheafCompose J G :=
      Functor.isoWhiskerLeft (sheafCompose J G)
        (sheafificationNatIso J (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ]))).symm ≪≫
        Functor.rightUnitor (sheafCompose J G)
    exact preservesFiniteColimits_of_natIso e
  · dsimp only [diagonalFiniteToPadic, sheafCompose]
    infer_instance

/-- Exact restriction, limits. Source: blueprint clause 4
(blueprint: det-prop-diagonal-tower-system). -/
instance diagonalFiniteToPadicLimits (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteLimits (diagonalFiniteToPadic ℓ n W) :=
  (diagonalFiniteToPadic_exact ℓ n W).1

/-- Exact restriction, colimits. Source: blueprint clause 4
(blueprint: det-prop-diagonal-tower-system). -/
instance diagonalFiniteToPadicColimits (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteColimits (diagonalFiniteToPadic ℓ n W) :=
  (diagonalFiniteToPadic_exact ℓ n W).2.1

/-- Additive restriction. Source: blueprint clause 4
(blueprint: det-prop-diagonal-tower-system). -/
instance diagonalFiniteToPadicAdditive (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    (diagonalFiniteToPadic ℓ n W).Additive :=
  (diagonalFiniteToPadic_exact ℓ n W).2.2

/-- The product of two projective lines. Source: blueprint opening
(blueprint: det-prop-diagonal-tower-system). -/
abbrev diagonalSurface (Y : Scheme.{u}) :=
  pullback (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)

/-- The diagonal. Source: blueprint opening
(blueprint: det-prop-diagonal-tower-system). -/
abbrev diagonalImmersion (Y : Scheme.{u}) : ProjectiveLine Y ⟶ diagonalSurface Y :=
  pullback.diagonal (ProjectiveLine Y ↘ Y)

/-- The diagonal is Cartier over every base, including the empty base.
Source: blueprint proof step 1 (blueprint: det-prop-diagonal-tower-system).
Proof: the first projection of the surface is smooth of relative dimension one,
as a base change of the projective line. Its composite with the diagonal is the
identity. The closed subscheme defined by the kernel of the diagonal is isomorphic
to the diagonal, so its projection is an isomorphism, hence finite, flat and locally
of finite presentation. The relative Cartier criterion gives the invertible ideal. -/
theorem diagonalImmersion_cartier (Y : Scheme.{u}) :
    (diagonalImmersion Y).ker.IsInvertible := by
  let d := diagonalImmersion Y
  let p := pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)
  let j := d.ker.subschemeι
  have hker : d.ker = j.ker := by simp [j]
  let e := IsClosedImmersion.lift d j hker.le
  have : IsIso e := IsClosedImmersion.isIso_lift d j hker
  have he : e ≫ d = j := IsClosedImmersion.lift_fac d j hker.le
  have hp : j ≫ p = e := by
    rw [← he, Category.assoc]
    simp [d, p, diagonalImmersion]
  have : IsIso (j ≫ p) := hp.symm ▸ inferInstance
  exact Scheme.IdealSheafData.isInvertible_of_isFinite_of_flat p
    (J := d.ker) inferInstance inferInstance inferInstance

/-- Invertibility pulls from the base to the diagonal surface and all powers.
Source: blueprint standing hypothesis (blueprint: det-prop-diagonal-tower-system).
Proof: apply the ring map of global sections for W→Y to the given unit, then take
its positive power. This also applies to the zero ring of the empty scheme. -/
theorem diagonalSurface_power_unit (ℓ : ℕ) (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤))) (n : ℕ) :
    IsUnit ((ℓ ^ (n + 1) : ℕ) : Γ(diagonalSurface Y, ⊤)) := by
  simpa using (hY.map
    ((pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) ≫
      (ProjectiveLine Y ↘ Y)).appTop.hom).pow (n + 1)

/-- The supported integral constant on the pro-etale site.
Source: blueprint clause 1 (blueprint: det-prop-diagonal-tower-system). -/
abbrev diagonalIntegralSource (Y : Scheme.{u}) :=
  (lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion Y)).obj
    ((constantSheaf (Scheme.ProEt.topology (ProjectiveLine Y)) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

/-- Units mean exact comparison pullback of etale units.
Source: blueprint clause 1 (blueprint: det-prop-diagonal-tower-system). -/
abbrev diagonalComparisonUnits (Y : Scheme.{u}) :=
  (comparisonUpperStar AddCommGrpCat.{u + 1} (diagonalSurface Y)).obj
    (diagonalSurface Y).gmSheaf

/-- The positive roof boundary: Ext uses the negative cone projection, so negate it.
This is the roof with [G_m→M] in degrees -1,0, quotient on the left and positive
projection on the right. The pole extension sends t inverse to +1.
Source: blueprint clause 1 and proof steps 1--2
(blueprint: det-prop-diagonal-tower-system). -/
def diagonalIntegralBoundary (Y : Scheme.{u}) :
    Ext (diagonalIntegralSource Y) (diagonalComparisonUnits Y) 1 :=
  -((Ext.mk₀ (cartierIntegralSourceIso (diagonalImmersion Y)).inv).comp
    ((Etale.cartierPoleBoundary (diagonalImmersion Y) (diagonalImmersion_cartier Y)).mapExactFunctor
       (comparisonUpperStar AddCommGrpCat.{u + 1} (diagonalSurface Y)))
    (zero_add 1))

/-- The integral derived-completion formula, with both inverse limits total right
derived functors on strict systems. The integral reduction is independently fixed by
the cokernels of l^(n+1) on the identity functor. Thus its composite with integral
Rlim is exactly Rlim_n(K tensor^L Z/l^(n+1)). The displayed natural isomorphism
retains the comparison after forgetting the constant Z_l action. In addition the
output is right orthogonal to every complex on which l is invertible, the intrinsic
derived l-completeness criterion. The natural unit is universal for maps to all
such complete complexes, so this asserts derived completion, not just a limit formula.
Source: blueprint clause 2 and Stacks 099M, 091S and 091Z
(blueprint: det-prop-diagonal-tower-system). -/
def DiagonalCompletionSpec (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W)) : Prop :=
  ∃ (I : DiagonalDerivedReduction ℓ (𝟭 (DiagonalAb W)))
    (RF : DerivedCategory (DiagonalSystems ℓ W) ⥤ DerivedCategory (DiagonalMod ℓ W))
    (η : (lim : DiagonalSystems ℓ W ⥤ DiagonalMod ℓ W).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (RZ : DerivedCategory (ℕᵒᵖ ⥤ DiagonalAb W) ⥤ DerivedCategory (DiagonalAb W))
    (ηZ : (lim : (ℕᵒᵖ ⥤ DiagonalAb W) ⥤ DiagonalAb W).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RZ),
    RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso (DiagonalSystems ℓ W) (.up ℤ)) ∧
    RZ.IsRightDerivedFunctor ηZ
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ DiagonalAb W) (.up ℤ)) ∧
    Nonempty (D.T ⋙ RF ⋙ (diagonalForget ℓ W).mapDerivedCategory ≅ I.T ⋙ RZ) ∧
    ∃ unit : 𝟭 (DerivedCategory (DiagonalAb W)) ⟶
        D.T ⋙ RF ⋙ (diagonalForget ℓ W).mapDerivedCategory,
      (∀ (K P : DerivedCategory (DiagonalAb W)), IsIso (ℓ • 𝟙 P) →
        Subsingleton (P ⟶ (D.T ⋙ RF ⋙ (diagonalForget ℓ W).mapDerivedCategory).obj K)) ∧
      ∀ (K N : DerivedCategory (DiagonalAb W)),
        (∀ P : DerivedCategory (DiagonalAb W), IsIso (ℓ • 𝟙 P) → Subsingleton (P ⟶ N)) →
        Function.Bijective (fun f :
          (D.T ⋙ RF ⋙ (diagonalForget ℓ W).mapDerivedCategory).obj K ⟶ N ↦
            unit.app K ≫ f)

/-- The levelwise finite-source comparison preserves the quotient unit, not an
arbitrary automorphism of the supported constant.
Source: blueprint clauses 3--4 (blueprint: det-prop-diagonal-tower-system). -/
def DiagonalSourceNormalization (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (D : DiagonalReductionPresentation ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (n : ℕ)
    (s : (D.E.obj (diagonalIntegralSource Y)).obj (op n) ≅
      (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
        ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)) (diagonalImmersion Y)).obj
          (geoCartierConstant (diagonalResidue.{u} ℓ n) (ProjectiveLine Y)))) : Prop :=
  HEq
    ((diagonalScalarAdjunction ℓ (diagonalSurface Y)).unit.app (diagonalIntegralSource Y) ≫
      (diagonalForget ℓ (diagonalSurface Y)).map ((D.π n).app (diagonalIntegralSource Y) ≫
        s.hom))
    (cartierProIntegralGenerator (diagonalResidue.{u} ℓ n) (diagonalImmersion Y))

/-- A single arrow in D(strict systems), its prescribed source and target, and its
finite cycle-class identifications. Ext^2 is used only as the standard homEquiv
presentation of a morphism from a degree-zero system to a system shifted by two.
Source: blueprint clauses 3--4 (blueprint: det-prop-diagonal-tower-system). -/
def DiagonalCycleSystemSpec (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y))) : Prop :=
  ∃ (H : DiagonalSystems ℓ (diagonalSurface Y))
    (roots : H ⋙ diagonalForget ℓ (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) ℓ (Fact.out : ℓ.Prime))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (c : Ext (D.ordinary.E.obj (diagonalIntegralSource Y)) H 2),
    a.hom = diagonalDerivedSingleCounit ℓ
      (diagonalScalarExtension ℓ (diagonalSurface Y)) D (diagonalIntegralSource Y) ∧
    c.hom = a.inv ≫ D.T.map (diagonalIntegralBoundary Y).hom ≫ b.hom ∧
    ∀ n : ℕ,
      ∃ (s : (D.ordinary.E.obj (diagonalIntegralSource Y)).obj (op n) ≅
          (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
            ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n))
              (diagonalImmersion Y)).obj
                (geoCartierConstant (diagonalResidue.{u} ℓ n) (ProjectiveLine Y))))
        (t : H.obj (op n) ≅ (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
          (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
            (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y))),
        DiagonalSourceNormalization ℓ Y D.ordinary n s ∧
        HEq ((diagonalForget ℓ (diagonalSurface Y)).map t.hom)
          (roots.hom.app (op n) ≫
            cartierProRootMap (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
              (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y)
              (pow_pos (Fact.out : ℓ.Prime).pos _) (diagonalSurface_power_unit ℓ Y hY n)) ∧
        (Ext.mk₀ s.inv).comp
          ((c.mapExactFunctor ((evaluation ℕᵒᵖ (DiagonalMod ℓ (diagonalSurface Y))).obj
            (op n))).comp (Ext.mk₀ t.hom) (add_zero 2)) (zero_add 2) =
          (cartierResidueReducedPro ℓ (Fact.out : ℓ.Prime) (n + 1) (diagonalImmersion Y)
            (diagonalImmersion_cartier Y) (diagonalSurface_power_unit ℓ Y hY n)).mapExactFunctor
               (diagonalFiniteToPadic ℓ n (diagonalSurface Y))
```

## New

The complete extracted interface, including the equivalent cycle predicate:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.AlgebraicGeometry.CartierReductionSiteComparison
public import Sheaf.Paper.ProEtaleTateTwists
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Adjunction

import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth

/-!
# The diagonal class in the derived category of strict torsion towers

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-system.md (blueprint: det-prop-diagonal-tower-system).
The index n denotes exponent n+1. Fixed-scalar module sheaves present modules over
constant ring sheaves; the underlying integer category is abelian sheaves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u uA uB vA vB wA wS w
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- Integral sheaves. Source: blueprint clause 1
(blueprint: det-prop-diagonal-tower-system). -/
abbrev DiagonalAb (W : Scheme.{u}) := Sheaf (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1}

/-- Discrete constant Z_l-module sheaves, not continuous-function coefficient sheaves.
Source: blueprint tower category (blueprint: det-prop-diagonal-tower-system). -/
abbrev DiagonalMod (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :=
  Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ]))

/-- Strict inverse systems. Source: blueprint tower category
(blueprint: det-prop-diagonal-tower-system). -/
abbrev DiagonalSystems (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :=
  ℕᵒᵖ ⥤ DiagonalMod ℓ W

/-- The canonical abelian structure, named once to share all its sheafification
witnesses throughout the strict-system specification. This is the existing Mathlib
structure, with no choice of a replacement category.
Source: blueprint coefficient conventions (blueprint: det-prop-diagonal-tower-system). -/
instance (priority := 2000) diagonalModuleSheafAbelian
    (A : Type (u + 1)) [CommRing A] (W : Scheme.{u}) :
    Abelian (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} A)) :=
  { (inferInstance : Abelian (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} A))) with
    toPreadditive := Preadditive.fullSubcategory _ }

/-- The canonical abelian-sheaf structure, with its witnesses shared by name.
Source: blueprint coefficient conventions (blueprint: det-prop-diagonal-tower-system). -/
instance (priority := 2000) diagonalAbSheafAbelian (W : Scheme.{u}) :
    Abelian (DiagonalAb W) :=
  { (inferInstance : Abelian (DiagonalAb W)) with
    toPreadditive := Preadditive.fullSubcategory _ }

/-- Ordinary extension from abelian groups to Z_l, before reduction, sheafified
sectionwise. Source: blueprint clause 2 (blueprint: det-prop-diagonal-tower-system). -/
def diagonalScalarExtension (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    DiagonalAb W ⥤ DiagonalMod ℓ W :=
  sheafToPresheaf (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringRight W.ProEtᵒᵖ AddCommGrpCat.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ]))).obj
        ((forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
          ModuleCat.extendScalars (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ]))) ⋙
    presheafToSheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ]))

/-- Forget scalars through the unique integer action.
Source: blueprint clause 2 (blueprint: det-prop-diagonal-tower-system). -/
def diagonalForget (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    DiagonalMod ℓ W ⥤ DiagonalAb W :=
  sheafCompose (Scheme.ProEt.topology W)
    (ModuleCat.restrictScalars (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ])) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1})

/-- The usual insertion-of-one scalar adjunction, lifted to sheaves.
Source: blueprint clause 2 (blueprint: det-prop-diagonal-tower-system). -/
def diagonalScalarAdjunction (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    diagonalScalarExtension ℓ W ⊣ diagonalForget ℓ W :=
  Sheaf.adjunction (Scheme.ProEt.topology W)
    ((forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).asEquivalence.symm.toAdjunction.comp
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
        (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ]))))

/-- Forgetting constant scalars is exact.
Source: blueprint clause 2 (blueprint: det-prop-diagonal-tower-system).
Proof: kernels are sectionwise; cokernels are sheafifications of the same additive
quotients. The unique integer action changes neither construction. -/
theorem diagonalForget_exact (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteLimits (diagonalForget ℓ W) ∧
      PreservesFiniteColimits (diagonalForget ℓ W) := by
  constructor
  · have := (diagonalScalarAdjunction ℓ W).rightAdjoint_preservesLimits
    infer_instance
  · let G := ModuleCat.restrictScalars
        (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ])) ⋙
        forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
    have : (ModuleCat.restrictScalars.{u + 1}
        (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ]))).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, 0, u + 1}
        (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ]))).isLeftAdjoint
    have : G.IsLeftAdjoint := inferInstance
    let J := Scheme.ProEt.topology W
    let e : Sheaf.composeAndSheafify J G ≅ sheafCompose J G :=
      Functor.isoWhiskerLeft (sheafCompose J G)
        (sheafificationNatIso J AddCommGrpCat.{u + 1}).symm ≪≫
        Functor.rightUnitor (sheafCompose J G)
    have : (Sheaf.composeAndSheafify J G).IsLeftAdjoint := inferInstance
    have : (sheafCompose J G).IsLeftAdjoint := Functor.isLeftAdjoint_of_iso e
    exact inferInstanceAs (PreservesFiniteColimits (sheafCompose J G))

/-- Exact scalar forgetting, limits. Source: blueprint clause 2
(blueprint: det-prop-diagonal-tower-system). -/
instance diagonalForgetLimits (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteLimits (diagonalForget ℓ W) := (diagonalForget_exact ℓ W).1

/-- Exact scalar forgetting, colimits. Source: blueprint clause 2
(blueprint: det-prop-diagonal-tower-system). -/
instance diagonalForgetColimits (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteColimits (diagonalForget ℓ W) := (diagonalForget_exact ℓ W).2

/-- Additivity of scalar forgetting. Source: blueprint clause 2
(blueprint: det-prop-diagonal-tower-system).
Proof: the underlying section maps add pointwise and forgetting retains them. -/
theorem diagonalForget_additive (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    (diagonalForget ℓ W).Additive := by
  dsimp only [diagonalForget, sheafCompose]
  infer_instance

attribute [instance] diagonalForget_additive

/-- A strict ordinary reduction functor, characterized by its quotient universal
properties and quotient transitions. With L=extension to Z_l this is tensor with the
whole coefficient system; with L=identity this is its integral version.
Source: blueprint clause 2 (blueprint: det-prop-diagonal-tower-system). -/
structure DiagonalReductionPresentation
    (ℓ : ℕ) {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] (L : A ⥤ B) where
  /-- One functor into the strict system category. -/
  E : A ⥤ (ℕᵒᵖ ⥤ B)
  /-- Termwise tensor is additive. -/
  [additive : E.Additive]
  /-- Quotient of extension by the positive prime power. -/
  π : ∀ n : ℕ, L ⟶ E ⋙ (evaluation ℕᵒᵖ B).obj (op n)
  /-- Its kernel relation. -/
  zero : ∀ (n : ℕ) (M : A),
    (ℓ ^ (n + 1) • 𝟙 (L.obj M)) ≫ (π n).app M = 0
  /-- The quotient is a cokernel, fixing its scalar action and maps. -/
  quotient : ∀ (n : ℕ) (M : A),
    IsColimit (CokernelCofork.ofπ ((π n).app M) (zero n M))
  /-- The transitions are the coefficient quotient maps, not independent level maps. -/
  transition : ∀ (n : ℕ) (M : A),
    (π (n + 1)).app M ≫ (E.obj M).map (homOfLE (Nat.le_succ n)).op = (π n).app M

attribute [instance] DiagonalReductionPresentation.additive

/-- The everywhere-defined left derived functor of a strict reduction presentation.
The universal counit and pointwise condition retain functoriality on all unbounded
complexes. Source: blueprint clause 2 (blueprint: det-prop-diagonal-tower-system). -/
structure DiagonalDerivedReduction
    (ℓ : ℕ) {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] (L : A ⥤ B)
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wS} (ℕᵒᵖ ⥤ B)] where
  /-- The ordinary simultaneous reduction. -/
  ordinary : DiagonalReductionPresentation ℓ L
  /-- Its left derived functor, valued in the derived category of strict systems. -/
  T : DerivedCategory A ⥤ DerivedCategory (ℕᵒᵖ ⥤ B)
  /-- Universal comparison with termwise scalar tensor. -/
  ε : DerivedCategory.Q ⋙ T ⟶ ordinary.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  /-- The left derived universal property determines T. -/
  universal : T.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ))
  /-- It exists pointwise at every complex. -/
  pointwise :
    (ordinary.E.mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q).HasPointwiseLeftDerivedFunctor (HomologicalComplex.quasiIso A (.up ℤ))
  /-- Exactness, including its shift comparison. -/
  triangulated : ∃ (_ : T.CommShift ℤ), T.IsTriangulated

/-- The source identification is the universal derived counit on a degree-zero
flat supported constant, with the standard single-complex comparisons.
Source: blueprint clause 3 (blueprint: det-prop-diagonal-tower-system). -/
def diagonalDerivedSingleCounit
    (ℓ : ℕ) {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] (L : A ⥤ B)
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wS} (ℕᵒᵖ ⥤ B)]
    (D : DiagonalDerivedReduction ℓ L) (M : A) :
    D.T.obj ((DerivedCategory.singleFunctor A 0).obj M) ⟶
      (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj (D.ordinary.E.obj M) :=
  D.T.map ((DerivedCategory.singleFunctorIsoCompQ A 0).hom.app M) ≫
    D.ε.app ((HomologicalComplex.single A (.up ℤ) 0).obj M) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex D.ordinary.E (.up ℤ) 0).hom.app M) ≫
    (DerivedCategory.singleFunctorIsoCompQ (ℕᵒᵖ ⥤ B) 0).inv.app (D.ordinary.E.obj M)

/-- The positive-exponent finite coefficient ring, lifted to the sheaf universe.
Source: blueprint clauses 3--4 (blueprint: det-prop-diagonal-tower-system). -/
abbrev diagonalResidue (ℓ n : ℕ) := cartierResidueRing.{u} ℓ (n + 1)

/-- The coefficient projection from Z_l to the lifted finite ring.
Source: blueprint clauses 2--4 (blueprint: det-prop-diagonal-tower-system). -/
def diagonalResidueProjection (ℓ n : ℕ) [Fact ℓ.Prime] :
    ULift.{u + 1} ℤ_[ℓ] →+* diagonalResidue.{u} ℓ n :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((PadicInt.toZModPow (n + 1)).comp ULift.ringEquiv.toRingHom)

/-- A finite-coefficient module, read as a Z_l-module through the specified projection.
Source: blueprint clause 4 (blueprint: det-prop-diagonal-tower-system). -/
def diagonalFiniteToPadic (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)) ⥤
      DiagonalMod ℓ W :=
  sheafCompose (Scheme.ProEt.topology W)
    (ModuleCat.restrictScalars (diagonalResidueProjection.{u} ℓ n))

/-- Finite coefficient restriction is exact and additive.
Source: blueprint clause 4 (blueprint: det-prop-diagonal-tower-system).
Proof: the underlying abelian kernels and sheafified cokernels are unchanged;
restriction retains every additive section map. -/
theorem diagonalFiniteToPadic_exact (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteLimits (diagonalFiniteToPadic ℓ n W) ∧
    PreservesFiniteColimits (diagonalFiniteToPadic ℓ n W) ∧
    (diagonalFiniteToPadic ℓ n W).Additive := by
  constructor
  · have := (Sheaf.adjunction (Scheme.ProEt.topology W)
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
        (diagonalResidueProjection.{u} ℓ n))).rightAdjoint_preservesLimits
    exact inferInstanceAs (PreservesFiniteLimits
      (sheafCompose (Scheme.ProEt.topology W)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          (diagonalResidueProjection.{u} ℓ n))))
  constructor
  · let q := diagonalResidueProjection.{u} ℓ n
    have hadj := ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} q
    have : PreservesLimitsOfSize.{u, u + 1}
        (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} q) :=
      hadj.rightAdjoint_preservesLimits
    have : (Scheme.ProEt.topology W).HasSheafCompose
        (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} q) :=
      hasSheafCompose_of_preservesLimitsOfSize _
    have := (Sheaf.adjunction (Scheme.ProEt.topology W) hadj).isLeftAdjoint
    let J := Scheme.ProEt.topology W
    let G := ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q
    let e : Sheaf.composeAndSheafify J G ≅ sheafCompose J G :=
      Functor.isoWhiskerLeft (sheafCompose J G)
        (sheafificationNatIso J (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ]))).symm ≪≫
        Functor.rightUnitor (sheafCompose J G)
    exact preservesFiniteColimits_of_natIso e
  · dsimp only [diagonalFiniteToPadic, sheafCompose]
    infer_instance

/-- Exact restriction, limits. Source: blueprint clause 4
(blueprint: det-prop-diagonal-tower-system). -/
instance diagonalFiniteToPadicLimits (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteLimits (diagonalFiniteToPadic ℓ n W) :=
  (diagonalFiniteToPadic_exact ℓ n W).1

/-- Exact restriction, colimits. Source: blueprint clause 4
(blueprint: det-prop-diagonal-tower-system). -/
instance diagonalFiniteToPadicColimits (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteColimits (diagonalFiniteToPadic ℓ n W) :=
  (diagonalFiniteToPadic_exact ℓ n W).2.1

/-- Additive restriction. Source: blueprint clause 4
(blueprint: det-prop-diagonal-tower-system). -/
instance diagonalFiniteToPadicAdditive (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    (diagonalFiniteToPadic ℓ n W).Additive :=
  (diagonalFiniteToPadic_exact ℓ n W).2.2

/-- The product of two projective lines. Source: blueprint opening
(blueprint: det-prop-diagonal-tower-system). -/
abbrev diagonalSurface (Y : Scheme.{u}) :=
  pullback (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)

/-- The diagonal. Source: blueprint opening
(blueprint: det-prop-diagonal-tower-system). -/
abbrev diagonalImmersion (Y : Scheme.{u}) : ProjectiveLine Y ⟶ diagonalSurface Y :=
  pullback.diagonal (ProjectiveLine Y ↘ Y)

/-- The diagonal of the separated projective line is closed.
Source: blueprint step 1 (blueprint: def-sfb-diagonal-system-interface). -/
instance diagonalImmersionClosed (Y : Scheme.{u}) :
    IsClosedImmersion (diagonalImmersion Y) := by
  change IsClosedImmersion (pullback.diagonal (ProjectiveLine Y ↘ Y))
  infer_instance

/-- The diagonal is Cartier over every base, including the empty base.
Source: blueprint proof step 1 (blueprint: det-prop-diagonal-tower-system).
Proof: the first projection of the surface is smooth of relative dimension one,
as a base change of the projective line. Its composite with the diagonal is the
identity. The closed subscheme defined by the kernel of the diagonal is isomorphic
to the diagonal, so its projection is an isomorphism, hence finite, flat and locally
of finite presentation. The relative Cartier criterion gives the invertible ideal. -/
theorem diagonalImmersion_cartier (Y : Scheme.{u}) :
    (diagonalImmersion Y).ker.IsInvertible := by
  let d := diagonalImmersion Y
  let p := pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)
  have : IsClosedImmersion d := diagonalImmersionClosed Y
  have : SmoothOfRelativeDimension 1 p :=
    smoothOfRelativeDimension_pullback_fst 1 _ _
  let j := d.ker.subschemeι
  have hker : d.ker = j.ker := by simp [j]
  let e := IsClosedImmersion.lift d j hker.le
  have : IsIso e := IsClosedImmersion.isIso_lift d j hker
  have he : e ≫ d = j := IsClosedImmersion.lift_fac d j hker.le
  have hp : j ≫ p = e := by
    rw [← he, Category.assoc]
    simp [d, p, diagonalImmersion]
  have : IsIso (j ≫ p) := hp.symm ▸ inferInstance
  exact Scheme.IdealSheafData.isInvertible_of_isFinite_of_flat p
    (J := d.ker)
      (by change IsFinite (j ≫ p); rw [hp]; exact MorphismProperty.of_isIso @IsFinite e)
      (by change Flat (j ≫ p); rw [hp]; exact MorphismProperty.of_isIso @Flat e)
      (by change LocallyOfFinitePresentation (j ≫ p); rw [hp]; infer_instance)

/-- Invertibility pulls from the base to the diagonal surface and all powers.
Source: blueprint standing hypothesis (blueprint: det-prop-diagonal-tower-system).
Proof: apply the ring map of global sections for W→Y to the given unit, then take
its positive power. This also applies to the zero ring of the empty scheme. -/
theorem diagonalSurface_power_unit (ℓ : ℕ) (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤))) (n : ℕ) :
    IsUnit ((ℓ ^ (n + 1) : ℕ) : Γ(diagonalSurface Y, ⊤)) := by
  let f : diagonalSurface Y ⟶ Y :=
    pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) ≫
      (ProjectiveLine Y ↘ Y)
  simpa using (hY.map f.appTop.hom).pow (n + 1)

/-- The supported integral constant on the pro-etale site.
Source: blueprint clause 1 (blueprint: det-prop-diagonal-tower-system). -/
abbrev diagonalIntegralSource (Y : Scheme.{u}) :=
  (lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion Y)).obj
    ((constantSheaf (Scheme.ProEt.topology (ProjectiveLine Y)) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

/-- Units mean exact comparison pullback of etale units.
Source: blueprint clause 1 (blueprint: det-prop-diagonal-tower-system). -/
abbrev diagonalComparisonUnits (Y : Scheme.{u}) :=
  (comparisonUpperStar AddCommGrpCat.{u + 1} (diagonalSurface Y)).obj
    (diagonalSurface Y).gmSheaf

/-- Transport an integral extension along an exact functor and a source isomorphism.
Source: naturality of Ext (blueprint: def-sfb-diagonal-system-interface). -/
def transportBoundarySource
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasExt.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasExt.{wS} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S U : A} {Q : B} (a : F.obj S ≅ Q) (δ : Ext S U 1) : Ext Q (F.obj U) 1 :=
  (Ext.mk₀ a.inv).comp (δ.mapExactFunctor F) (zero_add 1)

/-- The positive roof boundary: Ext uses the negative cone projection, so negate it.
This is the roof with [G_m→M] in degrees -1,0, quotient on the left and positive
projection on the right. The pole extension sends t inverse to +1.
Source: blueprint clause 1 and proof steps 1--2
(blueprint: det-prop-diagonal-tower-system). -/
def diagonalIntegralBoundary (Y : Scheme.{u}) :
    Ext (diagonalIntegralSource Y) (diagonalComparisonUnits Y) 1 :=
  -(transportBoundarySource (comparisonUpperStar AddCommGrpCat.{u + 1} (diagonalSurface Y))
    (cartierIntegralSourceIso (diagonalImmersion Y))
    (Etale.cartierPoleBoundary (diagonalImmersion Y) (diagonalImmersion_cartier Y)))

/-- The integral derived-completion formula, with both inverse limits total right
derived functors on strict systems. The integral reduction is independently fixed by
the cokernels of l^(n+1) on the identity functor. Thus its composite with integral
Rlim is exactly Rlim_n(K tensor^L Z/l^(n+1)). The displayed natural isomorphism
retains the comparison after forgetting the constant Z_l action. In addition the
output is right orthogonal to every complex on which l is invertible, the intrinsic
derived l-completeness criterion. The natural unit is universal for maps to all
such complete complexes, so this asserts derived completion, not just a limit formula.
Source: blueprint clause 2 and Stacks 099M, 091S and 091Z
(blueprint: det-prop-diagonal-tower-system). -/
def DiagonalCompletionSpec (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W)) : Prop :=
  ∃ (I : DiagonalDerivedReduction ℓ (𝟭 (DiagonalAb W)))
    (RF : DerivedCategory (DiagonalSystems ℓ W) ⥤ DerivedCategory (DiagonalMod ℓ W))
    (η : (lim : DiagonalSystems ℓ W ⥤ DiagonalMod ℓ W).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (RZ : DerivedCategory (ℕᵒᵖ ⥤ DiagonalAb W) ⥤ DerivedCategory (DiagonalAb W))
    (ηZ : (lim : (ℕᵒᵖ ⥤ DiagonalAb W) ⥤ DiagonalAb W).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RZ),
    RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso (DiagonalSystems ℓ W) (.up ℤ)) ∧
    RZ.IsRightDerivedFunctor ηZ
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ DiagonalAb W) (.up ℤ)) ∧
    Nonempty (D.T ⋙ RF ⋙ (diagonalForget ℓ W).mapDerivedCategory ≅ I.T ⋙ RZ) ∧
    ∃ unit : 𝟭 (DerivedCategory (DiagonalAb W)) ⟶
        D.T ⋙ RF ⋙ (diagonalForget ℓ W).mapDerivedCategory,
      (∀ (K P : DerivedCategory (DiagonalAb W)), IsIso (ℓ • 𝟙 P) →
        Subsingleton (P ⟶ (D.T ⋙ RF ⋙ (diagonalForget ℓ W).mapDerivedCategory).obj K)) ∧
      ∀ (K N : DerivedCategory (DiagonalAb W)),
        (∀ P : DerivedCategory (DiagonalAb W), IsIso (ℓ • 𝟙 P) → Subsingleton (P ⟶ N)) →
        Function.Bijective (fun f :
          (D.T ⋙ RF ⋙ (diagonalForget ℓ W).mapDerivedCategory).obj K ⟶ N ↦
            unit.app K ≫ f)

/-- The levelwise finite-source comparison preserves the quotient unit, not an
arbitrary automorphism of the supported constant.
Source: blueprint clauses 3--4 (blueprint: det-prop-diagonal-tower-system). -/
def DiagonalSourceNormalization (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (D : DiagonalReductionPresentation ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (n : ℕ)
    (s : (D.E.obj (diagonalIntegralSource Y)).obj (op n) ≅
      (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
        ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)) (diagonalImmersion Y)).obj
          (geoCartierConstant (diagonalResidue.{u} ℓ n) (ProjectiveLine Y)))) : Prop :=
  HEq
    ((diagonalScalarAdjunction ℓ (diagonalSurface Y)).unit.app (diagonalIntegralSource Y) ≫
      (diagonalForget ℓ (diagonalSurface Y)).map ((D.π n).app (diagonalIntegralSource Y) ≫
        s.hom))
    (cartierProIntegralGenerator (diagonalResidue.{u} ℓ n) (diagonalImmersion Y))

attribute [local irreducible] CategoryTheory.Abelian.Ext
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  diagonalDerivedSingleCounit DiagonalSourceNormalization
  transportBoundarySource
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison cartierRootsIso
  cartierEtaleKummerUnit cartierProKummerUnit cartierProIntegralGenerator cartierProRootMap
  cartierReducedEtale cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierResidueReducedPro diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The normalized Kummer target of a boundary with a fixed source identification.
Source: diagonal proof steps 5--7 (blueprint: def-sfb-diagonal-system-interface). -/
def normalizedBoundaryTarget
    (ℓ : ℕ) {A : Type uA} [Category.{vA} A] [Abelian A] [HasExt.{w} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasExt.{w} B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    (L : A ⥤ B) (F : B ⥤ A) (D : DiagonalDerivedReduction ℓ L)
    (S U : A) (δ : Ext S U 1) (rootsTower : ℕᵒᵖ ⥤ A) (Q R : ℕ → B)
    (sourceNorm : ∀ n, ((D.ordinary.E.obj S).obj (op n) ≅ Q n) → Prop)
    (rootNorm : ∀ (H : ℕᵒᵖ ⥤ B), (H ⋙ F ≅ rootsTower) →
      ∀ n, (H.obj (op n) ≅ R n) → Prop)
    (finiteClass : ∀ n, Ext (Q n) (R n) 2 → Prop)
    (a : D.T.obj ((DerivedCategory.singleFunctor A 0).obj S) ≅
      (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj (D.ordinary.E.obj S)) : Prop :=
  ∃ (H : ℕᵒᵖ ⥤ B) (roots : H ⋙ F ≅ rootsTower)
    (b : D.T.obj (((DerivedCategory.singleFunctor A 0).obj U)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H)⟦(2 : ℤ)⟧),
    ∀ n, ∃ (s : (D.ordinary.E.obj S).obj (op n) ≅ Q n)
      (t : H.obj (op n) ≅ R n),
      sourceNorm n s ∧ rootNorm H roots n t ∧
      finiteClass n ((Ext.mk₀ s.inv).comp
        (((Ext.homEquiv.symm (a.inv ≫ D.T.map δ.hom ≫ b.hom)).mapExactFunctor
          ((evaluation ℕᵒᵖ B).obj (op n))).comp
          (Ext.mk₀ t.hom) (add_zero 2)) (zero_add 2))

/-- Abstract simultaneous boundary with specified normalized finite evaluations.
Source: diagonal clauses 3--4 (blueprint: def-sfb-diagonal-system-interface). -/
def normalizedBoundarySystem
    (ℓ : ℕ) {A : Type uA} [Category.{vA} A] [Abelian A] [HasExt.{w} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasExt.{w} B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    (L : A ⥤ B) (F : B ⥤ A) (D : DiagonalDerivedReduction ℓ L)
    (S U : A) (δ : Ext S U 1) (rootsTower : ℕᵒᵖ ⥤ A) (Q R : ℕ → B)
    (sourceNorm : ∀ n, ((D.ordinary.E.obj S).obj (op n) ≅ Q n) → Prop)
    (rootNorm : ∀ (H : ℕᵒᵖ ⥤ B), (H ⋙ F ≅ rootsTower) →
      ∀ n, (H.obj (op n) ≅ R n) → Prop)
    (finiteClass : ∀ n, Ext (Q n) (R n) 2 → Prop) : Prop :=
  ∃ (H : ℕᵒᵖ ⥤ B) (roots : H ⋙ F ≅ rootsTower)
    (a : D.T.obj ((DerivedCategory.singleFunctor A 0).obj S) ≅
      (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj (D.ordinary.E.obj S))
    (b : D.T.obj (((DerivedCategory.singleFunctor A 0).obj U)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H)⟦(2 : ℤ)⟧)
    (c : Ext (D.ordinary.E.obj S) H 2),
    a.hom = diagonalDerivedSingleCounit ℓ L D S ∧
    c.hom = a.inv ≫ D.T.map δ.hom ≫ b.hom ∧
    ∀ n, ∃ (s : (D.ordinary.E.obj S).obj (op n) ≅ Q n)
      (t : H.obj (op n) ≅ R n),
      sourceNorm n s ∧ rootNorm H roots n t ∧
      finiteClass n ((Ext.mk₀ s.inv).comp
        ((c.mapExactFunctor ((evaluation ℕᵒᵖ B).obj (op n))).comp
          (Ext.mk₀ t.hom) (add_zero 2)) (zero_add 2))

/-- Eliminating the uniquely determined Ext class preserves the system assertion.
Source: the Ext/Hom equivalence (blueprint: def-sfb-diagonal-system-interface). -/
theorem normalizedBoundarySystem_iff_target
    (ℓ : ℕ) {A : Type uA} [Category.{vA} A] [Abelian A] [HasExt.{w} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasExt.{w} B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    (L : A ⥤ B) (F : B ⥤ A) (D : DiagonalDerivedReduction ℓ L)
    (S U : A) (δ : Ext S U 1) (rootsTower : ℕᵒᵖ ⥤ A) (Q R : ℕ → B)
    (sourceNorm : ∀ n, ((D.ordinary.E.obj S).obj (op n) ≅ Q n) → Prop)
    (rootNorm : ∀ (H : ℕᵒᵖ ⥤ B), (H ⋙ F ≅ rootsTower) →
      ∀ n, (H.obj (op n) ≅ R n) → Prop)
    (finiteClass : ∀ n, Ext (Q n) (R n) 2 → Prop) :
    normalizedBoundarySystem ℓ L F D S U δ rootsTower Q R
      sourceNorm rootNorm finiteClass ↔
      ∃ a, a.hom = diagonalDerivedSingleCounit ℓ L D S ∧
        normalizedBoundaryTarget ℓ L F D S U δ rootsTower Q R
          sourceNorm rootNorm finiteClass a := by
  constructor
  · rintro ⟨H, roots, a, b, c, ha, hc, hn⟩
    refine ⟨a, ha, H, roots, b, ?_⟩
    have he : c = Ext.homEquiv.symm (a.inv ≫ D.T.map δ.hom ≫ b.hom) :=
      Ext.homEquiv.injective (hc.trans (Ext.homEquiv.apply_symm_apply _).symm)
    simpa only [← he] using hn
  · rintro ⟨a, ha, H, roots, b, hn⟩
    refine ⟨H, roots, a, b, Ext.homEquiv.symm (a.inv ≫ D.T.map δ.hom ≫ b.hom),
      ha, ?_, hn⟩
    exact Ext.homEquiv.apply_symm_apply _

/-- The usual exact-functor image of an Ext class, with its interfaces shared.
Source: exact functoriality of Ext (blueprint: def-sfb-diagonal-system-interface). -/
def exactFunctorExtImage
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasExt.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasExt.{wS} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S U : A} {n : ℕ} (δ : Ext S U n) : Ext (F.obj S) (F.obj U) n :=
  δ.mapExactFunctor F

/-- The actual diagonal endpoints and normalizations for simultaneous Kummer reduction.
Source: diagonal clauses 3--4 (blueprint: def-sfb-diagonal-system-interface). -/
def diagonalBoundaryTarget (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y))) :
    Prop :=
  normalizedBoundaryTarget ℓ (diagonalScalarExtension ℓ (diagonalSurface Y))
    (diagonalForget ℓ (diagonalSurface Y)) D
    (diagonalIntegralSource Y) (diagonalComparisonUnits Y) (diagonalIntegralBoundary Y)
    (Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) ℓ (Fact.out : ℓ.Prime))
    (fun n ↦ (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
      ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)) (diagonalImmersion Y)).obj
        (geoCartierConstant (diagonalResidue.{u} ℓ n) (ProjectiveLine Y))))
    (fun n ↦ (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
      (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
        (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y)))
    (DiagonalSourceNormalization ℓ Y D.ordinary)
    (fun _H roots n t ↦ HEq ((diagonalForget ℓ (diagonalSurface Y)).map t.hom)
      (roots.hom.app (op n) ≫
        cartierProRootMap (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
          (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y)
          (pow_pos (Fact.out : ℓ.Prime).pos _) (diagonalSurface_power_unit ℓ Y hY n)))
    (fun n e ↦ HEq e
      (exactFunctorExtImage (diagonalFiniteToPadic ℓ n (diagonalSurface Y))
        (cartierResidueReducedPro ℓ (Fact.out : ℓ.Prime) (n + 1) (diagonalImmersion Y)
          (diagonalImmersion_cartier Y) (diagonalSurface_power_unit ℓ Y hY n)))) a

/-- A single arrow in D(strict systems), its prescribed source and target, and its
finite cycle-class identifications. Ext^2 is used only as the standard homEquiv
presentation of a morphism from a degree-zero system to a system shifted by two.
Source: blueprint clauses 3--4 (blueprint: det-prop-diagonal-tower-system). -/
def DiagonalCycleSystemSpec (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y))) : Prop :=
  ∃ a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)),
    a.hom = diagonalDerivedSingleCounit ℓ
      (diagonalScalarExtension ℓ (diagonalSurface Y)) D (diagonalIntegralSource Y) ∧
    diagonalBoundaryTarget ℓ Y hY D a

end AlgebraicGeometry.ProEtale
```

## Users

The downstream audit reads current shared sources; all consumers continue importing the original module. The extraction preserves names and signatures, including named Abelian structures. The generic equivalence preserves the cycle predicate. No forced consumer adaptation has been made. The claim holders below are read from the current shared claim records.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity` | C9 | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.AdicCommonStageHomTranspose` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.AdicExceptionalCompositorCoefficients` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.AdicExceptionalCompositorCoefficientsData` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.AdicNormalizedPurityLift` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.AdicProperLocalizingAdjunctionComparison` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.AdicRamifiedScalarCochainNormalization` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.AdicRamifiedScalarRealizationData` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.AdicUnitTraceConstruction` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.AdicUnitTraceReductionData` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.AdicUnitTraceScalarData` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.AdicUnitTraceTensorCoordinates` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.AdicUnitTraceTransposeReductions` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.AffineSpaceRationalInduction` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.CanonicalDiagonalRightDerived` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.CartesianSectionAdjointMates` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.CartesianSectionData` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.ChartDiagonalSourceMate` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.CondensedExceptionalReconstruction` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.CondensedHomChainRealization` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.ContinuousQbarExceptionalPreservation` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalBaseSquares` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalCoefficientCategory` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalCoefficientDiagrams` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalCoefficientEndpoints` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalCoefficientExchange` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalCoefficientFamilyExtension` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalCoefficientFamilyPullback` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalCoefficientFiniteDiagonal` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalCoefficientFiniteRealization` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalCoefficientMaps` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalCoefficientPullback` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalCoefficientPullbackEndpoints` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalCoefficientQuotientLine` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalCoefficientQuotients` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalCoefficientReference` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalCoefficientScalars` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalCoefficientSourcePullback` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalCoefficientUniformizerReduction` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalCompletedDiagramRealization` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalCompletedFrame` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalCompletedPushSquare` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalFiniteRootMap` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalIntegralRootMap` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalNonTorsionBaseChange` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalQuotientBaseChange` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalTowerCoefficients` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalTowerLimit` | V2 | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalTowerSystem` | H9 | Own item: publicly re-exports interface; proof uses the component results. |
| `Sheaf.Paper.DiagonalTowerTrace` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalTowerTraceCoefficients` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalTowerTraceLimit` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalTowerTraceModels` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalTowerTracePresentations` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalTraceIntegrationSystems` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalTracePresentationExistence` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalTraceResultExistence` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalTraceSingleFaithful` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalTraceSources` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.DiagonalUniformizerAnnihilator` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.ExceptionalInverseImageExistence` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.ExceptionalRealizationNormalization` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.ExceptionalReconstructionComparison` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.ExceptionalReconstructionContext` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.ExceptionalReconstructionPresentations` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.FiniteDiagonalOrientationReduction` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.FiniteDiagonalReductionComparisons` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.GeneralCondensedWeilRealization` | S6 | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.GeneralHomComparisonCocycles` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.GeometricComparisonData` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.GeometricOperations` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.InverseContravariantBidual` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.LevelwiseNormalizedAdjointDescent` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.ModelCompactComparisonUnit` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.NormalizedIntegralPurityTrace` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.PodHomChainCtfDomains` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.PointTraceReconstruction` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.ProjectiveDiagonalComposition` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.ProjectiveDiagonalPullback` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.ProperExceptionalRestriction` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.ProperProductCounitTranspose` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.RamifiedScalarSystemTranspose` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.RationalAffineAdjunctionCalculus` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.RationalAffineTensorCalculus` | J6 | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.RationalExceptionalRestriction` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.RationalHomScalarTranspose` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.RationalP1AmbientComposites` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.RationalP1DiagonalTensor` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.RationalP1KernelContractions` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.RationalP1Triangle` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.RationalP1UnitCounit` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.RationalRestrictionGlue` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.RationalTatePullback` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.RationalTensorSymmetry` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.RationalVerdierEvaluationAdjoints` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.RelativeKunneth` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.RelativeProductInputDomains` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.RestrictionLocal` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.SfPackageCoefficientDomains` | B4 | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.SfPackageExceptionalCoherenceRealization` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.SfPackageFieldOperationRealization` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.SitePerfectRationalBidual` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.SmoothPurityCoordinateCategories` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.SmoothPurityCoordinateRightComparisons` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.SmoothPurityCoordinateTensorComparisons` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.SmoothPurityTowerClasses` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.SmoothPurityTowerGluing` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.SmoothPurityTowerP1Adjunction` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.SystemProjectionFormulaCoherence` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.SystemScalarProjectionIdentification` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TateTwistedProjection` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerChernPullback` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerClassChern` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerClassCoefficients` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerClassDiagonal` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerClassFinite` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerClassFiniteDiagonal` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerClassProjective` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerClassPullback` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerClassReduction` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerClassSystems` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerClassTwisting` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerP1CoefficientCoordinates` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerP1ComparisonsWithLine` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerP1EtaleDelta` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerP1EtaleEpsilon` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerP1EtaleFiniteData` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerP1EtaleOperations` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerP1EtaleOriginComparisons` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerP1EtaleWords` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerP1FixedTotalTensor` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerP1FormulaLevelComparisons` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerP1GeometricCoordinates` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerP1KernelScalarNormalization` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerP1LevelWords` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerP1OrdinaryPushCoordinates` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerP1ProjectionLevelComparisons` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerP1ProjectiveCoordinates` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerP1PushCoordinates` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerP1SingleLevelTriangles` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerP1TensorChainCoordinates` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerP1TensorCoordinates` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerP1TensorOrdinaryCoordinates` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerP1TriangleFactorization` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TowerP1UniformCtfDomains` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TraceCorrespondences` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.WeilChosenDualityExchange` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.PoincareDuality.ConstructibleSheafBiduality` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | V1 | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | V3 | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.CtfStabilityDirectImages` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.FiniteAdjunctionTransition` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.FiniteExceptional` | X3 | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.FiniteScalarMateData` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.FiniteScalarMateRealization` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.IntegralAffinePurityInduction` | J9 | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.IntegralDualExceptionalSystem` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineChart` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.IntegralExceptionalDescendedCounit` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.IntegralExceptionalMappingSystem` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.IntegralExceptionalRestriction` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.IntegralProjectiveLineAdjunction` | K5 | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.IntegralRestrictionChartCover` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.IntegralRestrictionGlue` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.IntegralVerdier` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.NormalizedTowerTensorEvaluation` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.RationalOperations` | D2 | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.RationalVerdier` | B6 | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.ScalarCompositeModelPasting` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.ScalarRefinementClosureSquare` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.ScalarSixCompactSupport` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.ScalarSixCtf` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.ScalarSixDirectImage` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SixFunctors.WeilChosenDualityHom` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | Existing public names and types remain available through the original import. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | Existing public names and types remain available through the original import. |
| `TargetsCheck` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | M3 | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.PoincareDuality.Verdier` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.SmoothPurity.Defs` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.Statement` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.Additivity` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.BaseChangeCoherence` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.Basic` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.BorelMoore` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.CoefficientMorphism` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.CompactCohomology` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.CompactPullback` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.Correspondence` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.CorrespondencePair` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.CurvePieces` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.Dualizing` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.FibreCoherence` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.FibreModel` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.FixedPoint` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.FixedPointScheme` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.Frobenius` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.FrobeniusLocalTerm` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.GenericQuotient` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.HomologyUnit` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.KunnethVerdier` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.LefschetzVerdier` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.LocalTerm` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.LocalTermLocality` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.Main` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.ModelExtension` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.OpenPieceCoherence` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.OpenSquare` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.PointNormalization` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.Product` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.ProperCompatibility` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.ProperCurve` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.ProperPushforward` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.ProperPushforwardKernel` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.PullbackFamily` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.RelativeFrobenius` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.RelativeFrobeniusComparison` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.RelativeFrobeniusIterate` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.ShriekTraceFunction` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.ShriekTraceFunctionInduction` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.Stalk` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.Statement` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.SupportedPairing` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.TraceClass` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.TraceClassAdditivity` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.WeilBaseChange` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.WeilSheafUpperStar` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.TraceFormula.WeilTrace` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.WeilSheaf.EulerProduct` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.ZetaFunction.LissePurity` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | Existing public names and types remain available through the original import. |
| `WeilConjectures.ZetaFunction.WeilObjectComparison` | unclaimed | Existing public names and types remain available through the original import. |

## Status

landed 20261025T101147-L-3663305 2026-10-25 (merge of deliver/H9/Sheaf.Paper.DiagonalTowerSystem)
