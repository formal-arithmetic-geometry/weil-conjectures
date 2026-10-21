# CartesianTwistAssertions

## Reason

The item's old CartesianTwistMaps family duplicates the actual signed coefficient-module
comparisons already stated by its prescribed dependency CartesianCoefficientTwists.
Its separate existence-and-uniqueness hole reconstructs the same roots, finite tensor,
integral projection, rational balanced-quotient and Qbar colimit comparisons as adjoint
abelian maps. No other Lean module, including the quarantine tree, refers to this family
or its normalization. Reuse the existing normalized module-comparison API directly.

This is a representation change of the twist clause, not a proof of the removed
cartesianTwistMaps_existsUnique theorem. That hole is pruned; only the final
cartesianCoefficients hole is proved. The final theorem's written signature is unchanged,
but its CartesianTwistAssertions predicate changes, so the complete statement must be
independently reread. No locked Challenge declaration or definition appearing in its
type refers to any changed predicate; no target type is edited.

The replacement retains the mathematical data and normalizations:

| Old clause | Existing API used in the replacement |
| --- | --- |
| roots unit projection | proEtaleRootsOfUnityInverseImageMap, adjunct of the structural pullback of roots |
| zero and semilinearity | SpSignedComparison.zero and signed coefficient-module isomorphisms |
| positive tensor and negative evaluation | SpSignedComparison.positive and SpSignedComparison.negative |
| finite first line | spFiniteTwists_cartesian pure root-tensor formula over StrictTower.constantRingIso |
| finite annihilating exponent | all ZMod(ell^(r+1)) -> ULift A maps; the previous unique castHom is one such input |
| integral first line | SpInternalCartesian with the canonical spIntegralComparison, fixed by every finite projection |
| rational first line | balanced scalar-extension equation with the same alpha and integral map |
| Qbar first line | the specified finite-subextension colimit coprojection equations |
| inverse-image isomorphisms | SpSignedComparison.signed in every integer degree, over spCoefficientIso |

The replacement also retains the dependency's Kummer and finite-field inclusion
compatibilities and derived comparison fields. There is no arbitrary choice of an
unnormalized isomorphism: the actual normalized comparisons are quantified as witnesses
inside a proposition, and all their specified formulas are retained. We do not choose
any data in a new definition. Finite A still ranges in Type u, used through the exact
ULift A convention of the old statement. The empty scheme and zero finite ring are
allowed by the same dependency hypotheses. Negative degrees still use its internal dual
and evaluation record. The Qbar ring remains the finite-subextension condensed ring.

CartesianAdicComparison is a record with the two maps and all seven compatibility
clauses from spTwists_cartesian. Its Nonempty proposition replaces the corresponding
nested existential, so each equation has a stable named type during kernel checking.
This record is not a choice of data from an unproved existence theorem.

No source-library declaration, attribute, body or import changes. The unit's three proof
steps remain: alpha, Tate comparisons, finite-free coefficient extensions.

## Old

```lean
/-- The underlying abelian sheaf of a signed line, retaining the recorded powers and duals.
Source: blueprint twist clause (blueprint: sk-prop-sfb-cartesian-coefficients). -/
abbrev cartesianSignedAb (Z : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology Z) CommRingCat.{u + 1})
    (L : SheafOfModules.{u + 1} (Scheme.purTwistRing Z R)) (d : ℤ) :=
  (SheafOfModules.toSheaf _).obj (WeilConjectures.coefficientTwistLine Z L d)

/-- Direct-image maps on all signed lines. Their inverse-image mates are the comparisons.
Source: blueprint twist clause (blueprint: sk-prop-sfb-cartesian-coefficients). -/
abbrev CartesianSignedMaps (f : X ⟶ Y)
    (RX : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (RY : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (LX : SheafOfModules.{u + 1} (Scheme.purTwistRing X RX))
    (LY : SheafOfModules.{u + 1} (Scheme.purTwistRing Y RY)) :=
  ∀ d : ℤ, cartesianSignedAb Y RY LY d ⟶
    (lowerStar AddCommGrpCat.{u + 1} f).obj (cartesianSignedAb X RX LX d)

/-- Zero, linearity, positive tensor, and negative evaluation normalizations.
The first-line normalization is supplied separately for each coefficient construction.
All equations are on sections over a test object and its actual fibre product.
Source: blueprint powers and duals paragraph
(blueprint: sk-prop-sfb-cartesian-coefficients). -/
def CartesianSignedNormalization (f : X ⟶ Y)
    (RX : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (RY : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (LX : SheafOfModules.{u + 1} (Scheme.purTwistRing X RX))
    (LY : SheafOfModules.{u + 1} (Scheme.purTwistRing Y RY))
    (ρ : cartesianSignedAb Y RY LY 0 ⟶
      (lowerStar AddCommGrpCat.{u + 1} f).obj (cartesianSignedAb X RX LX 0))
    (c : CartesianSignedMaps f RX RY LX LY) : Prop :=
  c 0 = ρ ∧
  (∀ (d : ℤ) (V : Y.ProEt) (a : RY.obj.obj (Opposite.op V))
    (x : (WeilConjectures.coefficientTwistLine Y LY d).val.obj (Opposite.op V)),
    (c d).hom.app (Opposite.op V) (a • x) =
      @SMul.smul (RX.obj.obj (Opposite.op ((Scheme.proEtaleBaseChange f).obj V)))
        ((WeilConjectures.coefficientTwistLine X LX d).val.obj
          (Opposite.op ((Scheme.proEtaleBaseChange f).obj V))) inferInstance
        (ρ.hom.app (Opposite.op V) a) ((c d).hom.app (Opposite.op V) x)) ∧
  (∀ (n : ℕ) (V : Y.ProEt)
    (x : (WeilConjectures.coefficientTwistPower Y LY (n + 1)).val.obj (Opposite.op V))
    (y : LY.val.obj (Opposite.op V)),
    (c (Int.ofNat (n + 2))).hom.app (Opposite.op V)
        (SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
          (A := RY) _ _ (Opposite.op V) x y) =
      SheafOfModules.siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} (A := RX) _ _
        (Opposite.op ((Scheme.proEtaleBaseChange f).obj V))
        ((c (Int.ofNat (n + 1))).hom.app (Opposite.op V) x)
        ((c 1).hom.app (Opposite.op V) y)) ∧
  ∀ (n : ℕ) (V : Y.ProEt)
    (q : (WeilConjectures.coefficientTwistLine Y LY (Int.negSucc n)).val.obj
      (Opposite.op V))
    (x : (WeilConjectures.coefficientTwistPower Y LY (n + 1)).val.obj (Opposite.op V)),
    (((c (Int.negSucc n)).hom.app (Opposite.op V) q).app
        (Opposite.op (Over.mk (𝟙 ((Scheme.proEtaleBaseChange f).obj V)))))
          ((c (Int.ofNat (n + 1))).hom.app (Opposite.op V) x) =
      ρ.hom.app (Opposite.op V) ((q.app (Opposite.op (Over.mk (𝟙 V)))) x)

/-- The section-module model of an internal coefficient line.
Source: the recorded internal/sectionwise equivalence
(blueprint: sk-prop-sfb-cartesian-coefficients). -/
abbrev cartesianSectionLine (Z : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (L : Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1}) R) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology Z) R).functor.obj L

/-- The reconstructed ring sheaf, with exactly the recorded internal multiplication.
Source: the recorded internal/sectionwise equivalence
(blueprint: sk-prop-sfb-cartesian-coefficients). -/
abbrev cartesianSectionRing (Z : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
    [MonObj R] [IsCommMonObj R] :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology Z) R

/-- Signed direct-image maps for one fixed condensed coefficient and its actual first lines.
Source: blueprint twist clause (blueprint: sk-prop-sfb-cartesian-coefficients). -/
abbrev CartesianInternalSignedMaps
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (f : X ⟶ Y)
    (LX : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ X))
    (LY : Mod (Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ Y)) :=
  CartesianSignedMaps f (cartesianSectionRing X (condensedRingObj Λ X))
    (cartesianSectionRing Y (condensedRingObj Λ Y))
    (cartesianSectionLine X _ LX) (cartesianSectionLine Y _ LY)

/-- Canonical scalar and signed-power normalization for the internal coefficient model.
Source: blueprint twist clause, compatibility with alpha_f
(blueprint: sk-prop-sfb-cartesian-coefficients). -/
def CartesianInternalSignedNormalization
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (f : X ⟶ Y)
    (LX : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ X))
    (LY : Mod (Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ Y))
    (c : CartesianInternalSignedMaps Λ f LX LY) : Prop :=
  CartesianSignedNormalization f _ _ (cartesianSectionLine X _ LX)
    (cartesianSectionLine Y _ LY) (condensedPushforwardHom Λ f) c

/-- The full family of candidate comparisons, before any isomorphism is asserted.
Source: blueprint twist proof, roots, finite, integral, rational, colimit, powers and duals
(blueprint: sk-prop-sfb-cartesian-coefficients). -/
structure CartesianTwistMaps (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y) where
  /-- Roots comparison, as an inverse-image map. -/
  roots (n : ℕ) :
    (upperStar AddCommGrpCat.{u + 1} f).obj
        (Scheme.proEtaleRootsOfUnitySheaf Y (ℓ ^ (n + 1))) ⟶
      Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))
  /-- Finite signed maps, in the recorded constant coefficient presentation. -/
  finite (A : Type u) [CommRing A] [Finite A] (r : ℕ)
      (hA : (ℓ ^ (r + 1) : ULift.{u + 1} A) = 0) :
    CartesianSignedMaps f (Scheme.tateFiniteCoefficient X (ULift.{u + 1} A))
      (Scheme.tateFiniteCoefficient Y (ULift.{u + 1} A))
      (spFiniteTwist X ℓ (ULift.{u + 1} A) r hA)
      (spFiniteTwist Y ℓ (ULift.{u + 1} A) r hA)
  /-- Integral signed maps, in the recorded pulled-back coefficient presentation. -/
  integral (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    CartesianInternalSignedMaps (Profinite.padicIntegersRingObj ℓ E.1) f
      (spIntegralTwist X ℓ E) (spIntegralTwist Y ℓ E)
  /-- Rational signed maps, in the recorded pulled-back coefficient presentation. -/
  rational (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    CartesianInternalSignedMaps (Profinite.continuousMapRingObj E.1) f
      (spRationalTwist X ℓ E) (spRationalTwist Y ℓ E)
  /-- Algebraic-closure signed maps for finite-subextension-valued coefficients. -/
  qbar : CartesianInternalSignedMaps (Profinite.padicAlgClRingObj ℓ) f
    (spQbarTwist X ℓ) (spQbarTwist Y ℓ)

/-- The actual inverse-image mate of a direct-image abelian sheaf map.
Source: the recorded inverse-image adjunction
(blueprint: sk-prop-sfb-cartesian-coefficients). -/
abbrev cartesianTwistMate (f : X ⟶ Y)
    {M : Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}}
    {N : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}}
    (c : M ⟶ (lowerStar AddCommGrpCat.{u + 1} f).obj N) :=
  ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv M N).symm c

/-- Pull back units by the actual fibre-product projection, on each test object.
Source: blueprint roots paragraph (blueprint: sk-prop-sfb-cartesian-coefficients). -/
def cartesianUnitsBaseChange (f : X ⟶ Y) (V : Y.ProEt) :=
  (forget₂ CommRingCat.{u} CommMonCat.{u} ⋙ CommMonCat.units ⋙
    CommGrpCat.toAddCommGrp ⋙ AddCommGrpCat.uliftFunctor.{u + 1}).map
      (Scheme.Γ.map (pullback.fst V.hom f).op)

/-- The finite-level comparison is the tensor of the specified quotient-coefficient
comparison and roots comparison, using the actual strong monoidal tensorator.
Source: blueprint finite-level integral twist paragraph
(blueprint: sk-prop-sfb-cartesian-coefficients). -/
def cartesianTwistLevelMap (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y)
    (c : CartesianTwistMaps ℓ f) (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    (upperStar AddCommGrpCat.{u + 1} f).obj (spIntegralTwistLevel Y ℓ E n).X ⟶
      (spIntegralTwistLevel X ℓ E n).X :=
  (Functor.Monoidal.μIso (upperStar AddCommGrpCat.{u + 1} f) _ _).inv ≫
    (condensedPullbackHom (spEllPointRingObj ℓ E n) f ⊗ₘ c.roots n)

/-- The unique unital quotient map to the finite coefficient ring, in its section universe.
Source: blueprint finite first-line formula (blueprint: sk-prop-sfb-cartesian-coefficients). -/
abbrev cartesianFiniteQuotientHom (ℓ : ℕ) (A : Type u) [CommRing A] (r : ℕ)
    (hA : (ℓ ^ (r + 1) : ULift.{u + 1} A) = 0) :
    ZMod (ℓ ^ (r + 1)) →+* ULift.{u + 1} A :=
  letI : CharP (ULift.{u + 1} A) (ringChar (ULift.{u + 1} A)) :=
    ringChar.charP (R := ULift.{u + 1} A)
  ZMod.castHom
    (ringChar.dvd (R := ULift.{u + 1} A) (by simpa only [Nat.cast_pow] using hA))
    (ULift.{u + 1} A)

/-- The normalization which uniquely determines every comparison. The roots equation
uses the literal structural map on units; the first integral maps are determined by
all projections, rational maps by the balanced-tensor quotient, and Qbar by all finite
field coprojections. Signed tensor and dual equations fix every other degree.
Source: the six paragraphs of the blueprint Tate-twist comparison proof
(blueprint: sk-prop-sfb-cartesian-coefficients). -/
def CartesianTwistNormalization (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y)
    (c : CartesianTwistMaps ℓ f) : Prop :=
  (∀ (n : ℕ) (V : Y.ProEt),
    (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
        (c.roots n)).hom.app (Opposite.op V)) ≫
        (Scheme.proEtaleRootsOfUnityInclusion X (ℓ ^ (n + 1))).hom.app
          (Opposite.op ((Scheme.proEtaleBaseChange f).obj V)) =
      (Scheme.proEtaleRootsOfUnityInclusion Y (ℓ ^ (n + 1))).hom.app (Opposite.op V) ≫
        cartesianUnitsBaseChange f V) ∧
  (∀ (A : Type u) [CommRing A] [Finite A] (r : ℕ)
    (hA : (ℓ ^ (r + 1) : ULift.{u + 1} A) = 0),
    CartesianSignedNormalization f _ _
      (spFiniteTwist X ℓ (ULift.{u + 1} A) r hA)
      (spFiniteTwist Y ℓ (ULift.{u + 1} A) r hA)
      ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
          (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
            (CommRingCat.of (ULift.{u + 1} A)))) (c.finite A r hA)) ∧
  (∀ (A : Type u) [CommRing A] [Finite A] (r : ℕ)
    (hA : (ℓ ^ (r + 1) : ULift.{u + 1} A) = 0) (V : Y.ProEt)
    (b : (Scheme.tateFiniteCoefficient Y (ULift.{u + 1} A)).obj.obj (Opposite.op V))
    (x : (Scheme.proEtaleRootsOfUnitySheaf Y (ℓ ^ (r + 1))).obj.obj (Opposite.op V)),
    (c.finite A r hA 1).hom.app (Opposite.op V)
        (Scheme.tateFiniteTensor Y ℓ (ULift.{u + 1} A) r
          (cartesianFiniteQuotientHom ℓ A r hA) V b x) =
      Scheme.tateFiniteTensor X ℓ (ULift.{u + 1} A) r
        (cartesianFiniteQuotientHom ℓ A r hA)
        ((Scheme.proEtaleBaseChange f).obj V)
        ((Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} A))).hom.app (Opposite.op V) b)
        ((((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
          (c.roots r))).hom.app (Opposite.op V) x)) ∧
  (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
    CartesianInternalSignedNormalization (Profinite.padicIntegersRingObj ℓ E.1) f
      (spIntegralTwist X ℓ E) (spIntegralTwist Y ℓ E) (c.integral E) ∧
    CartesianInternalSignedNormalization (Profinite.continuousMapRingObj E.1) f
      (spRationalTwist X ℓ E) (spRationalTwist Y ℓ E) (c.rational E)) ∧
  (∀ (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ),
    cartesianTwistMate f (c.integral E 1) ≫
        (limit.π (spIntegralTwistSystem X ℓ E) (Opposite.op n)).hom =
      (upperStar AddCommGrpCat.{u + 1} f).map
          (limit.π (spIntegralTwistSystem Y ℓ E) (Opposite.op n)).hom ≫
        cartesianTwistLevelMap ℓ f c E n) ∧
  (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
    (upperStar AddCommGrpCat.{u + 1} f).map
        (Mod.extendπ (padicIntegersToPadicSubfield Y ℓ E) (spIntegralTwist Y ℓ E)) ≫
          cartesianTwistMate f (c.rational E 1) =
      (Functor.Monoidal.μIso (upperStar AddCommGrpCat.{u + 1} f) _ _).inv ≫
        (condensedPullbackHom (Profinite.continuousMapRingObj E.1) f ⊗ₘ
          cartesianTwistMate f (c.integral E 1)) ≫
        Mod.extendπ (padicIntegersToPadicSubfield X ℓ E) (spIntegralTwist X ℓ E)) ∧
  CartesianInternalSignedNormalization (Profinite.padicAlgClRingObj ℓ) f
    (spQbarTwist X ℓ) (spQbarTwist Y ℓ) c.qbar ∧
  ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
    (upperStar AddCommGrpCat.{u + 1} f).map
        (colimit.ι (spRationalTwistDiagram Y ℓ) E) ≫ cartesianTwistMate f (c.qbar 1) =
      cartesianTwistMate f (c.rational E 1) ≫ colimit.ι (spRationalTwistDiagram X ℓ) E

/-- There is exactly one family with these roots, scalar, tower, tensor and evaluation
normalizations. Its data are thus determined; this is not a choice of arbitrary maps.
Source: blueprint Tate-twist comparison proof, all paragraphs
(blueprint: sk-prop-sfb-cartesian-coefficients).
Proof: pull a root along the structural map on units and use the kernel property;
finite etale representability identifies this map with base change. Tensor its
finite comparison with the constant scalar map, using local pure tensor generation
for uniqueness. At each integral quotient use the strong tensorator, alpha and this
roots map. The root powers and scalar reductions commute, so these maps form a cone.
On a common compatible-root cover they identify with coefficient maps; the compatible
free tower comparison supplies the integral map, uniquely fixed by all projections.
Pass to rational scalar extension via its balanced coequalizer, and to Qbar via its
specified finite-subextension colimit. Both universal properties determine the maps.
They are semilinear for eta_f since all finite-level formulas are semilinear. At zero
use eta_f, at positive degrees tensor these maps, and at negative degrees use dual
evaluation on the pulled-back positive line. Local rank-one trivializations prove
existence and uniqueness of the dual map and all sheaf maps glue. No basis, cover,
or unnormalized isomorphism is chosen in the resulting family. -/
theorem cartesianTwistMaps_existsUnique (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y)
    (hX : ∀ x : X, Invertible (ℓ : X.residueField x))
    (hY : ∀ y : Y, Invertible (ℓ : Y.residueField y)) :
    ∃! c : CartesianTwistMaps ℓ f, CartesianTwistNormalization ℓ f c := by
  sorry

/-- The uniquely normalized canonical maps, defined by their determining universal
properties; the only postponed datum is the proof of their unique characterization.
Source: blueprint twist comparison (blueprint: sk-prop-sfb-cartesian-coefficients). -/
def cartesianTwistMaps (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y)
    (hX : ∀ x : X, Invertible (ℓ : X.residueField x))
    (hY : ∀ y : Y, Invertible (ℓ : Y.residueField y)) : CartesianTwistMaps ℓ f :=
  (cartesianTwistMaps_existsUnique ℓ f hX hY).exists.choose

/-- The isomorphism assertion for the specified normalized maps in every signed degree.
Linearity along alpha is part of their normalization, expressed on the adjoint maps
as semilinearity along eta. Adjointness gives exactly the transported alpha action.
Source: blueprint (1), twists (blueprint: sk-prop-sfb-cartesian-coefficients). -/
def CartesianTwistAssertions (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y) : Prop :=
  ∀ (hX : ∀ x : X, Invertible (ℓ : X.residueField x))
    (hY : ∀ y : Y, Invertible (ℓ : Y.residueField y)),
    (∀ (A : Type u) [CommRing A] [Finite A] (r : ℕ)
      (hA : (ℓ ^ (r + 1) : ULift.{u + 1} A) = 0) (d : ℤ),
      IsIso (cartesianTwistMate f ((cartesianTwistMaps ℓ f hX hY).finite A r hA d))) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ℓ) (d : ℤ),
      IsIso (cartesianTwistMate f ((cartesianTwistMaps ℓ f hX hY).integral E d)) ∧
      IsIso (cartesianTwistMate f ((cartesianTwistMaps ℓ f hX hY).rational E d))) ∧
    ∀ d : ℤ, IsIso (cartesianTwistMate f ((cartesianTwistMaps ℓ f hX hY).qbar d))

```

The proof-only imports removed are LocalFieldIntegralBasis, RingedSiteGrothendieckAbelian,
SheafTensor, SheafTensorClosed, ProEtaleToposFunctorialityInverseImage,
ModuleObjects.LiftExact and the redundant ModuleObject.Basic import.
The CartesianCoefficientTwists import becomes public because its comparison records
now occur in the statement itself; the other four public imports are retained verbatim.

## New

```lean
/-- The normalized finite signed comparisons over the recorded constant coefficient map.
The first-line formula fixes the map on root tensors; the second clause retains all
Kummer identifications. Every signed comparison includes zero, tensor and evaluation
normalizations, and is an isomorphism of coefficient modules in every degree.
Source: blueprint finite coefficients and powers and duals paragraphs
(blueprint: sk-prop-sfb-cartesian-coefficients). -/
@[irreducible] def CartesianFiniteTwistAssertions (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)] : Prop :=
  ∀ (A : Type u) [CommRing A] [Finite A],
    ∃ β : ∀ (r : ℕ) (a : ZMod (ℓ ^ (r + 1)) →+* (ULift.{u + 1} A)),
      SpSignedComparison f (Scheme.tateFiniteCoefficient Y (ULift.{u + 1} A))
        (Scheme.tateFiniteCoefficient X (ULift.{u + 1} A))
        (StrictTower.constantRingIso (ULift.{u + 1} A) f)
        (Scheme.tateFiniteLine Y ℓ (ULift.{u + 1} A) r a)
        (Scheme.tateFiniteLine X ℓ (ULift.{u + 1} A) r a),
      (∀ (r : ℕ) (a : ZMod (ℓ ^ (r + 1)) →+* (ULift.{u + 1} A)) (V : Y.ProEt)
        (b : (Scheme.tateFiniteCoefficient Y (ULift.{u + 1} A)).obj.obj (op V))
        (z : (Scheme.proEtaleRootsOfUnitySheaf Y (ℓ ^ (r + 1))).obj.obj (op V)),
        (((Scheme.proEtaleRingModuleAdjunction f _ _ _).homEquiv _ _)
          ((β r a).signed 1).hom).val.app (op V)
            (Scheme.tateFiniteTensor Y ℓ (ULift.{u + 1} A) r a V b z) =
          Scheme.tateFiniteTensor X ℓ (ULift.{u + 1} A) r a ((Scheme.proEtaleBaseChange f).obj V)
            ((Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
              (CommRingCat.of (ULift.{u + 1} A))).hom.app (op V) b)
            ((Scheme.proEtaleRootsOfUnityDirectImageMap f (ℓ ^ (r + 1))).hom.app
              (op V) z)) ∧
      (∀ (r n : ℕ) (h : r ≤ n) (a : ZMod (ℓ ^ (r + 1)) →+* (ULift.{u + 1} A)),
        (Scheme.proEtaleRingModulePullback f _ _ _).map
          (spFiniteKummer Y ℓ (ULift.{u + 1} A) r n h a) ≫ ((β r a).signed 1).hom =
        ((β n (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ h))
          (ZMod (ℓ ^ (r + 1)))))).signed 1).hom ≫ spFiniteKummer X ℓ (ULift.{u + 1} A) r n h a)

/-- The normalized integral, rational and algebraic-closure signed comparisons.
Integral maps are fixed by all finite projections through spIntegralComparison;
rational maps by the displayed scalar-extension equation, and Qbar by its finite-field
coprojections. SpInternalCartesian retains precisely alpha_f and the sectionwise
signed coefficient-module comparisons, together with their tensor and dual equations.
Source: blueprint integral, rational, colimit, powers and duals paragraphs
(blueprint: sk-prop-sfb-cartesian-coefficients). -/
structure CartesianAdicComparison (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)] where
  rational : ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
        (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
          (spRationalTwist.{u} Y ℓ E).X ⟶ (spRationalTwist.{u} X ℓ E).X
  qbar : (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
          (spQbarTwist.{u} Y ℓ).X ⟶ (spQbarTwist.{u} X ℓ).X
  rational_scalar : (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
          (Mod.extendπ (padicIntegersToPadicSubfield Y ℓ E) (spIntegralTwist.{u} Y ℓ E)) ≫
        rational E =
      Functor.OplaxMonoidal.δ (upperStar AddCommGrpCat.{u + 1} f)
        (condensedRingObj (Profinite.continuousMapRingObj.{u} E.1) Y)
        (spIntegralTwist.{u} Y ℓ E).X ≫
      (condensedPullbackHom (Profinite.continuousMapRingObj.{u} E.1) f ⊗ₘ
        spIntegralComparison f ℓ E) ≫
      Mod.extendπ (padicIntegersToPadicSubfield X ℓ E) (spIntegralTwist.{u} X ℓ E))
  qbar_coprojection : (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
          (colimit.ι (spRationalTwistDiagram Y ℓ) E) ≫ qbar =
        rational E ≫ colimit.ι (spRationalTwistDiagram X ℓ) E)
  integral_rational_cartesian : (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      SpInternalCartesian f (Profinite.padicIntegersRingObj.{u} ℓ E.1)
        (spIntegralTwist.{u} Y ℓ E) (spIntegralTwist.{u} X ℓ E) (spIntegralComparison f ℓ E) ∧
      SpInternalCartesian f (Profinite.continuousMapRingObj.{u} E.1)
        (spRationalTwist.{u} Y ℓ E) (spRationalTwist.{u} X ℓ E) (rational E))
  qbar_cartesian : SpInternalCartesian f (Profinite.padicAlgClRingObj.{u} ℓ)
      (spQbarTwist.{u} Y ℓ) (spQbarTwist.{u} X ℓ) qbar
  integral_inclusion : (∀ (E F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F),
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
          (spIntegralTwistMap Y ℓ h) ≫ spIntegralComparison f ℓ F =
        spIntegralComparison f ℓ E ≫ spIntegralTwistMap X ℓ h)
  rational_inclusion : (∀ (E F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F),
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
          (spRationalTwistMap Y ℓ h) ≫ rational F =
        rational E ≫ spRationalTwistMap X ℓ h)
  root_transition : (∀ (n m : ℕ) (h : n ≤ m),
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
        (Scheme.proEtaleRootsOfUnityTransition Y (ℓ ^ n) (ℓ ^ m)
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ h)) ≫ Scheme.proEtaleRootsOfUnityInverseImageMap f (ℓ ^ n) =
      Scheme.proEtaleRootsOfUnityInverseImageMap f (ℓ ^ m) ≫
        Scheme.proEtaleRootsOfUnityTransition X (ℓ ^ n) (ℓ ^ m)
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ h))

/-- Existence of the normalized adic signed comparison data.
Source: blueprint twists (blueprint: sk-prop-sfb-cartesian-coefficients). -/
def CartesianAdicTwistAssertions (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)] : Prop :=
  Nonempty (CartesianAdicComparison ℓ f)

/-- The canonical normalized comparisons of roots and every signed coefficient twist.
The finite comparisons cover every finite coefficient ring annihilated by an ell power:
its unital quotient map is the input a. The adic comparisons use the recorded internal
and sectionwise encodings and their same coefficient map alpha_f.
Source: blueprint (1), twists (blueprint: sk-prop-sfb-cartesian-coefficients). -/
def CartesianTwistAssertions (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y) : Prop :=
  ∀ (hX : ∀ x : X, Invertible (ℓ : X.residueField x))
    (hY : ∀ y : Y, Invertible (ℓ : Y.residueField y)),
    letI := hX
    letI := hY
    (∀ n : ℕ, IsIso (Scheme.proEtaleRootsOfUnityInverseImageMap f (ℓ ^ n))) ∧
    CartesianFiniteTwistAssertions ℓ f ∧ CartesianAdicTwistAssertions ℓ f
```

## Users

The downstream.py queries were run for CartesianTwistAssertions and cartesianTwistMaps.
Their only named user is the item itself. A token search of all lean/ and quarantine/
confirms that none of the sixteen changed/removed names has a consumer outside the item.
The complete transitive module consumer list is below, including holders at this check.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | B7 | No reference to the changed/removed API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | C5 | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.AdicConstructibilityPredicateComparison | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.CoefficientHeart | D6 | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.CoefficientHeartFiltration | T8 | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.CondensedBoundedHomContinuity | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | G6 | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | W6 | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | S4 | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | T9 | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | W7 | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.IntegralModels | U1 | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.IntegralModelsOperations | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | K6 | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.InternalHomDualConstructibleModels | P1 | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.ScalarModelImmersionExtension | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Z7 | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | K2 | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.StratifiedLatticeRank | D2 | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | Z6 | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.TraceBaseChangeFirst | V9 | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.SixFunctors.BrownHypothesesSmall | A6 | No reference to the changed/removed API; no adaptation. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | A7 | No reference to the changed/removed API; no adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | No reference to the changed/removed API; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | W8 | No reference to the changed/removed API; no adaptation. |
| Sheaf.Paper.CartesianCoefficients | N3 | Reuse normalized signed comparisons; complete final assembly. |

## Status

landed 20261021T163817-L-1103184 2026-10-21 (merge of deliver/N3/Sheaf.Paper.CartesianCoefficients)
