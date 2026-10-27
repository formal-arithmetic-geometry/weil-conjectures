# AlgebraicGeometry.ProEtale.AffineOrderedIntegration.integrationTranspose

## Reason

Isolate the independently constructed integration maps from the theorem comparing them
with the ordered recursion. The successor calculation must be an independently provable
step which imports these constructions without importing its parent theorem. This is a
dependency separation for the proof, not a compile-time split. The original construction
prefix already compiles within the per-file limit. Every moved declaration keeps its
name, universe parameters, signature, visibility, attributes and body verbatim.
The original module publicly imports AffineOrderedIntegrationData, retaining its former
public imports as well. No consumer's statement, proof or object construction changes.
Targets using the definitions see the same constructions, so this relocation introduces
no semantic target-definition change. The independent reader should compare the moved
prefix and compile representative consumers.

## Old

In lean/Sheaf/Paper/AffineOrderedIntegrationTransposes.lean, the complete construction
prefix was the following (all public and private declarations are included to make the
verbatim relocation reviewable):

```lean
/-- Cache the published derived category structure in fixed scalar coordinates.
Source: small pro-etale derived category
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
instance proCategory (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Category.{u + 1} (C A T) := inferInstanceAs (Category (DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))))

/-- Cache the published ordinary derived category structure in fixed scalar coordinates.
Source: small etale derived category
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
instance etaleCategory (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Category.{u + 1} (Etale.DerivedCategoryModule A T) := inferInstanceAs (Category
      (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))))

/-- The specified exponent, with no divisibility condition on the positive level.
Source: finite Tate realization (blueprint: lem-pur-affine-ordered-integration-transposes). -/
abbrev exponent (P : WeilConjectures.PurityFiniteSetting.{u}) : ℕ :=
  P.coefficients.l ^ (P.level + 1)

/-- The canonical normalized projective-line Tate transport, not an orientation choice.
Source: def-amb-p1-trace (blueprint: lem-pur-affine-ordered-integration-transposes). -/
def transport (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Etale.OrdinaryFiniteTwistTransport (AffineLinePurity.Ring P) (exponent P) (annihilates P) :=
  Etale.projectiveLineTraceTransport (exponent P)
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (AffineLinePurity.Ring P) (annihilates P)

/-- The normalized projective-line datum whose trace is the specified second projection.
Source: def-amb-p1-trace (blueprint: lem-pur-affine-ordered-integration-transposes). -/
def projectiveDatum (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (exponent P : Γ(T, ⊤))) :
    Etale.OrdinaryFiniteP1Datum (AffineLinePurity.Ring P) (exponent P) (annihilates P) (transport
      P) T hT :=
  Etale.projectiveLineTraceDatum (exponent P)
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (AffineLinePurity.Ring P) (annihilates P)
      T hT

/-- The ordered ordinary adjunction, with identity adjunction at zero coordinates.
Source: lem-amb-affine-space-top-trace
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def orderedAdjunction (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ) :
    Etale.affineTraceLeft (AffineLinePurity.Ring P) Y d ⊣
      Etale.affineTraceRight (AffineLinePurity.Ring P) (exponent P) (annihilates P) Y d :=
  Etale.affineTraceAdjunction (AffineLinePurity.Ring P) (exponent P) (annihilates P)
    (transport P) (projectiveDatum P) Y (exponentUnit P Y aY) d

/-- A_X(d)[2d], using the existing ordered finite Tate coefficient on X itself.
Source: finite twist convention (blueprint: lem-pur-affine-ordered-integration-transposes). -/
def etaleCoefficient (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (d : ℕ) :
    Etale.DerivedCategoryModule (AffineLinePurity.Ring P) (iteratedAffineLine Y d) :=
  Etale.affineLinearBaseCoefficient (AffineLinePurity.Ring P) (exponent P) (annihilates P)
    (iteratedAffineLine Y d) d

/-- Its canonical realization on the small pro-etale site.
Source: lem-pur-vector-integration-site-comparison
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def coefficient (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (d : ℕ) : D P (iteratedAffineLine Y d) :=
  (comparison (AffineLinePurity.Ring P) (iteratedAffineLine Y d)).obj (etaleCoefficient P Y d)

/-- Canonical comparison from the ordered ordinary constant-input source to A_X(d)[2d].
Only normalized Tate pullback and tensor reassociations occur.
Source: ordered trivial-frame trace (blueprint: lem-pur-affine-ordered-integration-transposes).
-/
def coefficientComparison (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ) :
    (Etale.affineTraceRight (AffineLinePurity.Ring P) (exponent P) (annihilates P) Y d).obj
      (Etale.ordinaryFiniteUnit (AffineLinePurity.Ring P) Y) ≅
        Etale.affineLinearBaseCoefficient (AffineLinePurity.Ring P) (exponent P) (annihilates P)
          (affineTraceTower Y d) d :=
  Etale.affineLinearCoefficientDescent (AffineLinePurity.Ring P) (exponent P) (annihilates P)
    (transport P) Y (exponentUnit P Y aY) d ≪≫
  Etale.vectorIntegrationBaseCoefficientPullback (AffineLinePurity.Ring P) (exponent P)
    (annihilates P)
    (transport P) (affineTraceProjection Y d) (exponentUnit P Y aY) d

/-- The actual ordinary trace on the coordinate projection. The first map changes
only coefficient coordinates; the second is the normalized proper/open tower compositor.
Source: lem-amb-affine-space-top-trace and the trivial-frame definition of integration
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def ordinaryTraceRaw (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ) :=
  (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
    (affineTraceProjection Y d)).map (coefficientComparison P Y aY d).inv ≫
  (Etale.affineLinearCompactComparison (exponent P)
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (AffineLinePurity.Ring P) (annihilates P)
    Y (exponentUnit P Y aY) d).inv ≫
  (orderedAdjunction P Y aY d).counit.app (Etale.ordinaryFiniteUnit (AffineLinePurity.Ring P) Y)

/-- Standing ordinary compact support in the normalized coordinate model.
Source: compact-support convention
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def ordinaryLower (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u}) (d : ℕ) :=
  letI := (projection_geometry Y d).2
  Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
    (iteratedAffineLineProj Y d)

attribute [local irreducible] Etale.rightDerivedLowerShriek
  Etale.affineLinearBaseCoefficient in
/-- The computed ordinary trace has the stated projection and coefficient endpoints.
The equality is only transport between the two identical recursive affine-line models.
Source: coordinate normalization
(blueprint: lem-pur-affine-ordered-integration-transposes).
Proof: induct on d. At zero both schemes and projections are identity. At a successor
both constructions apply AffineSpace PUnit to the preceding scheme and compose its
projection with the preceding projection. Induction identifies the schemes and arrows.
Finite Tate coefficients are the same ordered tensor recursion. The HasCompactification
instances are proofs, hence proof-irrelevant; their standing functors therefore agree
under this transport. The raw trace now has exactly the displayed endpoints. Transport
it along these equalities. HEq determines the transported map uniquely. -/
theorem ordinaryTrace_existsUnique (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ) :
    ∃! t : (ordinaryLower P Y d).obj (etaleCoefficient P Y d) ⟶
        Etale.ordinaryFiniteUnit (AffineLinePurity.Ring P) Y,
      HEq t (ordinaryTraceRaw P Y aY d) := by
  unfold ordinaryLower etaleCoefficient
  have hp : (⟨affineTraceTower Y d, affineTraceProjection Y d⟩ : Σ X : Scheme.{u}, X ⟶ Y) =
      ⟨iteratedAffineLine Y d, iteratedAffineLineProj Y d⟩ := by
    induction d with
    | zero => rfl
    | succ d ih =>
      exact congrArg (fun q : Σ X : Scheme.{u}, X ⟶ Y ↦
        (⟨AffineSpace PUnit.{u + 1} q.1,
          (AffineSpace PUnit.{u + 1} q.1 ↘ q.1) ≫ q.2⟩ : Σ X : Scheme.{u}, X ⟶ Y)) ih
  let W := fun X : Scheme.{u} ↦ Etale.affineLinearBaseCoefficient
    (AffineLinePurity.Ring P) (exponent P) (annihilates P) X d
  let typ := fun q : {q : Σ X : Scheme.{u}, X ⟶ Y // HasCompactification q.2} ↦
    letI := q.property
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (AffineLinePurity.Ring P)) q.val.2).obj
      (W q.val.1) ⟶ Etale.ordinaryFiniteUnit (AffineLinePurity.Ring P) Y
  have ht : typ ⟨⟨affineTraceTower Y d, affineTraceProjection Y d⟩, inferInstance⟩ =
      typ ⟨⟨iteratedAffineLine Y d, iteratedAffineLineProj Y d⟩,
        (projection_geometry Y d).2⟩ := by
    exact congrArg typ (Subtype.ext hp)
  refine ⟨cast ht (ordinaryTraceRaw P Y aY d), cast_heq ht _, ?_⟩
  intro t ht'
  exact eq_of_heq (ht'.trans (cast_heq ht _).symm)

/-- The uniquely transported actual ordered counit trace. The HEq characterization
fixes the map itself; it does not choose an unspecified orientation or isomorphism.
Source: canonical coordinate transport
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def ordinaryTrace (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ) :=
  (ordinaryTrace_existsUnique P Y aY d).exists.choose

private theorem flat_tensor_shift_plus
    {B : Type*} [Category B] [Abelian B] [IsGrothendieckAbelian B]
    [HasDerivedCategory B] [MonoidalCategory B] [MonoidalPreadditive B]
    [BraidedCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (L : B) (hL : ObjectProperty.flat L) (K : DerivedCategory B)
    (hK : DerivedCategory.TStructure.t.plus K) :
    DerivedCategory.TStructure.t.plus
      (K ⊗ ((DerivedCategory.singleFunctor B 0).obj L)⟦(2 : ℤ)⟧) := by
  let := Classical.choice (DerivedCategory.nonempty_braidedCategory B)
  obtain ⟨a, ha⟩ := hK
  have : K.IsGE a := ha
  let S := (DerivedCategory.singleFunctor B 0).obj L
  have ht := DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hL
  have : (S ⊗ K).IsGE (0 + a) :=
    DerivedCategory.isGE_tensor_of_torAmplitudeIn ht K a
  have hs : DerivedCategory.TStructure.t.plus ((S ⊗ K)⟦(2 : ℤ)⟧) :=
    ⟨0 + a - 2, DerivedCategory.TStructure.t.isGE_shift _ (0 + a) 2
      (0 + a - 2) (by omega)⟩
  have hs' : DerivedCategory.TStructure.t.plus (S⟦(2 : ℤ)⟧ ⊗ K) :=
    DerivedCategory.TStructure.t.plus.prop_of_iso
      (((MonoidalCategory.tensorRight K).commShiftIso (2 : ℤ)).app S).symm hs
  exact DerivedCategory.TStructure.t.plus.prop_of_iso (β_ _ _) hs'

private theorem tensor_plus_of_tor
    (B : Type v) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u}) (K W : DerivedCategory (Sheaf X.smallEtaleTopology B))
    {a b : ℤ} (ht : Etale.DerivedCategory.torAmplitudeIn B X a b K)
    (hW : DerivedCategory.TStructure.t.plus W) :
    DerivedCategory.TStructure.t.plus (((Etale.derivedTensor B X).obj K).obj W) := by
  obtain ⟨c, hc⟩ := hW
  have : W.IsGE c := hc
  exact ⟨a + c, DerivedCategory.isGE_tensor_of_torAmplitudeIn ht W c⟩

private theorem flat_unit (B : Type*) [Category B] [Abelian B]
    [MonoidalCategory B] [MonoidalPreadditive B] [BraidedCategory B] :
    ObjectProperty.flat (𝟙_ B) :=
  ObjectProperty.flat_of_tensorIso (λ_ (𝟙_ B))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorLine_plus (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) (K : Etale.DerivedCategoryModule A T)
    (hK : DerivedCategory.TStructure.t.plus K) :
    DerivedCategory.TStructure.t.plus
      ((Etale.derivedTensorRight (ModuleCat.{u + 1} A) T
        ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)).obj K) := by
  let L := Scheme.finiteEtaleTateLine T N A hA
  have hInv : ∀ x : T, IsUnit (N : T.presheaf.stalk x) := fun x ↦ by
    simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ x (by trivial)).hom
  have hf : ObjectProperty.flat L :=
    (ObjectProperty.flat_iff_preservesFiniteLimits _).2
      (Scheme.finite_etale_torsion_twist_line T N hN hInv A hA 1).2.2.1
  exact flat_tensor_shift_plus L hf K hK

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullback_plus (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : Etale.DerivedCategoryModule A Y)
    (hK : DerivedCategory.TStructure.t.plus K) :
    DerivedCategory.TStructure.t.plus ((Etale.ordinaryFinitePullback A f).obj K) := by
  exact DerivedCategory.TStructure.t.plus.prop_of_iso
    ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).app K).symm
    (((Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus.obj ⟨K, hK⟩).property)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

/-- The finite Tate coefficient is bounded below.
Source: finite Tate lines (blueprint: lem-pur-affine-ordered-integration-transposes).
Proof: the zero coefficient is the constant sheaf in degree zero. Each successor tensors
with a locally free degree-zero Tate line and shifts by two. Induction gives the single
sheaf A(d) shifted by 2d; this also applies on the empty scheme. -/
theorem coefficient_plus_on_base (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ) :
    DerivedCategory.TStructure.t.plus (etaleCoefficient P Y d) := by
  let T := iteratedAffineLine Y d
  have hT := affineTracePullbackInvertible (exponent P)
    (iteratedAffineLineProj Y d) (exponentUnit P Y aY)
  have h : ∀ n, DerivedCategory.TStructure.t.plus
      (Etale.affineLinearBaseCoefficient (AffineLinePurity.Ring P) (exponent P)
        (annihilates P) T n) := by
    intro n
    induction n with
    | zero =>
      change DerivedCategory.TStructure.t.plus (Etale.ordinaryFiniteUnit _ T)
      exact ⟨0, inferInstance⟩
    | succ n ih =>
      exact tensorLine_plus _ _ (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
        _ T hT _ ih
  exact h d

/-- The chosen compactification used by the standing functor, with no replacement map.
Source: def-compact-support-direct-image-detailed
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def compactification (Y : Scheme.{u}) (d : ℕ) :
    Compactification (iteratedAffineLineProj Y d) :=
  letI := (projection_geometry Y d).2
  HasCompactification.compactification (iteratedAffineLineProj Y d)

/-- Canonical realization of a given ordinary trace through the proper/open site map.
Source: compact support site comparison
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def realizeTrace (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    (c : Compactification f) (W : Etale.DerivedCategoryModule A X)
    (hW : DerivedCategory.TStructure.t.plus W)
    (t : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W ⟶
      Etale.ordinaryFiniteUnit A Y) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
      ((comparison A X).obj W) ⟶ unit A Y :=
  (compactSupportSiteComparison A c).hom.app ⟨W, hW⟩ ≫
    (comparison A Y).map
      ((Etale.rightDerivedLowerShriekIso A c).hom.app W ≫ t)

/-- The vector integration in the trivial frame, realized by the specified site comparison.
Its ordinary source trace is the ordered adjunction counit.
Source: def-amb-vector-integration and lem-pur-vector-integration-site-comparison
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def integration (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
      (compactification Y d)).obj (coefficient P Y d) ⟶ unit (AffineLinePurity.Ring P) Y :=
  letI := (projection_geometry Y d).2
  realizeTrace (AffineLinePurity.Ring P) (iteratedAffineLineProj Y d) (compactification Y d)
    (etaleCoefficient P Y d) (coefficient_plus_on_base P Y aY d) (ordinaryTrace P Y aY d)

/-- Canonical tensor reassociation, after caching the actual finite-scalar tensor.
Source: finite tensor associator (blueprint: lem-pur-affine-ordered-integration-transposes). -/
def reassociate (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (K L M : C A T) :
    ((tensor A T).obj (((tensor A T).obj K).obj L)).obj M ≅
      ((tensor A T).obj K).obj (((tensor A T).obj L).obj M) :=
  ProEtale.projectionActionAssociator (ModuleCat.{u + 1} A) T K L M

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Canonical tensor-action reassociation in fixed coefficient coordinates.
Source: ordered tensor powers
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def coefficientActionComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u}) (K : C A T) : (d : ℕ) →
    ((tensor A T).obj K).obj
      ((comparison A T).obj (Etale.affineLinearBaseCoefficient A N hA T d)) ≅
      (action ((tensor A T).flip.obj
        ((comparison A T).obj ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧))) d).obj K
  | 0 => AffineLinePurity.moduleRightUnit A T K
  | d + 1 =>
    ((tensor A T).obj K).mapIso
      (tensorComparison A T (Etale.affineLinearBaseCoefficient A N hA T d)
        ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)) ≪≫
    (reassociate A T K _ _).symm ≪≫
    tensorIso A T (coefficientActionComparison A N hA T K d) (Iso.refl _)

/-- The identity-pullback coefficient source comparison in cached scalar coordinates.
Source: rank-zero normalization
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def zeroSourceComparison (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u}) (K : C A Y) :
    K ≅ ((tensor A Y).obj ((inverseImage A (𝟙 Y)).obj K)).obj (unit A Y) :=
  (AffineLinePurity.moduleRightUnit A Y K).symm ≪≫
    tensorIso A Y ((inverseImageId A Y).app K).symm (Iso.refl _)

/-- Explicit source-coordinate isomorphism before endpoint normalization.
Source: canonical coefficient reassociation, including the rank-zero right unitor
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def sourceComparisonRaw (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (K : D P Y) : (d : ℕ) →
    Σ M N : D P (iteratedAffineLine Y d), M ≅ N
  | 0 => ⟨_, _, zeroSourceComparison (AffineLinePurity.Ring P) Y K⟩
  | d + 1 => ⟨_, _, (coefficientActionComparison (AffineLinePurity.Ring P) (exponent P)
    (annihilates P)
      (iteratedAffineLine Y (d + 1))
      ((inverseImage (AffineLinePurity.Ring P) (iteratedAffineLineProj Y (d + 1))).obj K)
      (d + 1)).symm⟩

private theorem isoHEq_existsUnique {Cat : Type*} [Category Cat]
    {K L : Cat} (e : K ≅ L) : ∃! e' : K ≅ L, HEq e'.hom e.hom :=
  ⟨e, HEq.rfl, fun _ he ↦ Iso.ext (eq_of_heq he)⟩

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- The explicit source-coordinate map has the recorded ordered-source endpoints.
Source: endpoint normalization
(blueprint: lem-pur-affine-ordered-integration-transposes).
Proof: split d into zero or a successor. At zero unfold the identity source and the
zero coefficient, and use the literal inverse-image identity comparison and right unitor.
At a successor unfold orderedSource and projectionSourceObject; coefficientActionComparison has
exactly those endpoints. Transport the raw isomorphism along these definitional
equalities. Its hom determines the isomorphism uniquely. -/
theorem sourceComparison_existsUnique (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (K : D P Y) (d : ℕ) :
    ∃! e : (orderedSource P Y d).obj K ≅
      AffineLinePurity.projectionSourceObject (AffineLinePurity.Ring P) (iteratedAffineLineProj Y d)
        (coefficient P Y d) K,
      HEq e.hom (sourceComparisonRaw P Y K d).2.2.hom := by
  cases d with
  | zero =>
    unfold orderedSource AffineLinePurity.projectionSourceObject
    dsimp only [coefficient, etaleCoefficient, shiftedLine, inverseImage,
      AffineSpacePurity.tensor, Functor.comp_obj, exponent]
    exact isoHEq_existsUnique (sourceComparisonRaw P Y K 0).2.2
  | succ d =>
    unfold orderedSource AffineLinePurity.projectionSourceObject
    dsimp only [coefficient, etaleCoefficient, shiftedLine, inverseImage,
      AffineSpacePurity.tensor, Functor.comp_obj, exponent]
    unfold twistAction
    dsimp only [shiftedLine, Functor.comp_obj]
    exact isoHEq_existsUnique (sourceComparisonRaw P Y K (d + 1)).2.2

/-- The canonical source-coordinate isomorphism, with its map fixed by the explicit
raw construction. Source: Lp_d*K(d)[2d]
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def sourceComparison (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (K : D P Y) (d : ℕ) :
    (orderedSource P Y d).obj K ≅
      AffineLinePurity.projectionSourceObject (AffineLinePurity.Ring P) (iteratedAffineLineProj Y d)
        (coefficient P Y d) K :=
  (sourceComparison_existsUnique P Y K d).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

private theorem tensorSource_origin (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : C A Y)
    (Ke : Etale.DerivedCategoryModule A Y) (W : Etale.DerivedCategoryModule A X)
    (hp : etaleFiniteTor A Y Ke)
    (hW : DerivedCategory.TStructure.t.plus W)
    (eK : (comparison A Y).obj Ke ≅ K) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X
      (AffineLinePurity.projectionSourceObject A f ((comparison A X).obj W) K) := by
  obtain ⟨a, b, ht⟩ :=
    (Etale.constructibleFiniteTor_leftDerivedUpperStar (ModuleCat.{u + 1} A) f hp).2
  have hs : DerivedCategory.TStructure.t.plus
      (AffineLinePurity.ordinarySourceObject A f W Ke) := by
    unfold AffineLinePurity.ordinarySourceObject
    exact tensor_plus_of_tor (ModuleCat.{u + 1} A) X _ W ht hW
  have e := AffineLinePurity.realizedTensorComparison A f K Ke W eK
  unfold AffineLinePurity.proSourceObject at e
  exact (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).prop_of_iso
    e (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj hs)

/-- The source has a bounded-below etale origin, which is an applicability conclusion.
Source: coordinate finite-Tor input and lem-sf-pullback-tor-amplitude
(blueprint: lem-pur-affine-ordered-integration-transposes).
Proof: use the ordinary source Ke pulled back along p_d and tensor it with the explicit
finite Tate coefficient. Its lower bound follows from the finite Tor interval of Ke.
The canonical pullback/tensor comparison and eK identify its realization with the stated
source. Exact comparison preserves the lower bound and gives the etale-origin witness. -/
theorem source_origin (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y) (Ke : Etale.DerivedCategoryModule
      (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
      (iteratedAffineLine Y d)
      (AffineLinePurity.projectionSourceObject (AffineLinePurity.Ring P) (iteratedAffineLineProj Y
        d)
        (coefficient P Y d) K.obj) := by
  exact tensorSource_origin (AffineLinePurity.Ring P) (iteratedAffineLineProj Y d)
    K.obj Ke (etaleCoefficient P Y d)
    hKe (coefficient_plus_on_base P Y aY d) eK

section GenericCoefficient
variable (B : Type v) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  [HasSmallSiteSheafify B]
  {FB : B → B → Type (u + 1)} {CB : B → Type (u + 1)}
  [∀ X Y, FunLike (FB X Y) (CB X) (CB Y)] [ConcreteCategory.{u + 1} B FB]
  [PreservesFiniteLimits (forget B)] [PreservesFilteredColimitsOfSize.{u, u} (forget B)]

omit [PreservesFilteredColimitsOfSize.{u, u} (forget B)] in
private theorem flatSingle_ctf (T : Scheme.{u})
    (L : Sheaf T.smallEtaleTopology B) [Scheme.IsConstructibleSheaf L]
    (hf : ObjectProperty.flat L) :
    Etale.DerivedCategory.constructibleFiniteTor B T
      ((DerivedCategory.singleFunctor _ 0).obj L) :=
  ⟨Etale.DerivedCategory.boundedConstructible_singleFunctor_obj L 0,
    0, 0, Etale.torAmplitudeIn_singleFunctor_zero_of_flat B L hf⟩

omit [HasSmallSiteSheafify B] [PreservesFiniteLimits (forget B)]
  [PreservesFilteredColimitsOfSize.{u, u} (forget B)] in
private theorem ctf_shift (T : Scheme.{u})
    (L : DerivedCategory (Sheaf T.smallEtaleTopology B))
    (hL : Etale.DerivedCategory.constructibleFiniteTor B T L) (n : ℤ) :
    Etale.DerivedCategory.constructibleFiniteTor B T (L⟦n⟧) := by
  obtain ⟨hbc, a, b, ht⟩ := hL
  exact ⟨(Etale.DerivedCategory.boundedConstructible B T).le_shift n _ hbc,
    a - n, b - n, Etale.torAmplitudeIn_shift B ht n⟩

omit [Abelian.HasFunctorialFlatResolution B] [HasSmallSiteSheafify B] in
private theorem constantUnit_flat (T : Scheme.{u}) :
    ObjectProperty.flat ((constantSheaf T.smallEtaleTopology B).obj (𝟙_ B)) :=
  ObjectProperty.flat.prop_of_iso (Functor.Monoidal.εIso
    (constantSheaf T.smallEtaleTopology B)).symm
    (flat_unit (Sheaf T.smallEtaleTopology B))

omit [PreservesFilteredColimitsOfSize.{u, u} (forget B)] in
private theorem constantUnit_ctf (T : Scheme.{u})
    [Scheme.IsConstructibleSheaf ((constantSheaf T.smallEtaleTopology B).obj (𝟙_ B))] :
    Etale.DerivedCategory.constructibleFiniteTor B T
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf T.smallEtaleTopology B).obj (𝟙_ B))) :=
  flatSingle_ctf B T _ (constantUnit_flat B T)

end GenericCoefficient

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem shiftedLine_ctf (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) :
    etaleFiniteTor A T ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) := by
  let L := Scheme.finiteEtaleTateLine T N A hA
  have hInv : ∀ x : T, IsUnit (N : T.presheaf.stalk x) := fun x ↦ by
    simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ x (by trivial)).hom
  have hLine := Scheme.finite_etale_torsion_twist_line T N hN hInv A hA 1
  obtain ⟨cover, hcover⟩ := hLine.1
  have : Scheme.IsFiniteLocallyConstantSheaf L := by
    apply (Scheme.finite_locally_constant_module_values_iff L).1.1
    refine ⟨⟨cover, fun i ↦ ?_⟩, fun i ↦ ⟨ModuleCat.of A A, inferInstance, hcover i⟩⟩
    obtain ⟨e⟩ := hcover i
    exact Sheaf.isConstant_of_iso _ e
  have : Scheme.IsConstructibleSheaf L :=
    Scheme.IsFiniteLocallyConstantSheaf.isConstructibleSheaf inferInstance
  have hf : ObjectProperty.flat L :=
    (ObjectProperty.flat_iff_preservesFiniteLimits _).2 hLine.2.2.1
  exact ctf_shift (ModuleCat.{u + 1} A) T _
    (flatSingle_ctf (ModuleCat.{u + 1} A) T L hf) 2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem baseCoefficient_ctf (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) :
    etaleFiniteTor A T (Etale.affineLinearBaseCoefficient A N hA T d) := by
  have hL := shiftedLine_ctf A N hN hA T hT
  induction d with
  | zero =>
    change etaleFiniteTor A T (Etale.ordinaryFiniteUnit A T)
    have : Scheme.IsConstructibleSheaf (Etale.ordinaryFiniteConstant A T) :=
      Scheme.isConstructibleSheaf_constantSheaf (ModuleCat.of A A)
    exact constantUnit_ctf (ModuleCat.{u + 1} A) T
  | succ d ih => exact Etale.constructibleFiniteTor_tensor A T ih hL

attribute [local irreducible] projectionMapOfCompactification

private theorem reorderedProjection_isIso
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {X Z : Scheme.{u}} {f : X ⟶ Z} (c : Compactification f)
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) B))
    (h : IsIso (((projectionMapOfCompactification B c).app F).app K)) :
    IsIso (projection B c F K) := by
  have h₁ : IsIso (((symmetry B Z).hom.app K).app
      ((rightDerivedLowerShriekOfCompactification B c).obj F)) :=
    (((symmetry B Z).app K).app _).isIso_hom
  have h₂ : IsIso ((rightDerivedLowerShriekOfCompactification B c).map
      (((symmetry B X).hom.app F).app ((upperStar B f).leftDerivedFunctor.obj K))) :=
    ((rightDerivedLowerShriekOfCompactification B c).mapIso
      (((symmetry B X).app F).app _)).isIso_hom
  unfold projection
  exact IsIso.comp_isIso' h₁ (IsIso.comp_isIso' h h₂)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem projectionFromOrigin_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} {f : X ⟶ Z} (c : Compactification f)
    (W : Etale.DerivedCategoryModule A X) (hW : DerivedCategory.TStructure.t.bounded W)
    (K : C A Z) (Ke : Etale.DerivedCategoryModule A Z)
    (hKe : etaleFiniteTor A Z Ke) (eK : (comparison A Z).obj Ke ≅ K) :
    IsIso (projection (ModuleCat.{u + 1} A) c ((comparison A X).obj W) K) := by
  obtain ⟨a, b, hTor⟩ := hKe.2
  have hM := (Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} A) c.i).bounded_mapDerivedCategory_obj hW
  have hML := Etale.plus_derivedTensor_leftDerivedUpperStar c.g hM hTor
  have := Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite A c.g
  have hPF := hasProjectionFormulaOfCompactification_of_comparison c
    (Iso.refl ((comparison A X).obj W)) eK hW hML inferInstance
  exact reorderedProjection_isIso (ModuleCat.{u + 1} A) c _ K hPF

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

/-- Invertibility of the actual symmetry-adjusted compactification projection.
Source: finite projection formula on the stated coordinate inputs
(blueprint: lem-pur-affine-ordered-integration-transposes).
Proof: the coefficient is a bounded finite locally free Tate complex. The comparison
origin of Ke gives the stated constructible finite-Tor coefficient. Apply the finite
compact-support projection formula at the specified compactification, and insert the
two canonical tensor symmetries. No ambient pro-etale projection isomorphism is assumed. -/
theorem projection_isIso (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y) (Ke : Etale.DerivedCategoryModule
      (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    ProjectionInvertible (AffineLinePurity.Ring P) (compactification Y d) (coefficient P Y d)
      K.obj := by
  have hW := baseCoefficient_ctf (AffineLinePurity.Ring P) (exponent P)
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
    (iteratedAffineLine Y d)
    (affineTracePullbackInvertible (exponent P) (iteratedAffineLineProj Y d)
      (exponentUnit P Y aY)) d
  unfold ProjectionInvertible
  exact projectionFromOrigin_isIso (AffineLinePurity.Ring P) (compactification Y d)
    (etaleCoefficient P Y d) hW.1.1 K.obj Ke hKe eK

/-- The coefficient integration (1_K tensor t_p) Pi, with the canonical right unitor.
Source: displayed counit formula
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def augmentation (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y) (Ke : Etale.DerivedCategoryModule
      (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :=
  letI : IsNoetherian Y := tower_noetherian P Y aY 0
  projectionTensorTrace (AffineLinePurity.Ring P) (compactification Y d) (coefficient P Y d) K.obj
    (integration P Y aY d) (projection_isIso P Y aY K Ke hKe eK d)

/-- The specified exceptional transpose with the standing compactification made explicit.
Source: restricted exceptional Hom correspondence
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def standingTranspose (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    [QuasiCompact f] [CompactSpace Y]
    (M : C A X) (K : C A Y)
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M)
    (hK : boundedBelow A Y K)
    (z : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (HasCompactification.compactification f)).obj M ⟶ K) :
    M ⟶ (rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K :=
  rightDerivedUpperShriekHomEquiv f hM hK z

/-- The actual integration transpose before the exceptional endpoint normalization.
Source: definition of P, the specified restricted exceptional Hom bijection
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def integrationTransposeRaw (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y) (Ke : Etale.DerivedCategoryModule
      (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) :
    (d : ℕ) → Σ M N : D P (iteratedAffineLine Y d), M ⟶ N
  | 0 => ⟨_, _, 𝟙 K.obj⟩
  | d + 1 =>
    letI := (projection_geometry Y (d + 1)).1
    letI := (projection_geometry Y (d + 1)).2
    letI : IsNoetherian Y := tower_noetherian P Y aY 0
    ⟨_, _, (sourceComparison P Y K.obj (d + 1)).hom ≫
      standingTranspose (AffineLinePurity.Ring P) (iteratedAffineLineProj Y (d + 1))
        _ K.obj (source_origin P Y aY K Ke hKe eK (d + 1)) K.property
        (augmentation P Y aY K Ke hKe eK (d + 1))⟩

private theorem homHEq_existsUnique {Cat : Type*} [Category Cat]
    {K L : Cat} (f : K ⟶ L) : ∃! g : K ⟶ L, HEq g f :=
  ⟨f, HEq.rfl, fun _ hg ↦ eq_of_heq hg⟩

/-- This exact transpose has the recorded exceptional comparison endpoints.
Source: normalized standing exceptional functor
(blueprint: lem-pur-affine-ordered-integration-transposes).
Proof: at zero both functors are normalized to identity. At a positive stage unfold
ComparisonHom and exceptional at the outer successor. The specified restricted Hom
bijection has exactly this standing exceptional target, while sourceComparison has
exactly the ordered source. Proof irrelevance identifies compactifiability witnesses.
Transport the computed arrow along these endpoint equalities. HEq fixes it uniquely. -/
theorem integrationTranspose_existsUnique (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y) (Ke : Etale.DerivedCategoryModule
      (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    ∃! p : ComparisonHom P Y K.obj d,
      HEq p (integrationTransposeRaw P Y aY K Ke hKe eK d).2.2 := by
  cases d with
  | zero =>
    unfold ComparisonHom orderedSource exceptional
    exact homHEq_existsUnique (𝟙 K.obj)
  | succ d =>
    unfold ComparisonHom exceptional
    exact homHEq_existsUnique (integrationTransposeRaw P Y aY K Ke hKe eK (d + 1)).2.2

/-- The integration transpose, with its map fixed by the independent integration
construction. Source: P_(p_d,K)
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
@[irreducible]
def integrationTranspose (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y) (Ke : Etale.DerivedCategoryModule
      (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    ComparisonHom P Y K.obj d :=
  (integrationTranspose_existsUnique P Y aY K Ke hKe eK d).exists.choose

/-- The explicit ordinary tensor-source representative of Lp_d*K(d)[2d].
Source: bounded etale origin (blueprint: lem-pur-affine-ordered-integration-transposes). -/
def sourceEtale (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y) (d : ℕ) :=
  AffineLinePurity.ordinarySourceObject (AffineLinePurity.Ring P) (iteratedAffineLineProj Y d)
    (etaleCoefficient P Y d) Ke

attribute [local semireducible] AffineLinePurity.proSourceObject

/-- The ordinary tensor source realizes to the literal pro-etale tensor source.
Source: canonical pullback/tensor comparison
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def realizeTensorSource (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : C A Y)
    (Ke : Etale.DerivedCategoryModule A Y) (W : Etale.DerivedCategoryModule A X)
    (eK : (comparison A Y).obj Ke ≅ K) :
    (comparison A X).obj (AffineLinePurity.ordinarySourceObject A f W Ke) ≅
      AffineLinePurity.projectionSourceObject A f ((comparison A X).obj W) K := by
  exact AffineLinePurity.realizedTensorComparison A f K Ke W eK

/-- Its canonical realization, using the actual tensor/pullback comparison and eK.
Source: site source normalization
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def sourceRealization (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (K : D P Y) (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K) (d : ℕ) :=
  realizeTensorSource (AffineLinePurity.Ring P) (iteratedAffineLineProj Y d)
    K Ke (etaleCoefficient P Y d) eK ≪≫ (sourceComparison P Y K d).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

/-- Both coordinate sources retain the bounded constructible finite-Tor domain.
Source: pullback and tensor finite-Tor preservation
(blueprint: lem-pur-affine-ordered-integration-transposes).
Proof: pullback preserves the bounds and the finite Tor interval of Ke. The coefficient
is locally free of rank one shifted by 2d. Tensoring translates the two intervals;
comparison identifies the result with the ordered source by sourceRealization. -/
theorem source_applicability (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y) (Ke : Etale.DerivedCategoryModule
      (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    boundedBelow (AffineLinePurity.Ring P) (iteratedAffineLine Y d) ((orderedSource P Y d).obj
      K.obj) ∧
      etaleFiniteTor (AffineLinePurity.Ring P) (iteratedAffineLine Y d) (sourceEtale P Y Ke d) := by
  let A := AffineLinePurity.Ring P
  let f := iteratedAffineLineProj Y d
  have ht := baseCoefficient_ctf A (exponent P)
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
    (iteratedAffineLine Y d)
    (affineTracePullbackInvertible (exponent P) f (exponentUnit P Y aY)) d
  have hs : etaleFiniteTor A (iteratedAffineLine Y d) (sourceEtale P Y Ke d) := by
    unfold sourceEtale AffineLinePurity.ordinarySourceObject
    exact Etale.constructibleFiniteTor_tensor A _
      (Etale.constructibleFiniteTor_leftDerivedUpperStar (ModuleCat.{u + 1} A) f hKe) ht
  refine ⟨?_, hs⟩
  exact (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) _).prop_of_iso
    (sourceComparison P Y K.obj d).symm (source_origin P Y aY K Ke hKe eK d) |>.plus

/-- Gamma_q at the actual exceptional input Rp_d!K, with its retained canonical origin.
Source: the displayed recursion (blueprint: lem-pur-affine-ordered-integration-transposes). -/
def exceptionalLine (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y) (Ke : Etale.DerivedCategoryModule
      (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :=
  letI : LocallyOfFiniteType (towerBase aY d) := (tower_geometry aY d).1
  letI : QuasiCompact (towerBase aY d) := (tower_geometry aY d).2.1
  letI : IsSeparated (towerBase aY d) := (tower_geometry aY d).2.2
  lineComparison P (iteratedAffineLine Y d) (towerBase aY d)
    ⟨(exceptional P Y d).obj K.obj, (stage_applicability P Y aY K Ke hKe eK d).1⟩
    (stageEtale P Y K.obj Ke d) (stage_applicability P Y aY K Ke hKe eK d).2
    (stageComparison P Y K.obj Ke eK d)

/-- Gamma_q at G_dK, with the canonical tensor-source etale representative.
Source: the naturality square (blueprint: lem-pur-affine-ordered-integration-transposes). -/
def sourceLine (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y) (Ke : Etale.DerivedCategoryModule
      (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :=
  letI : LocallyOfFiniteType (towerBase aY d) := (tower_geometry aY d).1
  letI : QuasiCompact (towerBase aY d) := (tower_geometry aY d).2.1
  letI : IsSeparated (towerBase aY d) := (tower_geometry aY d).2.2
  lineComparison P (iteratedAffineLine Y d) (towerBase aY d)
    ⟨(orderedSource P Y d).obj K.obj, (source_applicability P Y aY K Ke hKe eK d).1⟩
    (sourceEtale P Y Ke d) (source_applicability P Y aY K Ke hKe eK d).2
    (sourceRealization P Y K.obj Ke eK d)
```

## New

The exact same declaration block is in
lean/Sheaf/Paper/AffineOrderedIntegrationData.lean:

```lean
/-- Cache the published derived category structure in fixed scalar coordinates.
Source: small pro-etale derived category
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
instance proCategory (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Category.{u + 1} (C A T) := inferInstanceAs (Category (DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))))

/-- Cache the published ordinary derived category structure in fixed scalar coordinates.
Source: small etale derived category
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
instance etaleCategory (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Category.{u + 1} (Etale.DerivedCategoryModule A T) := inferInstanceAs (Category
      (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))))

/-- The specified exponent, with no divisibility condition on the positive level.
Source: finite Tate realization (blueprint: lem-pur-affine-ordered-integration-transposes). -/
abbrev exponent (P : WeilConjectures.PurityFiniteSetting.{u}) : ℕ :=
  P.coefficients.l ^ (P.level + 1)

/-- The canonical normalized projective-line Tate transport, not an orientation choice.
Source: def-amb-p1-trace (blueprint: lem-pur-affine-ordered-integration-transposes). -/
def transport (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Etale.OrdinaryFiniteTwistTransport (AffineLinePurity.Ring P) (exponent P) (annihilates P) :=
  Etale.projectiveLineTraceTransport (exponent P)
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (AffineLinePurity.Ring P) (annihilates P)

/-- The normalized projective-line datum whose trace is the specified second projection.
Source: def-amb-p1-trace (blueprint: lem-pur-affine-ordered-integration-transposes). -/
def projectiveDatum (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (exponent P : Γ(T, ⊤))) :
    Etale.OrdinaryFiniteP1Datum (AffineLinePurity.Ring P) (exponent P) (annihilates P) (transport
      P) T hT :=
  Etale.projectiveLineTraceDatum (exponent P)
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (AffineLinePurity.Ring P) (annihilates P)
      T hT

/-- The ordered ordinary adjunction, with identity adjunction at zero coordinates.
Source: lem-amb-affine-space-top-trace
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def orderedAdjunction (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ) :
    Etale.affineTraceLeft (AffineLinePurity.Ring P) Y d ⊣
      Etale.affineTraceRight (AffineLinePurity.Ring P) (exponent P) (annihilates P) Y d :=
  Etale.affineTraceAdjunction (AffineLinePurity.Ring P) (exponent P) (annihilates P)
    (transport P) (projectiveDatum P) Y (exponentUnit P Y aY) d

/-- A_X(d)[2d], using the existing ordered finite Tate coefficient on X itself.
Source: finite twist convention (blueprint: lem-pur-affine-ordered-integration-transposes). -/
def etaleCoefficient (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (d : ℕ) :
    Etale.DerivedCategoryModule (AffineLinePurity.Ring P) (iteratedAffineLine Y d) :=
  Etale.affineLinearBaseCoefficient (AffineLinePurity.Ring P) (exponent P) (annihilates P)
    (iteratedAffineLine Y d) d

/-- Its canonical realization on the small pro-etale site.
Source: lem-pur-vector-integration-site-comparison
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def coefficient (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (d : ℕ) : D P (iteratedAffineLine Y d) :=
  (comparison (AffineLinePurity.Ring P) (iteratedAffineLine Y d)).obj (etaleCoefficient P Y d)

/-- Canonical comparison from the ordered ordinary constant-input source to A_X(d)[2d].
Only normalized Tate pullback and tensor reassociations occur.
Source: ordered trivial-frame trace (blueprint: lem-pur-affine-ordered-integration-transposes).
-/
def coefficientComparison (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ) :
    (Etale.affineTraceRight (AffineLinePurity.Ring P) (exponent P) (annihilates P) Y d).obj
      (Etale.ordinaryFiniteUnit (AffineLinePurity.Ring P) Y) ≅
        Etale.affineLinearBaseCoefficient (AffineLinePurity.Ring P) (exponent P) (annihilates P)
          (affineTraceTower Y d) d :=
  Etale.affineLinearCoefficientDescent (AffineLinePurity.Ring P) (exponent P) (annihilates P)
    (transport P) Y (exponentUnit P Y aY) d ≪≫
  Etale.vectorIntegrationBaseCoefficientPullback (AffineLinePurity.Ring P) (exponent P)
    (annihilates P)
    (transport P) (affineTraceProjection Y d) (exponentUnit P Y aY) d

/-- The actual ordinary trace on the coordinate projection. The first map changes
only coefficient coordinates; the second is the normalized proper/open tower compositor.
Source: lem-amb-affine-space-top-trace and the trivial-frame definition of integration
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def ordinaryTraceRaw (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ) :=
  (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
    (affineTraceProjection Y d)).map (coefficientComparison P Y aY d).inv ≫
  (Etale.affineLinearCompactComparison (exponent P)
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (AffineLinePurity.Ring P) (annihilates P)
    Y (exponentUnit P Y aY) d).inv ≫
  (orderedAdjunction P Y aY d).counit.app (Etale.ordinaryFiniteUnit (AffineLinePurity.Ring P) Y)

/-- Standing ordinary compact support in the normalized coordinate model.
Source: compact-support convention
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def ordinaryLower (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u}) (d : ℕ) :=
  letI := (projection_geometry Y d).2
  Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
    (iteratedAffineLineProj Y d)

attribute [local irreducible] Etale.rightDerivedLowerShriek
  Etale.affineLinearBaseCoefficient in
/-- The computed ordinary trace has the stated projection and coefficient endpoints.
The equality is only transport between the two identical recursive affine-line models.
Source: coordinate normalization
(blueprint: lem-pur-affine-ordered-integration-transposes).
Proof: induct on d. At zero both schemes and projections are identity. At a successor
both constructions apply AffineSpace PUnit to the preceding scheme and compose its
projection with the preceding projection. Induction identifies the schemes and arrows.
Finite Tate coefficients are the same ordered tensor recursion. The HasCompactification
instances are proofs, hence proof-irrelevant; their standing functors therefore agree
under this transport. The raw trace now has exactly the displayed endpoints. Transport
it along these equalities. HEq determines the transported map uniquely. -/
theorem ordinaryTrace_existsUnique (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ) :
    ∃! t : (ordinaryLower P Y d).obj (etaleCoefficient P Y d) ⟶
        Etale.ordinaryFiniteUnit (AffineLinePurity.Ring P) Y,
      HEq t (ordinaryTraceRaw P Y aY d) := by
  unfold ordinaryLower etaleCoefficient
  have hp : (⟨affineTraceTower Y d, affineTraceProjection Y d⟩ : Σ X : Scheme.{u}, X ⟶ Y) =
      ⟨iteratedAffineLine Y d, iteratedAffineLineProj Y d⟩ := by
    induction d with
    | zero => rfl
    | succ d ih =>
      exact congrArg (fun q : Σ X : Scheme.{u}, X ⟶ Y ↦
        (⟨AffineSpace PUnit.{u + 1} q.1,
          (AffineSpace PUnit.{u + 1} q.1 ↘ q.1) ≫ q.2⟩ : Σ X : Scheme.{u}, X ⟶ Y)) ih
  let W := fun X : Scheme.{u} ↦ Etale.affineLinearBaseCoefficient
    (AffineLinePurity.Ring P) (exponent P) (annihilates P) X d
  let typ := fun q : {q : Σ X : Scheme.{u}, X ⟶ Y // HasCompactification q.2} ↦
    letI := q.property
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (AffineLinePurity.Ring P)) q.val.2).obj
      (W q.val.1) ⟶ Etale.ordinaryFiniteUnit (AffineLinePurity.Ring P) Y
  have ht : typ ⟨⟨affineTraceTower Y d, affineTraceProjection Y d⟩, inferInstance⟩ =
      typ ⟨⟨iteratedAffineLine Y d, iteratedAffineLineProj Y d⟩,
        (projection_geometry Y d).2⟩ := by
    exact congrArg typ (Subtype.ext hp)
  refine ⟨cast ht (ordinaryTraceRaw P Y aY d), cast_heq ht _, ?_⟩
  intro t ht'
  exact eq_of_heq (ht'.trans (cast_heq ht _).symm)

/-- The uniquely transported actual ordered counit trace. The HEq characterization
fixes the map itself; it does not choose an unspecified orientation or isomorphism.
Source: canonical coordinate transport
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def ordinaryTrace (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ) :=
  (ordinaryTrace_existsUnique P Y aY d).exists.choose

private theorem flat_tensor_shift_plus
    {B : Type*} [Category B] [Abelian B] [IsGrothendieckAbelian B]
    [HasDerivedCategory B] [MonoidalCategory B] [MonoidalPreadditive B]
    [BraidedCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (L : B) (hL : ObjectProperty.flat L) (K : DerivedCategory B)
    (hK : DerivedCategory.TStructure.t.plus K) :
    DerivedCategory.TStructure.t.plus
      (K ⊗ ((DerivedCategory.singleFunctor B 0).obj L)⟦(2 : ℤ)⟧) := by
  let := Classical.choice (DerivedCategory.nonempty_braidedCategory B)
  obtain ⟨a, ha⟩ := hK
  have : K.IsGE a := ha
  let S := (DerivedCategory.singleFunctor B 0).obj L
  have ht := DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hL
  have : (S ⊗ K).IsGE (0 + a) :=
    DerivedCategory.isGE_tensor_of_torAmplitudeIn ht K a
  have hs : DerivedCategory.TStructure.t.plus ((S ⊗ K)⟦(2 : ℤ)⟧) :=
    ⟨0 + a - 2, DerivedCategory.TStructure.t.isGE_shift _ (0 + a) 2
      (0 + a - 2) (by omega)⟩
  have hs' : DerivedCategory.TStructure.t.plus (S⟦(2 : ℤ)⟧ ⊗ K) :=
    DerivedCategory.TStructure.t.plus.prop_of_iso
      (((MonoidalCategory.tensorRight K).commShiftIso (2 : ℤ)).app S).symm hs
  exact DerivedCategory.TStructure.t.plus.prop_of_iso (β_ _ _) hs'

private theorem tensor_plus_of_tor
    (B : Type v) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u}) (K W : DerivedCategory (Sheaf X.smallEtaleTopology B))
    {a b : ℤ} (ht : Etale.DerivedCategory.torAmplitudeIn B X a b K)
    (hW : DerivedCategory.TStructure.t.plus W) :
    DerivedCategory.TStructure.t.plus (((Etale.derivedTensor B X).obj K).obj W) := by
  obtain ⟨c, hc⟩ := hW
  have : W.IsGE c := hc
  exact ⟨a + c, DerivedCategory.isGE_tensor_of_torAmplitudeIn ht W c⟩

private theorem flat_unit (B : Type*) [Category B] [Abelian B]
    [MonoidalCategory B] [MonoidalPreadditive B] [BraidedCategory B] :
    ObjectProperty.flat (𝟙_ B) :=
  ObjectProperty.flat_of_tensorIso (λ_ (𝟙_ B))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorLine_plus (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) (K : Etale.DerivedCategoryModule A T)
    (hK : DerivedCategory.TStructure.t.plus K) :
    DerivedCategory.TStructure.t.plus
      ((Etale.derivedTensorRight (ModuleCat.{u + 1} A) T
        ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)).obj K) := by
  let L := Scheme.finiteEtaleTateLine T N A hA
  have hInv : ∀ x : T, IsUnit (N : T.presheaf.stalk x) := fun x ↦ by
    simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ x (by trivial)).hom
  have hf : ObjectProperty.flat L :=
    (ObjectProperty.flat_iff_preservesFiniteLimits _).2
      (Scheme.finite_etale_torsion_twist_line T N hN hInv A hA 1).2.2.1
  exact flat_tensor_shift_plus L hf K hK

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullback_plus (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : Etale.DerivedCategoryModule A Y)
    (hK : DerivedCategory.TStructure.t.plus K) :
    DerivedCategory.TStructure.t.plus ((Etale.ordinaryFinitePullback A f).obj K) := by
  exact DerivedCategory.TStructure.t.plus.prop_of_iso
    ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).app K).symm
    (((Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus.obj ⟨K, hK⟩).property)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

/-- The finite Tate coefficient is bounded below.
Source: finite Tate lines (blueprint: lem-pur-affine-ordered-integration-transposes).
Proof: the zero coefficient is the constant sheaf in degree zero. Each successor tensors
with a locally free degree-zero Tate line and shifts by two. Induction gives the single
sheaf A(d) shifted by 2d; this also applies on the empty scheme. -/
theorem coefficient_plus_on_base (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ) :
    DerivedCategory.TStructure.t.plus (etaleCoefficient P Y d) := by
  let T := iteratedAffineLine Y d
  have hT := affineTracePullbackInvertible (exponent P)
    (iteratedAffineLineProj Y d) (exponentUnit P Y aY)
  have h : ∀ n, DerivedCategory.TStructure.t.plus
      (Etale.affineLinearBaseCoefficient (AffineLinePurity.Ring P) (exponent P)
        (annihilates P) T n) := by
    intro n
    induction n with
    | zero =>
      change DerivedCategory.TStructure.t.plus (Etale.ordinaryFiniteUnit _ T)
      exact ⟨0, inferInstance⟩
    | succ n ih =>
      exact tensorLine_plus _ _ (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
        _ T hT _ ih
  exact h d

/-- The chosen compactification used by the standing functor, with no replacement map.
Source: def-compact-support-direct-image-detailed
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def compactification (Y : Scheme.{u}) (d : ℕ) :
    Compactification (iteratedAffineLineProj Y d) :=
  letI := (projection_geometry Y d).2
  HasCompactification.compactification (iteratedAffineLineProj Y d)

/-- Canonical realization of a given ordinary trace through the proper/open site map.
Source: compact support site comparison
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def realizeTrace (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    (c : Compactification f) (W : Etale.DerivedCategoryModule A X)
    (hW : DerivedCategory.TStructure.t.plus W)
    (t : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W ⟶
      Etale.ordinaryFiniteUnit A Y) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
      ((comparison A X).obj W) ⟶ unit A Y :=
  (compactSupportSiteComparison A c).hom.app ⟨W, hW⟩ ≫
    (comparison A Y).map
      ((Etale.rightDerivedLowerShriekIso A c).hom.app W ≫ t)

/-- The vector integration in the trivial frame, realized by the specified site comparison.
Its ordinary source trace is the ordered adjunction counit.
Source: def-amb-vector-integration and lem-pur-vector-integration-site-comparison
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def integration (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
      (compactification Y d)).obj (coefficient P Y d) ⟶ unit (AffineLinePurity.Ring P) Y :=
  letI := (projection_geometry Y d).2
  realizeTrace (AffineLinePurity.Ring P) (iteratedAffineLineProj Y d) (compactification Y d)
    (etaleCoefficient P Y d) (coefficient_plus_on_base P Y aY d) (ordinaryTrace P Y aY d)

/-- Canonical tensor reassociation, after caching the actual finite-scalar tensor.
Source: finite tensor associator (blueprint: lem-pur-affine-ordered-integration-transposes). -/
def reassociate (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (K L M : C A T) :
    ((tensor A T).obj (((tensor A T).obj K).obj L)).obj M ≅
      ((tensor A T).obj K).obj (((tensor A T).obj L).obj M) :=
  ProEtale.projectionActionAssociator (ModuleCat.{u + 1} A) T K L M

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Canonical tensor-action reassociation in fixed coefficient coordinates.
Source: ordered tensor powers
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def coefficientActionComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u}) (K : C A T) : (d : ℕ) →
    ((tensor A T).obj K).obj
      ((comparison A T).obj (Etale.affineLinearBaseCoefficient A N hA T d)) ≅
      (action ((tensor A T).flip.obj
        ((comparison A T).obj ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧))) d).obj K
  | 0 => AffineLinePurity.moduleRightUnit A T K
  | d + 1 =>
    ((tensor A T).obj K).mapIso
      (tensorComparison A T (Etale.affineLinearBaseCoefficient A N hA T d)
        ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)) ≪≫
    (reassociate A T K _ _).symm ≪≫
    tensorIso A T (coefficientActionComparison A N hA T K d) (Iso.refl _)

/-- The identity-pullback coefficient source comparison in cached scalar coordinates.
Source: rank-zero normalization
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def zeroSourceComparison (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u}) (K : C A Y) :
    K ≅ ((tensor A Y).obj ((inverseImage A (𝟙 Y)).obj K)).obj (unit A Y) :=
  (AffineLinePurity.moduleRightUnit A Y K).symm ≪≫
    tensorIso A Y ((inverseImageId A Y).app K).symm (Iso.refl _)

/-- Explicit source-coordinate isomorphism before endpoint normalization.
Source: canonical coefficient reassociation, including the rank-zero right unitor
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def sourceComparisonRaw (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (K : D P Y) : (d : ℕ) →
    Σ M N : D P (iteratedAffineLine Y d), M ≅ N
  | 0 => ⟨_, _, zeroSourceComparison (AffineLinePurity.Ring P) Y K⟩
  | d + 1 => ⟨_, _, (coefficientActionComparison (AffineLinePurity.Ring P) (exponent P)
    (annihilates P)
      (iteratedAffineLine Y (d + 1))
      ((inverseImage (AffineLinePurity.Ring P) (iteratedAffineLineProj Y (d + 1))).obj K)
      (d + 1)).symm⟩

private theorem isoHEq_existsUnique {Cat : Type*} [Category Cat]
    {K L : Cat} (e : K ≅ L) : ∃! e' : K ≅ L, HEq e'.hom e.hom :=
  ⟨e, HEq.rfl, fun _ he ↦ Iso.ext (eq_of_heq he)⟩

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- The explicit source-coordinate map has the recorded ordered-source endpoints.
Source: endpoint normalization
(blueprint: lem-pur-affine-ordered-integration-transposes).
Proof: split d into zero or a successor. At zero unfold the identity source and the
zero coefficient, and use the literal inverse-image identity comparison and right unitor.
At a successor unfold orderedSource and projectionSourceObject; coefficientActionComparison has
exactly those endpoints. Transport the raw isomorphism along these definitional
equalities. Its hom determines the isomorphism uniquely. -/
theorem sourceComparison_existsUnique (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (K : D P Y) (d : ℕ) :
    ∃! e : (orderedSource P Y d).obj K ≅
      AffineLinePurity.projectionSourceObject (AffineLinePurity.Ring P) (iteratedAffineLineProj Y d)
        (coefficient P Y d) K,
      HEq e.hom (sourceComparisonRaw P Y K d).2.2.hom := by
  cases d with
  | zero =>
    unfold orderedSource AffineLinePurity.projectionSourceObject
    dsimp only [coefficient, etaleCoefficient, shiftedLine, inverseImage,
      AffineSpacePurity.tensor, Functor.comp_obj, exponent]
    exact isoHEq_existsUnique (sourceComparisonRaw P Y K 0).2.2
  | succ d =>
    unfold orderedSource AffineLinePurity.projectionSourceObject
    dsimp only [coefficient, etaleCoefficient, shiftedLine, inverseImage,
      AffineSpacePurity.tensor, Functor.comp_obj, exponent]
    unfold twistAction
    dsimp only [shiftedLine, Functor.comp_obj]
    exact isoHEq_existsUnique (sourceComparisonRaw P Y K (d + 1)).2.2

/-- The canonical source-coordinate isomorphism, with its map fixed by the explicit
raw construction. Source: Lp_d*K(d)[2d]
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def sourceComparison (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (K : D P Y) (d : ℕ) :
    (orderedSource P Y d).obj K ≅
      AffineLinePurity.projectionSourceObject (AffineLinePurity.Ring P) (iteratedAffineLineProj Y d)
        (coefficient P Y d) K :=
  (sourceComparison_existsUnique P Y K d).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

private theorem tensorSource_origin (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : C A Y)
    (Ke : Etale.DerivedCategoryModule A Y) (W : Etale.DerivedCategoryModule A X)
    (hp : etaleFiniteTor A Y Ke)
    (hW : DerivedCategory.TStructure.t.plus W)
    (eK : (comparison A Y).obj Ke ≅ K) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X
      (AffineLinePurity.projectionSourceObject A f ((comparison A X).obj W) K) := by
  obtain ⟨a, b, ht⟩ :=
    (Etale.constructibleFiniteTor_leftDerivedUpperStar (ModuleCat.{u + 1} A) f hp).2
  have hs : DerivedCategory.TStructure.t.plus
      (AffineLinePurity.ordinarySourceObject A f W Ke) := by
    unfold AffineLinePurity.ordinarySourceObject
    exact tensor_plus_of_tor (ModuleCat.{u + 1} A) X _ W ht hW
  have e := AffineLinePurity.realizedTensorComparison A f K Ke W eK
  unfold AffineLinePurity.proSourceObject at e
  exact (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).prop_of_iso
    e (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj hs)

/-- The source has a bounded-below etale origin, which is an applicability conclusion.
Source: coordinate finite-Tor input and lem-sf-pullback-tor-amplitude
(blueprint: lem-pur-affine-ordered-integration-transposes).
Proof: use the ordinary source Ke pulled back along p_d and tensor it with the explicit
finite Tate coefficient. Its lower bound follows from the finite Tor interval of Ke.
The canonical pullback/tensor comparison and eK identify its realization with the stated
source. Exact comparison preserves the lower bound and gives the etale-origin witness. -/
theorem source_origin (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y) (Ke : Etale.DerivedCategoryModule
      (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
      (iteratedAffineLine Y d)
      (AffineLinePurity.projectionSourceObject (AffineLinePurity.Ring P) (iteratedAffineLineProj Y
        d)
        (coefficient P Y d) K.obj) := by
  exact tensorSource_origin (AffineLinePurity.Ring P) (iteratedAffineLineProj Y d)
    K.obj Ke (etaleCoefficient P Y d)
    hKe (coefficient_plus_on_base P Y aY d) eK

section GenericCoefficient
variable (B : Type v) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  [HasSmallSiteSheafify B]
  {FB : B → B → Type (u + 1)} {CB : B → Type (u + 1)}
  [∀ X Y, FunLike (FB X Y) (CB X) (CB Y)] [ConcreteCategory.{u + 1} B FB]
  [PreservesFiniteLimits (forget B)] [PreservesFilteredColimitsOfSize.{u, u} (forget B)]

omit [PreservesFilteredColimitsOfSize.{u, u} (forget B)] in
private theorem flatSingle_ctf (T : Scheme.{u})
    (L : Sheaf T.smallEtaleTopology B) [Scheme.IsConstructibleSheaf L]
    (hf : ObjectProperty.flat L) :
    Etale.DerivedCategory.constructibleFiniteTor B T
      ((DerivedCategory.singleFunctor _ 0).obj L) :=
  ⟨Etale.DerivedCategory.boundedConstructible_singleFunctor_obj L 0,
    0, 0, Etale.torAmplitudeIn_singleFunctor_zero_of_flat B L hf⟩

omit [HasSmallSiteSheafify B] [PreservesFiniteLimits (forget B)]
  [PreservesFilteredColimitsOfSize.{u, u} (forget B)] in
private theorem ctf_shift (T : Scheme.{u})
    (L : DerivedCategory (Sheaf T.smallEtaleTopology B))
    (hL : Etale.DerivedCategory.constructibleFiniteTor B T L) (n : ℤ) :
    Etale.DerivedCategory.constructibleFiniteTor B T (L⟦n⟧) := by
  obtain ⟨hbc, a, b, ht⟩ := hL
  exact ⟨(Etale.DerivedCategory.boundedConstructible B T).le_shift n _ hbc,
    a - n, b - n, Etale.torAmplitudeIn_shift B ht n⟩

omit [Abelian.HasFunctorialFlatResolution B] [HasSmallSiteSheafify B] in
private theorem constantUnit_flat (T : Scheme.{u}) :
    ObjectProperty.flat ((constantSheaf T.smallEtaleTopology B).obj (𝟙_ B)) :=
  ObjectProperty.flat.prop_of_iso (Functor.Monoidal.εIso
    (constantSheaf T.smallEtaleTopology B)).symm
    (flat_unit (Sheaf T.smallEtaleTopology B))

omit [PreservesFilteredColimitsOfSize.{u, u} (forget B)] in
private theorem constantUnit_ctf (T : Scheme.{u})
    [Scheme.IsConstructibleSheaf ((constantSheaf T.smallEtaleTopology B).obj (𝟙_ B))] :
    Etale.DerivedCategory.constructibleFiniteTor B T
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf T.smallEtaleTopology B).obj (𝟙_ B))) :=
  flatSingle_ctf B T _ (constantUnit_flat B T)

end GenericCoefficient

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem shiftedLine_ctf (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) :
    etaleFiniteTor A T ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) := by
  let L := Scheme.finiteEtaleTateLine T N A hA
  have hInv : ∀ x : T, IsUnit (N : T.presheaf.stalk x) := fun x ↦ by
    simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ x (by trivial)).hom
  have hLine := Scheme.finite_etale_torsion_twist_line T N hN hInv A hA 1
  obtain ⟨cover, hcover⟩ := hLine.1
  have : Scheme.IsFiniteLocallyConstantSheaf L := by
    apply (Scheme.finite_locally_constant_module_values_iff L).1.1
    refine ⟨⟨cover, fun i ↦ ?_⟩, fun i ↦ ⟨ModuleCat.of A A, inferInstance, hcover i⟩⟩
    obtain ⟨e⟩ := hcover i
    exact Sheaf.isConstant_of_iso _ e
  have : Scheme.IsConstructibleSheaf L :=
    Scheme.IsFiniteLocallyConstantSheaf.isConstructibleSheaf inferInstance
  have hf : ObjectProperty.flat L :=
    (ObjectProperty.flat_iff_preservesFiniteLimits _).2 hLine.2.2.1
  exact ctf_shift (ModuleCat.{u + 1} A) T _
    (flatSingle_ctf (ModuleCat.{u + 1} A) T L hf) 2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem baseCoefficient_ctf (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) :
    etaleFiniteTor A T (Etale.affineLinearBaseCoefficient A N hA T d) := by
  have hL := shiftedLine_ctf A N hN hA T hT
  induction d with
  | zero =>
    change etaleFiniteTor A T (Etale.ordinaryFiniteUnit A T)
    have : Scheme.IsConstructibleSheaf (Etale.ordinaryFiniteConstant A T) :=
      Scheme.isConstructibleSheaf_constantSheaf (ModuleCat.of A A)
    exact constantUnit_ctf (ModuleCat.{u + 1} A) T
  | succ d ih => exact Etale.constructibleFiniteTor_tensor A T ih hL

attribute [local irreducible] projectionMapOfCompactification

private theorem reorderedProjection_isIso
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {X Z : Scheme.{u}} {f : X ⟶ Z} (c : Compactification f)
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) B))
    (h : IsIso (((projectionMapOfCompactification B c).app F).app K)) :
    IsIso (projection B c F K) := by
  have h₁ : IsIso (((symmetry B Z).hom.app K).app
      ((rightDerivedLowerShriekOfCompactification B c).obj F)) :=
    (((symmetry B Z).app K).app _).isIso_hom
  have h₂ : IsIso ((rightDerivedLowerShriekOfCompactification B c).map
      (((symmetry B X).hom.app F).app ((upperStar B f).leftDerivedFunctor.obj K))) :=
    ((rightDerivedLowerShriekOfCompactification B c).mapIso
      (((symmetry B X).app F).app _)).isIso_hom
  unfold projection
  exact IsIso.comp_isIso' h₁ (IsIso.comp_isIso' h h₂)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem projectionFromOrigin_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} {f : X ⟶ Z} (c : Compactification f)
    (W : Etale.DerivedCategoryModule A X) (hW : DerivedCategory.TStructure.t.bounded W)
    (K : C A Z) (Ke : Etale.DerivedCategoryModule A Z)
    (hKe : etaleFiniteTor A Z Ke) (eK : (comparison A Z).obj Ke ≅ K) :
    IsIso (projection (ModuleCat.{u + 1} A) c ((comparison A X).obj W) K) := by
  obtain ⟨a, b, hTor⟩ := hKe.2
  have hM := (Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} A) c.i).bounded_mapDerivedCategory_obj hW
  have hML := Etale.plus_derivedTensor_leftDerivedUpperStar c.g hM hTor
  have := Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite A c.g
  have hPF := hasProjectionFormulaOfCompactification_of_comparison c
    (Iso.refl ((comparison A X).obj W)) eK hW hML inferInstance
  exact reorderedProjection_isIso (ModuleCat.{u + 1} A) c _ K hPF

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

/-- Invertibility of the actual symmetry-adjusted compactification projection.
Source: finite projection formula on the stated coordinate inputs
(blueprint: lem-pur-affine-ordered-integration-transposes).
Proof: the coefficient is a bounded finite locally free Tate complex. The comparison
origin of Ke gives the stated constructible finite-Tor coefficient. Apply the finite
compact-support projection formula at the specified compactification, and insert the
two canonical tensor symmetries. No ambient pro-etale projection isomorphism is assumed. -/
theorem projection_isIso (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y) (Ke : Etale.DerivedCategoryModule
      (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    ProjectionInvertible (AffineLinePurity.Ring P) (compactification Y d) (coefficient P Y d)
      K.obj := by
  have hW := baseCoefficient_ctf (AffineLinePurity.Ring P) (exponent P)
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
    (iteratedAffineLine Y d)
    (affineTracePullbackInvertible (exponent P) (iteratedAffineLineProj Y d)
      (exponentUnit P Y aY)) d
  unfold ProjectionInvertible
  exact projectionFromOrigin_isIso (AffineLinePurity.Ring P) (compactification Y d)
    (etaleCoefficient P Y d) hW.1.1 K.obj Ke hKe eK

/-- The coefficient integration (1_K tensor t_p) Pi, with the canonical right unitor.
Source: displayed counit formula
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def augmentation (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y) (Ke : Etale.DerivedCategoryModule
      (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :=
  letI : IsNoetherian Y := tower_noetherian P Y aY 0
  projectionTensorTrace (AffineLinePurity.Ring P) (compactification Y d) (coefficient P Y d) K.obj
    (integration P Y aY d) (projection_isIso P Y aY K Ke hKe eK d)

/-- The specified exceptional transpose with the standing compactification made explicit.
Source: restricted exceptional Hom correspondence
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def standingTranspose (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    [QuasiCompact f] [CompactSpace Y]
    (M : C A X) (K : C A Y)
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M)
    (hK : boundedBelow A Y K)
    (z : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (HasCompactification.compactification f)).obj M ⟶ K) :
    M ⟶ (rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K :=
  rightDerivedUpperShriekHomEquiv f hM hK z

/-- The actual integration transpose before the exceptional endpoint normalization.
Source: definition of P, the specified restricted exceptional Hom bijection
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def integrationTransposeRaw (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y) (Ke : Etale.DerivedCategoryModule
      (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) :
    (d : ℕ) → Σ M N : D P (iteratedAffineLine Y d), M ⟶ N
  | 0 => ⟨_, _, 𝟙 K.obj⟩
  | d + 1 =>
    letI := (projection_geometry Y (d + 1)).1
    letI := (projection_geometry Y (d + 1)).2
    letI : IsNoetherian Y := tower_noetherian P Y aY 0
    ⟨_, _, (sourceComparison P Y K.obj (d + 1)).hom ≫
      standingTranspose (AffineLinePurity.Ring P) (iteratedAffineLineProj Y (d + 1))
        _ K.obj (source_origin P Y aY K Ke hKe eK (d + 1)) K.property
        (augmentation P Y aY K Ke hKe eK (d + 1))⟩

private theorem homHEq_existsUnique {Cat : Type*} [Category Cat]
    {K L : Cat} (f : K ⟶ L) : ∃! g : K ⟶ L, HEq g f :=
  ⟨f, HEq.rfl, fun _ hg ↦ eq_of_heq hg⟩

/-- This exact transpose has the recorded exceptional comparison endpoints.
Source: normalized standing exceptional functor
(blueprint: lem-pur-affine-ordered-integration-transposes).
Proof: at zero both functors are normalized to identity. At a positive stage unfold
ComparisonHom and exceptional at the outer successor. The specified restricted Hom
bijection has exactly this standing exceptional target, while sourceComparison has
exactly the ordered source. Proof irrelevance identifies compactifiability witnesses.
Transport the computed arrow along these endpoint equalities. HEq fixes it uniquely. -/
theorem integrationTranspose_existsUnique (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y) (Ke : Etale.DerivedCategoryModule
      (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    ∃! p : ComparisonHom P Y K.obj d,
      HEq p (integrationTransposeRaw P Y aY K Ke hKe eK d).2.2 := by
  cases d with
  | zero =>
    unfold ComparisonHom orderedSource exceptional
    exact homHEq_existsUnique (𝟙 K.obj)
  | succ d =>
    unfold ComparisonHom exceptional
    exact homHEq_existsUnique (integrationTransposeRaw P Y aY K Ke hKe eK (d + 1)).2.2

/-- The integration transpose, with its map fixed by the independent integration
construction. Source: P_(p_d,K)
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
@[irreducible]
def integrationTranspose (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y) (Ke : Etale.DerivedCategoryModule
      (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    ComparisonHom P Y K.obj d :=
  (integrationTranspose_existsUnique P Y aY K Ke hKe eK d).exists.choose

/-- The explicit ordinary tensor-source representative of Lp_d*K(d)[2d].
Source: bounded etale origin (blueprint: lem-pur-affine-ordered-integration-transposes). -/
def sourceEtale (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y) (d : ℕ) :=
  AffineLinePurity.ordinarySourceObject (AffineLinePurity.Ring P) (iteratedAffineLineProj Y d)
    (etaleCoefficient P Y d) Ke

attribute [local semireducible] AffineLinePurity.proSourceObject

/-- The ordinary tensor source realizes to the literal pro-etale tensor source.
Source: canonical pullback/tensor comparison
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def realizeTensorSource (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : C A Y)
    (Ke : Etale.DerivedCategoryModule A Y) (W : Etale.DerivedCategoryModule A X)
    (eK : (comparison A Y).obj Ke ≅ K) :
    (comparison A X).obj (AffineLinePurity.ordinarySourceObject A f W Ke) ≅
      AffineLinePurity.projectionSourceObject A f ((comparison A X).obj W) K := by
  exact AffineLinePurity.realizedTensorComparison A f K Ke W eK

/-- Its canonical realization, using the actual tensor/pullback comparison and eK.
Source: site source normalization
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def sourceRealization (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (K : D P Y) (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K) (d : ℕ) :=
  realizeTensorSource (AffineLinePurity.Ring P) (iteratedAffineLineProj Y d)
    K Ke (etaleCoefficient P Y d) eK ≪≫ (sourceComparison P Y K d).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

/-- Both coordinate sources retain the bounded constructible finite-Tor domain.
Source: pullback and tensor finite-Tor preservation
(blueprint: lem-pur-affine-ordered-integration-transposes).
Proof: pullback preserves the bounds and the finite Tor interval of Ke. The coefficient
is locally free of rank one shifted by 2d. Tensoring translates the two intervals;
comparison identifies the result with the ordered source by sourceRealization. -/
theorem source_applicability (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y) (Ke : Etale.DerivedCategoryModule
      (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    boundedBelow (AffineLinePurity.Ring P) (iteratedAffineLine Y d) ((orderedSource P Y d).obj
      K.obj) ∧
      etaleFiniteTor (AffineLinePurity.Ring P) (iteratedAffineLine Y d) (sourceEtale P Y Ke d) := by
  let A := AffineLinePurity.Ring P
  let f := iteratedAffineLineProj Y d
  have ht := baseCoefficient_ctf A (exponent P)
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
    (iteratedAffineLine Y d)
    (affineTracePullbackInvertible (exponent P) f (exponentUnit P Y aY)) d
  have hs : etaleFiniteTor A (iteratedAffineLine Y d) (sourceEtale P Y Ke d) := by
    unfold sourceEtale AffineLinePurity.ordinarySourceObject
    exact Etale.constructibleFiniteTor_tensor A _
      (Etale.constructibleFiniteTor_leftDerivedUpperStar (ModuleCat.{u + 1} A) f hKe) ht
  refine ⟨?_, hs⟩
  exact (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) _).prop_of_iso
    (sourceComparison P Y K.obj d).symm (source_origin P Y aY K Ke hKe eK d) |>.plus

/-- Gamma_q at the actual exceptional input Rp_d!K, with its retained canonical origin.
Source: the displayed recursion (blueprint: lem-pur-affine-ordered-integration-transposes). -/
def exceptionalLine (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y) (Ke : Etale.DerivedCategoryModule
      (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :=
  letI : LocallyOfFiniteType (towerBase aY d) := (tower_geometry aY d).1
  letI : QuasiCompact (towerBase aY d) := (tower_geometry aY d).2.1
  letI : IsSeparated (towerBase aY d) := (tower_geometry aY d).2.2
  lineComparison P (iteratedAffineLine Y d) (towerBase aY d)
    ⟨(exceptional P Y d).obj K.obj, (stage_applicability P Y aY K Ke hKe eK d).1⟩
    (stageEtale P Y K.obj Ke d) (stage_applicability P Y aY K Ke hKe eK d).2
    (stageComparison P Y K.obj Ke eK d)

/-- Gamma_q at G_dK, with the canonical tensor-source etale representative.
Source: the naturality square (blueprint: lem-pur-affine-ordered-integration-transposes). -/
def sourceLine (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y) (Ke : Etale.DerivedCategoryModule
      (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :=
  letI : LocallyOfFiniteType (towerBase aY d) := (tower_geometry aY d).1
  letI : QuasiCompact (towerBase aY d) := (tower_geometry aY d).2.1
  letI : IsSeparated (towerBase aY d) := (tower_geometry aY d).2.2
  lineComparison P (iteratedAffineLine Y d) (towerBase aY d)
    ⟨(orderedSource P Y d).obj K.obj, (source_applicability P Y aY K Ke hKe eK d).1⟩
    (sourceEtale P Y Ke d) (source_applicability P Y aY K Ke hKe eK d).2
    (sourceRealization P Y K.obj Ke eK d)
```

The original module adds this public reexport:

```lean
public import Sheaf.Paper.AffineOrderedIntegrationData
```

## Users

The following is the complete downstream.py result for the original module. All its
public names remain available under that import. No downstream source is adapted.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AffineOrderedIntegrationTransposes | J7 | Construction prefix publicly reexported; final theorem has an induction proof. |
| Sheaf.Paper.AffineOrderedIntegrationData | J7 (new) | Verbatim construction prefix, with no sorry. |
| Sheaf.Paper.AffineOrderedIntegrationSuccessor | J7 (new) | Imports construction data to state one successor equation. |
| Sheaf.Paper.AffineLineComparisonNaturality | J7 (new) | Proves the line square from dimension-one ordered naturality. |
| Sheaf.Paper.AdicActualSystemsNormalized | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.AdicNormalizedPuritySystems | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.AdicPuritySourceFiniteness | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.AdicPuritySourceNormalization | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.AdicPuritySourceTransitionSquare | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.AffineIntegrationExponentTransition | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.CentredDiagonalSourcePasting | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.ChartDiagonalAssemblyData | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.ChartDiagonalSourceSquare | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.ChartDncNaturality | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.ChartDncSquare | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.ChartDncVectorFactorData | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.ChartDncVectorFactors | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.ChartEpsilonPasting | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.ChartExceptionalCounitEquation | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.ChartExceptionalMateCoherence | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.ChartIntegrationAdjoints | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.ChartNormalIntegrationSquare | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.CompositionIteratedMateExpansion | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.CompositionModelOrientationDefinitions | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.CompositionSingleMatePresentation | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.DiagonalDncAssemblyGlobal | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.DiagonalDncChartNormalization | S2 | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.DiagonalOrientationCharts | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteDiagonalBaseChangeReduction | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteDiagonalDncReduction | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationAssembly | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteDiagonalVectorReduction | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteFirstRootChart | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteGeometricPurityMate | M1 | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteOrientationScalarPresentation | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FinitePositiveChartFrameExt | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FinitePositiveChartRecursion | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FinitePositiveRootChartPower | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FinitePositiveRootCharts | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteProductReductionComparisons | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FinitePublishedRootChartPower | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteReductionBaseChangeSource | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteReductionExceptionalFiniteModel | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteReductionLineChartScalars | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteReductionLineInputConstructible | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteReductionPositiveLineComparison | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteReductionReassociation | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteReductionShiftedPullbackCube | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteReductionSourceChartIndependence | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteReductionTensorFactors | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteReductionTensorPurity | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteReductionTensorSource | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteReductionThetaFactor | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteRootLinePowerTransition | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteRootTensorPresentation | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteSignedTwistProducts | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteSourceChartPowerTransition | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteSourceChartScalarTransition | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteSupportedReductionEquation | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteTensorComparisonEquations | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteTensorFixedComparisons | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteTensorLineChartReduction | G4 | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteTensorLineDerivedExistence | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteTensorLineDerivedExistenceWitness | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteTensorPresentationReduction | A3 | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteTensorProductFrameExt | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteTensorProductMap | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteTensorProductMapIsIso | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteTensorReductionData | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteTensorSemilinearReduction | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteTensorShiftCoherence | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteTensorShiftFirst | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteTensorShiftSecond | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteTensorSignedReduction | J2 | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.FiniteTensorSymmetryCoherence | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.GeneralChartComparisons | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.ModelAffineIntegrationOrientation | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.ModelChartOrientationAssembly | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.ModelOrientationChartDescent | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.ModelOrientationSourceNaturality | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.ModelOrientationTateDetection | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.NormalModelSectionOrientation | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.NormalSectionIntegrationBaseChange | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.NormalSectionIntegrationData | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.NormalSectionIntegrationOrientation | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.ProjectionPurityAgreement | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.ProjectionTensorIntegration | unclaimed | Identical public constructions through reexport; compiled unchanged as a direct consumer. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.RetaggingCoordinateOrientations | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.SectionDncIntegrationSquare | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.SectionEtaleOpenCancellation | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.TowerPurityRealizedData | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.TowerPurityRealizedNormalization | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.VectorIntegrationChartComparison | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.VectorIntegrationChartCoordinates | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.VectorIntegrationChartTranspose | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.VectorIntegrationUnitTranspose | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.VectorModelChartDescent | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineOrientation | R4 | Identical public constructions through reexport; no source adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineOrientationCoordinates | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.IntegralPurityComparisonCocycles | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.IntegralPurityCounitReduction | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.IteratedPurityScalarPasting | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTrace | K4 | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceCommonStage | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | unclaimed | Identical public constructions through reexport; no source adaptation. |
| Sheaf.Paper.SmoothPurityBaseChangeFactors | M4 | Identical public constructions through reexport; no source adaptation. |

## Status

landed 20261026T070110-L-3382120 2026-10-26 (merge of deliver/J7/Sheaf.Paper.AffineOrderedIntegrationTransposes)
