module
public import Sheaf.Paper.RootBoundaryComparison
public import Sheaf.Paper.IntegralLisseClosedBaseChange
public import Sheaf.Paper.ProfiniteConstantDerivedFunctions
/-!
# Scalar-restriction diagrams for the normalized boundary comparison

Source: main-20261015, sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3),
agent expansion of the tame-boundary calculation.
(blueprint: def-sfb-root-boundary-scalar-comparison).

All coefficients retain every continuous function, including for incomplete algebraic closures.
All derived categories are ordinary and unbounded.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.RootBoundary
variable (F : Type u) [NormedField F]
variable {G : Type u} [NormedField G]
variable (c : coefficients F ⟶ coefficients G) [IsMonHom c]
/-- The dependency's exact restriction of scalars on unbounded derived categories.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-scalar-comparison). -/
abbrev scalarRestrictionD (X : Scheme.{u}) :
    DerivedCategory (SiteMod G X) ⥤ DerivedCategory (SiteMod F X) :=
  IntegralLisseClosedBaseChange.restrict c X
/-- The dependency's canonical inverse-image/restriction isomorphism.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-scalar-comparison). -/
abbrev scalarPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullD G f ⋙ scalarRestrictionD F c X ≅
      scalarRestrictionD F c Y ⋙ pullD F f :=
  IntegralLisseClosedBaseChange.restrictPull c f
/-- The dependency's canonical right-derived restriction comparison in its natural direction.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-scalar-comparison). -/
abbrev scalarPush {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pushD G f ⋙ scalarRestrictionD F c Y ⟶
      scalarRestrictionD F c X ⋙ pushD F f :=
  IntegralLisseClosedBaseChange.restrictPush c f
/-- Ordinary extension of scalars on internal modules, with no derived tensor substituted.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-scalar-comparison). -/
abbrev scalarExtension (X : Scheme.{u}) : SiteMod F X ⥤ SiteMod G X :=
  Mod.extendScalars (coefficientMap c X)
/-- The dependency's actual ordinary scalar-extension unit in degree zero: x maps to 1 tensor x.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-scalar-comparison). -/
abbrev scalarZeroUnit (X : Scheme.{u}) (N : SiteMod F X) :
    moduleAtZero F N ⟶ (scalarRestrictionD F c X).obj
      (moduleAtZero G ((scalarExtension F c X).obj N)) :=
  IntegralLisseClosedBaseChange.scalarUnit c X N
variable (p : ℕ) {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R)
/-- The full-source construction applied to an arbitrary derived module on the test tower.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-scalar-comparison). -/
def fullOn (P : Profinite.{u}) (K : DerivedCategory (SiteMod F (test (tower p t) P).left)) :
    DerivedCategory (SiteMod F (stratumScheme t)) :=
  (pullD F (stratumInclusion t)).obj ((pushD F (qP p t P)).obj K)
/-- The direct image of the boundary pullback of an arbitrary derived module on the test tower.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-scalar-comparison). -/
def boundaryOn (P : Profinite.{u})
    (K : DerivedCategory (SiteMod F (test (tower p t) P).left)) :
    DerivedCategory (SiteMod F (stratumScheme t)) :=
  (pushD F (test (stratumScheme t) P).hom).obj
    ((pullD F (testMap (boundary p t) P)).obj K)
/-- The dependency's actual boundary exchange adjunct on an arbitrary test-tower complex.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-scalar-comparison). -/
def restrictionOn (P : Profinite.{u})
    (K : DerivedCategory (SiteMod F (test (tower p t) P).left)) :
    fullOn F p t P K ⟶ boundaryOn F p t P K :=
  (RootCoordinateFace.exchange (coefficients F) (testMap (boundary p t) P)
    (test (stratumScheme t) P).hom (qP p t P) (stratumInclusion t)
    (test_boundary_square p t P)).app K
/-- The map on full direct images induced by a derived coefficient-module arrow.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-scalar-comparison). -/
def fullOnMap (P : Profinite.{u})
    {K L : DerivedCategory (SiteMod F (test (tower p t) P).left)} (f : K ⟶ L) :
    fullOn F p t P K ⟶ fullOn F p t P L :=
  (pullD F (stratumInclusion t)).map ((pushD F (qP p t P)).map f)
/-- The map on boundary direct images induced by that same derived coefficient-module arrow.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-scalar-comparison). -/
def boundaryOnMap (P : Profinite.{u})
    {K L : DerivedCategory (SiteMod F (test (tower p t) P).left)} (f : K ⟶ L) :
    boundaryOn F p t P K ⟶ boundaryOn F p t P L :=
  (pushD F (test (stratumScheme t) P).hom).map
    ((pullD F (testMap (boundary p t) P)).map f)
/-- Pullback of the actual ordinary extension unit to the full-tower test, with the
canonical inverse-image/restriction identification.
Source: the root-tower boundary calculation, paragraph (3) of the direct-image proof
(blueprint: def-sfb-root-boundary-scalar-comparison). -/
def scalarTestUnit (N : SiteMod F (tower p t)) (P : Profinite.{u}) :
    testModule F p t N P ⟶ (scalarRestrictionD F c (test (tower p t) P).left).obj
      (testModule G p t ((scalarExtension F c (tower p t)).obj N) P) :=
  (pullD F (test (tower p t) P).hom).map (scalarZeroUnit F c (tower p t) N) ≫
    (scalarPull F c (test (tower p t) P).hom).inv.app
      (moduleAtZero G ((scalarExtension F c (tower p t)).obj N))
section FiniteModels

variable (E Ω : Type u) [NormedField E] [NormedField Ω] [NormedAlgebra E Ω]
variable (M : Type u) [AddCommGroup M] [Module E M] [FiniteDimensional E M]

/-- The recorded section identification of the chosen continuous-functions condensation.
Source: paragraph (3), the finite-dimensional all-continuous model
(blueprint: def-sfb-root-boundary-scalar-comparison). -/
def modelSections (K : Type u) [NormedField K] [Algebra E K] (P : Profinite.{u}) :
    (model K E M).X.obj.obj (Opposite.op P) ≃+ C(P, tensorModule K E M) :=
  (Profinite.topologicalModule_condensation K).choose_spec.choose (tensorModule K E M) P

/-- The two recorded presentations of the continuous model have a unique sectionwise identity.
Source: paragraph (3), the supplied continuous boundary model
(blueprint: def-sfb-root-boundary-scalar-comparison).
Proof: both section identifications identify the underlying sheaf with all continuous maps
into the same tensor module, with its module topology. Transport the identity of those maps
through the two identifications. The restriction formulas make this a sheaf map; the
pointwise action formulas make it linear. Reverse the transport for its inverse. The
section formulas show both composites are identities and determine the isomorphism uniquely.
No basis, completion or finite-subextension factorization is chosen. -/
theorem modelIso_existsUnique (K : Type u) [NormedField K] [Algebra E K] :
    ∃! i : model K E M ≅ ProfiniteFunctions.constantModel E K M,
      ∀ (P : Profinite.{u}) (x : (model K E M).X.obj.obj (Opposite.op P)) (q : P),
        (ProfiniteFunctions.modelSection K (ProfiniteFunctions.ScalarModel E K M) P
          (i.hom.hom.hom.app (Opposite.op P) x)).down q = modelSections E M K P x q := by
  sorry

/-- The canonical identity between the two continuous-model presentations.
Source: paragraph (3), the supplied continuous boundary model
(blueprint: def-sfb-root-boundary-scalar-comparison). -/
def modelIso (K : Type u) [NormedField K] [Algebra E K] :
    model K E M ≅ ProfiniteFunctions.constantModel E K M :=
  (modelIso_existsUnique E M K).choose

/-- The existing sectionwise x-to-one-tensor-x map, transported along canonical model identities.
Source: paragraph (3), compatibility for E to Omega
(blueprint: def-sfb-root-boundary-scalar-comparison). -/
def scalarModelMap : model E E M ⟶
    (Mod.comap (ProfiniteFunctions.coefficientInclusion E Ω)).obj
      (model Ω E M) :=
  (modelIso E M E).hom ≫ ProfiniteFunctions.scalarConstantMap E Ω M ≫
    (Mod.comap (ProfiniteFunctions.coefficientInclusion E Ω)).map
      (modelIso E M Ω).inv

/-- The actual boundary-model unit in degree zero with exact restriction transport.
Source: paragraph (3), x maps to one tensor x on the target model
(blueprint: def-sfb-root-boundary-scalar-comparison). -/
def scalarModelMapD : (pointZeroFunctor E).obj (model E E M) ⟶
    (Mod.comap (ProfiniteFunctions.coefficientInclusion E Ω)).mapDerivedCategory.obj
        ((pointZeroFunctor Ω).obj (model Ω E M)) :=
  (pointZeroFunctor E).map (scalarModelMap E Ω M) ≫
    ((Mod.comap (ProfiniteFunctions.coefficientInclusion E Ω)).mapDerivedCategorySingleFunctor
      0).inv.app (model Ω E M)

/-- The actual ordinary tensor-unit equation transported to degree zero.
The degree-zero embedding is fully faithful, so this fixes the ordinary identification.
Source: paragraph (3), scalar extension of the supplied identification
(blueprint: def-sfb-root-boundary-scalar-comparison). -/
def IsScalarExtendedBoundary (N : SiteMod E (tower p t))
    (e : (CondensedRing.upperStar (coefficients E) (boundary p t)).obj N ≅
      (pointPull E (stratumScheme t)).obj (model E E M))
    (eΩ : (CondensedRing.upperStar (coefficients Ω) (boundary p t)).obj
      ((scalarExtension (G := Ω) E (ProfiniteFunctions.coefficientInclusion E Ω)
        (tower p t)).obj N) ≅ (pointPull Ω (stratumScheme t)).obj (model Ω E M)) : Prop :=
  (pullD E (boundary p t)).map
    (scalarZeroUnit (G := Ω) E (ProfiniteFunctions.coefficientInclusion E Ω) (tower p t) N) ≫
  (scalarPull (G := Ω) E (ProfiniteFunctions.coefficientInclusion E Ω) (boundary p t)).inv.app
    (moduleAtZero Ω ((scalarExtension (G := Ω) E (ProfiniteFunctions.coefficientInclusion E Ω)
      (tower p t)).obj N)) ≫
  (scalarRestrictionD (G := Ω) E (ProfiniteFunctions.coefficientInclusion E Ω)
    (stratumScheme t)).map
      (boundaryIdentification Ω p t
        ((scalarExtension (G := Ω) E (ProfiniteFunctions.coefficientInclusion E Ω)
          (tower p t)).obj N) (model Ω E M) eΩ).hom ≫
  (ProfiniteFunctions.restrictPointPullD (Mon.mk (coefficients E))
    (Mon.mk (coefficients Ω)) (ProfiniteFunctions.coefficientInclusion E Ω)
    (stratumScheme t)).inv.app ((pointZeroFunctor Ω).obj (model Ω E M)) =
  (boundaryIdentification E p t N (model E E M) e).hom ≫
    (pointPullD E (stratumScheme t)).map (scalarModelMapD E Ω M)

/-- There is exactly one ordinary scalar-extended boundary identification with this actual unit.
Source: paragraph (3), ordinary scalar extension of the supplied boundary identification
(blueprint: def-sfb-root-boundary-scalar-comparison).
Proof: the canonical ordinary pullback/extension isomorphism CondensedRing.pullIso identifies
boundary pullback of the ordinary extension of N with ordinary extension of its boundary
pullback. Extend e by ordinary tensor. In a finite E-basis of M, its target extends from
a finite sum of regular E-coefficient modules to the corresponding finite sum over Omega.
The model section formulas give the canonical isomorphism of this sum with model Omega E M,
with coordinate map x to one tensor x; it remains valid for incomplete Omega and rank zero.
These actual maps construct e_Omega. The extension/restriction adjunction unit says that
restricting this homomorphism along the pulled tensor unit is e followed by the model unit.
The canonical exact degree-zero restriction comparisons turn this ordinary unit equation
into IsScalarExtendedBoundary. Full faithfulness of degree-zero embedding recovers the
ordinary equation; the extension/restriction adjunction bijection determines the
homomorphism uniquely, hence the isomorphism uniquely.
Thus the scalar clause quantifies over the actual scalar-extended identification, with
existence ensured and no unrelated choice or added assumption on the E-extension. -/
theorem scalarBoundaryIdentification_existsUnique (N : SiteMod E (tower p t))
    (e : (CondensedRing.upperStar (coefficients E) (boundary p t)).obj N ≅
      (pointPull E (stratumScheme t)).obj (model E E M)) :
    ∃! eΩ : (CondensedRing.upperStar (coefficients Ω) (boundary p t)).obj
      ((scalarExtension (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω) (tower p t)).obj N) ≅
        (pointPull Ω (stratumScheme t)).obj (model Ω E M),
      IsScalarExtendedBoundary p t E Ω M N e eΩ := by
  sorry

/-- The common target is E-derived internal functions with values in the restricted Omega-model.
Source: paragraph (3), compatibility after scalar restriction
(blueprint: def-sfb-root-boundary-scalar-comparison). -/
def scalarCommonTarget (P : Profinite.{u}) :
    DerivedCategory (SiteMod E (stratumScheme t)) :=
  (pointPullD E (stratumScheme t)).obj ((parameterFunctions E P).obj
    ((Mod.comap (ProfiniteFunctions.coefficientInclusion E Ω)).mapDerivedCategory.obj
        ((pointZeroFunctor Ω).obj (model Ω E M))))

/-- The E-target map is RHom applied to the actual boundary-model unit.
Source: paragraph (3), x maps to one tensor x on derived internal functions
(blueprint: def-sfb-root-boundary-scalar-comparison). -/
def scalarTargetUnit (P : Profinite.{u}) :
    target E t (model E E M) P ⟶ scalarCommonTarget t E Ω M P :=
  (pointPullD E (stratumScheme t)).map
    ((parameterFunctions E P).map (scalarModelMapD E Ω M))

/-- The Omega-target map uses the existing directional restriction of derived internal Hom.
Source: paragraph (3), compatibility after scalar restriction
(blueprint: def-sfb-root-boundary-scalar-comparison). -/
def scalarTargetRestriction (P : Profinite.{u}) :
    (scalarRestrictionD (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω)
      (stratumScheme t)).obj (target Ω t (model Ω E M) P) ⟶
        scalarCommonTarget t E Ω M P :=
  (ProfiniteFunctions.restrictPointPullD (Mon.mk (coefficients E))
    (Mon.mk (coefficients Ω))
    (ProfiniteFunctions.coefficientInclusion E Ω)
    (stratumScheme t)).inv.app
      ((parameterFunctions Ω P).obj ((pointZeroFunctor Ω).obj (model Ω E M))) ≫
  (pointPullD E (stratumScheme t)).map
    ((ProfiniteFunctions.restrictHomD (Mon.mk (coefficients E))
      (Mon.mk (coefficients Ω))
      (ProfiniteFunctions.coefficientInclusion E Ω) P).app
        ((pointZeroFunctor Ω).obj (model Ω E M)))

/-- The common parameter direct image of the restricted Omega-model.
Source: paragraph (3), common codomain of scalar compatibility
(blueprint: def-sfb-root-boundary-scalar-comparison). -/
def scalarEvaluatedTarget (P : Profinite.{u}) :
    DerivedCategory (SiteMod E (stratumScheme t)) :=
  (pushD E (test (stratumScheme t) P).hom).obj
    ((pointPullD E (test (stratumScheme t) P).left).obj
      ((Mod.comap (ProfiniteFunctions.coefficientInclusion E Ω)).mapDerivedCategory.obj
          ((pointZeroFunctor Ω).obj (model Ω E M))))

/-- Evaluation of the common E-internal-functions target on the actual boundary test scheme.
Source: paragraph (3), compatibility through canonical parameter evaluation
(blueprint: def-sfb-root-boundary-scalar-comparison). -/
def scalarCommonEvaluation (P : Profinite.{u}) :
    scalarCommonTarget t E Ω M P ⟶ scalarEvaluatedTarget t E Ω M P :=
  (derivedEvaluation E (stratumScheme t) P).app
    ((Mod.comap (ProfiniteFunctions.coefficientInclusion E Ω)).mapDerivedCategory.obj
        ((pointZeroFunctor Ω).obj (model Ω E M)))

/-- The canonical map from the restricted Omega full source to the E full source of Res N_Omega.
All pullback and pushforward restriction comparisons retain their given directions.
Source: paragraph (3), canonical scalar-restriction comparisons
(blueprint: def-sfb-root-boundary-scalar-comparison). -/
def scalarFullRestriction (N : SiteMod E (tower p t)) (P : Profinite.{u}) :
    (scalarRestrictionD (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω)
      (stratumScheme t)).obj
        (fullSource Ω p t
          ((scalarExtension (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω)
            (tower p t)).obj N) P) ⟶
      fullOn E p t P
        ((scalarRestrictionD (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω)
          (test (tower p t) P).left).obj
            (testModule Ω p t
              ((scalarExtension (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω)
                (tower p t)).obj N) P)) :=
  (scalarPull (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω)
    (stratumInclusion t)).hom.app
      ((pushD Ω (qP p t P)).obj (testModule Ω p t
        ((scalarExtension (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω)
          (tower p t)).obj N) P)) ≫
  (pullD E (stratumInclusion t)).map
    ((scalarPush (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω) (qP p t P)).app
      (testModule Ω p t
        ((scalarExtension (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω)
          (tower p t)).obj N) P))

/-- Boundary exchange on Res N_Omega followed by the actual scalar-extended identification.
Its target is the same evaluated restricted model as both normalized comparisons.
Source: paragraph (3), scalar restriction and the supplied boundary identification
(blueprint: def-sfb-root-boundary-scalar-comparison). -/
def scalarCommonBoundary (N : SiteMod E (tower p t))
    (eΩ : (CondensedRing.upperStar (coefficients Ω) (boundary p t)).obj
      ((scalarExtension (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω) (tower p t)).obj N) ≅
        (pointPull Ω (stratumScheme t)).obj (model Ω E M)) (P : Profinite.{u}) :
    fullOn E p t P
      ((scalarRestrictionD (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω)
        (test (tower p t) P).left).obj
          (testModule Ω p t
            ((scalarExtension (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω)
              (tower p t)).obj N) P)) ⟶ scalarEvaluatedTarget t E Ω M P :=
  restrictionOn E p t P
    ((scalarRestrictionD (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω)
      (test (tower p t) P).left).obj
        (testModule Ω p t
          ((scalarExtension (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω)
            (tower p t)).obj N) P)) ≫
  (pushD E (test (stratumScheme t) P).hom).map
    ((scalarPull (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω)
        (testMap (boundary p t) P)).inv.app
      (testModule Ω p t
        ((scalarExtension (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω)
          (tower p t)).obj N) P) ≫
    (scalarRestrictionD (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω)
      (test (stratumScheme t) P).left).map
        (boundaryModelDerivedMap Ω p t
          ((scalarExtension (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω)
            (tower p t)).obj N) P (model Ω E M)
          eΩ) ≫
    (ProfiniteFunctions.restrictPointPullD (Mon.mk (coefficients E))
      (Mon.mk (coefficients Ω))
      (ProfiniteFunctions.coefficientInclusion E Ω)
      (test (stratumScheme t) P).left).inv.app
        ((pointZeroFunctor Ω).obj (model Ω E M)))

/-- The scalar compatibility equation for the two normalized comparisons in a common target.
The first summand uses alpha_E followed by RHom of the actual model unit; the second uses
restricted alpha_Omega followed by the canonical internal-Hom restriction comparison.
The biproduct packages the two legs of the canonical full-source cospan into one equation;
its right side uses the actual tensor unit and directional restrictionPush, then the same
boundary exchange. No restrictionPush or scalar/direct-image comparison is inverted.
Only M_Omega and the scalar extension of e occur, never arbitrary new boundary data.
Source: paragraph (3), compatibility under ordinary scalar extension E to Omega
(blueprint: def-sfb-root-boundary-scalar-comparison). -/
def ScalarCompatibility : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module E M] [FiniteDimensional E M]
    (N : SiteMod E (tower p t)),
    IsLisseCoefficientModule (coefficients E) N →
    ∀ (e : (CondensedRing.upperStar (coefficients E) (boundary p t)).obj N ≅
      (pointPull E (stratumScheme t)).obj (model E E M))
    (eΩ : (CondensedRing.upperStar (coefficients Ω) (boundary p t)).obj
      ((scalarExtension (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω) (tower p t)).obj N) ≅
        (pointPull Ω (stratumScheme t)).obj (model Ω E M)),
    IsScalarExtendedBoundary p t E Ω M N e eΩ →
    ∀ (P : Profinite.{u}) (α : openSource E p t N P ≅ target E t (model E E M) P)
    (α' : openSource Ω p t
      ((scalarExtension (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω)
        (tower p t)).obj N) P ≅ target Ω t (model Ω E M) P),
    Normalization E p t N (model E E M) e P α →
    Normalization Ω p t
      ((scalarExtension (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω)
        (tower p t)).obj N) (model Ω E M)
      eΩ P α' →
    biprod.desc
      (openUnit E p t N P ≫ α.hom ≫ scalarTargetUnit t E Ω M P ≫
        scalarCommonEvaluation t E Ω M P)
      ((scalarRestrictionD (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω)
        (stratumScheme t)).map
          (openUnit Ω p t
            ((scalarExtension (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω)
              (tower p t)).obj N) P ≫ α'.hom) ≫
        scalarTargetRestriction t E Ω M P ≫ scalarCommonEvaluation t E Ω M P) =
    biprod.desc
      (fullOnMap E p t P
        (scalarTestUnit (G := Ω) E
      (ProfiniteFunctions.coefficientInclusion E Ω) p t N P))
      (scalarFullRestriction p t E Ω N P) ≫ scalarCommonBoundary p t E Ω M N eΩ P

end FiniteModels
end AlgebraicGeometry.ProEtale.RootBoundary
