# CategoryTheory.InternalActionSite.Object and the action-site foundation

## Reason

The planned proof dependencies imported the module containing the presentation theorem. Importing them back to prove that theorem creates the cycles Presentation -> TwistedModulePresheafEquivalence -> TwistedSiteSieveGeometry -> Presentation and Presentation -> EquivariantModuleSheafificationReflector -> Presentation. Extract the pre-existing foundational declarations without changing any signature or data definition, prove their ten outstanding laws directly, and publicly re-export them from Presentation. This is a dependency-cycle repair, not a compile-time split. The original complete module was already well below the per-file limit.

The original import-cycle repair in the formerly held module (TwistedSiteSieveGeometry, J7; now unclaimed after landing) changes its public-import target. The original source imports would produce this cycle after adding the required proof import (derived directly from their headers): `import cycle: Sheaf.CategoryTheory.InternalActionSitePresentation -> Sheaf.CategoryTheory.TwistedModulePresheafEquivalence -> Sheaf.CategoryTheory.TwistedSiteSieveGeometry -> Sheaf.CategoryTheory.InternalActionSitePresentation`. Compiling against stale compiled outputs can hide this cycle; the source dependency graph cannot. All existing public declarations and the complete sieve_geometry argument are preserved; the two private helper proofs are shared as described below. The reflector and module-equivalence modules are currently unclaimed. Their newly landed complete proofs are preserved.

The returned packet also duplicated `arrow_ext` and `labeled_pullback`, which were
already proved privately in TwistedSiteSieveGeometry. The repair moves those existing
proofs into the common Basic module and makes them public for reuse. Geometry removes
its private copies and uses the imported lemmas, keeping one proof of each fact.
Its pullback proof's local `comp_label` simplification becomes the same definitional
composition equation followed by `simp`; the original lift and universality proof
are preserved. This sharing is necessary because importing geometry from Basic
would close the dependency cycle again. Geometry is unclaimed at repair time.

## Old

The foundational declaration block in InternalActionSitePresentation, verbatim:

```lean
/-- Objects of the twisted category, with the same carrier as the base category.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation). -/
structure Object (K : Cᵒᵖ ⥤ GrpCat.{u}) where
  /-- The base object. -/
  base : C

/-- An arrow is a base arrow and a section of the group at its source.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation). -/
structure Arrow (X Y : Object K) where
  /-- The underlying arrow. -/
  base : X.base ⟶ Y.base
  /-- Its label. -/
  label : K.obj (op X.base)

/-- Identities and the prescribed multiplication order on labels.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation). -/
instance categoryStruct : CategoryStruct (Object K) where
  Hom := Arrow K
  id X := ⟨𝟙 X.base, 1⟩
  comp f g := ⟨f.base ≫ g.base, f.label * K.map f.base.op g.label⟩

/-- The category equations for the displayed raw composition.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation).
Proof: functoriality and preservation of multiplication by restrictions give the same
label c h*b (gh)*a for both associations. Identity labels are 1. -/
theorem category_laws :
    (∀ (X Y : Object K) (f : X ⟶ Y), 𝟙 X ≫ f = f) ∧
    (∀ (X Y : Object K) (f : X ⟶ Y), f ≫ 𝟙 Y = f) ∧
    (∀ (W X Y Z : Object K) (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),
      (f ≫ g) ≫ h = f ≫ (g ≫ h)) := by
  sorry

/-- The twisted category, with its actual objects, arrows, and composition.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation). -/
instance category : SmallCategory (Object K) where
  __ := categoryStruct K
  id_comp := (category_laws K).1 _ _
  comp_id := (category_laws K).2.1 _ _
  assoc := (category_laws K).2.2 _ _ _ _

/-- Projection forgets the label.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation). -/
def projection : Object K ⥤ C where
  obj X := X.base
  map f := f.base

/-- Covering families have covering underlying families in the prescribed base site.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation). -/
def precoverage (J : Precoverage C) : Precoverage (Object K) where
  coverings X := {S | (fun _Y f => ∃ a, S (Arrow.mk f a)) ∈ J X.base}

/-- A twisted arrow in the opposite category, for module restriction maps.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation). -/
def opArrow {X Y : C} (f : X ⟶ Y) (a : K.obj (op X)) :
    op (Object.mk (K := K) Y) ⟶ op (Object.mk (K := K) X) :=
  @Quiver.Hom.op (Object K) inferInstance ⟨X⟩ ⟨Y⟩ ⟨f, a⟩

/-- The topology generated by the prescribed covering families.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation). -/
def topology (J : Precoverage C) : GrothendieckTopology (Object K) :=
  (precoverage K J).toGrothendieck

/-- Singleton presieves of isomorphisms are among the prescribed covers.
Source: Stacks 00VH, axiom (1)
(blueprint: lem-sfb-internal-action-site-presentation).
Proof: projection sends an inverse to an inverse, so the underlying singleton
is an isomorphism cover by hJ.1. Its image is the prescribed base singleton. -/
theorem hasIsos (J : Precoverage C) (hJ : J.IsSiteForCoverings) :
    (precoverage K J).HasIsos := by
  sorry

/-- Every prescribed cover admits covering pullbacks, for some choice of pullbacks.
Source: Stacks 00VH, axiom (3) and its clarification
(blueprint: lem-sfb-internal-action-site-presentation).
Proof: apply hJ.2.2 to the indexed underlying base family and base arrow.
For arrows (f,a),(g,b), the chosen base pullback with legs p,q lifts to legs
(p,1),(q,p*a (q*b)^-1). The cone equation determines the unique factor and label.
The projected covering is exactly the chosen base covering. No closure under
bind, or under all alternative choices of pullbacks, is asserted. -/
theorem covering_pullbacks [HasFiniteLimits C] (J : Precoverage C)
    (hJ : J.IsSiteForCoverings) :
    ∀ (I : Type u) (X : Object K) (U : I → Object K) (a : ∀ i, U i ⟶ X),
      Presieve.ofArrows U a ∈ precoverage K J X →
      ∀ (Y : Object K) (b : Y ⟶ X),
        ∃ (P : I → Object K) (p : ∀ i, P i ⟶ Y) (q : ∀ i, P i ⟶ U i),
          (∀ i, IsPullback (p i) (q i) b (a i)) ∧
            Presieve.ofArrows P p ∈ precoverage K J Y := by
  sorry

/-- The label-1 arrows in a twisted sieve are closed under base precomposition.
Source: action-site construction; Stacks, definition of a sieve
(blueprint: lem-sfb-internal-action-site-presentation).
Proof: precompose (f,1) with (g,1) and use preservation of 1 by restriction.
The composite is (g ≫ f,1), so downward closure of S gives the assertion. -/
theorem labelOne_downward {X : Object K} (S : Sieve X)
    {Y Z : C} (f : Y ⟶ X.base) (g : Z ⟶ Y) :
    S (Arrow.mk f 1) → S (Arrow.mk (g ≫ f) 1) := by
  sorry

/-- The base sieve consisting of the arrows whose label-1 lifts lie in S.
Source: action-site construction; Stacks, definition of a sieve
(blueprint: lem-sfb-internal-action-site-presentation). -/
def labelOneSieve {X : Object K} (S : Sieve X) : Sieve X.base where
  arrows := fun _ f ↦ S (Arrow.mk f 1)
  downward_closed := fun hf g ↦ labelOne_downward K S _ g hf

/-- The generated topology is characterized by the base covering label-1 sieve.
Source: Stacks, Sites, definition-topology and definition-topology-associated-site;
action-site construction (blueprint: lem-sfb-internal-action-site-presentation).
Proof: membership of (f,a) in a sieve is equivalent to membership of (f,1),
by precomposing with the invertible arrows (1,a) and (1,a^-1). Thus twisted
sieves correspond to base sieves. Under this correspondence the sieve generated
by a prescribed covering family corresponds to the sieve generated by its base
family, and normalized families lift every base cover. Maximal sieves and
pullbacks correspond. For local character, test on all labels above each base
arrow; the corresponding base-sieve local-character condition is unchanged.
Consequently the topology transported from J.toGrothendieck is a Grothendieck
topology containing the prescribed generators, and the normalized generators
and the same three closure operations give the reverse containment. -/
theorem topology_mem_iff [HasFiniteLimits C] (J : Precoverage C)
    (hJ : J.IsSiteForCoverings) (X : Object K) (S : Sieve X) :
    S ∈ topology K J X ↔ labelOneSieve K S ∈ J.toGrothendieck X.base := by
  sorry

/-- The coefficient presheaf ignores labels and keeps commutative rings.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation). -/
def coefficientPresheaf (R : Cᵒᵖ ⥤ CommRingCat.{u}) :
    (Object K)ᵒᵖ ⥤ CommRingCat.{u} :=
  (projection K).op ⋙ R

/-- The trivial action makes the coefficient presheaf a sheaf on the action site.
Source: Stacks 00VH, 00YR (blueprint: lem-sfb-internal-action-site-presentation).
Proof: normalize every cover. Its matching equalizer is the original ring-sheaf
equalizer, because restrictions ignore labels and normalized pullbacks have label 1. -/
theorem coefficient_isSheaf [HasFiniteLimits C] (J : Precoverage C)
    (hJ : J.IsSiteForCoverings) (R : Sheaf J.toGrothendieck CommRingCat.{u}) :
    Presheaf.IsSheaf (topology K J) (coefficientPresheaf K R.obj) := by
  sorry

/-- The actual commutative coefficient sheaf on the action site.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation). -/
def coefficientSheaf [HasFiniteLimits C] (J : Precoverage C)
    (hJ : J.IsSiteForCoverings) (R : Sheaf J.toGrothendieck CommRingCat.{u}) :
    Sheaf (topology K J) CommRingCat.{u} :=
  ⟨coefficientPresheaf K R.obj, coefficient_isSheaf K J hJ R⟩

/-- A sectionwise linear action, natural under restriction. The monoid hom records
both action laws; the codomain consists of linear endomorphisms.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation). -/
structure LinearAction {R : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} R) where
  /-- Each group section acts by a linear endomorphism. -/
  act (X : Cᵒᵖ) : K.obj X →* Module.End (R.obj X) (M.obj X)
  /-- Action and restriction commute, with restriction of the group section. -/
  naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) (a : K.obj X) (m : M.obj X) :
    M.map f (act X a m) = act Y (K.map f a) (M.map f m)

/-- Equivariant presheaves of modules, with genuine sectionwise action data.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation). -/
structure EquivariantPresheaf (R : Cᵒᵖ ⥤ RingCat.{u}) where
  /-- The underlying presheaf of modules. -/
  val : PresheafOfModules.{u} R
  /-- Its natural linear group action. -/
  action : LinearAction K val

variable {K} {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- Equivariance of an ordinary module-presheaf morphism.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation). -/
def Equivariant {M N : EquivariantPresheaf K R} (f : M.val ⟶ N.val) : Prop :=
  ∀ (X : Cᵒᵖ) (a : K.obj X) (m : M.val.obj X),
    f.app X (M.action.act X a m) = N.action.act X a (f.app X m)

/-- Equivariant linear maps form an additive subgroup.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation).
Proof: zero and sums commute with each action by linearity; negatives do as well. -/
theorem equivariant_add_laws (M N : EquivariantPresheaf K R) :
    Equivariant (0 : M.val ⟶ N.val) ∧
    (∀ f g : M.val ⟶ N.val, Equivariant f → Equivariant g → Equivariant (f + g)) ∧
    (∀ f : M.val ⟶ N.val, Equivariant f → Equivariant (-f)) := by
  sorry

/-- Equivariant morphisms, as a subgroup of the ordinary linear morphisms.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation). -/
def homGroup (M N : EquivariantPresheaf K R) : AddSubgroup (M.val ⟶ N.val) where
  carrier := {f | Equivariant f}
  zero_mem' := (equivariant_add_laws M N).1
  add_mem' := (equivariant_add_laws M N).2.1 _ _
  neg_mem' := (equivariant_add_laws M N).2.2 _

/-- Identities and composition preserve equivariance.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation).
Proof: identities commute with the action; for a composite apply the two
successive equivariance equations to each section. -/
theorem equivariant_comp_laws :
    (∀ M : EquivariantPresheaf K R, Equivariant (𝟙 M.val)) ∧
    (∀ (M N P : EquivariantPresheaf K R) (f : M.val ⟶ N.val) (g : N.val ⟶ P.val),
      Equivariant f → Equivariant g → Equivariant (f ≫ g)) := by
  sorry

/-- Actual identities and composition of equivariant maps.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation). -/
instance equivariantCategoryStruct : CategoryStruct (EquivariantPresheaf K R) where
  Hom M N := homGroup M N
  id M := ⟨𝟙 M.val, equivariant_comp_laws.1 M⟩
  comp f g := ⟨f.val ≫ g.val, equivariant_comp_laws.2 _ _ _ _ _ f.property g.property⟩

/-- Category laws for equivariant maps.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation).
Proof: the underlying maps obey the category equations, and subtype equality
identifies equivariant maps having the same underlying map. -/
theorem equivariant_category_laws :
    (∀ (M N : EquivariantPresheaf K R) (f : M ⟶ N), 𝟙 M ≫ f = f) ∧
    (∀ (M N : EquivariantPresheaf K R) (f : M ⟶ N), f ≫ 𝟙 N = f) ∧
    (∀ (L M N P : EquivariantPresheaf K R) (f : L ⟶ M) (g : M ⟶ N) (h : N ⟶ P),
      (f ≫ g) ≫ h = f ≫ (g ≫ h)) := by
  sorry

/-- The category of sectionwise equivariant presheaves.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation). -/
instance equivariantCategory : Category (EquivariantPresheaf K R) where
  __ := equivariantCategoryStruct
  id_comp := equivariant_category_laws.1 _ _
  comp_id := equivariant_category_laws.2.1 _ _
  assoc := equivariant_category_laws.2.2 _ _ _ _

/-- Addition of equivariant maps is inherited from their additive subgroup.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation). -/
instance homAddCommGroup (M N : EquivariantPresheaf K R) : AddCommGroup (M ⟶ N) :=
  inferInstanceAs (AddCommGroup (homGroup M N))

/-- The distributivity laws for equivariant linear maps.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation).
Proof: forget to module-presheaf maps and use distributivity there. Subtype
extensionality lifts both equations; the inherited additions have the same carrier. -/
theorem equivariant_distributivity :
    (∀ (M N P : EquivariantPresheaf K R) (f g : M ⟶ N) (h : N ⟶ P),
      (f + g) ≫ h = f ≫ h + g ≫ h) ∧
    (∀ (M N P : EquivariantPresheaf K R) (f : M ⟶ N) (g h : N ⟶ P),
      f ≫ (g + h) = f ≫ g + f ≫ h) := by
  sorry

/-- The preadditive structure uses the actual addition of linear maps.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation). -/
instance equivariantPreadditive : Preadditive (EquivariantPresheaf K R) where
  homGroup := homAddCommGroup
  add_comp := (equivariant_distributivity (K := K) (R := R)).1
  comp_add := (equivariant_distributivity (K := K) (R := R)).2

/-- Forgetting the action keeps the module presheaf and every component map.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation). -/
def forgetPresheaf : EquivariantPresheaf K R ⥤ PresheafOfModules.{u} R where
  obj M := M.val
  map f := f.val

/-- Equivariant sheaves are equivariant presheaves whose module is a sheaf.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation). -/
abbrev EquivariantSheaf (J : GrothendieckTopology C) (S : Sheaf J RingCat.{u}) :=
  ObjectProperty.FullSubcategory
    (fun M : EquivariantPresheaf K S.obj => Presheaf.IsSheaf J M.val.presheaf)

/-- The inclusion of equivariant sheaves in equivariant presheaves.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation). -/
def inclusion (J : GrothendieckTopology C) (S : Sheaf J RingCat.{u}) :
    EquivariantSheaf (K := K) J S ⥤ EquivariantPresheaf K S.obj :=
  ObjectProperty.ι _

/-- Forgetting the action on a module sheaf.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation). -/
def forgetSheaf (J : GrothendieckTopology C) (S : Sheaf J RingCat.{u}) :
    EquivariantSheaf (K := K) J S ⥤ ringedSiteModules S where
  obj M := ⟨M.obj.val, M.property⟩
  map f := ⟨f.hom.val⟩



variable (K)

/-- The original commutative coefficient sheaf viewed as a ring sheaf.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation). -/
abbrev baseRing (J : GrothendieckTopology C) (S : Sheaf J CommRingCat.{u}) :
    Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj S

/-- The twisted coefficient sheaf viewed as a ring sheaf.
Source: action-site construction (blueprint: lem-sfb-internal-action-site-presentation). -/
abbrev twistedRing [HasFiniteLimits C] (J : Precoverage C)
    (hJ : J.IsSiteForCoverings)
    (S : Sheaf J.toGrothendieck CommRingCat.{u}) : Sheaf (topology K J) RingCat.{u} :=
  (sheafCompose (topology K J) (forget₂ CommRingCat RingCat)).obj
    (coefficientSheaf K J hJ S)
```

Original dependency imports:

```lean
public import Sheaf.CategoryTheory.InternalActionSitePresentation
```

in TwistedSiteSieveGeometry and EquivariantModuleSheafificationReflector.

The relocated geometry helpers originally had these private signatures (the
namespace variables C, its category instance, and K are unchanged):

```lean
private theorem arrow_ext {X Y : Object K} {f g : X ⟶ Y}
    (hb : f.base = g.base) (ha : f.label = g.label) : f = g

private theorem labeled_pullback {U V W P : Object K} (f : V ⟶ U) (g : W ⟶ U)
    (p : P.base ⟶ V.base) (q : P.base ⟶ W.base)
    (hp : IsPullback p q f.base g.base) :
    IsPullback (Arrow.mk p 1 : P ⟶ V)
      (Arrow.mk q (K.map p.op f.label * (K.map q.op g.label)⁻¹) : P ⟶ W) f g
```

## New

The original declarations are extracted to `InternalActionSiteBasic` with their
signatures and data definitions preserved, their theorem proofs completed, and
Presentation publicly re-exporting Basic. Two existing private geometry lemmas
become shared public lemmas in Basic, with their statements unchanged:

```lean
theorem arrow_ext {X Y : Object K} {f g : X ⟶ Y}
    (hb : f.base = g.base) (ha : f.label = g.label) : f = g := by
  -- Existing complete proof relocated from TwistedSiteSieveGeometry.

theorem labeled_pullback {U V W P : Object K} (f : V ⟶ U) (g : W ⟶ U)
    (p : P.base ⟶ V.base) (q : P.base ⟶ W.base)
    (hp : IsPullback p q f.base g.base) :
    IsPullback (Arrow.mk p 1 : P ⟶ V)
      (Arrow.mk q (K.map p.op f.label * (K.map q.op g.label)⁻¹) : P ⟶ W) f g := by
  -- Existing complete proof relocated from TwistedSiteSieveGeometry.

```

Both proofs are complete in the delivered Lean file; the comments above abbreviate
the change record only. The private copies in TwistedSiteSieveGeometry are removed,
and its existing uses resolve through its new public import of Basic. The reflector
also imports Basic, avoiding the presentation cycle. Presentation contains its
unchanged Presentation structure and a complete proof of presentation.

Existing definition-node attachments now identify Basic. The new foundation node
also attaches the two shared public lemmas. The geometry node records its dependency
on that foundation. No target statement or definition changes its meaning.

## Users

The complete transitive downstream list from tools/downstream.py is audited below. Declaration names, elaborated types and data expressions are preserved. The theorem proofs replace sorry with actual proofs; typeclass proof fields remain proof-irrelevant. Direct consumers are individually compiled against the delivered overlay.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CondensedGaloisGlobalDescent | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.FieldActionCoefficientTransportData | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.FieldActionDerivedSectionTransport | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.FieldActionGeometricTransportData | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.FieldActionScalarTransportData | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.FieldActionTransportData | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.CategoryTheory.ActionToposGeometricRestriction | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.CategoryTheory.CondensedBarScalarResolutionComparison | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.CategoryTheory.CondensedDerivedInflationArrows | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.CategoryTheory.CondensedGroupAlgebraExactForgetful | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.CategoryTheory.CondensedNormalSubgroupComparison | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.CategoryTheory.CondensedSplitCosetInduction | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.CategoryTheory.CondensedTensorInductionAdjunction | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.CategoryTheory.DiscreteLatticeCupExterior | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.CategoryTheory.EquivariantModuleSheafificationReflector | unclaimed | Only public import retargeted to Basic to break the proof-dependency cycle; declaration text unchanged. |
| Sheaf.CategoryTheory.InternalInflationGradedCup | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.CategoryTheory.LatticeAlgebraDerivedCup | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.CategoryTheory.LatticeDerivedInvariantsTensor | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.CategoryTheory.LatticeKoszulTriangulatedCupComparison | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.CategoryTheory.LatticeRestrictionCupComparison | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.CategoryTheory.OpenNormalActionInjectiveModels | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.CategoryTheory.ProfiniteActionCoherentPresentation | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.CategoryTheory.RelativeCyclicRestrictionModel | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.CategoryTheory.RelativeLatticeBridge | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.CategoryTheory.SheafActionGrothendieckInflation | X7 | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.CategoryTheory.SheafProductFixedAdjunction | X9 | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.CategoryTheory.TwistedModulePresheafEquivalence | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.CategoryTheory.TwistedSiteSieveGeometry | unclaimed | Import Basic; reuse the shared arrow_ext and labeled_pullback proofs moved from this module; sieve_geometry signature unchanged. |
| Sheaf.Paper.CanonicalPointScalarComparison | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.Paper.FieldActionToposCoefficients | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.Paper.FiniteImageOpenKernelInflation | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.Paper.GeometricCondensedFiniteScalarModel | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.Paper.IndUnipotentProcyclicDifference | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |
| Sheaf.Paper.PrimeToEllDerivedInvariantsReduction | unclaimed | Same names, signatures, definitions and public imports through the presentation re-export; no adaptation. |

The repair's read-only `downstream.py --uses` audit for each moved helper finds only
TwistedSiteSieveGeometry as a direct textual user. Its downstream module is
TwistedModulePresheafEquivalence, which retains its current source and compiles
against the repaired geometry. Presentation and all its direct consumers are also
checked against the repaired overlay. Public mathematical statements and target
meanings are unchanged; the added public helpers expose already-proved facts.

## Status

landed 20261023T230416-L-3424073 2026-10-23 (merge of deliver/B3/Sheaf.CategoryTheory.InternalActionSitePresentation)
