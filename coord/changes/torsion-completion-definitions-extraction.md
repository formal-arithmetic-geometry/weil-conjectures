# AlgebraicGeometry.Scheme.torsionCompletionRing and companion definitions

## Reason

The proved ideal-power lemma and the independent multiplication-difference criterion need
coefficient definitions without importing their consumer theorem. Extract the existing
17 definitions, abbreviations and instances into `Sheaf.Paper.TorsionCompletionDefinitions`.
The item publicly imports that module, so importing the original module still exposes every
original declaration. Bodies, types, universes, names and visibility are unchanged; only
source docstring node references move. No target changes meaning. The theorem signature is
unchanged. No module held by another group is adapted.

The original direct public imports are supplied transitively by the definitions module.
The proof now imports only the actual algebra, locality, localization, ideal-power and
criterion modules it uses. The extraction is for an acyclic mathematical interface, not
to address a compile timeout. Every file compiles separately within the normal limit.

## Old

In `lean/Sheaf/Paper/TorsionLimitSheafCompleteness.lean`:

```lean
/-- The constant commutative coefficient sheaf on the recorded small model.
Source: Stacks Tags 099P, 099Q
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
abbrev torsionCompletionRing (X : Scheme.{t}) (A : Type u) [CommRing A] :=
  (constantSheaf (coefficientProEtaleModelTopology.{t, u} X)
    CommRingCat.{max u (t + 1)}).obj (CommRingCat.of (ULift.{t + 1} A))

/-- Forget commutativity of the constant ring sheaf, retaining the actual ring sheaf.
Source: Stacks Tags 099P, 099Q
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
abbrev torsionCompletionModuleRing (X : Scheme.{t}) (A : Type u) [CommRing A] :=
  (sheafCompose (coefficientProEtaleModelTopology.{t, u} X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj (torsionCompletionRing X A)

/-- The module-sheaf category on this model is precisely the recorded ringed-site category.
Source: Stacks Tags 099P, 099Q
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
abbrev TorsionCompletionModules (X : Scheme.{t}) (A : Type u) [CommRing A] :=
  ringedSiteModules.{max u (t + 1)} (torsionCompletionModuleRing X A)

/-- The constant quotient morphism, obtained by sheafifying the actual quotient ring map.
Source: Stacks Tag 099P
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
def torsionCompletionQuotient (X : Scheme.{t}) {A : Type u} [CommRing A] (I : Ideal A) :
    torsionCompletionModuleRing X A ⟶ torsionCompletionModuleRing X (A ⧸ I) :=
  (sheafCompose (coefficientProEtaleModelTopology.{t, u} X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
    ((constantSheaf _ CommRingCat.{max u (t + 1)}).map
      (CommRingCat.ofHom (RingHom.ulift (Ideal.Quotient.mk I))))

/-- The quotient ring as a module over the constant original ring.
Source: Stacks Tag 099P
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
abbrev torsionCompletionQuotientModule (X : Scheme.{t}) {A : Type u}
    [CommRing A] (I : Ideal A) :=
  (SheafOfModules.restrictScalars (torsionCompletionQuotient X I)).obj
    (SheafOfModules.unit (torsionCompletionModuleRing X (A ⧸ I)))

/-- The unit sections of the quotient ring form a global section of its module sheaf.
Source: Stacks Tag 099P
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
def torsionCompletionQuotientOne (X : Scheme.{t}) {A : Type u}
    [CommRing A] (I : Ideal A) : (torsionCompletionQuotientModule X I).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ (1 : (torsionCompletionModuleRing X (A ⧸ I)).obj.obj U))
    (fun {_ _} f ↦ ((torsionCompletionModuleRing X (A ⧸ I)).obj.map f).hom.map_one)

/-- The quotient map on modules sends the unit generator to one, hence sends a to its
quotient image. No arbitrary map is chosen.
Source: Stacks Tag 099P
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
def torsionCompletionQuotientMap (X : Scheme.{t}) {A : Type u} [CommRing A] (I : Ideal A) :
    SheafOfModules.unit (torsionCompletionModuleRing X A) ⟶
      torsionCompletionQuotientModule X I :=
  (SheafOfModules.unitHomEquiv _).symm (torsionCompletionQuotientOne X I)

/-- The extended ideal I A is the kernel of A → A/I as module sheaves. Constant
sheafification is exact, so this is the ideal generated locally by the constants in I.
Source: Stacks Tags 099P, 099Q
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
def torsionCompletionIdeal (X : Scheme.{t}) {A : Type u} [CommRing A] (I : Ideal A) :
    TorsionCompletionModules X A :=
  kernel (torsionCompletionQuotientMap X I)

/-- The canonical ideal inclusion, not a separately chosen embedding.
Source: Stacks Tags 099P, 099Q
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
def torsionCompletionIdealInclusion (X : Scheme.{t}) {A : Type u}
    [CommRing A] (I : Ideal A) :
    torsionCompletionIdeal X I ⟶ SheafOfModules.unit (torsionCompletionModuleRing X A) :=
  kernel.ι (torsionCompletionQuotientMap X I)

/-- Sheafification of abelian coefficients on the coefficient-sized small model.
This invokes the general small-site theorem, avoiding successor-universe inference.
Source: Stacks Tags 03DA, 099Q
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
instance (priority := 20000) torsionCompletionSheafify (X : Scheme.{t}) :
    HasSheafify (coefficientProEtaleModelTopology.{t, u} X)
      AddCommGrpCat.{max u (t + 1)} :=
  GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _

/-- The same abelian sheafification on each slice of the unchanged model site.
Source: Stacks Tags 03DA, 03DJ, 099Q
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
instance (priority := 20000) torsionCompletionSliceSheafify (X : Scheme.{t})
    (U : coefficientProEtaleSiteModel.{t, u} X) :
    HasSheafify ((coefficientProEtaleModelTopology.{t, u} X).over U)
      AddCommGrpCat.{max u (t + 1)} :=
  GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _

/-- Use the standard localization at quasi-isomorphisms for the module-sheaf category.
Source: Stacks Tags 05RU, 099Q
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
abbrev TorsionCompletionDerived (X : Scheme.{t}) (A : Type u) [CommRing A] :=
  @DerivedCategory (TorsionCompletionModules X A) _ _ (HasDerivedCategory.standard _)

/-- The localization functor for this choice of derived-category universe.
Source: Stacks Tags 05RU, 099Q
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
def torsionCompletionLocalization (X : Scheme.{t}) (A : Type u) [CommRing A] :
    CochainComplex (TorsionCompletionModules X A) ℤ ⥤ TorsionCompletionDerived X A :=
  @DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)

/-- Derived completeness is the recorded vanishing condition on every slice and for
 every section of the extended ideal. The standard derived categories are chosen on
 all slices as well; no additional existence hypothesis is imposed.
Source: Stacks Tags 0999, 099F, 099Q
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
def IsTorsionCompletionComplete (X : Scheme.{t}) {A : Type u} [CommRing A] (I : Ideal A)
    (K : TorsionCompletionDerived X A) : Prop :=
  letI := HasDerivedCategory.standard (TorsionCompletionModules X A)
  letI : ∀ U : coefficientProEtaleSiteModel.{t, u} X,
      HasDerivedCategory.{max u (t + 1) + 1} (ringedSiteModules.{max u (t + 1)}
        ((sheafCompose _
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
            ((torsionCompletionRing X A).over U))) :=
    fun _ ↦ HasDerivedCategory.standard _
  IsLocallyDerivedRingedIdealComplete (torsionCompletionRing X A)
    (torsionCompletionIdeal X I) (torsionCompletionIdealInclusion X I) K

/-- Degree-zero derived completeness of a sheaf.
Source: Stacks Tag 099Q (1)
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
def IsTorsionCompletionCompleteSheaf (X : Scheme.{t}) {A : Type u} [CommRing A]
    (I : Ideal A) (F : TorsionCompletionModules X A) : Prop :=
  IsTorsionCompletionComplete X I ((torsionCompletionLocalization X A).obj
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F))

/-- An ideal subsheaf annihilates a module if every one of its local sections acts by zero.
This expresses sheaf annihilation, with no section-finiteness hypothesis.
Source: Stacks Tag 099P
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
def IsAnnihilatedByModuleIdeal {C : Type v} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{v})
    (M : SheafOfModules.{v} R)
    (ι : M ⟶ SheafOfModules.unit R) (F : SheafOfModules.{v} R) : Prop :=
  ∀ (U : C) (y : M.val.obj (op U)) (x : F.val.obj (op U)),
    ι.val.app (op U) y • x = 0

/-- Locally F is an ordinary countable inverse limit, with level n indexed by the
positive exponent n+1. The covering sieve condition includes every object and arbitrary
further slices. Transition maps have no epimorphism condition.
Source: Stacks Tags 099P, 099Q (4)
(blueprint: lem-weil-pbc-torsion-limit-sheaf-completeness). -/
def IsLocallyPowerTorsionLimit (X : Scheme.{t}) {A : Type u} [CommRing A] (I : Ideal A)
    (F : TorsionCompletionModules X A) : Prop :=
  ∀ U : coefficientProEtaleSiteModel.{t, u} X,
    ∃ S : Sieve U, S ∈ coefficientProEtaleModelTopology.{t, u} X U ∧
      ∀ (V : coefficientProEtaleSiteModel.{t, u} X) (f : V ⟶ U), S f →
        ∃ (G : ℕ → SheafOfModules.{max u (t + 1)}
            ((torsionCompletionModuleRing X A).over V))
          (g : ∀ n : ℕ, G (n + 1) ⟶ G n),
          (∀ n : ℕ, IsAnnihilatedByModuleIdeal
            ((torsionCompletionModuleRing X A).over V)
            ((torsionCompletionIdeal X (I ^ (n + 1))).over V)
            ((torsionCompletionIdealInclusion X (I ^ (n + 1))).over V) (G n)) ∧
          Nonempty (F.over V ≅ limit (Functor.ofOpSequence g))
```

## New

In `lean/Sheaf/Paper/TorsionCompletionDefinitions.lean`, publicly imported by the item:

```lean
/-- The constant commutative coefficient sheaf on the recorded small model.
Source: Stacks Tags 099P, 099Q
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
abbrev torsionCompletionRing (X : Scheme.{t}) (A : Type u) [CommRing A] :=
  (constantSheaf (coefficientProEtaleModelTopology.{t, u} X)
    CommRingCat.{max u (t + 1)}).obj (CommRingCat.of (ULift.{t + 1} A))

/-- Forget commutativity of the constant ring sheaf, retaining the actual ring sheaf.
Source: Stacks Tags 099P, 099Q
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
abbrev torsionCompletionModuleRing (X : Scheme.{t}) (A : Type u) [CommRing A] :=
  (sheafCompose (coefficientProEtaleModelTopology.{t, u} X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj (torsionCompletionRing X A)

/-- The module-sheaf category on this model is precisely the recorded ringed-site category.
Source: Stacks Tags 099P, 099Q
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
abbrev TorsionCompletionModules (X : Scheme.{t}) (A : Type u) [CommRing A] :=
  ringedSiteModules.{max u (t + 1)} (torsionCompletionModuleRing X A)

/-- The constant quotient morphism, obtained by sheafifying the actual quotient ring map.
Source: Stacks Tag 099P
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
def torsionCompletionQuotient (X : Scheme.{t}) {A : Type u} [CommRing A] (I : Ideal A) :
    torsionCompletionModuleRing X A ⟶ torsionCompletionModuleRing X (A ⧸ I) :=
  (sheafCompose (coefficientProEtaleModelTopology.{t, u} X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
    ((constantSheaf _ CommRingCat.{max u (t + 1)}).map
      (CommRingCat.ofHom (RingHom.ulift (Ideal.Quotient.mk I))))

/-- The quotient ring as a module over the constant original ring.
Source: Stacks Tag 099P
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
abbrev torsionCompletionQuotientModule (X : Scheme.{t}) {A : Type u}
    [CommRing A] (I : Ideal A) :=
  (SheafOfModules.restrictScalars (torsionCompletionQuotient X I)).obj
    (SheafOfModules.unit (torsionCompletionModuleRing X (A ⧸ I)))

/-- The unit sections of the quotient ring form a global section of its module sheaf.
Source: Stacks Tag 099P
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
def torsionCompletionQuotientOne (X : Scheme.{t}) {A : Type u}
    [CommRing A] (I : Ideal A) : (torsionCompletionQuotientModule X I).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ (1 : (torsionCompletionModuleRing X (A ⧸ I)).obj.obj U))
    (fun {_ _} f ↦ ((torsionCompletionModuleRing X (A ⧸ I)).obj.map f).hom.map_one)

/-- The quotient map on modules sends the unit generator to one, hence sends a to its
quotient image. No arbitrary map is chosen.
Source: Stacks Tag 099P
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
def torsionCompletionQuotientMap (X : Scheme.{t}) {A : Type u} [CommRing A] (I : Ideal A) :
    SheafOfModules.unit (torsionCompletionModuleRing X A) ⟶
      torsionCompletionQuotientModule X I :=
  (SheafOfModules.unitHomEquiv _).symm (torsionCompletionQuotientOne X I)

/-- The extended ideal I A is the kernel of A → A/I as module sheaves. Constant
sheafification is exact, so this is the ideal generated locally by the constants in I.
Source: Stacks Tags 099P, 099Q
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
def torsionCompletionIdeal (X : Scheme.{t}) {A : Type u} [CommRing A] (I : Ideal A) :
    TorsionCompletionModules X A :=
  kernel (torsionCompletionQuotientMap X I)

/-- The canonical ideal inclusion, not a separately chosen embedding.
Source: Stacks Tags 099P, 099Q
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
def torsionCompletionIdealInclusion (X : Scheme.{t}) {A : Type u}
    [CommRing A] (I : Ideal A) :
    torsionCompletionIdeal X I ⟶ SheafOfModules.unit (torsionCompletionModuleRing X A) :=
  kernel.ι (torsionCompletionQuotientMap X I)

/-- Sheafification of abelian coefficients on the coefficient-sized small model.
This invokes the general small-site theorem, avoiding successor-universe inference.
Source: Stacks Tags 03DA, 099Q
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
instance (priority := 20000) torsionCompletionSheafify (X : Scheme.{t}) :
    HasSheafify (coefficientProEtaleModelTopology.{t, u} X)
      AddCommGrpCat.{max u (t + 1)} :=
  GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _

/-- The same abelian sheafification on each slice of the unchanged model site.
Source: Stacks Tags 03DA, 03DJ, 099Q
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
instance (priority := 20000) torsionCompletionSliceSheafify (X : Scheme.{t})
    (U : coefficientProEtaleSiteModel.{t, u} X) :
    HasSheafify ((coefficientProEtaleModelTopology.{t, u} X).over U)
      AddCommGrpCat.{max u (t + 1)} :=
  GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _

/-- Use the standard localization at quasi-isomorphisms for the module-sheaf category.
Source: Stacks Tags 05RU, 099Q
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
abbrev TorsionCompletionDerived (X : Scheme.{t}) (A : Type u) [CommRing A] :=
  @DerivedCategory (TorsionCompletionModules X A) _ _ (HasDerivedCategory.standard _)

/-- The localization functor for this choice of derived-category universe.
Source: Stacks Tags 05RU, 099Q
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
def torsionCompletionLocalization (X : Scheme.{t}) (A : Type u) [CommRing A] :
    CochainComplex (TorsionCompletionModules X A) ℤ ⥤ TorsionCompletionDerived X A :=
  @DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)

/-- Derived completeness is the recorded vanishing condition on every slice and for
 every section of the extended ideal. The standard derived categories are chosen on
 all slices as well; no additional existence hypothesis is imposed.
Source: Stacks Tags 0999, 099F, 099Q
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
def IsTorsionCompletionComplete (X : Scheme.{t}) {A : Type u} [CommRing A] (I : Ideal A)
    (K : TorsionCompletionDerived X A) : Prop :=
  letI := HasDerivedCategory.standard (TorsionCompletionModules X A)
  letI : ∀ U : coefficientProEtaleSiteModel.{t, u} X,
      HasDerivedCategory.{max u (t + 1) + 1} (ringedSiteModules.{max u (t + 1)}
        ((sheafCompose _
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
            ((torsionCompletionRing X A).over U))) :=
    fun _ ↦ HasDerivedCategory.standard _
  IsLocallyDerivedRingedIdealComplete (torsionCompletionRing X A)
    (torsionCompletionIdeal X I) (torsionCompletionIdealInclusion X I) K

/-- Degree-zero derived completeness of a sheaf.
Source: Stacks Tag 099Q (1)
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
def IsTorsionCompletionCompleteSheaf (X : Scheme.{t}) {A : Type u} [CommRing A]
    (I : Ideal A) (F : TorsionCompletionModules X A) : Prop :=
  IsTorsionCompletionComplete X I ((torsionCompletionLocalization X A).obj
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F))

/-- An ideal subsheaf annihilates a module if every one of its local sections acts by zero.
This expresses sheaf annihilation, with no section-finiteness hypothesis.
Source: Stacks Tag 099P
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
def IsAnnihilatedByModuleIdeal {C : Type v} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{v})
    (M : SheafOfModules.{v} R)
    (ι : M ⟶ SheafOfModules.unit R) (F : SheafOfModules.{v} R) : Prop :=
  ∀ (U : C) (y : M.val.obj (op U)) (x : F.val.obj (op U)),
    ι.val.app (op U) y • x = 0

/-- Locally F is an ordinary countable inverse limit, with level n indexed by the
positive exponent n+1. The covering sieve condition includes every object and arbitrary
further slices. Transition maps have no epimorphism condition.
Source: Stacks Tags 099P, 099Q (4)
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
def IsLocallyPowerTorsionLimit (X : Scheme.{t}) {A : Type u} [CommRing A] (I : Ideal A)
    (F : TorsionCompletionModules X A) : Prop :=
  ∀ U : coefficientProEtaleSiteModel.{t, u} X,
    ∃ S : Sieve U, S ∈ coefficientProEtaleModelTopology.{t, u} X U ∧
      ∀ (V : coefficientProEtaleSiteModel.{t, u} X) (f : V ⟶ U), S f →
        ∃ (G : ℕ → SheafOfModules.{max u (t + 1)}
            ((torsionCompletionModuleRing X A).over V))
          (g : ∀ n : ℕ, G (n + 1) ⟶ G n),
          (∀ n : ℕ, IsAnnihilatedByModuleIdeal
            ((torsionCompletionModuleRing X A).over V)
            ((torsionCompletionIdeal X (I ^ (n + 1))).over V)
            ((torsionCompletionIdealInclusion X (I ^ (n + 1))).over V) (G n)) ∧
          Nonempty (F.over V ≅ limit (Functor.ofOpSequence g))
```

## Users

`tools/downstream.py Sheaf.Paper.TorsionLimitSheafCompleteness --uses` was run for all
17 moved declaration names. There are zero downstream modules; each declaration occurs
only in the original module. Its public import remains the compatibility entry point.
The corresponding DAG parents remain active and are not withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.TorsionLimitSheafCompleteness | S1 | Publicly imports the definitions; same signatures and meanings; complete combining proof. |
| Sheaf.Paper.TorsionCompletionDefinitions | S1, new | Holds the 17 unchanged declarations. |
| Sheaf.Paper.TorsionCompletionIdealPowers | S1, new | Uses coefficient kernels in its proved power-membership theorem. |
| Sheaf.Paper.ProEtaleMultiplicationDifferenceCriterion | S1, new | Uses the model and standard slice derived-category instances. |

## Status

landed 20261020T221341-L-4176958 2026-10-20 (merge of deliver/S1/Sheaf.Paper.TorsionLimitSheafCompleteness)
