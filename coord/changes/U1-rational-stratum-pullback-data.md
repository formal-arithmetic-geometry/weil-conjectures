# RationalStratumPullback data declaration ownership

## Reason

The supporting ambient and finite-free lemmas must refer to the existing Pull,
Composition, Stratum, FreeModel and Chart structures without importing their
existence theorem. Move all 16 data declarations verbatim into a publicly reexported
module. Names, signatures, definition bodies, universes and visibility are unchanged.
No target statement or meaning changes. This prevents a circular import.

## Old

The following declarations were in `Sheaf.Paper.RationalStratumPullbackModels`:

```lean
/-- The actual continuous coefficient map, adjoint to precomposition on functions.
Source: BS 6.8.1--6.8.2 (blueprint: lem-per-rational-stratum-pullback-models). -/
def coefficient {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (adicTowerInverseImage f).obj (rationalCoefficientSheaf l X E) ⟶
      rationalCoefficientSheaf l Y E := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientPullback (ULift.{u + 1, u} E) f

/-- The structural scalar map on a base-changed chart, evaluated by precomposition.
Source: BS 6.8.1 (blueprint: lem-per-rational-stratum-pullback-models). -/
def scalarImage {X Y : Scheme.{u}} (f : Y ⟶ X) (V : X.ProEt)
    (b : (rationalCoefficientSheaf l X E).obj.obj (op V)) :
    (rationalCoefficientSheaf l Y E).obj.obj (op ((proEtaleBaseChange f).obj V)) := by
  letI := coefficientExtensionNormedField l E
  exact (continuousCoefficientDirectMap (ULift.{u + 1, u} E) f).hom.app (op V) b

/-- The existing finite free sheaf, with a lifted finite basis in the coefficient universe.
Source: BS 6.8.3 (blueprint: lem-per-rational-stratum-pullback-models). -/
abbrev free (X : Scheme.{u}) (r : ℕ) : pbcModules X (rationalCoefficientSheaf l X E) :=
  SheafOfModules.free (ULift.{u + 1} (Fin r))

/-- A basis section of the finite free sheaf on an arbitrary site object.
Source: BS 6.8.3 (blueprint: lem-per-rational-stratum-pullback-models). -/
def basis (X : Scheme.{u}) (r : ℕ) (j : Fin r) (V : X.ProEt) :
    (free l E X r).val.obj (op V) :=
  (SheafOfModules.freeSection (R := (adicLisseForget X).obj
    (rationalCoefficientSheaf l X E)) (ULift.up j)).val (op V)

/-- The ordinary and derived pullbacks are the published inverse image and scalar extension.
Only the universal comparison is recorded; its normalization fixes it on complexes.
Source: BS 6.8.15; Stacks 06YY
(blueprint: lem-per-rational-stratum-pullback-models). -/
structure Pull {X Y : Scheme.{u}} (f : Y ⟶ X)
    (c : (adicTowerInverseImage f).obj (rationalCoefficientSheaf l X E) ⟶
      rationalCoefficientSheaf l Y E) where
  [additive : (ContinuousRational.modulePull f c).Additive]
  counit : DerivedCategory.Q ⋙ ContinuousRational.derivedPull f c ⟶
    (ContinuousRational.modulePull f c).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  normalized : ContinuousRational.IsNormalizedPullCounit f c counit
  universal : (ContinuousRational.derivedPull f c).IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso _ (.up ℤ))
  computes : ∀ P : CochainComplex (pbcModules X (rationalCoefficientSheaf l X E)) ℤ,
    CochainComplex.IsAcyclicTensorKFlat (J := ProEt.topology X)
      (R := rationalCoefficientSheaf l X E) P → IsIso (counit.app P)


/-- The comparison supplied by the specified realization retains its completion-unit law.
Source: BS 6.8.14--6.8.15 (blueprint: lem-per-rational-stratum-pullback-models). -/
def pullAlong {X Y : ContinuousRational.Base.{u} l} {g : Y.scheme ⟶ X.scheme}
    {aX : ContinuousRational.At l E X} {aY : ContinuousRational.At l E Y}
    (a : ContinuousRational.Along l E g aY aX) : Pull l E g a.coefficient where
  additive := a.ordinaryAdditive
  counit := a.counit
  normalized := a.normalized_counit
  universal := a.universal
  computes := a.computes

/-- The canonical derived-to-ordinary map on a sheaf in degree zero.
Source: Stacks 06YY (blueprint: lem-per-rational-stratum-pullback-models). -/
def Pull.singleMap {X Y : Scheme.{u}} {f : Y ⟶ X}
    {c : (adicTowerInverseImage f).obj (rationalCoefficientSheaf l X E) ⟶
      rationalCoefficientSheaf l Y E} (p : Pull l E f c)
    (F : pbcModules X (rationalCoefficientSheaf l X E)) :
    (ContinuousRational.derivedPull f c).obj ((DerivedCategory.singleFunctor _ 0).obj F) ⟶
      (DerivedCategory.singleFunctor _ 0).obj ((ContinuousRational.modulePull f c).obj F) :=
  letI := p.additive
  p.counit.app ((CochainComplex.singleFunctor _ 0).obj F) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (ContinuousRational.modulePull f c) (.up ℤ) 0).hom.app F)

/-- Ambient composition, normalized on ordinary units and flat-term K-flat complexes.
This is the ambient comparison even when the schemes are arbitrary chart schemes.
Source: Stacks 0D6D; BS 6.8.15
(blueprint: lem-per-rational-stratum-pullback-models). -/
structure Composition {X Y Z : Scheme.{u}} (g : Y ⟶ X) (h : Z ⟶ Y)
    (cg : (adicTowerInverseImage g).obj (rationalCoefficientSheaf l X E) ⟶
      rationalCoefficientSheaf l Y E)
    (ch : (adicTowerInverseImage h).obj (rationalCoefficientSheaf l Y E) ⟶
      rationalCoefficientSheaf l Z E)
    (pg : Pull l E g cg) (ph : Pull l E h ch)
    (pc : Pull l E (h ≫ g) (coefficient l E (h ≫ g))) where
  [additiveG : (ContinuousRational.modulePull g cg).Additive]
  [additiveH : (ContinuousRational.modulePull h ch).Additive]
  [additiveC : (ContinuousRational.modulePull (h ≫ g)
    (coefficient l E (h ≫ g))).Additive]
  coefficients : coefficient l E (h ≫ g) =
    (proEtaleRingInverseImageComp h g).hom.app (rationalCoefficientSheaf l X E) ≫
      (adicTowerInverseImage h).map cg ≫ ch
  ordinary : ContinuousRational.modulePull (h ≫ g) (coefficient l E (h ≫ g)) ≅
    ContinuousRational.modulePull g cg ⋙ ContinuousRational.modulePull h ch
  units : ∀ (M : pbcModules X (rationalCoefficientSheaf l X E))
      (V : X.ProEt) (m : M.val.obj (op V)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange (h ≫ g)).obj V))
        (ContinuousRational.moduleUnit (h ≫ g) (coefficient l E (h ≫ g)) M V m) =
      (((ContinuousRational.modulePull h ch).obj
        ((ContinuousRational.modulePull g cg).obj M)).val.map
          ((MorphismProperty.Over.pullbackComp h g).hom.app V).op)
        (ContinuousRational.moduleUnit h ch ((ContinuousRational.modulePull g cg).obj M)
          ((proEtaleBaseChange g).obj V) (ContinuousRational.moduleUnit g cg M V m))
  complex :
    (ContinuousRational.modulePull (h ≫ g) (coefficient l E (h ≫ g))).mapHomologicalComplex
        (.up ℤ) ≅
      (ContinuousRational.modulePull g cg).mapHomologicalComplex (.up ℤ) ⋙
        (ContinuousRational.modulePull h ch).mapHomologicalComplex (.up ℤ)
  components : ∀ P (n : ℤ), (complex.hom.app P).f n = ordinary.hom.app (P.X n)
  derived : ContinuousRational.derivedPull (h ≫ g) (coefficient l E (h ≫ g)) ≅
    ContinuousRational.derivedPull g cg ⋙ ContinuousRational.derivedPull h ch
  normalization : ∀ P : CochainComplex (pbcModules X (rationalCoefficientSheaf l X E)) ℤ,
    CochainComplex.IsAcyclicTensorKFlat (J := ProEt.topology X)
        (R := rationalCoefficientSheaf l X E) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
      (R := rationalCoefficientSheaf l X E) (P.X n)) →
    pc.counit.app P ≫ DerivedCategory.Q.map (complex.hom.app P) =
      derived.hom.app (DerivedCategory.Q.obj P) ≫
        (ContinuousRational.derivedPull h ch).map (pg.counit.app P) ≫
        ph.counit.app (((ContinuousRational.modulePull g cg).mapHomologicalComplex
          (.up ℤ)).obj P)

/-- Data fixing the stratum square by its two normalized ambient compositions.
No reduced structure is put on the fibre product.
Source: BS 6.8.15; Stacks 0D6D
(blueprint: lem-per-rational-stratum-pullback-models). -/
structure Stratum {X Y : ContinuousRational.Base.{u} l} (g : Y.scheme ⟶ X.scheme)
    (aX : ContinuousRational.At l E X) (aY : ContinuousRational.At l E Y)
    (a : ContinuousRational.Along l E g aY aX) {S : Scheme.{u}} (i : S ⟶ X.scheme) where
  inclusion : Pull l E i (coefficient l E i)
  projection : Pull l E (pullback.fst g i) (coefficient l E (pullback.fst g i))
  stratumMap : Pull l E (pullback.snd g i) (coefficient l E (pullback.snd g i))
  compositeLeft : Pull l E (pullback.fst g i ≫ g)
    (coefficient l E (pullback.fst g i ≫ g))
  compositeRight : Pull l E (pullback.snd g i ≫ i)
    (coefficient l E (pullback.snd g i ≫ i))
  leftComposition : Composition l E g (pullback.fst g i) a.coefficient
    (coefficient l E (pullback.fst g i)) (pullAlong l E a) projection compositeLeft
  rightComposition : Composition l E i (pullback.snd g i) (coefficient l E i)
    (coefficient l E (pullback.snd g i)) inclusion stratumMap compositeRight
  exactInclusion : ∀ F, IsIso (inclusion.singleMap l E F)

/-- The natural ambient square: composition, the fibre-product equation, then composition.
Source: Stacks 0D6D (blueprint: lem-per-rational-stratum-pullback-models). -/
def Stratum.square {X Y : ContinuousRational.Base.{u} l} {g : Y.scheme ⟶ X.scheme}
    {aX : ContinuousRational.At l E X} {aY : ContinuousRational.At l E Y}
    {a : ContinuousRational.Along l E g aY aX} {S : Scheme.{u}} {i : S ⟶ X.scheme}
    (m : Stratum l E g aX aY a i) :
    ContinuousRational.derivedPull g a.coefficient ⋙
        ContinuousRational.derivedPull (pullback.fst g i) (coefficient l E (pullback.fst g i)) ≅
      ContinuousRational.derivedPull i (coefficient l E i) ⋙
        ContinuousRational.derivedPull (pullback.snd g i)
          (coefficient l E (pullback.snd g i)) :=
  m.leftComposition.derived.symm ≪≫
    eqToIso (congrArg (fun f ↦ ContinuousRational.derivedPull f (coefficient l E f))
      (pullback.condition (f := g) (g := i))) ≪≫ m.rightComposition.derived

/-- The requested stratum isomorphism, natural relative to the supplied realization of K.
The exact-inclusion counit identifies the restricted F with its degree-zero complex.
Source: BS 6.8.14--6.8.15 (blueprint: lem-per-rational-stratum-pullback-models). -/
def Stratum.comparison {X Y : ContinuousRational.Base.{u} l} {g : Y.scheme ⟶ X.scheme}
    {aX : ContinuousRational.At l E X} {aY : ContinuousRational.At l E Y}
    {a : ContinuousRational.Along l E g aY aX} {S : Scheme.{u}} {i : S ⟶ X.scheme}
    (m : Stratum l E g aX aY a i)
    (F : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E))
    (K : PbcRationalCategory X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E))
    (e : aX.J.obj K ≅ (DerivedCategory.singleFunctor _ 0).obj F) :
    (ContinuousRational.derivedPull (pullback.fst g i)
        (coefficient l E (pullback.fst g i))).obj (aY.J.obj ((a.raw l E).obj K)) ≅
      (ContinuousRational.derivedPull (pullback.snd g i)
        (coefficient l E (pullback.snd g i))).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((ContinuousRational.modulePull i (coefficient l E i)).obj F)) := by
  letI := m.exactInclusion F
  exact (ContinuousRational.derivedPull (pullback.fst g i)
      (coefficient l E (pullback.fst g i))).mapIso (a.comparison.app K) ≪≫
    (m.square l E).app (aX.J.obj K) ≪≫
    (ContinuousRational.derivedPull (pullback.snd g i)
      (coefficient l E (pullback.snd g i))).mapIso
        ((ContinuousRational.derivedPull i (coefficient l E i)).mapIso e ≪≫
          asIso (m.inclusion.singleMap l E F))

/-- The finite-free computation for an arbitrary scheme map. The forward formula is
`a tensor (b_j) ↦ (a f♯(b_j))`; the inverse sends `a e_j` to `a tensor e_j`.
The module unit is the actual inverse-image unit followed by `1 tensor -`.
Source: Stacks 06YY; BS 6.8.15
(blueprint: lem-per-rational-stratum-pullback-models). -/
structure FreeModel {X Y : Scheme.{u}} (f : Y ⟶ X)
    (p : Pull l E f (coefficient l E f)) (r : ℕ) where
  ordinary : (ContinuousRational.modulePull f (coefficient l E f)).obj (free l E X r) ≅
    free l E Y r
  forward : ∀ (V : X.ProEt)
      (a : (rationalCoefficientSheaf l Y E).obj.obj (op ((proEtaleBaseChange f).obj V)))
      (b : Fin r → (rationalCoefficientSheaf l X E).obj.obj (op V)),
    ordinary.hom.val.app (op ((proEtaleBaseChange f).obj V))
        (a • ContinuousRational.moduleUnit f (coefficient l E f) (free l E X r) V
          (∑ j : Fin r, b j • basis l E X r j V)) =
      ∑ j : Fin r,
        (a * scalarImage l E f V (b j)) •
            basis l E Y r j ((proEtaleBaseChange f).obj V)
  backward : ∀ (V : X.ProEt) (j : Fin r)
      (a : (rationalCoefficientSheaf l Y E).obj.obj (op ((proEtaleBaseChange f).obj V))),
    ordinary.inv.val.app (op ((proEtaleBaseChange f).obj V))
        (a • basis l E Y r j ((proEtaleBaseChange f).obj V)) =
      a • ContinuousRational.moduleUnit f (coefficient l E f) (free l E X r) V
        (basis l E X r j V)
  computes : IsIso (p.singleMap l E (free l E X r))

/-- The finite-free derived comparison is the ordinary balanced map after the canonical
K-flat counit, rather than a freely chosen derived isomorphism.
Source: Stacks 06YY (blueprint: lem-per-rational-stratum-pullback-models). -/
def FreeModel.derived {X Y : Scheme.{u}} {f : Y ⟶ X}
    {p : Pull l E f (coefficient l E f)} {r : ℕ} (b : FreeModel l E f p r) :
    (ContinuousRational.derivedPull f (coefficient l E f)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (free l E X r)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (free l E Y r) := by
  letI := b.computes
  exact asIso (p.singleMap l E (free l E X r)) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso b.ordinary

/-- Normalized ambient data for one arbitrary trivializing chart and its base change.
The finite-free result is computed on the real fibre product, without noetherian or
flatness assumptions on its coefficient structural map.
Source: BS 6.8.2, 6.8.3 and 6.8.15; Stacks 0D6D and 06YY
(blueprint: lem-per-rational-stratum-pullback-models). -/
structure Chart {X Y : ContinuousRational.Base.{u} l} {g : Y.scheme ⟶ X.scheme}
    {aX : ContinuousRational.At l E X} {aY : ContinuousRational.At l E Y}
    {a : ContinuousRational.Along l E g aY aX} {S : Scheme.{u}} {i : S ⟶ X.scheme}
    (m : Stratum l E g aX aY a i)
    (F : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E)) (U : S.ProEt)
    (r : ℕ)
    (e : (ContinuousRational.modulePull U.hom (coefficient l E U.hom)).obj
      ((ContinuousRational.modulePull i (coefficient l E i)).obj F) ≅ free l E U.left r) where
  chart : Pull l E U.hom (coefficient l E U.hom)
  baseChange : Pull l E ((proEtaleBaseChange (pullback.snd g i)).obj U).hom
    (coefficient l E ((proEtaleBaseChange (pullback.snd g i)).obj U).hom)
  chartMap : Pull l E (pullback.fst U.hom (pullback.snd g i))
    (coefficient l E (pullback.fst U.hom (pullback.snd g i)))
  compositeLeft : Pull l E
    (((proEtaleBaseChange (pullback.snd g i)).obj U).hom ≫ pullback.snd g i)
    (coefficient l E
      (((proEtaleBaseChange (pullback.snd g i)).obj U).hom ≫ pullback.snd g i))
  compositeRight : Pull l E (pullback.fst U.hom (pullback.snd g i) ≫ U.hom)
    (coefficient l E (pullback.fst U.hom (pullback.snd g i) ≫ U.hom))
  leftComposition : Composition l E (pullback.snd g i)
    ((proEtaleBaseChange (pullback.snd g i)).obj U).hom
    (coefficient l E (pullback.snd g i))
    (coefficient l E ((proEtaleBaseChange (pullback.snd g i)).obj U).hom)
    m.stratumMap baseChange compositeLeft
  rightComposition : Composition l E U.hom (pullback.fst U.hom (pullback.snd g i))
    (coefficient l E U.hom) (coefficient l E (pullback.fst U.hom (pullback.snd g i)))
    chart chartMap compositeRight
  exactChart : IsIso (chart.singleMap l E
    ((ContinuousRational.modulePull i (coefficient l E i)).obj F))
  freeModel : FreeModel l E (pullback.fst U.hom (pullback.snd g i)) chartMap r

/-- Restriction of the right side of the stratum comparison, followed by the chart
trivialization and precisely the balanced finite-free computation.
Source: BS 6.8.15; Stacks 0D6D and 06YY
(blueprint: lem-per-rational-stratum-pullback-models). -/
def Chart.right {X Y : ContinuousRational.Base.{u} l} {g : Y.scheme ⟶ X.scheme}
    {aX : ContinuousRational.At l E X} {aY : ContinuousRational.At l E Y}
    {a : ContinuousRational.Along l E g aY aX} {S : Scheme.{u}} {i : S ⟶ X.scheme}
    {m : Stratum l E g aX aY a i}
    {F : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E)} {U : S.ProEt}
    {r : ℕ}
    {e : (ContinuousRational.modulePull U.hom (coefficient l E U.hom)).obj
      ((ContinuousRational.modulePull i (coefficient l E i)).obj F) ≅ free l E U.left r}
    (b : Chart l E m F U r e) :
    (ContinuousRational.derivedPull ((proEtaleBaseChange (pullback.snd g i)).obj U).hom
        (coefficient l E ((proEtaleBaseChange (pullback.snd g i)).obj U).hom)).obj
      ((ContinuousRational.derivedPull (pullback.snd g i)
        (coefficient l E (pullback.snd g i))).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((ContinuousRational.modulePull i (coefficient l E i)).obj F))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (free l E ((proEtaleBaseChange (pullback.snd g i)).obj U).left r) := by
  letI := b.exactChart
  exact (b.leftComposition.derived.symm.app _) ≪≫
    (eqToIso (congrArg (fun f ↦ ContinuousRational.derivedPull f (coefficient l E f))
      (pullback.condition (f := U.hom) (g := pullback.snd g i)).symm)).app _ ≪≫
    b.rightComposition.derived.app _ ≪≫
    (ContinuousRational.derivedPull (pullback.fst U.hom (pullback.snd g i))
      (coefficient l E (pullback.fst U.hom (pullback.snd g i)))).mapIso
        (asIso (b.chart.singleMap l E
          ((ContinuousRational.modulePull i (coefficient l E i)).obj F)) ≪≫
            (DerivedCategory.singleFunctor _ 0).mapIso e) ≪≫ b.freeModel.derived l E

/-- Restriction of the displayed stratum isomorphism identifies its left side with the
same free object by this composite. This definition makes the chart comparison square
commute, including naturality in K and F relative to their given identification.
Source: BS 6.8.15 (blueprint: lem-per-rational-stratum-pullback-models). -/
def Chart.left {X Y : ContinuousRational.Base.{u} l} {g : Y.scheme ⟶ X.scheme}
    {aX : ContinuousRational.At l E X} {aY : ContinuousRational.At l E Y}
    {a : ContinuousRational.Along l E g aY aX} {S : Scheme.{u}} {i : S ⟶ X.scheme}
    {m : Stratum l E g aX aY a i}
    {F : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E)} {U : S.ProEt}
    {r : ℕ}
    {e : (ContinuousRational.modulePull U.hom (coefficient l E U.hom)).obj
      ((ContinuousRational.modulePull i (coefficient l E i)).obj F) ≅ free l E U.left r}
    (b : Chart l E m F U r e)
    (K : PbcRationalCategory X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E))
    (eK : aX.J.obj K ≅ (DerivedCategory.singleFunctor _ 0).obj F) :=
  (ContinuousRational.derivedPull ((proEtaleBaseChange (pullback.snd g i)).obj U).hom
    (coefficient l E ((proEtaleBaseChange (pullback.snd g i)).obj U).hom)).mapIso
      (m.comparison l E F K eK) ≪≫ b.right l E

```

## New

Exactly the same declarations, byte for byte, are in
`Sheaf.Paper.RationalStratumPullbackData`:

```lean
/-- The actual continuous coefficient map, adjoint to precomposition on functions.
Source: BS 6.8.1--6.8.2 (blueprint: lem-per-rational-stratum-pullback-models). -/
def coefficient {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (adicTowerInverseImage f).obj (rationalCoefficientSheaf l X E) ⟶
      rationalCoefficientSheaf l Y E := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientPullback (ULift.{u + 1, u} E) f

/-- The structural scalar map on a base-changed chart, evaluated by precomposition.
Source: BS 6.8.1 (blueprint: lem-per-rational-stratum-pullback-models). -/
def scalarImage {X Y : Scheme.{u}} (f : Y ⟶ X) (V : X.ProEt)
    (b : (rationalCoefficientSheaf l X E).obj.obj (op V)) :
    (rationalCoefficientSheaf l Y E).obj.obj (op ((proEtaleBaseChange f).obj V)) := by
  letI := coefficientExtensionNormedField l E
  exact (continuousCoefficientDirectMap (ULift.{u + 1, u} E) f).hom.app (op V) b

/-- The existing finite free sheaf, with a lifted finite basis in the coefficient universe.
Source: BS 6.8.3 (blueprint: lem-per-rational-stratum-pullback-models). -/
abbrev free (X : Scheme.{u}) (r : ℕ) : pbcModules X (rationalCoefficientSheaf l X E) :=
  SheafOfModules.free (ULift.{u + 1} (Fin r))

/-- A basis section of the finite free sheaf on an arbitrary site object.
Source: BS 6.8.3 (blueprint: lem-per-rational-stratum-pullback-models). -/
def basis (X : Scheme.{u}) (r : ℕ) (j : Fin r) (V : X.ProEt) :
    (free l E X r).val.obj (op V) :=
  (SheafOfModules.freeSection (R := (adicLisseForget X).obj
    (rationalCoefficientSheaf l X E)) (ULift.up j)).val (op V)

/-- The ordinary and derived pullbacks are the published inverse image and scalar extension.
Only the universal comparison is recorded; its normalization fixes it on complexes.
Source: BS 6.8.15; Stacks 06YY
(blueprint: lem-per-rational-stratum-pullback-models). -/
structure Pull {X Y : Scheme.{u}} (f : Y ⟶ X)
    (c : (adicTowerInverseImage f).obj (rationalCoefficientSheaf l X E) ⟶
      rationalCoefficientSheaf l Y E) where
  [additive : (ContinuousRational.modulePull f c).Additive]
  counit : DerivedCategory.Q ⋙ ContinuousRational.derivedPull f c ⟶
    (ContinuousRational.modulePull f c).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  normalized : ContinuousRational.IsNormalizedPullCounit f c counit
  universal : (ContinuousRational.derivedPull f c).IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso _ (.up ℤ))
  computes : ∀ P : CochainComplex (pbcModules X (rationalCoefficientSheaf l X E)) ℤ,
    CochainComplex.IsAcyclicTensorKFlat (J := ProEt.topology X)
      (R := rationalCoefficientSheaf l X E) P → IsIso (counit.app P)


/-- The comparison supplied by the specified realization retains its completion-unit law.
Source: BS 6.8.14--6.8.15 (blueprint: lem-per-rational-stratum-pullback-models). -/
def pullAlong {X Y : ContinuousRational.Base.{u} l} {g : Y.scheme ⟶ X.scheme}
    {aX : ContinuousRational.At l E X} {aY : ContinuousRational.At l E Y}
    (a : ContinuousRational.Along l E g aY aX) : Pull l E g a.coefficient where
  additive := a.ordinaryAdditive
  counit := a.counit
  normalized := a.normalized_counit
  universal := a.universal
  computes := a.computes

/-- The canonical derived-to-ordinary map on a sheaf in degree zero.
Source: Stacks 06YY (blueprint: lem-per-rational-stratum-pullback-models). -/
def Pull.singleMap {X Y : Scheme.{u}} {f : Y ⟶ X}
    {c : (adicTowerInverseImage f).obj (rationalCoefficientSheaf l X E) ⟶
      rationalCoefficientSheaf l Y E} (p : Pull l E f c)
    (F : pbcModules X (rationalCoefficientSheaf l X E)) :
    (ContinuousRational.derivedPull f c).obj ((DerivedCategory.singleFunctor _ 0).obj F) ⟶
      (DerivedCategory.singleFunctor _ 0).obj ((ContinuousRational.modulePull f c).obj F) :=
  letI := p.additive
  p.counit.app ((CochainComplex.singleFunctor _ 0).obj F) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (ContinuousRational.modulePull f c) (.up ℤ) 0).hom.app F)

/-- Ambient composition, normalized on ordinary units and flat-term K-flat complexes.
This is the ambient comparison even when the schemes are arbitrary chart schemes.
Source: Stacks 0D6D; BS 6.8.15
(blueprint: lem-per-rational-stratum-pullback-models). -/
structure Composition {X Y Z : Scheme.{u}} (g : Y ⟶ X) (h : Z ⟶ Y)
    (cg : (adicTowerInverseImage g).obj (rationalCoefficientSheaf l X E) ⟶
      rationalCoefficientSheaf l Y E)
    (ch : (adicTowerInverseImage h).obj (rationalCoefficientSheaf l Y E) ⟶
      rationalCoefficientSheaf l Z E)
    (pg : Pull l E g cg) (ph : Pull l E h ch)
    (pc : Pull l E (h ≫ g) (coefficient l E (h ≫ g))) where
  [additiveG : (ContinuousRational.modulePull g cg).Additive]
  [additiveH : (ContinuousRational.modulePull h ch).Additive]
  [additiveC : (ContinuousRational.modulePull (h ≫ g)
    (coefficient l E (h ≫ g))).Additive]
  coefficients : coefficient l E (h ≫ g) =
    (proEtaleRingInverseImageComp h g).hom.app (rationalCoefficientSheaf l X E) ≫
      (adicTowerInverseImage h).map cg ≫ ch
  ordinary : ContinuousRational.modulePull (h ≫ g) (coefficient l E (h ≫ g)) ≅
    ContinuousRational.modulePull g cg ⋙ ContinuousRational.modulePull h ch
  units : ∀ (M : pbcModules X (rationalCoefficientSheaf l X E))
      (V : X.ProEt) (m : M.val.obj (op V)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange (h ≫ g)).obj V))
        (ContinuousRational.moduleUnit (h ≫ g) (coefficient l E (h ≫ g)) M V m) =
      (((ContinuousRational.modulePull h ch).obj
        ((ContinuousRational.modulePull g cg).obj M)).val.map
          ((MorphismProperty.Over.pullbackComp h g).hom.app V).op)
        (ContinuousRational.moduleUnit h ch ((ContinuousRational.modulePull g cg).obj M)
          ((proEtaleBaseChange g).obj V) (ContinuousRational.moduleUnit g cg M V m))
  complex :
    (ContinuousRational.modulePull (h ≫ g) (coefficient l E (h ≫ g))).mapHomologicalComplex
        (.up ℤ) ≅
      (ContinuousRational.modulePull g cg).mapHomologicalComplex (.up ℤ) ⋙
        (ContinuousRational.modulePull h ch).mapHomologicalComplex (.up ℤ)
  components : ∀ P (n : ℤ), (complex.hom.app P).f n = ordinary.hom.app (P.X n)
  derived : ContinuousRational.derivedPull (h ≫ g) (coefficient l E (h ≫ g)) ≅
    ContinuousRational.derivedPull g cg ⋙ ContinuousRational.derivedPull h ch
  normalization : ∀ P : CochainComplex (pbcModules X (rationalCoefficientSheaf l X E)) ℤ,
    CochainComplex.IsAcyclicTensorKFlat (J := ProEt.topology X)
        (R := rationalCoefficientSheaf l X E) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
      (R := rationalCoefficientSheaf l X E) (P.X n)) →
    pc.counit.app P ≫ DerivedCategory.Q.map (complex.hom.app P) =
      derived.hom.app (DerivedCategory.Q.obj P) ≫
        (ContinuousRational.derivedPull h ch).map (pg.counit.app P) ≫
        ph.counit.app (((ContinuousRational.modulePull g cg).mapHomologicalComplex
          (.up ℤ)).obj P)

/-- Data fixing the stratum square by its two normalized ambient compositions.
No reduced structure is put on the fibre product.
Source: BS 6.8.15; Stacks 0D6D
(blueprint: lem-per-rational-stratum-pullback-models). -/
structure Stratum {X Y : ContinuousRational.Base.{u} l} (g : Y.scheme ⟶ X.scheme)
    (aX : ContinuousRational.At l E X) (aY : ContinuousRational.At l E Y)
    (a : ContinuousRational.Along l E g aY aX) {S : Scheme.{u}} (i : S ⟶ X.scheme) where
  inclusion : Pull l E i (coefficient l E i)
  projection : Pull l E (pullback.fst g i) (coefficient l E (pullback.fst g i))
  stratumMap : Pull l E (pullback.snd g i) (coefficient l E (pullback.snd g i))
  compositeLeft : Pull l E (pullback.fst g i ≫ g)
    (coefficient l E (pullback.fst g i ≫ g))
  compositeRight : Pull l E (pullback.snd g i ≫ i)
    (coefficient l E (pullback.snd g i ≫ i))
  leftComposition : Composition l E g (pullback.fst g i) a.coefficient
    (coefficient l E (pullback.fst g i)) (pullAlong l E a) projection compositeLeft
  rightComposition : Composition l E i (pullback.snd g i) (coefficient l E i)
    (coefficient l E (pullback.snd g i)) inclusion stratumMap compositeRight
  exactInclusion : ∀ F, IsIso (inclusion.singleMap l E F)

/-- The natural ambient square: composition, the fibre-product equation, then composition.
Source: Stacks 0D6D (blueprint: lem-per-rational-stratum-pullback-models). -/
def Stratum.square {X Y : ContinuousRational.Base.{u} l} {g : Y.scheme ⟶ X.scheme}
    {aX : ContinuousRational.At l E X} {aY : ContinuousRational.At l E Y}
    {a : ContinuousRational.Along l E g aY aX} {S : Scheme.{u}} {i : S ⟶ X.scheme}
    (m : Stratum l E g aX aY a i) :
    ContinuousRational.derivedPull g a.coefficient ⋙
        ContinuousRational.derivedPull (pullback.fst g i) (coefficient l E (pullback.fst g i)) ≅
      ContinuousRational.derivedPull i (coefficient l E i) ⋙
        ContinuousRational.derivedPull (pullback.snd g i)
          (coefficient l E (pullback.snd g i)) :=
  m.leftComposition.derived.symm ≪≫
    eqToIso (congrArg (fun f ↦ ContinuousRational.derivedPull f (coefficient l E f))
      (pullback.condition (f := g) (g := i))) ≪≫ m.rightComposition.derived

/-- The requested stratum isomorphism, natural relative to the supplied realization of K.
The exact-inclusion counit identifies the restricted F with its degree-zero complex.
Source: BS 6.8.14--6.8.15 (blueprint: lem-per-rational-stratum-pullback-models). -/
def Stratum.comparison {X Y : ContinuousRational.Base.{u} l} {g : Y.scheme ⟶ X.scheme}
    {aX : ContinuousRational.At l E X} {aY : ContinuousRational.At l E Y}
    {a : ContinuousRational.Along l E g aY aX} {S : Scheme.{u}} {i : S ⟶ X.scheme}
    (m : Stratum l E g aX aY a i)
    (F : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E))
    (K : PbcRationalCategory X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E))
    (e : aX.J.obj K ≅ (DerivedCategory.singleFunctor _ 0).obj F) :
    (ContinuousRational.derivedPull (pullback.fst g i)
        (coefficient l E (pullback.fst g i))).obj (aY.J.obj ((a.raw l E).obj K)) ≅
      (ContinuousRational.derivedPull (pullback.snd g i)
        (coefficient l E (pullback.snd g i))).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((ContinuousRational.modulePull i (coefficient l E i)).obj F)) := by
  letI := m.exactInclusion F
  exact (ContinuousRational.derivedPull (pullback.fst g i)
      (coefficient l E (pullback.fst g i))).mapIso (a.comparison.app K) ≪≫
    (m.square l E).app (aX.J.obj K) ≪≫
    (ContinuousRational.derivedPull (pullback.snd g i)
      (coefficient l E (pullback.snd g i))).mapIso
        ((ContinuousRational.derivedPull i (coefficient l E i)).mapIso e ≪≫
          asIso (m.inclusion.singleMap l E F))

/-- The finite-free computation for an arbitrary scheme map. The forward formula is
`a tensor (b_j) ↦ (a f♯(b_j))`; the inverse sends `a e_j` to `a tensor e_j`.
The module unit is the actual inverse-image unit followed by `1 tensor -`.
Source: Stacks 06YY; BS 6.8.15
(blueprint: lem-per-rational-stratum-pullback-models). -/
structure FreeModel {X Y : Scheme.{u}} (f : Y ⟶ X)
    (p : Pull l E f (coefficient l E f)) (r : ℕ) where
  ordinary : (ContinuousRational.modulePull f (coefficient l E f)).obj (free l E X r) ≅
    free l E Y r
  forward : ∀ (V : X.ProEt)
      (a : (rationalCoefficientSheaf l Y E).obj.obj (op ((proEtaleBaseChange f).obj V)))
      (b : Fin r → (rationalCoefficientSheaf l X E).obj.obj (op V)),
    ordinary.hom.val.app (op ((proEtaleBaseChange f).obj V))
        (a • ContinuousRational.moduleUnit f (coefficient l E f) (free l E X r) V
          (∑ j : Fin r, b j • basis l E X r j V)) =
      ∑ j : Fin r,
        (a * scalarImage l E f V (b j)) •
            basis l E Y r j ((proEtaleBaseChange f).obj V)
  backward : ∀ (V : X.ProEt) (j : Fin r)
      (a : (rationalCoefficientSheaf l Y E).obj.obj (op ((proEtaleBaseChange f).obj V))),
    ordinary.inv.val.app (op ((proEtaleBaseChange f).obj V))
        (a • basis l E Y r j ((proEtaleBaseChange f).obj V)) =
      a • ContinuousRational.moduleUnit f (coefficient l E f) (free l E X r) V
        (basis l E X r j V)
  computes : IsIso (p.singleMap l E (free l E X r))

/-- The finite-free derived comparison is the ordinary balanced map after the canonical
K-flat counit, rather than a freely chosen derived isomorphism.
Source: Stacks 06YY (blueprint: lem-per-rational-stratum-pullback-models). -/
def FreeModel.derived {X Y : Scheme.{u}} {f : Y ⟶ X}
    {p : Pull l E f (coefficient l E f)} {r : ℕ} (b : FreeModel l E f p r) :
    (ContinuousRational.derivedPull f (coefficient l E f)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (free l E X r)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (free l E Y r) := by
  letI := b.computes
  exact asIso (p.singleMap l E (free l E X r)) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso b.ordinary

/-- Normalized ambient data for one arbitrary trivializing chart and its base change.
The finite-free result is computed on the real fibre product, without noetherian or
flatness assumptions on its coefficient structural map.
Source: BS 6.8.2, 6.8.3 and 6.8.15; Stacks 0D6D and 06YY
(blueprint: lem-per-rational-stratum-pullback-models). -/
structure Chart {X Y : ContinuousRational.Base.{u} l} {g : Y.scheme ⟶ X.scheme}
    {aX : ContinuousRational.At l E X} {aY : ContinuousRational.At l E Y}
    {a : ContinuousRational.Along l E g aY aX} {S : Scheme.{u}} {i : S ⟶ X.scheme}
    (m : Stratum l E g aX aY a i)
    (F : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E)) (U : S.ProEt)
    (r : ℕ)
    (e : (ContinuousRational.modulePull U.hom (coefficient l E U.hom)).obj
      ((ContinuousRational.modulePull i (coefficient l E i)).obj F) ≅ free l E U.left r) where
  chart : Pull l E U.hom (coefficient l E U.hom)
  baseChange : Pull l E ((proEtaleBaseChange (pullback.snd g i)).obj U).hom
    (coefficient l E ((proEtaleBaseChange (pullback.snd g i)).obj U).hom)
  chartMap : Pull l E (pullback.fst U.hom (pullback.snd g i))
    (coefficient l E (pullback.fst U.hom (pullback.snd g i)))
  compositeLeft : Pull l E
    (((proEtaleBaseChange (pullback.snd g i)).obj U).hom ≫ pullback.snd g i)
    (coefficient l E
      (((proEtaleBaseChange (pullback.snd g i)).obj U).hom ≫ pullback.snd g i))
  compositeRight : Pull l E (pullback.fst U.hom (pullback.snd g i) ≫ U.hom)
    (coefficient l E (pullback.fst U.hom (pullback.snd g i) ≫ U.hom))
  leftComposition : Composition l E (pullback.snd g i)
    ((proEtaleBaseChange (pullback.snd g i)).obj U).hom
    (coefficient l E (pullback.snd g i))
    (coefficient l E ((proEtaleBaseChange (pullback.snd g i)).obj U).hom)
    m.stratumMap baseChange compositeLeft
  rightComposition : Composition l E U.hom (pullback.fst U.hom (pullback.snd g i))
    (coefficient l E U.hom) (coefficient l E (pullback.fst U.hom (pullback.snd g i)))
    chart chartMap compositeRight
  exactChart : IsIso (chart.singleMap l E
    ((ContinuousRational.modulePull i (coefficient l E i)).obj F))
  freeModel : FreeModel l E (pullback.fst U.hom (pullback.snd g i)) chartMap r

/-- Restriction of the right side of the stratum comparison, followed by the chart
trivialization and precisely the balanced finite-free computation.
Source: BS 6.8.15; Stacks 0D6D and 06YY
(blueprint: lem-per-rational-stratum-pullback-models). -/
def Chart.right {X Y : ContinuousRational.Base.{u} l} {g : Y.scheme ⟶ X.scheme}
    {aX : ContinuousRational.At l E X} {aY : ContinuousRational.At l E Y}
    {a : ContinuousRational.Along l E g aY aX} {S : Scheme.{u}} {i : S ⟶ X.scheme}
    {m : Stratum l E g aX aY a i}
    {F : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E)} {U : S.ProEt}
    {r : ℕ}
    {e : (ContinuousRational.modulePull U.hom (coefficient l E U.hom)).obj
      ((ContinuousRational.modulePull i (coefficient l E i)).obj F) ≅ free l E U.left r}
    (b : Chart l E m F U r e) :
    (ContinuousRational.derivedPull ((proEtaleBaseChange (pullback.snd g i)).obj U).hom
        (coefficient l E ((proEtaleBaseChange (pullback.snd g i)).obj U).hom)).obj
      ((ContinuousRational.derivedPull (pullback.snd g i)
        (coefficient l E (pullback.snd g i))).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((ContinuousRational.modulePull i (coefficient l E i)).obj F))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (free l E ((proEtaleBaseChange (pullback.snd g i)).obj U).left r) := by
  letI := b.exactChart
  exact (b.leftComposition.derived.symm.app _) ≪≫
    (eqToIso (congrArg (fun f ↦ ContinuousRational.derivedPull f (coefficient l E f))
      (pullback.condition (f := U.hom) (g := pullback.snd g i)).symm)).app _ ≪≫
    b.rightComposition.derived.app _ ≪≫
    (ContinuousRational.derivedPull (pullback.fst U.hom (pullback.snd g i))
      (coefficient l E (pullback.fst U.hom (pullback.snd g i)))).mapIso
        (asIso (b.chart.singleMap l E
          ((ContinuousRational.modulePull i (coefficient l E i)).obj F)) ≪≫
            (DerivedCategory.singleFunctor _ 0).mapIso e) ≪≫ b.freeModel.derived l E

/-- Restriction of the displayed stratum isomorphism identifies its left side with the
same free object by this composite. This definition makes the chart comparison square
commute, including naturality in K and F relative to their given identification.
Source: BS 6.8.15 (blueprint: lem-per-rational-stratum-pullback-models). -/
def Chart.left {X Y : ContinuousRational.Base.{u} l} {g : Y.scheme ⟶ X.scheme}
    {aX : ContinuousRational.At l E X} {aY : ContinuousRational.At l E Y}
    {a : ContinuousRational.Along l E g aY aX} {S : Scheme.{u}} {i : S ⟶ X.scheme}
    {m : Stratum l E g aX aY a i}
    {F : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E)} {U : S.ProEt}
    {r : ℕ}
    {e : (ContinuousRational.modulePull U.hom (coefficient l E U.hom)).obj
      ((ContinuousRational.modulePull i (coefficient l E i)).obj F) ≅ free l E U.left r}
    (b : Chart l E m F U r e)
    (K : PbcRationalCategory X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E))
    (eK : aX.J.obj K ≅ (DerivedCategory.singleFunctor _ 0).obj F) :=
  (ContinuousRational.derivedPull ((proEtaleBaseChange (pullback.snd g i)).obj U).hom
    (coefficient l E ((proEtaleBaseChange (pullback.snd g i)).obj U).hom)).mapIso
      (m.comparison l E F K eK) ≪≫ b.right l E

```

The original module publicly imports the data module and retains its original
main theorem with its unchanged signature. The data module retains the original
public imports. Unused private proof imports are removed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RationalStratumPullbackModels | U1 | Same declarations through public reexport; main proof supplied |
| Sheaf.Paper.RationalAmbientPullModels | new in U1 packet | Uses Pull data only |
| Sheaf.Paper.RationalAmbientPullComposition | new in U1 packet | Uses normalized Composition data only |
| Sheaf.Paper.RationalPullSingleComputation | new in U1 packet | Uses Pull.singleMap only |
| Sheaf.Paper.RationalBalancedFreePullback | new in U1 packet | Uses ordinary free/basis/unit definitions only |

`tools/downstream.py Sheaf.Paper.RationalStratumPullbackModels --uses
AlgebraicGeometry.Scheme.RationalStratumPullback.Pull` reports zero downstream
modules and only the item itself as a textual user. A search of both Lean roots
confirms that no other existing module names these declarations. The original
public import path is preserved for future consumers.

## Status

landed 20261025T164433-L-1013788 2026-10-25 (merge of deliver/U1/Sheaf.Paper.RationalStratumPullbackModels)
