# WeilConjectures.ConstructibleExceptionalCoefficients construction interface extraction

## Reason

Move the existing construction records and proved mate lemmas verbatim into a public
interface module, re-exported by the original module. New assembly proof dependencies
can then refer to these data without importing the theorem they are to prove. This is
an import-cycle repair for the new proof decomposition, not a response to a timeout.
The original module retains its exact theorem statement and all existing public names.
No existing consumer is edited. The target statements and their definitions are unchanged.

## Old

The following declarations were directly in
`Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction`:

```lean
/-- The individual invertible coefficient mate with its defining counit equation.
Source: coefficient transpose construction
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
structure CounitComparison {X Y : Scheme.{max u v}} {s t : Stage.{max u v} l}
    (A : Operation.{u, v} l Ω X Y s) (B : Operation.{u, v} l Ω X Y t)
    (TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t) (TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t)
    [TX.CommShift ℤ] [TY.CommShift ℤ] where
  q : A.F ⋙ TY ≅ TX ⋙ B.F
  b : A.G ⋙ TX ≅ TY ⋙ B.G
  counit (L : C.{u, v} l Ω Y s) :
    q.hom.app (A.G.obj L) ≫ B.F.map (b.hom.app L) ≫
      B.adjunction.counit.app (TY.obj L) = TY.map (A.adjunction.counit.app L)
  qShift : q.hom.CommShift ℤ
  bShift : b.hom.CommShift ℤ


set_option backward.isDefEq.respectTransparency false in
/-- The counit transpose respects the units, by naturality and the triangles.
Source: coefficient transpose calculation
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
theorem comparison_unit_of_counit
    {X Y : Scheme.{max u v}} {s t : Stage.{max u v} l}
    (A : Operation.{u, v} l Ω X Y s) (B : Operation.{u, v} l Ω X Y t)
    (TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t) (TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t)
    (q : A.F ⋙ TY ≅ TX ⋙ B.F) (b : A.G ⋙ TX ⟶ TY ⋙ B.G)
    (hc : ∀ L, q.hom.app (A.G.obj L) ≫ B.F.map (b.app L) ≫
      B.adjunction.counit.app (TY.obj L) = TY.map (A.adjunction.counit.app L))
    (K : C.{u, v} l Ω X s) :
    TX.map (A.adjunction.unit.app K) ≫ b.app (A.F.obj K) ≫
      B.G.map (q.hom.app K) = B.adjunction.unit.app (TX.obj K) := by
  apply (B.adjunction.homEquiv _ _).symm.injective
  change B.F.map _ ≫ B.adjunction.counit.app _ =
    B.F.map _ ≫ B.adjunction.counit.app _
  simp only [Functor.map_comp, Category.assoc]
  erw [B.adjunction.counit_naturality]
  rw [← Category.assoc (B.F.map (b.app _))]
  have hc' := hc (A.F.obj K)
  have htrans : B.F.map (b.app (A.F.obj K)) ≫
      B.adjunction.counit.app (TY.obj (A.F.obj K)) =
      q.inv.app (A.G.obj (A.F.obj K)) ≫
        TY.map (A.adjunction.counit.app (A.F.obj K)) := by
    rw [← hc', ← Category.assoc, ← Category.assoc]
    simp only [Iso.inv_hom_id_app, Category.id_comp]
  rw [htrans]
  have hn := q.inv.naturality (A.adjunction.unit.app K)
  dsimp only [Functor.comp_map] at hn
  erw [← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← Category.assoc (TY.map _) (TY.map _), ← TY.map_comp]
  erw [A.adjunction.left_triangle_components K]
  change q.inv.app K ≫ TY.map (𝟙 (A.F.obj K)) ≫ q.hom.app K =
    B.F.map (B.adjunction.unit.app (TX.obj K)) ≫
      B.adjunction.counit.app (B.F.obj (TX.obj K))
  rw [TY.map_id]
  calc
    _ = q.inv.app K ≫ q.hom.app K :=
      congrArg (fun h ↦ q.inv.app K ≫ h) (Category.id_comp (q.hom.app K))
    _ = 𝟙 _ := q.inv_hom_id_app K
    _ = _ := (B.adjunction.left_triangle_components (TX.obj K)).symm

/-- Complete a counit-normalized invertible mate using the triangle identities.
Source: the coefficient comparison construction, inverse-transpose argument
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
def CounitComparison.complete {X Y : Scheme.{max u v}} {s t : Stage.{max u v} l}
    {A : Operation.{u, v} l Ω X Y s} {B : Operation.{u, v} l Ω X Y t}
    {TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t} {TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t}
    [TX.CommShift ℤ] [TY.CommShift ℤ]
    (d : CounitComparison.{u, v} l Ω A B TX TY) : Comparison.{u, v} l Ω A B TX TY where
  q := d.q
  b := d.b
  unit := comparison_unit_of_counit.{u, v} l Ω A B TX TY d.q d.b.hom d.counit
  counit := d.counit
  qShift := d.qShift
  bShift := d.bShift

/-- The right coefficient cocycle follows from the left cocycle by taking transposes.
Source: mate pasting, blueprint coefficient adjunction Step 6
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
theorem comparison_right_cocycle_of_left
    {X Y : Scheme.{max u v}} {s t r : Stage.{max u v} l}
    {A : Operation.{u, v} l Ω X Y s}
    {B : Operation.{u, v} l Ω X Y t} {D : Operation.{u, v} l Ω X Y r}
    {TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t} {TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t}
    {UX : C.{u, v} l Ω X t ⥤ C.{u, v} l Ω X r} {UY : C.{u, v} l Ω Y t ⥤ C.{u, v} l Ω Y r}
    {VX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X r} {VY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y r}
    [TX.CommShift ℤ] [TY.CommShift ℤ] [UX.CommShift ℤ] [UY.CommShift ℤ]
    [VX.CommShift ℤ] [VY.CommShift ℤ]
    (a : Comparison.{u, v} l Ω A B TX TY) (b : Comparison.{u, v} l Ω B D UX UY)
    (d : Comparison.{u, v} l Ω A D VX VY) (αX : TX ⋙ UX ≅ VX) (αY : TY ⋙ UY ≅ VY)
    (hleft : ∀ K, UY.map (a.q.hom.app K) ≫ b.q.hom.app (TX.obj K) ≫
      D.F.map (αX.hom.app K) = αY.hom.app (A.F.obj K) ≫ d.q.hom.app K)
    (L : C.{u, v} l Ω Y s) :
    UX.map (a.b.hom.app L) ≫ b.b.hom.app (TY.obj L) ≫ D.G.map (αY.hom.app L) =
      αX.hom.app (A.G.obj L) ≫ d.b.hom.app L := by
  apply (D.adjunction.homEquiv _ _).symm.injective
  change D.F.map _ ≫ D.adjunction.counit.app _ =
    D.F.map _ ≫ D.adjunction.counit.app _
  simp only [Functor.map_comp, Category.assoc]
  erw [D.adjunction.counit_naturality]
  apply (cancel_epi (UY.map (a.q.hom.app (A.G.obj L)) ≫
    b.q.hom.app (TX.obj (A.G.obj L)))).1
  simp only [Category.assoc]
  have hn := b.q.hom.naturality (a.b.hom.app L)
  dsimp only [Functor.comp_map] at hn
  have hα := αY.hom.naturality (A.adjunction.counit.app L)
  dsimp only [Functor.comp_map] at hα
  calc
    _ = UY.map (a.q.hom.app (A.G.obj L)) ≫
        UY.map (B.F.map (a.b.hom.app L)) ≫
        b.q.hom.app (B.G.obj (TY.obj L)) ≫
        D.F.map (b.b.hom.app (TY.obj L)) ≫
        D.adjunction.counit.app (UY.obj (TY.obj L)) ≫ αY.hom.app L := by
      rw [reassoc_of% hn]
    _ = UY.map (a.q.hom.app (A.G.obj L)) ≫
        UY.map (B.F.map (a.b.hom.app L)) ≫
        UY.map (B.adjunction.counit.app (TY.obj L)) ≫ αY.hom.app L := by
      rw [reassoc_of% (b.counit (TY.obj L))]
    _ = UY.map (TY.map (A.adjunction.counit.app L)) ≫ αY.hom.app L := by
      rw [← UY.map_comp_assoc, ← UY.map_comp_assoc, Category.assoc, a.counit]
    _ = αY.hom.app (A.F.obj (A.G.obj L)) ≫
        VY.map (A.adjunction.counit.app L) := hα
    _ = αY.hom.app (A.F.obj (A.G.obj L)) ≫ d.q.hom.app (A.G.obj L) ≫
        D.F.map (d.b.hom.app L) ≫ D.adjunction.counit.app (VY.obj L) := by
      rw [d.counit L]
    _ = _ := by rw [← reassoc_of% (hleft (A.G.obj L))]

/-- A counit-normalized field comparison retaining the endpoint shift structures.
Source: field coefficient comparisons
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
structure CounitFieldComparison {X Y : Scheme.{max u v}} {s t : Stage.{max u v} l}
    (A : Operation.{u, v} l Ω X Y s) (B : Operation.{u, v} l Ω X Y t)
    (TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t) (TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t) where
  [shiftX : TX.CommShift ℤ]
  [shiftY : TY.CommShift ℤ]
  comparison : CounitComparison.{u, v} l Ω A B TX TY

/-- Left comparison with the output shift structures retained in its type.
Source: blueprint coefficient q (blueprint:
lem-sf-constructible-exceptional-coefficient-construction).
-/
def CounitFieldComparison.q {X Y : Scheme.{max u v}} {s t : Stage.{max u v} l}
    {A : Operation.{u, v} l Ω X Y s} {B : Operation.{u, v} l Ω X Y t}
    {TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t} {TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t}
    (d : CounitFieldComparison.{u, v} l Ω A B TX TY) : A.F ⋙ TY ≅ TX ⋙ B.F :=
  letI := d.shiftX
  letI := d.shiftY
  d.comparison.q

/-- Right comparison with the output shift structures retained in its type.
Source: blueprint coefficient b (blueprint:
lem-sf-constructible-exceptional-coefficient-construction).
-/
def CounitFieldComparison.b {X Y : Scheme.{max u v}} {s t : Stage.{max u v} l}
    {A : Operation.{u, v} l Ω X Y s} {B : Operation.{u, v} l Ω X Y t}
    {TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t} {TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t}
    (d : CounitFieldComparison.{u, v} l Ω A B TX TY) : A.G ⋙ TX ≅ TY ⋙ B.G :=
  letI := d.shiftX
  letI := d.shiftY
  d.comparison.b

/-- Complete the field-stage mate while keeping its chosen shift structures.
Source: the same inverse-transpose argument
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
def CounitFieldComparison.complete {X Y : Scheme.{max u v}} {s t : Stage.{max u v} l}
    {A : Operation.{u, v} l Ω X Y s} {B : Operation.{u, v} l Ω X Y t}
    {TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t} {TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t}
    (d : CounitFieldComparison.{u, v} l Ω A B TX TY) : FieldComparison.{u, v} l Ω A B TX TY :=
  letI := d.shiftX
  letI := d.shiftY
  { shiftX := d.shiftX
    shiftY := d.shiftY
    comparison := d.comparison.complete l Ω }

/-- Canonical q normalization before completing its unit equation.
Source: proper/open scalar mate
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
def CounitQNormalized {X Y : Scheme.{max u v}} {f : X ⟶ Y} (c : Compactification f)
    {s t : RingStage.{max u v} l}
    {A : Operation.{u, v} l Ω X Y (s.stage l)} {B : Operation.{u, v} l Ω X Y (t.stage l)}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (SX : Scalar.{u, v} l Ω a X) (SY : Scalar.{u, v} l Ω a Y)
    (rA : LeftRealization.{u, v} l Ω c s A) (rB : LeftRealization.{u, v} l Ω c t B)
    (d : CounitComparison.{u, v} l Ω A B SX.functor SY.functor) : Prop :=
  ∀ K : C.{u, v} l Ω X (s.stage l),
    (RingStage.inclusion.{u, v} l Ω Y t).map (d.q.hom.app K) ≫
        rB.hom.app (SX.functor.obj K) ≫
        (PurCompactSupport.image (t.coefficients l) c).map (SX.realization.hom.app K) =
      SY.realization.hom.app (A.F.obj K) ≫
        (pbcDerivedExtend (a.map Y)).map (rA.hom.app K) ≫
        (PurCompactSupport.comparison a c).app ((RingStage.inclusion.{u, v} l Ω X s).obj K)


/-- Projection of the constructed scalar mate.
Source: coefficient comparison
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
def Scalar.counitQ {X Y : Scheme.{max u v}} {s t : RingStage.{max u v} l}
    {a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)}
    {A : Operation.{u, v} l Ω X Y (s.stage l)} {B : Operation.{u, v} l Ω X Y (t.stage l)}
    (SX : Scalar.{u, v} l Ω a X) (SY : Scalar.{u, v} l Ω a Y)
    (d : CounitComparison.{u, v} l Ω A B SX.functor SY.functor) :
    A.F ⋙ SY.functor ≅ SX.functor ⋙ B.F :=
  d.q

/-- The normalized construction before the separate coherence identities.
Source: coefficient construction in the exceptional inverse image paragraph
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
structure CoefficientConstructionRing (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] where
  operation (c : Compactification f) (s : Stage.{max u v} l) : Operation.{u, v} l Ω X Y s
  left (c : Compactification f) (s : RingStage.{max u v} l) :
    LeftRealization.{u, v} l Ω c s (operation c (s.stage l))
  finiteRight (c : Compactification f) (E : FieldStage.{max u v} l) (n : ℕ+) :
    (operation c (.finite E n)).G ⋙ RingStage.inclusion.{u, v} l Ω X (RingStage.finite E n) ≅
      RingStage.inclusion.{u, v} l Ω Y (RingStage.finite E n) ⋙
        @ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E.carrier n) _
          (Padic.finite_coefficientExtensionRing l E.carrier n n.pos) X Y f c
  integralLeft (c : Compactification f) (E : FieldStage.{max u v} l) :
    (operation c (.integral E)).F ⋙ PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y ≅
      PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c
          E.carrier
  integralLeft_normalized (c : Compactification f) (E : FieldStage.{max u v} l)
      (K : C.{u, v} l Ω X (.integral E)) :
    ((sfIntegralConstructible l E.carrier Y).ι.map
        ((integralLeft c E).hom.app K)) =
      (left c (.integral E)).hom.app K ≫
        (sfQcqsCompactSupportRealization l E.carrier D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl)
          c).hom.app
          ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).obj K)
  rationalLeft (c : Compactification f) (E : FieldStage.{max u v} l) :
    (operation c (.rational E)).F ≅
      sfCompactSupportFiniteFunctor l D.k (PurCompactSupport.coefficientPrimeUnit l D hl) c
          E.carrier
  scalar {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) (side : Bool) : Scalar.{u, v} l Ω a (endpoint X Y side)
  finiteScalar_eq {s : RingStage.{max u v} l} (E : FieldStage.{max u v} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a) (side : Bool) :
    (scalar (s := s) (t := .finite E n) a ha side).functor ⋙
        RingStage.inclusion.{u, v} l Ω (endpoint X Y side) (RingStage.finite E n) =
      RingStage.inclusion.{u, v} l Ω (endpoint X Y side) s ⋙
        pbcDerivedExtend (a.map (endpoint X Y side))
  finiteScalar_normalized {s : RingStage.{max u v} l} (E : FieldStage.{max u v} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a) (side : Bool) :
    (scalar (s := s) (t := .finite E n) a ha side).realization =
      eqToIso (finiteScalar_eq (s := s) E n a ha side)
  integralScalar_eq (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (side : Bool) :
    (scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i) side).functor ⋙
        RingStage.inclusion.{u, v} l Ω (endpoint X Y side) (RingStage.integral L) =
      RingStage.inclusion.{u, v} l Ω (endpoint X Y side) (RingStage.integral E) ⋙
        integralScalarExtensionOfUniverses l E.carrier L.carrier i (endpoint X Y side)
  integralScalar_normalized (E L : FieldStage.{max u v} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) (side : Bool)
      (K : C.{u, v} l Ω (endpoint X Y side) (.integral E)) :
    HEq ((scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i) side).realization.inv.app K)
      ((completedScalarComparison l E.carrier L.carrier i (endpoint X Y side)).app K.obj)
  comparison (c : Compactification f) {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) :
    CounitComparison.{u, v} l Ω (operation c (s.stage l)) (operation c (t.stage l))
      (scalar a ha true).functor (scalar a ha false).functor
  comparison_normalized (c : Compactification f) {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) :
    CounitQNormalized.{u, v} l Ω c a (scalar a ha true) (scalar a ha false)
      (left c s) (left c t) (comparison c a ha)
  scalarComposition {s t r : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l))
      (d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l))
      (h : ∀ T : Scheme.{max u v}, a.map T ≫ b.map T = d.map T)
      (ha : Allowed l a) (hb : Allowed l b) (hd : Allowed l d) (side : Bool) :
    ScalarComposition.{u, v} l Ω h (endpoint X Y side)
      (scalar a ha side) (scalar b hb side) (scalar d hd side)
  scalarIdentity {s : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{max u v}, a.map T = 𝟙 _) (ha : Allowed l a) (side : Bool) :
    ScalarIdentity.{u, v} l Ω h (endpoint X Y side) (scalar a ha side)

/-- The normalized construction before the separate coherence identities.
Source: coefficient construction in the exceptional inverse image paragraph
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
structure CoefficientConstructionFields (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f)) where
  rationalizationComparison (c : Compactification f) (E : FieldStage.{max u v} l) :
    CounitFieldComparison.{u, v} l Ω (R.operation c (.integral E)) (R.operation c (.rational E))
      (rationalization.{u, v} l Ω E X) (rationalization.{u, v} l Ω E Y)
  rationalization_normalized (c : Compactification f) (E : FieldStage.{max u v} l)
      (K : C.{u, v} l Ω X (.integral E)) :
    (rationalizationComparison c E).q.hom.app K ≫
        (R.rationalLeft c E).hom.app ((rationalization.{u, v} l Ω E X).obj K) =
      (sfRationalConstructibleLocalization l E.carrier Y).map
        ((R.integralLeft c E).hom.app K)
  rationalComparison (c : Compactification f) (E L : FieldStage.{max u v} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) :
    CounitFieldComparison.{u, v} l Ω (R.operation c (.rational E)) (R.operation c (.rational L))
      (rationalScalar.{u, v} l Ω E L i X) (rationalScalar.{u, v} l Ω E L i Y)
  rational_normalized (c : Compactification f) (E L : FieldStage.{max u v} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) (K : C.{u, v} l Ω X (.integral E)) :
    HEq ((rationalComparison c E L i).q.hom.app
        ((rationalization.{u, v} l Ω E X).obj K))
      ((rationalization.{u, v} l Ω L Y).map
        ((Scalar.counitQ.{u, v} l Ω
          (R.scalar (s := .integral E) (t := .integral L)
            (PurCompactSupport.completedChange l E.carrier L.carrier i)
            (Allowed.integral E L i) true)
          (R.scalar (s := .integral E) (t := .integral L)
            (PurCompactSupport.completedChange l E.carrier L.carrier i)
            (Allowed.integral E L i) false)
          (R.comparison c (s := .integral E) (t := .integral L)
            (PurCompactSupport.completedChange l E.carrier L.carrier i)
            (Allowed.integral E L i))).hom.app K))

/-- The normalized construction before the separate coherence identities.
Source: coefficient construction in the exceptional inverse image paragraph
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
structure CoefficientConstructionCommon (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R) where
  commonComparison (c : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    CounitFieldComparison.{u, v} l Ω (R.operation c (.rational (commonField.{u, v} l Ω i)))
      (R.operation c .closed)
      (commonInclusion.{u, v} l Ω X i) (commonInclusion.{u, v} l Ω Y i)
  common_normalized (c : Compactification f)
      (i : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω i))) :
    HEq ((commonComparison c i).q.hom.app K)
      (𝟙 ((commonInclusion.{u, v} l Ω Y i).obj
        ((R.operation c (.rational (commonField.{u, v} l Ω i))).F.obj K)))

/-- The normalized construction before the separate coherence identities.
Source: coefficient construction in the exceptional inverse image paragraph
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
structure CoefficientConstructionRefinements (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R)
    (M : CoefficientConstructionCommon.{u, v} l Ω D hl R F) where
  refinement {c d : Compactification f} (r : c.Refinement d) (s : Stage.{max u v} l) :
    RefinementComparison.{u, v} l Ω (R.operation c s) (R.operation d s)
  refinement_normalized {c d : Compactification f} (r : c.Refinement d)
      (s : RingStage.{max u v} l) :
    RingRefinementNormalized.{u, v} l Ω r s (R.left c s) (R.left d s) (refinement r (s.stage l))
  refinementRational {c d : Compactification f} (r : c.Refinement d)
      (E : FieldStage.{max u v} l) (K : C.{u, v} l Ω X (.integral E)) :
    HEq ((refinement r (.rational E)).left.hom.app ((rationalization.{u, v} l Ω E X).obj K))
      ((rationalization.{u, v} l Ω E Y).map ((refinement r (.integral E)).left.hom.app K))
  refinementCommon {c d : Compactification f} (r : c.Refinement d)
      (i : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω i))) :
    (M.commonComparison c i).q.inv.app K ≫
        (commonInclusion.{u, v} l Ω Y i).map
          ((refinement r (.rational (commonField.{u, v} l Ω i))).left.hom.app K) ≫
        (M.commonComparison d i).q.hom.app K =
      (refinement r .closed).left.hom.app
        ((commonInclusion.{u, v} l Ω X i).obj K)

/-- The normalized construction before the separate coherence identities.
Source: coefficient construction in the exceptional inverse image paragraph
(blueprint: lem-sf-constructible-exceptional-coefficient-construction). -/
structure CoefficientConstruction (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
 where
  ring : CoefficientConstructionRing.{u, v} l Ω D hl (f := f)
  fields : CoefficientConstructionFields.{u, v} l Ω D hl ring
  common : CoefficientConstructionCommon.{u, v} l Ω D hl ring fields
  refinements : CoefficientConstructionRefinements.{u, v} l Ω D hl ring fields common

```

## New

The declarations above, including every signature and body, are unchanged in
`Sheaf.Paper.ConstructibleExceptionalCoefficientConstructionData`. Its original
public prerequisite remains `ConstructibleExceptionalAdjunctionCoefficientsData`.
The original module now re-exports them with:

```lean
public import Sheaf.Paper.ConstructibleExceptionalCoefficientConstructionData
```

The new modules `ConstructibleExceptionalRefinementMate` and
`ConstructibleExceptionalCoefficientAssemblyData` add the explicitly defined adjunction
conjugate constructor, inherited inclusion shifts, normalization predicate and left
refinement data. They contain no holes. The two new statement modules are separate
geometric steps of the construction; their output data is only eliminated in theorem
proofs, never selected as a definition by arbitrary choice.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineDifferenceTowerFactorization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.ClosedDirectImageStrictReduction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.ClosedTransportedHomCounitFormula | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceReesFrame | U1 | Identical public declarations by re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | C9 | Identical public declarations by re-export; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.FourierTransform.FourierDeligneTransform | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicOperationDomainsSourceComparison | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicPuritySourceFiniteness | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicRealizationIsomorphismNormalization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdmissibleHomSubstitution | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AffineCoefficientCounitMaps | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AffineCoefficientCounitNormalization | C1 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AffineDiagonalIntegrationOrientation | W9 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AffineDiagonalTateCoordinates | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AffineDiagonalTensorCoordinates | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AffineLineCompositeTranspose | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AffineLinePurityComparison | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AffineLinePurityCoordinateMaps | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AffineLinePuritySource | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | K4 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceCoordinateBoundaries | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AffineSpacePurityComparison | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AffineSpacePurityComposition | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceThomMap | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AffineTargetDiagonalDnc | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AffineTranslationTrace | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.AnchoredPureCurveCriterion | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.BaseChangedLineTraceEvaluation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | F7 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.BoundaryComparisonCompositionTransport | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.BoundaryFiniteSiteRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.BoundaryFiniteTorDomains | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.BoundedSiteExchangeTransposes | D3 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.BoundedSiteTensorTransposes | V9 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CartesianSectionData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ChartDiagonalAssemblyData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ChartDncVectorFactors | S9 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ChartExceptionalMateCoherence | W3 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | S7 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ClopenCanonicalFiniteEvaluation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ClopenCanonicalRestrictionEvaluation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ClopenCompletedTowerRestriction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ClopenCounitAdjointComparison | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ClopenExceptionalScalarDescent | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ClopenSystemFiniteRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ClopenSystemIntegralRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ClopenSystemOrdinaryRestrictionRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ClopenSystemRealizationData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ClopenSystemRestrictionEvaluation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ClosedCoefficientTransposeCocycles | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ClosedScalarDomains | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ClosedSupportExceptionalMate | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CoefFiniteHomSiteDescent | C5 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CoefFiniteSiteHomTransport | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CoefSupportOpenTensorModel | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CoefSupportPointSectionsData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CoefficientMapGeometricSquares | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | V8 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CommonStagePointReturn | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CommonStageWeilShriek | C6 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CompactSupportCompletedProjectionData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CompactSupportCompositeTransposeDomains | M2 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | Y5 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CompactSupportLimitEquationRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | S4 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CompactSupportScalarProjectionIdentification | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CompactWeilCocycleEndomorphismRecurrence | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CompactificationCompletedRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CompleteProjectionMateDescent | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CompletedHomScalarTranspose | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | U2 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CompositionTensorMate | G8 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | D6 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ConcreteProjectionFieldDescent | A2 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstruction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ConstantDirectImageTowerRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionPullbackReturnResidue | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnLocalOperators | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetHeartCoordinates | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | D6 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCompositor | D8 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ConstructibleMateCoherence | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ConstructibleTensorComposition | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ConstructibleWeilModelSquares | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CoordinateLineAdjunction | G9 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CoordinateLineAdjunctionMaps | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CoordinateProductPresentations | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CoordinateSectionArrows | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CoordinateSectionProductRecursion | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CoordinateSectionProjection | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CoordinateTowerNormalizationInduction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CoordinateZeroBaseChange | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.DerivedPoincarePairing | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.DiagonalAffineTraceCoordinates | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.DiagonalAffineTraceSiteComparison | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.DiagonalDncAssemblyGlobal | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.DiagonalDncChartNormalization | T5 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.DiagonalExchangeCube | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrientationCharts | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrientationRefinement | T8 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.DifferenceCoordinateSectionIdentifications | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.DoubleDiagonalSectionIdentifications | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.DualBaseChange | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.DualizingClosedSite | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.DualizingSigmaCocycleLocality | D4 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.DualizingUnitComposite | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.EtaleCartesianTowerTensorComparison | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.EtaleLisseHomReduction | E8 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ExceptionalDualizingBaseChangePasting | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ExchangeFunctoriality | F6 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | W9 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FdPullbackWeilReturnSquare | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FieldCohomologyPerfectDescent | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FilteredCondensedRepresentingPair | D2 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | K1 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportCoefficientSquare | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportEvaluationRefinement | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | K3 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteExceptionalCompositorCoefficients | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteExceptionalSiteNormalization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteFirstRootChart | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtensionData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteGeometricPurityMate | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteGeometricSectionsPointOrbits | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteHomDomainCalculus | G7 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteHorizontalShriekMate | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteOrientationScalarPresentation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FinitePointCounitUnitNormalization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FinitePointReconstructedEvaluationSquare | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FinitePositiveRootCharts | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteProductReductionComparisons | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteProjectionExchangeTransposes | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteRationalHeartComparison | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteRootTensorPresentation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteSheafH0Augmentation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteSignedTwistProducts | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | U8 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteSupportedReductionEquation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteTargetChangeCoherence | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorComparisonEquations | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorFixedComparisons | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorPresentationReduction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorReductionData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorSignedReduction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteTripleProductNormalForms | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FixProjectionCompactificationComparison | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ForwardProductCoordinateTransport | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FrameworkPbcComparisonData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FrameworkPbcComparisonSystem | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FrameworkPbcPullbackScalarBridge | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FrameworkPbcRawComparisonData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence | H5 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FrobeniusSquareExchange | H6 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.FrobeniusSystemExchangeInverse | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.GeneralChartComparisons | G6 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | S6 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.GeometricComparisonData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.GeometricOperations | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.GermReparametrizationDerivedDescent | H8 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | T2 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.IdentificationCoefficientTransport | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.IdentityCompactificationLimitComparisons | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.IdentityCompactificationSystemMate | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.IntegralExceptionalInverseImage | V6 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.IntegralScalarIsomorphismExchange | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.IntegralSectionsPerfectReduction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.IntegralSemilinearGermSquare | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.IntegrationExponentTransposeTransport | V7 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.IsomorphismExchangeScalarRefinementDescent | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.IsomorphismFiniteExchangeCoherence | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusCoefficientExtension | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.LocalizationScalarUnit | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.LocallyClosedScalarPasting | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.MiddleExchangeProjectionBaseChange | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.MixedCompactSupportExchangeData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.MixedCupCoefficientChange | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.MixedCupFieldCoordinates | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.MixedCupFieldNormalization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.MixedCupFieldOperations | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.MixedCupRingedNormalization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.MixedCupTensorClosure | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.MixedCupTensorElementary | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.MixedCupTensorNormalization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.NativeGeometricBrownConstructibleComparison | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.NormalModelSectionOrientation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.NormalizedFiniteFibreModels | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.NormalizedFiniteRealizationFibre | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.NormalizedStageCoefficientCalculus | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.OrderedAffineTransposeProjection | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.OrientationGroundFieldRetagging | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.OrientedPerfectDuality | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PerfectDualPairAndTateStability | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PfReductionProperOpenIdentities | A9 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PointEquivariantDiagramLift | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PointFrobeniusTransportNormalization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PointPullbackConeLocalization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PointQuotientTowerHomotopy | A6 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PointRestrictionSystemChainMap | G3 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PointRestrictionWholeRoosSquare | G4 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PointSectionsCompletionCone | H1 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PointSystemNormalizedComparisonData | H3 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PointSystemPowerRoosCoherence | W8 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PointSystemRoosTransport | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PointSystemTransportDescent | X5 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PointTransportConeComparisonDescent | H4 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PointTransportResolutionCancellation | A7 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PointTransportStrictQuotient | J1 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PointWeilHeartFlag | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PointWeilPairingRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ProductExchangeCounitCoordinates | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ProductOpenTensorProjection | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | H8 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoherence | Y5 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ProjectionPurityAgreement | N2 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ProjectionReductionPresentation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | P4 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ProjectionWeilTensorDomainBridge | X6 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ProperIntegralTowerComparison | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ProperWeilIterateGermFormula | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPair | B9 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparison | Q4 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PurStrictIntegralExchangeNormalization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PurityAffineChartExceptionalIdentification | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PurityAffineLineBoundaryRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | K3 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PuritySectionEtaleRestriction | Y2 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PurityWitnessedMateNormalization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.PurityWitnessedOpenChartTransport | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.RationalOrdinaryCohomologyTensor | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.RationalReturnBlockPower | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ResidueControlledFiniteHoms | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.RetaggingCoordinateOrientations | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SectionDncIntegrationSquare | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SemilinearExchangeCubeCoherence | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SemilinearExchangeReindexing | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SemilinearExchangeReindexingData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SemilinearGermIterationDescent | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SfBcCompletedMateDomain | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SfFieldMateDomain | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SfPackageBaseChangeDomainRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | B4 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SfPackageQbarAdjunctionMapDescent | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SfProEtaleProjectionFormula | N4 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SfQbarLocalizationCommonStage | T1 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SfRecollementReductionBoundary | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SmoothExceptionalTensorPasting | M2 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | B4 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGamma | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SourceSectionStalkConeComparison | K6 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.StrictReductionCompactSupportNormalization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SystemClopenMateIdentification | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SystemClopenTensorCompatibility | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SystemCompositorRefinementSquare | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SystemEnrichedProjectionAdjunction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SystemInternalHomRepresentability | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.SystemTensorPresentationIdentification | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | S1 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TensorExchangeCtfDomains | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TensorMateBaseChange | P5 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TraceBoundedQuotientStalkRealization | K8 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TraceCorrespondences | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TraceStalkCompositorTowerRealization | K9 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwConventions | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCartier | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCoprojection | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCore | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionMaps | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionNormalization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionOrdinary | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionProjective | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionSign | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionTower | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackTowerDomain | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.VaryingDimensionDualizingInverse | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.VectorIntegrationChartComparison | Z9 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.VectorIntegrationSiteComparison | S6 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.VectorModelChartDescent | W7 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.VerdierPairingThreeTransposes | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.WeilBaseChangeSemilinearPasting | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.WeilInternalHomWeil | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.WfTensorCompletionFrobenius | J3 | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionCohomology | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ZlImmersionPullbackWeightPreservation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ZlWeilHeartLocalizationExact | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | U4 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | N2 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.AmbientExactClopenComparison | R4 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | H4 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.AmbientUnderivedClopenPasting | S1 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.CoefDualizingSiteMates | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.CoefFinitePairingEvaluationData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.CoefPairingFiniteNormalization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.CoefPairingSystemDinaturality | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | V1 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.CoefSystemProjectionEvaluation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.CoefficientDualizingClosedDescent | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.CoefficientProjectionPointData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.CompactifiedProperTowerExchange | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.CompletedProjectionExchangeRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.CompletedShriekCompositionLaws | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.CompositionProjectionMate | U7 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteCounitRestrictionSquare | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | E9 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | X3 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptionalDomain | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteFreeEtaleProEtaleTransport | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteReturnFrobeniusCancellation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusAffineEqualizerPresentation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFiniteExchangeInverse | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | S2 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | G2 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionRecursion | T2 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralNormalizedRefinementPasting | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierModels | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierReductionPairing | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierSignedCalculus | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.KunnethFirstOpenSubstitution | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.KunnethSecondOpenSubstitution | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | A5 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.OpenInterchangeReductionSquares | E3 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.OpenScalarAdjunctionCounit | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.ProductCompactificationIdentity | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.ProductNormalizationRealizationTransport | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.ProductSystemUniformRealizationDomain | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly | C2 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization | D2 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.ProjectionRefinementDescent | E2 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | J3 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | D2 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | B6 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.RefinementProjectionCounit | T3 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisComparisonNormalForm | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.SupportedWeilMateLift | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.TensorAdjunctionReductionSquares | C2 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.TensorHomTranspositionData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.ThreeCellCompositor | J2 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.TriangleProjectionNormalForm | T4 | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.VerdierExchangeData | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.SmoothPurity.OrdinaryTripleProductTranspose | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.TraceFormula.CompactDirectPowerTransportNormalization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.TraceFormula.FrobeniusCompactPowerExchange | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.TraceFormula.FrobeniusProperPowerExchange | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.TraceFormula.LocalNormalizationStrictRealization | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.TraceFormula.PointConeLiftsChainNaturality | E5 | Identical public declarations by re-export; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | unclaimed | Identical public declarations by re-export; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Identical public declarations by re-export; no adaptation. |

## Status

landed 20261025T100757-L-3622475 2026-10-25 (merge of deliver/A3/Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction)
