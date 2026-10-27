# Strict-totalization definitions

## Reason

Repeated elaboration of the full sheaf tensor instances was expensive. Named
comparison, total-map, differential and inclusion maps share those original
constructions. The section formulas are defined once in the three calculation
modules and retained here as definitionally equal wrappers. Every existing
argument, result and mathematical formula is unchanged. No existence witness
is used to supply data.

## Old

```lean
def TotalDifferentials {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}
    (f : RingedPullback R S) (c : Comparison f) : Prop :=
  ∀ (P Q : Complex R) (n n' : ℤ),
    (f.L.map (HomologicalComplex.mapBifunctor.D₁ P Q (curriedTensor (Modules R))
        (.up ℤ) n n') ≫ (comparison f c P Q).hom.f n' =
      (comparison f c P Q).hom.f n ≫
        HomologicalComplex.mapBifunctor.D₁ ((pull f).obj P) ((pull f).obj Q)
          (curriedTensor (Modules S)) (.up ℤ) n n') ∧
    (f.L.map (HomologicalComplex.mapBifunctor.D₂ P Q (curriedTensor (Modules R))
        (.up ℤ) n n') ≫ (comparison f c P Q).hom.f n' =
      (comparison f c P Q).hom.f n ≫
        HomologicalComplex.mapBifunctor.D₂ ((pull f).obj P) ((pull f).obj Q)
          (curriedTensor (Modules S)) (.up ℤ) n n') ∧
    (HomologicalComplex.mapBifunctor.D₁ ((pull f).obj P) ((pull f).obj Q)
        (curriedTensor (Modules S)) (.up ℤ) n n' ≫ (comparison f c P Q).inv.f n' =
      (comparison f c P Q).inv.f n ≫
        f.L.map (HomologicalComplex.mapBifunctor.D₁ P Q (curriedTensor (Modules R))
          (.up ℤ) n n')) ∧
    (HomologicalComplex.mapBifunctor.D₂ ((pull f).obj P) ((pull f).obj Q)
        (curriedTensor (Modules S)) (.up ℤ) n n' ≫ (comparison f c P Q).inv.f n' =
      (comparison f c P Q).inv.f n ≫
        f.L.map (HomologicalComplex.mapBifunctor.D₂ P Q (curriedTensor (Modules R))
          (.up ℤ) n n'))
```

```lean
def Comparisons.KappaDifferentials {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) : Prop :=
  ∀ {i j : Index} (a : i ⟶ j) (P Q : Complex (d.R.obj i)) (n n' : ℤ)
    (v : Fin 2),
    ((d.L i ⋙ extensionFunctor (d.S.map a)).map
        ((if v = 0 then HomologicalComplex.mapBifunctor.D₁ else
          HomologicalComplex.mapBifunctor.D₂) P Q (curriedTensor (Modules (d.R.obj i)))
            (.up ℤ) n n') ≫ (e.kappaC a (total P Q)).hom.f n' =
      (e.kappaC a (total P Q)).hom.f n ≫
        (extensionFunctor (d.R.map a) ⋙ d.L j).map
          ((if v = 0 then HomologicalComplex.mapBifunctor.D₁ else
            HomologicalComplex.mapBifunctor.D₂) P Q (curriedTensor (Modules (d.R.obj i)))
              (.up ℤ) n n')) ∧
    ((extensionFunctor (d.R.map a) ⋙ d.L j).map
        ((if v = 0 then HomologicalComplex.mapBifunctor.D₁ else
          HomologicalComplex.mapBifunctor.D₂) P Q (curriedTensor (Modules (d.R.obj i)))
            (.up ℤ) n n') ≫ (e.kappaC a (total P Q)).inv.f n' =
      (e.kappaC a (total P Q)).inv.f n ≫
        (d.L i ⋙ extensionFunctor (d.S.map a)).map
          ((if v = 0 then HomologicalComplex.mapBifunctor.D₁ else
            HomologicalComplex.mapBifunctor.D₂) P Q (curriedTensor (Modules (d.R.obj i)))
              (.up ℤ) n n'))
```

```lean
def TotalNaturality {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}
    (f : RingedPullback R S) (c : Comparison f) : Prop :=
  ∀ (P Q P' Q' : Complex R) (a : P ⟶ P') (b : Q ⟶ Q'),
    (pull f).map (totalMap a b) ≫ (comparison f c P' Q').hom =
      (comparison f c P Q).hom ≫ totalMap ((pull f).map a) ((pull f).map b) ∧
    totalMap ((pull f).map a) ((pull f).map b) ≫ (comparison f c P' Q').inv =
      (comparison f c P Q).inv ≫ (pull f).map (totalMap a b)
```

```lean
def TotalSummands {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}
    (f : RingedPullback R S) (c : Comparison f) : Prop :=
  ∀ (P Q : Complex R) (p q n : ℤ) (h : p + q = n),
    (f.L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules R)) p q n h) ≫
        (comparison f c P Q).hom.f n =
      (c.mu (P.X p) (Q.X q)).hom ≫
        CochainComplex.ιMapBifunctor ((pull f).obj P) ((pull f).obj Q)
          (curriedTensor (Modules S)) p q n h) ∧
    (CochainComplex.ιMapBifunctor ((pull f).obj P) ((pull f).obj Q)
        (curriedTensor (Modules S)) p q n h ≫ (comparison f c P Q).inv.f n =
      (c.mu (P.X p) (Q.X q)).inv ≫
        f.L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules R)) p q n h))
```

```lean
def Comparisons.TensorSquare {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) (c : ∀ i : Index, Comparison (d.ringed i)) : Prop :=
  ∀ {i j : Index} (a : i ⟶ j) (P Q : Complex (d.R.obj i)),
    e.kappaC a (total P Q) ≪≫
        (pull (d.ringed j)).mapIso (e.sigmaRC a P Q) ≪≫
        comparison (d.ringed j) (c j)
          ((extend (d.R.map a)).obj P) ((extend (d.R.map a)).obj Q) =
      (extend (d.S.map a)).mapIso (comparison (d.ringed i) (c i) P Q) ≪≫
        e.sigmaSC a ((pull (d.ringed i)).obj P) ((pull (d.ringed i)).obj Q) ≪≫
        totalIso (e.kappaC a P) (e.kappaC a Q)
```

```lean
def Comparisons.PullTensorTransitions {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) (c : ∀ i : Index, Comparison (d.ringed i)) : Prop :=
  ∀ {i j : Index} (t : i ⟶ j)
    (P Q : Complex (d.R.obj i)) (P' Q' : Complex (d.R.obj j))
    (f : (extend (d.R.map t)).obj P ⟶ P')
    (g : (extend (d.R.map t)).obj Q ⟶ Q'),
    (extend (d.S.map t)).map (comparison (d.ringed i) (c i) P Q).hom ≫
        (e.sigmaSC t ((pull (d.ringed i)).obj P) ((pull (d.ringed i)).obj Q)).hom ≫
        totalMap (e.pullArrow t P P' f) (e.pullArrow t Q Q' g) =
      e.pullArrow t (total P Q) (total P' Q') (e.tensorArrow t P Q P' Q' f g) ≫
        (comparison (d.ringed j) (c j) P' Q').hom
```

```lean
def semilinearSectionMap {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    {P : Complex A} {Q : Complex B} (f : (extend a).obj P ⟶ Q) (p : ℤ) :
    (underlying A).obj (P.X p) ⟶ (underlying B).obj (Q.X p) :=
  insertion a (P.X p) ≫ (underlying B).map (f.f p)
```

```lean
def inverseSectionMap (d : Diagram (J := J) (K := K)) {i j : Index} (a : i ⟶ j)
    {P : Complex (d.R.obj i)} {Q : Complex (d.R.obj j)}
    (f : (extend (d.R.map a)).obj P ⟶ Q) (p : ℤ) :
    (underlying (d.RI.obj i)).obj ((d.algebraic i).modules.obj (P.X p)) ⟶
      (underlying (d.RI.obj j)).obj ((d.algebraic j).modules.obj (Q.X p)) :=
  (d.algebraic i).moduleUnderlying.hom.app (P.X p) ≫
    d.inverse.map (semilinearSectionMap (d.R.map a) f p) ≫
      (d.algebraic j).moduleUnderlying.inv.app (Q.X p)
```

```lean
def diagramInsertion (d : Diagram (J := J) (K := K)) {i j : Index} (a : i ⟶ j)
    (M : Modules (d.R.obj i)) :
    (underlying (d.RI.obj i)).obj ((d.algebraic i).modules.obj M) ⟶
      (underlying (d.RI.obj j)).obj
        ((d.algebraic j).modules.obj ((extensionFunctor (d.R.map a)).obj M)) :=
  (d.algebraic i).moduleUnderlying.hom.app M ≫
    d.inverse.map (insertion (d.R.map a) M) ≫
      (d.algebraic j).moduleUnderlying.inv.app ((extensionFunctor (d.R.map a)).obj M)
```

```lean
def diagramPullSection (d : Diagram (J := J) (K := K)) (i : Index)
    (M : Modules (d.R.obj i)) (U : Dᵒᵖ) (b : (d.S.obj i).obj.obj U)
    (x : ((d.algebraic i).modules.obj M).val.obj U) : ((d.L i).obj M).val.obj U :=
  (eqToHom (d.hobj i M).symm).val.app U
    (extensionTmul (d.phi.app i) ((d.algebraic i).modules.obj M) U b x)
```

```lean
def diagramGeneratorSection (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (i : Index)
    (M : Modules (d.R.obj i)) (Z : Sheaf J (Type w))
    (x : Z ⟶ (underlying (d.R.obj i)).obj M) (U : Dᵒᵖ)
    (v : (d.inverse.obj Z).obj.obj U) : ((d.L i).obj M).val.obj U :=
  @id (((d.L i).obj M).val.obj U) ((generator (d.ringed i) (c i) x).hom.app U v)
```

```lean
def Comparisons.kappaTransitionForward {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l)
    (r : i ⟶ k) (s : j ⟶ l) (h : a ≫ s = r ≫ b)
    (P : Complex (d.R.obj i)) (Q : Complex (d.R.obj k))
    (f : (extend (d.R.map r)).obj P ⟶ Q) :=
  (extend (d.S.map s)).map (e.kappaC a P).hom ≫
    e.pullArrow s ((extend (d.R.map a)).obj P) ((extend (d.R.map b)).obj Q)
      (squareArrow d.R a b r s h P Q f)
```

```lean
def Comparisons.kappaTransitionInverse {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l)
    (r : i ⟶ k) (s : j ⟶ l) (h : a ≫ s = r ≫ b)
    (P : Complex (d.R.obj i)) (Q : Complex (d.R.obj k))
    (f : (extend (d.R.map r)).obj P ⟶ Q) :=
  (extend (d.S.map s)).map (e.kappaC a P).inv ≫
    squareArrow d.S a b r s h ((pull (d.ringed i)).obj P)
      ((pull (d.ringed k)).obj Q) (e.pullArrow r P Q f)
```

```lean
def Comparisons.KappaTransitionValues {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) : Prop :=
  ∀ {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l) (r : i ⟶ k) (s : j ⟶ l)
    (h : a ≫ s = r ≫ b) (P : Complex (d.R.obj i)) (Q : Complex (d.R.obj k))
    (f : (extend (d.R.map r)).obj P ⟶ Q) (p : ℤ) (U : Dᵒᵖ)
    (v : (d.S.obj j).obj.obj U) (z : (d.S.obj i).obj.obj U)
    (x : ((d.algebraic i).modules.obj (P.X p)).val.obj U),
    ((((e.kappaTransitionForward a b r s h P Q f).f p).val.app U
      (extensionTmul (d.S.map s) (((extend (d.S.map a)).obj
          ((pull (d.ringed i)).obj P)).X p) U 1
        (extensionTmul (d.S.map a) ((d.L i).obj (P.X p)) U v
          (diagramPullSection d i (P.X p) U z x)))) =
      diagramPullSection d l ((extensionFunctor (d.R.map b)).obj (Q.X p)) U
        ((d.S.map s).hom.app U v *
          (d.S.map b).hom.app U ((d.S.map r).hom.app U z))
        ((diagramInsertion d b (Q.X p)).hom.app U
          ((inverseSectionMap d r f p).hom.app U x))) ∧
    (∀ z' : (d.RI.obj j).obj.obj U,
      (((e.kappaTransitionInverse a b r s h P Q f).f p).val.app U
        (extensionTmul (d.S.map s)
          ((d.L j).obj ((extensionFunctor (d.R.map a)).obj (P.X p))) U 1
          (diagramPullSection d j ((extensionFunctor (d.R.map a)).obj (P.X p)) U v
            (z' • (@id (((d.algebraic j).modules.obj
              ((extensionFunctor (d.R.map a)).obj (P.X p))).val.obj U)
                ((diagramInsertion d a (P.X p)).hom.app U x)))))) =
        extensionTmul (d.S.map b) ((d.L k).obj (Q.X p)) U
          ((d.S.map s).hom.app U v *
            (d.phi.app l).hom.app U ((d.RI.map s).hom.app U z'))
          (diagramPullSection d k (Q.X p) U 1
            ((inverseSectionMap d r f p).hom.app U x)))
```

```lean
def totalPure {A : Sheaf J CommRingCat.{w}} (P Q : Complex A)
    (p q n : ℤ) (h : p + q = n) (U : Cᵒᵖ) (x : (P.X p).val.obj U)
    (y : (Q.X q).val.obj U) : ((total P Q).X n).val.obj U :=
  (CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules A)) p q n h).val.app U
    (ringedComparisonPure A (P.X p) (Q.X q) U x y)
```

```lean
def tensorTransitionForward (B : Index ⥤ Sheaf J CommRingCat.{w})
    (z : ∀ {i j : Index} (a : i ⟶ j), Comparison (extensionPullback (B.map a)))
    {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l) (r : i ⟶ k) (s : j ⟶ l)
    (h : a ≫ s = r ≫ b) (P Q : Complex (B.obj i)) (P' Q' : Complex (B.obj k))
    (f : (extend (B.map r)).obj P ⟶ P') (g : (extend (B.map r)).obj Q ⟶ Q') :=
  (extend (B.map s)).map (comparison (extensionPullback (B.map a)) (z a) P Q).hom ≫
    (comparison (extensionPullback (B.map s)) (z s)
      ((extend (B.map a)).obj P) ((extend (B.map a)).obj Q)).hom ≫
    totalMap (squareArrow B a b r s h P P' f) (squareArrow B a b r s h Q Q' g)
```

```lean
def tensorTransitionInverse (B : Index ⥤ Sheaf J CommRingCat.{w})
    (z : ∀ {i j : Index} (a : i ⟶ j), Comparison (extensionPullback (B.map a)))
    {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l) (r : i ⟶ k) (s : j ⟶ l)
    (h : a ≫ s = r ≫ b) (P Q : Complex (B.obj i)) (P' Q' : Complex (B.obj k))
    (f : (extend (B.map r)).obj P ⟶ P') (g : (extend (B.map r)).obj Q ⟶ Q') :=
  (extend (B.map s)).map (comparison (extensionPullback (B.map a)) (z a) P Q).inv ≫
    squareArrow B a b r s h (total P Q) (total P' Q')
      (tensorArrowFor B z r P Q P' Q' f g)
```

```lean
def TensorTransitionValues (B : Index ⥤ Sheaf J CommRingCat.{w})
    (z : ∀ {i j : Index} (a : i ⟶ j), Comparison (extensionPullback (B.map a))) : Prop :=
  ∀ {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l) (r : i ⟶ k) (s : j ⟶ l)
    (h : a ≫ s = r ≫ b) (P Q : Complex (B.obj i)) (P' Q' : Complex (B.obj k))
    (f : (extend (B.map r)).obj P ⟶ P') (g : (extend (B.map r)).obj Q ⟶ Q')
    (p q n : ℤ) (hpq : p + q = n) (U : Cᵒᵖ) (v v' : (B.obj j).obj.obj U)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
    ((((tensorTransitionForward B z a b r s h P Q P' Q' f g).f n).val.app U
      (extensionTmul (B.map s) (((extend (B.map a)).obj (total P Q)).X n) U 1
        (extensionTmul (B.map a) ((total P Q).X n) U v (totalPure P Q p q n hpq U x y)))) =
      totalPure ((extend (B.map b)).obj P') ((extend (B.map b)).obj Q') p q n hpq U
        (extensionTmul (B.map b) (P'.X p) U ((B.map s).hom.app U v)
          ((semilinearSectionMap (B.map r) f p).hom.app U x))
        (extensionTmul (B.map b) (Q'.X q) U 1
          ((semilinearSectionMap (B.map r) g q).hom.app U y))) ∧
    ((((tensorTransitionInverse B z a b r s h P Q P' Q' f g).f n).val.app U
      (extensionTmul (B.map s)
        ((total ((extend (B.map a)).obj P) ((extend (B.map a)).obj Q)).X n) U 1
        (totalPure ((extend (B.map a)).obj P) ((extend (B.map a)).obj Q) p q n hpq U
          (extensionTmul (B.map a) (P.X p) U v x)
          (extensionTmul (B.map a) (Q.X q) U v' y)))) =
      extensionTmul (B.map b) ((total P' Q').X n) U
        ((B.map s).hom.app U v * (B.map s).hom.app U v')
        (totalPure P' Q' p q n hpq U
          ((semilinearSectionMap (B.map r) f p).hom.app U x)
          ((semilinearSectionMap (B.map r) g q).hom.app U y)))
```

```lean
def Comparisons.PullTensorTransitionValues {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) (c : ∀ i : Index, Comparison (d.ringed i)) : Prop :=
  ∀ {i j : Index} (a : i ⟶ j)
    (P Q : Complex (d.R.obj i)) (P' Q' : Complex (d.R.obj j))
    (f : (extend (d.R.map a)).obj P ⟶ P')
    (g : (extend (d.R.map a)).obj Q ⟶ Q')
    (p q n : ℤ) (hpq : p + q = n) (Z : Sheaf J (Type w))
    (x : Z ⟶ (underlying (d.R.obj i)).obj (P.X p))
    (y : Z ⟶ (underlying (d.R.obj i)).obj (Q.X q))
    (z : Z ⟶ (underlying (d.R.obj i)).obj ((total P Q).X n)),
    (∀ (V : Cᵒᵖ) (v : Z.obj.obj V),
      z.hom.app V v = totalPure P Q p q n hpq V (x.hom.app V v) (y.hom.app V v)) →
    ∀ (U : Dᵒᵖ) (v : (d.inverse.obj Z).obj.obj U) (b : (d.S.obj i).obj.obj U),
      (((extend (d.S.map a)).map (comparison (d.ringed i) (c i) P Q).hom ≫
          (e.sigmaSC a ((pull (d.ringed i)).obj P) ((pull (d.ringed i)).obj Q)).hom ≫
          totalMap (e.pullArrow a P P' f) (e.pullArrow a Q Q' g)).f n).val.app U
        (extensionTmul (d.S.map a) ((d.L i).obj ((total P Q).X n)) U 1
          (b • (diagramGeneratorSection d c i ((total P Q).X n) Z z U v))) =
        totalPure ((pull (d.ringed j)).obj P') ((pull (d.ringed j)).obj Q') p q n hpq U
          (((d.S.map a).hom.app U b) •
            (diagramGeneratorSection d c j (P'.X p) Z
              (x ≫ semilinearSectionMap (d.R.map a) f p) U v))
          (diagramGeneratorSection d c j (Q'.X q) Z
            (y ≫ semilinearSectionMap (d.R.map a) g q) U v)
```

```lean
def Comparisons.TensorSquareValue {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) (c : ∀ i : Index, Comparison (d.ringed i)) : Prop :=
  ∀ {i j : Index} (a : i ⟶ j) (P Q : Complex (d.R.obj i))
    (p q n : ℤ) (hpq : p + q = n) (Z : Sheaf J (Type w))
    (x : Z ⟶ (underlying (d.R.obj i)).obj (P.X p))
    (y : Z ⟶ (underlying (d.R.obj i)).obj (Q.X q))
    (z : Z ⟶ (underlying (d.R.obj i)).obj ((total P Q).X n)),
    (∀ (V : Cᵒᵖ) (v : Z.obj.obj V),
      z.hom.app V v = totalPure P Q p q n hpq V (x.hom.app V v) (y.hom.app V v)) →
    ∀ (U : Dᵒᵖ) (v : (d.inverse.obj Z).obj.obj U)
      (b : (d.S.obj j).obj.obj U) (b' : (d.S.obj i).obj.obj U),
      ((e.kappaC a (total P Q) ≪≫
          (pull (d.ringed j)).mapIso (e.sigmaRC a P Q) ≪≫
          comparison (d.ringed j) (c j)
            ((extend (d.R.map a)).obj P) ((extend (d.R.map a)).obj Q)).hom.f n).val.app U
        (extensionTmul (d.S.map a) ((d.L i).obj ((total P Q).X n)) U b
          (b' • (diagramGeneratorSection d c i ((total P Q).X n) Z z U v))) =
        totalPure ((pull (d.ringed j)).obj ((extend (d.R.map a)).obj P))
          ((pull (d.ringed j)).obj ((extend (d.R.map a)).obj Q)) p q n hpq U
          ((b * (d.S.map a).hom.app U b') •
            (diagramGeneratorSection d c j ((extensionFunctor (d.R.map a)).obj (P.X p)) Z
              (x ≫ insertion (d.R.map a) (P.X p)) U v))
          (diagramGeneratorSection d c j ((extensionFunctor (d.R.map a)).obj (Q.X q)) Z
            (y ≫ insertion (d.R.map a) (Q.X q)) U v)
```

## New

```lean
noncomputable abbrev tensorComparison {R : Sheaf J CommRingCat.{w}}
    {S : Sheaf K CommRingCat.{w}} (f : RingedPullback R S) (c : Comparison f)
    (P Q : Complex R) : (pull f).obj (total P Q) ≅
      total ((pull f).obj P) ((pull f).obj Q) := comparison f c P Q
```

```lean
noncomputable abbrev tensorTotalMap {R : Sheaf J CommRingCat.{w}}
    {P Q P' Q' : Complex R} (f : P ⟶ P') (g : Q ⟶ Q') :
    total P Q ⟶ total P' Q' := totalMap f g
```

```lean
noncomputable abbrev tensorTotalIso {R : Sheaf J CommRingCat.{w}}
    {P Q P' Q' : Complex R} (f : P ≅ P') (g : Q ≅ Q') :
    total P Q ≅ total P' Q' := totalIso f g
```

```lean
noncomputable def tensorD₁ {R : Sheaf J CommRingCat.{w}}
    (P Q : Complex R) (n m : ℤ) : (total P Q).X n ⟶ (total P Q).X m :=
  HomologicalComplex.mapBifunctor.D₁ P Q (curriedTensor (Modules R)) (.up ℤ) n m
```

```lean
noncomputable def tensorD₂ {R : Sheaf J CommRingCat.{w}}
    (P Q : Complex R) (n m : ℤ) : (total P Q).X n ⟶ (total P Q).X m :=
  HomologicalComplex.mapBifunctor.D₂ P Q (curriedTensor (Modules R)) (.up ℤ) n m
```

```lean
noncomputable abbrev tensorι {R : Sheaf J CommRingCat.{w}}
    (P Q : Complex R) (p q n : ℤ) (h : p + q = n) :
    P.X p ⊗ Q.X q ⟶ (total P Q).X n :=
  ScalarCalculation.tensorι P Q p q n h
```

```lean
def TotalDifferentials {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}
    (f : RingedPullback R S) (c : Comparison f) : Prop :=
  ∀ (P Q : Complex R) (n n' : ℤ),
    (f.L.map (tensorD₁ P Q n n') ≫ (tensorComparison f c P Q).hom.f n' =
      (tensorComparison f c P Q).hom.f n ≫
        tensorD₁ ((pull f).obj P) ((pull f).obj Q) n n') ∧
    (f.L.map (tensorD₂ P Q n n') ≫ (tensorComparison f c P Q).hom.f n' =
      (tensorComparison f c P Q).hom.f n ≫
        tensorD₂ ((pull f).obj P) ((pull f).obj Q) n n') ∧
    (tensorD₁ ((pull f).obj P) ((pull f).obj Q) n n' ≫ (tensorComparison f c P Q).inv.f n' =
      (tensorComparison f c P Q).inv.f n ≫
        f.L.map (tensorD₁ P Q n n')) ∧
    (tensorD₂ ((pull f).obj P) ((pull f).obj Q) n n' ≫ (tensorComparison f c P Q).inv.f n' =
      (tensorComparison f c P Q).inv.f n ≫
        f.L.map (tensorD₂ P Q n n'))
```

```lean
def Comparisons.KappaDifferentials {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) : Prop :=
  ∀ {i j : Index} (a : i ⟶ j) (P Q : Complex (d.R.obj i)) (n n' : ℤ)
    (v : Fin 2),
    ((d.L i ⋙ extensionFunctor (d.S.map a)).map
        ((if v = 0 then tensorD₁ else
          tensorD₂) P Q n n') ≫ (e.kappaC a (total P Q)).hom.f n' =
      (e.kappaC a (total P Q)).hom.f n ≫
        (extensionFunctor (d.R.map a) ⋙ d.L j).map
          ((if v = 0 then tensorD₁ else
            tensorD₂) P Q n n')) ∧
    ((extensionFunctor (d.R.map a) ⋙ d.L j).map
        ((if v = 0 then tensorD₁ else
          tensorD₂) P Q n n') ≫ (e.kappaC a (total P Q)).inv.f n' =
      (e.kappaC a (total P Q)).inv.f n ≫
        (d.L i ⋙ extensionFunctor (d.S.map a)).map
          ((if v = 0 then tensorD₁ else
            tensorD₂) P Q n n'))
```

```lean
def TotalNaturality {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}
    (f : RingedPullback R S) (c : Comparison f) : Prop :=
  ∀ (P Q P' Q' : Complex R) (a : P ⟶ P') (b : Q ⟶ Q'),
    (pull f).map (tensorTotalMap a b) ≫ (tensorComparison f c P' Q').hom =
      (tensorComparison f c P Q).hom ≫ tensorTotalMap ((pull f).map a) ((pull f).map b) ∧
    tensorTotalMap ((pull f).map a) ((pull f).map b) ≫ (tensorComparison f c P' Q').inv =
      (tensorComparison f c P Q).inv ≫ (pull f).map (tensorTotalMap a b)
```

```lean
def TotalSummands {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}
    (f : RingedPullback R S) (c : Comparison f) : Prop :=
  ∀ (P Q : Complex R) (p q n : ℤ) (h : p + q = n),
    (f.L.map (tensorι P Q p q n h) ≫
        (tensorComparison f c P Q).hom.f n =
      (c.mu (P.X p) (Q.X q)).hom ≫
        tensorι ((pull f).obj P) ((pull f).obj Q) p q n h) ∧
    (tensorι ((pull f).obj P) ((pull f).obj Q) p q n h ≫ (tensorComparison f c P Q).inv.f n =
      (c.mu (P.X p) (Q.X q)).inv ≫
        f.L.map (tensorι P Q p q n h))
```

```lean
def Comparisons.TensorSquare {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) (c : ∀ i : Index, Comparison (d.ringed i)) : Prop :=
  ∀ {i j : Index} (a : i ⟶ j) (P Q : Complex (d.R.obj i)),
    e.kappaC a (total P Q) ≪≫
        (pull (d.ringed j)).mapIso (e.sigmaRC a P Q) ≪≫
        tensorComparison (d.ringed j) (c j)
          ((extend (d.R.map a)).obj P) ((extend (d.R.map a)).obj Q) =
      (extend (d.S.map a)).mapIso (tensorComparison (d.ringed i) (c i) P Q) ≪≫
        e.sigmaSC a ((pull (d.ringed i)).obj P) ((pull (d.ringed i)).obj Q) ≪≫
        tensorTotalIso (e.kappaC a P) (e.kappaC a Q)
```

```lean
def Comparisons.PullTensorTransitions {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) (c : ∀ i : Index, Comparison (d.ringed i)) : Prop :=
  ∀ {i j : Index} (t : i ⟶ j)
    (P Q : Complex (d.R.obj i)) (P' Q' : Complex (d.R.obj j))
    (f : (extend (d.R.map t)).obj P ⟶ P')
    (g : (extend (d.R.map t)).obj Q ⟶ Q'),
    (extend (d.S.map t)).map (tensorComparison (d.ringed i) (c i) P Q).hom ≫
        (e.sigmaSC t ((pull (d.ringed i)).obj P) ((pull (d.ringed i)).obj Q)).hom ≫
        tensorTotalMap (e.pullArrow t P P' f) (e.pullArrow t Q Q' g) =
      e.pullArrow t (total P Q) (total P' Q') (e.tensorArrow t P Q P' Q' f g) ≫
        (tensorComparison (d.ringed j) (c j) P' Q').hom
```

```lean
def semilinearSectionMap {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    {P : Complex A} {Q : Complex B} (f : (extend a).obj P ⟶ Q) (p : ℤ) :
    (underlying A).obj (P.X p) ⟶ (underlying B).obj (Q.X p) :=
  KappaCalculation.semilinearSectionMap a f p
```

```lean
def inverseSectionMap (d : Diagram (J := J) (K := K)) {i j : Index} (a : i ⟶ j)
    {P : Complex (d.R.obj i)} {Q : Complex (d.R.obj j)}
    (f : (extend (d.R.map a)).obj P ⟶ Q) (p : ℤ) :
    (underlying (d.RI.obj i)).obj ((d.algebraic i).modules.obj (P.X p)) ⟶
      (underlying (d.RI.obj j)).obj ((d.algebraic j).modules.obj (Q.X p)) :=
  KappaCalculation.inverseSectionMap d a f p
```

```lean
def diagramInsertion (d : Diagram (J := J) (K := K)) {i j : Index} (a : i ⟶ j)
    (M : Modules (d.R.obj i)) :
    (underlying (d.RI.obj i)).obj ((d.algebraic i).modules.obj M) ⟶
      (underlying (d.RI.obj j)).obj
        ((d.algebraic j).modules.obj ((extensionFunctor (d.R.map a)).obj M)) :=
  KappaCalculation.diagramInsertion d a M
```

```lean
def diagramPullSection (d : Diagram (J := J) (K := K)) (i : Index)
    (M : Modules (d.R.obj i)) (U : Dᵒᵖ) (b : (d.S.obj i).obj.obj U)
    (x : ((d.algebraic i).modules.obj M).val.obj U) : ((d.L i).obj M).val.obj U :=
  KappaCalculation.diagramPullSection d i M U b x
```

```lean
def diagramGeneratorSection (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (i : Index)
    (M : Modules (d.R.obj i)) (Z : Sheaf J (Type w))
    (x : Z ⟶ (underlying (d.R.obj i)).obj M) (U : Dᵒᵖ)
    (v : (d.inverse.obj Z).obj.obj U) : ((d.L i).obj M).val.obj U :=
  PullCalculation.diagramGeneratorSection d c i M Z x U v
```

```lean
def Comparisons.kappaTransitionForward {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l)
    (r : i ⟶ k) (s : j ⟶ l) (h : a ≫ s = r ≫ b)
    (P : Complex (d.R.obj i)) (Q : Complex (d.R.obj k))
    (f : (extend (d.R.map r)).obj P ⟶ Q) :=
  KappaCalculation.kappaTransitionForward e a b r s h P Q f
```

```lean
def Comparisons.kappaTransitionInverse {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l)
    (r : i ⟶ k) (s : j ⟶ l) (h : a ≫ s = r ≫ b)
    (P : Complex (d.R.obj i)) (Q : Complex (d.R.obj k))
    (f : (extend (d.R.map r)).obj P ⟶ Q) :=
  KappaCalculation.kappaTransitionInverse e a b r s h P Q f
```

```lean
def Comparisons.KappaTransitionValues {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) : Prop :=
  KappaCalculation.KappaTransitionValues e
```

```lean
def totalPure {A : Sheaf J CommRingCat.{w}} (P Q : Complex A)
    (p q n : ℤ) (h : p + q = n) (U : Cᵒᵖ) (x : (P.X p).val.obj U)
    (y : (Q.X q).val.obj U) : ((total P Q).X n).val.obj U :=
  ScalarCalculation.totalPure P Q p q n h U x y
```

```lean
def tensorTransitionForward (B : Index ⥤ Sheaf J CommRingCat.{w})
    (z : ∀ {i j : Index} (a : i ⟶ j), Comparison (extensionPullback (B.map a)))
    {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l) (r : i ⟶ k) (s : j ⟶ l)
    (h : a ≫ s = r ≫ b) (P Q : Complex (B.obj i)) (P' Q' : Complex (B.obj k))
    (f : (extend (B.map r)).obj P ⟶ P') (g : (extend (B.map r)).obj Q ⟶ Q') :=
  ScalarCalculation.tensorTransitionForward B z a b r s h P Q P' Q' f g
```

```lean
def tensorTransitionInverse (B : Index ⥤ Sheaf J CommRingCat.{w})
    (z : ∀ {i j : Index} (a : i ⟶ j), Comparison (extensionPullback (B.map a)))
    {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l) (r : i ⟶ k) (s : j ⟶ l)
    (h : a ≫ s = r ≫ b) (P Q : Complex (B.obj i)) (P' Q' : Complex (B.obj k))
    (f : (extend (B.map r)).obj P ⟶ P') (g : (extend (B.map r)).obj Q ⟶ Q') :=
  ScalarCalculation.tensorTransitionInverse B z a b r s h P Q P' Q' f g
```

```lean
def TensorTransitionValues (B : Index ⥤ Sheaf J CommRingCat.{w})
    (z : ∀ {i j : Index} (a : i ⟶ j), Comparison (extensionPullback (B.map a))) : Prop :=
  ScalarCalculation.TensorTransitionValues B z
```

```lean
def Comparisons.PullTensorTransitionValues {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) (c : ∀ i : Index, Comparison (d.ringed i)) : Prop :=
  PullCalculation.PullTensorTransitionValues e c
```

```lean
def Comparisons.TensorSquareValue {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) (c : ∀ i : Index, Comparison (d.ringed i)) : Prop :=
  ∀ {i j : Index} (a : i ⟶ j) (P Q : Complex (d.R.obj i))
    (p q n : ℤ) (hpq : p + q = n) (Z : Sheaf J (Type w))
    (x : Z ⟶ (underlying (d.R.obj i)).obj (P.X p))
    (y : Z ⟶ (underlying (d.R.obj i)).obj (Q.X q))
    (z : Z ⟶ (underlying (d.R.obj i)).obj ((total P Q).X n)),
    (∀ (V : Cᵒᵖ) (v : Z.obj.obj V),
      z.hom.app V v = totalPure P Q p q n hpq V (x.hom.app V v) (y.hom.app V v)) →
    ∀ (U : Dᵒᵖ) (v : (d.inverse.obj Z).obj.obj U)
      (b : (d.S.obj j).obj.obj U) (b' : (d.S.obj i).obj.obj U),
      ((e.kappaC a (total P Q) ≪≫
          (pull (d.ringed j)).mapIso (e.sigmaRC a P Q) ≪≫
          tensorComparison (d.ringed j) (c j)
            ((extend (d.R.map a)).obj P) ((extend (d.R.map a)).obj Q)).hom.f n).val.app U
        (extensionTmul (d.S.map a) ((d.L i).obj ((total P Q).X n)) U b
          (b' • (diagramGeneratorSection d c i ((total P Q).X n) Z z U v))) =
        totalPure ((pull (d.ringed j)).obj ((extend (d.R.map a)).obj P))
          ((pull (d.ringed j)).obj ((extend (d.R.map a)).obj Q)) p q n hpq U
          ((b * (d.S.map a).hom.app U b') •
            (diagramGeneratorSection d c j ((extensionFunctor (d.R.map a)).obj (P.X p)) Z
              (x ≫ insertion (d.R.map a) (P.X p)) U v))
          (diagramGeneratorSection d c j ((extensionFunctor (d.R.map a)).obj (Q.X q)) Z
            (y ≫ insertion (d.R.map a) (Q.X q)) U v)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SecSmoothPurity.CoefficientComparisonsStrictTotalization | G4 | Its proof uses the shared definitions; all original propositions and formulas are retained definitionally. |
| Sheaf.SecSmoothPurity.StrictCoefficientComparisonCalculus | unclaimed | Consumes the same conjunction; its original proof is preserved. |
| Sheaf.Paper.BalancedFiniteTowerGeneratorComparison | unclaimed | Transitive consumer, with unchanged mathematical statements. |
| Sheaf.Paper.CompletedComparisonQuotientRealization | unclaimed | Transitive consumer, with unchanged mathematical statements. |

The downstream strict coefficient calculus now imports the item and consumes its
unchanged theorem signature. Its transitive consumers are listed below. The
original consumer sources compiled unchanged against this packet.
No adopted source-library module is modified. These are presentation changes;
target meaning is unchanged.

## Status

landed 20261024T185821-L-3693383 2026-10-24 (merge of deliver/G4/Sheaf.SecSmoothPurity.CoefficientComparisonsStrictTotalization)
