# Compact universal witnesses and transition cones

## Reason

The componentwise universal witnesses and transition maps repeatedly reduce to
records during the abelian proof. Move their compatibility and naturality proofs
into named private theorems, leaving the actual component maps, lifts, descents
and universal properties unchanged. This reduces repeated checking of the same
large proof fields. Every new theorem is completely proved from the original
argument; no data is selected from an existence theorem.

These private construction changes do not change a public signature or object.
The complete final module, including the new abelian proof and the official
axiom probe, compiled in 52.9 seconds within the unchanged 60-second limit.

## Old

```lean
private def system_isColimit {K : Type} [SmallCategory K]
    {F : K ⥤ StrictRingSystem B} (c : Cocone F)
    (hc : ∀ n, IsColimit ((systemEvaluation B n).mapCocone c)) : IsColimit c where
  desc s :=
    { app := fun n ↦ (hc n).desc ((systemEvaluation B n).mapCocone s)
      comm := by
        intro m n h
        apply (hc n).hom_ext
        intro j
        change (c.ι.app j).app n ≫ _ = (c.ι.app j).app n ≫ _
        erw [← Category.assoc, (hc n).fac ((systemEvaluation B n).mapCocone s) j]
        erw [← Category.assoc, (c.ι.app j).comm h, Category.assoc, ← Functor.map_comp,
          (hc m).fac ((systemEvaluation B m).mapCocone s) j]
        exact (s.ι.app j).comm h }
  fac s j := system_hom_ext _ _ (fun n ↦ (hc n).fac _ j)
  uniq s f hf := by
    apply system_hom_ext
    intro n
    apply (hc n).uniq ((systemEvaluation B n).mapCocone s) (f.app n)
    intro j
    exact congrArg (fun g : F.obj j ⟶ s.pt ↦ g.app n) (hf j)
```

```lean
private def system_isLimit {K : Type} [SmallCategory K] [FinCategory K]
    {F : K ⥤ StrictRingSystem B} (c : Cone F)
    (hc : ∀ n, IsLimit ((systemEvaluation B n).mapCone c)) : IsLimit c where
  lift s :=
    { app := fun n ↦ (hc n).lift ((systemEvaluation B n).mapCone s)
      comm := by
        intro m n h
        apply (isLimitOfPreserves (systemRestriction B h) (hc m)).hom_ext
        intro j
        change _ ≫ (systemRestriction B h).map ((c.π.app j).app m) =
          _ ≫ (systemRestriction B h).map ((c.π.app j).app m)
        erw [Category.assoc, ← (c.π.app j).comm h, ← Category.assoc,
          (hc n).fac ((systemEvaluation B n).mapCone s) j]
        erw [Category.assoc, ← Functor.map_comp,
          (hc m).fac ((systemEvaluation B m).mapCone s) j]
        exact (s.π.app j).comm h }
  fac s j := system_hom_ext _ _ (fun n ↦ (hc n).fac _ j)
  uniq s f hf := by
    apply system_hom_ext
    intro n
    apply (hc n).uniq ((systemEvaluation B n).mapCone s) (f.app n)
    intro j
    exact congrArg (fun g : s.pt ⟶ F.obj j ↦ g.app n) (hf j)
```

```lean
private def system_colimit_transition {K : Type} [SmallCategory K] [FinCategory K]
    (F : K ⥤ StrictRingSystem B) {m n : ℕ} (h : m ≤ n) :
    colimit (F ⋙ systemEvaluation B n) ⟶
      (systemRestriction B h).obj (colimit (F ⋙ systemEvaluation B m)) :=
  colimit.desc (F ⋙ systemEvaluation B n)
    { pt := (systemRestriction B h).obj (colimit (F ⋙ systemEvaluation B m))
      ι :=
        { app := fun j ↦ (F.obj j).transition h ≫
            (systemRestriction B h).map (colimit.ι (F ⋙ systemEvaluation B m) j)
          naturality := by
            intro j k f
            change (F.map f).app n ≫ ((F.obj k).transition h ≫ _) = _ ≫ 𝟙 _
            rw [Category.comp_id, ← Category.assoc, (F.map f).comm h,
              Category.assoc, ← Functor.map_comp]
            exact congrArg (fun g ↦ (F.obj j).transition h ≫ (systemRestriction B h).map g)
              (colimit.w (F ⋙ systemEvaluation B m) f) } }
```

```lean
private def system_limit_transition {K : Type} [SmallCategory K] [FinCategory K]
    (F : K ⥤ StrictRingSystem B) {m n : ℕ} (h : m ≤ n) :
    limit (F ⋙ systemEvaluation B n) ⟶
      (systemRestriction B h).obj (limit (F ⋙ systemEvaluation B m)) :=
  (isLimitOfPreserves (systemRestriction B h)
    (limit.isLimit (F ⋙ systemEvaluation B m))).lift
    { pt := limit (F ⋙ systemEvaluation B n)
      π :=
        { app := fun j ↦ limit.π (F ⋙ systemEvaluation B n) j ≫ (F.obj j).transition h
          naturality := by
            intro j k f
            change 𝟙 _ ≫ (limit.π (F ⋙ systemEvaluation B n) k ≫ _) =
              (limit.π (F ⋙ systemEvaluation B n) j ≫ (F.obj j).transition h) ≫
                (systemRestriction B h).map ((F.map f).app m)
            rw [Category.id_comp, Category.assoc, ← (F.map f).comm h, ← Category.assoc]
            exact congrArg (fun g ↦ g ≫ (F.obj k).transition h)
              (limit.w (F ⋙ systemEvaluation B n) f).symm } }
```

## New

```lean
private theorem system_desc_comm {K : Type} [SmallCategory K]
    {F : K ⥤ StrictRingSystem B} (c : Cocone F)
    (hc : ∀ n, IsColimit ((systemEvaluation B n).mapCocone c)) (s : Cocone F)
    {m n : ℕ} (h : m ≤ n) :
    (hc n).desc ((systemEvaluation B n).mapCocone s) ≫ s.pt.transition h =
      c.pt.transition h ≫ (systemRestriction B h).map
        ((hc m).desc ((systemEvaluation B m).mapCocone s)) := by
  apply (hc n).hom_ext
  intro j
  change (c.ι.app j).app n ≫ _ = (c.ι.app j).app n ≫ _
  erw [← Category.assoc, (hc n).fac ((systemEvaluation B n).mapCocone s) j]
  erw [← Category.assoc, (c.ι.app j).comm h, Category.assoc, ← Functor.map_comp,
    (hc m).fac ((systemEvaluation B m).mapCocone s) j]
  exact (s.ι.app j).comm h

private def system_isColimit {K : Type} [SmallCategory K]
    {F : K ⥤ StrictRingSystem B} (c : Cocone F)
    (hc : ∀ n, IsColimit ((systemEvaluation B n).mapCocone c)) : IsColimit c where
  desc s :=
    { app := fun n ↦ (hc n).desc ((systemEvaluation B n).mapCocone s)
      comm := system_desc_comm c hc s }
  fac s j := system_hom_ext _ _ (fun n ↦ (hc n).fac _ j)
  uniq s f hf := by
    apply system_hom_ext
    intro n
    apply (hc n).uniq ((systemEvaluation B n).mapCocone s) (f.app n)
    intro j
    exact congrArg (fun g : F.obj j ⟶ s.pt ↦ g.app n) (hf j)
```

```lean
private theorem system_lift_comm {K : Type} [SmallCategory K] [FinCategory K]
    {F : K ⥤ StrictRingSystem B} (c : Cone F)
    (hc : ∀ n, IsLimit ((systemEvaluation B n).mapCone c)) (s : Cone F)
    {m n : ℕ} (h : m ≤ n) :
    (hc n).lift ((systemEvaluation B n).mapCone s) ≫ c.pt.transition h =
      s.pt.transition h ≫ (systemRestriction B h).map
        ((hc m).lift ((systemEvaluation B m).mapCone s)) := by
  apply (isLimitOfPreserves (systemRestriction B h) (hc m)).hom_ext
  intro j
  change _ ≫ (systemRestriction B h).map ((c.π.app j).app m) =
    _ ≫ (systemRestriction B h).map ((c.π.app j).app m)
  erw [Category.assoc, ← (c.π.app j).comm h, ← Category.assoc,
    (hc n).fac ((systemEvaluation B n).mapCone s) j]
  erw [Category.assoc, ← Functor.map_comp,
    (hc m).fac ((systemEvaluation B m).mapCone s) j]
  exact (s.π.app j).comm h

private def system_isLimit {K : Type} [SmallCategory K] [FinCategory K]
    {F : K ⥤ StrictRingSystem B} (c : Cone F)
    (hc : ∀ n, IsLimit ((systemEvaluation B n).mapCone c)) : IsLimit c where
  lift s :=
    { app := fun n ↦ (hc n).lift ((systemEvaluation B n).mapCone s)
      comm := system_lift_comm c hc s }
  fac s j := system_hom_ext _ _ (fun n ↦ (hc n).fac _ j)
  uniq s f hf := by
    apply system_hom_ext
    intro n
    apply (hc n).uniq ((systemEvaluation B n).mapCone s) (f.app n)
    intro j
    exact congrArg (fun g : s.pt ⟶ F.obj j ↦ g.app n) (hf j)
```

```lean
private theorem system_colimit_transition_naturality {K : Type}
    [SmallCategory K] [FinCategory K] (F : K ⥤ StrictRingSystem B)
    {m n : ℕ} (h : m ≤ n) {j k : K} (f : j ⟶ k) :
    (F.map f).app n ≫ ((F.obj k).transition h ≫
        (systemRestriction B h).map (colimit.ι (F ⋙ systemEvaluation B m) k)) =
      ((F.obj j).transition h ≫
        (systemRestriction B h).map (colimit.ι (F ⋙ systemEvaluation B m) j)) ≫ 𝟙 _ := by
  rw [Category.comp_id, ← Category.assoc, (F.map f).comm h,
    Category.assoc, ← Functor.map_comp]
  exact congrArg (fun g ↦ (F.obj j).transition h ≫ (systemRestriction B h).map g)
    (colimit.w (F ⋙ systemEvaluation B m) f)

private def system_colimit_transition {K : Type} [SmallCategory K] [FinCategory K]
    (F : K ⥤ StrictRingSystem B) {m n : ℕ} (h : m ≤ n) :
    colimit (F ⋙ systemEvaluation B n) ⟶
      (systemRestriction B h).obj (colimit (F ⋙ systemEvaluation B m)) :=
  colimit.desc (F ⋙ systemEvaluation B n)
    { pt := (systemRestriction B h).obj (colimit (F ⋙ systemEvaluation B m))
      ι :=
        { app := fun j ↦ (F.obj j).transition h ≫
            (systemRestriction B h).map (colimit.ι (F ⋙ systemEvaluation B m) j)
          naturality := fun _ _ f ↦ system_colimit_transition_naturality F h f } }
```

```lean
private theorem system_limit_transition_naturality {K : Type}
    [SmallCategory K] [FinCategory K] (F : K ⥤ StrictRingSystem B)
    {m n : ℕ} (h : m ≤ n) {j k : K} (f : j ⟶ k) :
    𝟙 _ ≫ (limit.π (F ⋙ systemEvaluation B n) k ≫ (F.obj k).transition h) =
      (limit.π (F ⋙ systemEvaluation B n) j ≫ (F.obj j).transition h) ≫
        (systemRestriction B h).map ((F.map f).app m) := by
  rw [Category.id_comp, Category.assoc, ← (F.map f).comm h, ← Category.assoc]
  exact congrArg (fun g ↦ g ≫ (F.obj k).transition h)
    (limit.w (F ⋙ systemEvaluation B n) f).symm

private def system_limit_transition {K : Type} [SmallCategory K] [FinCategory K]
    (F : K ⥤ StrictRingSystem B) {m n : ℕ} (h : m ≤ n) :
    limit (F ⋙ systemEvaluation B n) ⟶
      (systemRestriction B h).obj (limit (F ⋙ systemEvaluation B m)) :=
  (isLimitOfPreserves (systemRestriction B h)
    (limit.isLimit (F ⋙ systemEvaluation B m))).lift
    { pt := limit (F ⋙ systemEvaluation B n)
      π :=
        { app := fun j ↦ limit.π (F ⋙ systemEvaluation B n) j ≫ (F.obj j).transition h
          naturality := fun _ _ f ↦ system_limit_transition_naturality F h f } }
```

## Users

All four definitions and all four new lemmas are private to
`Sheaf.CategoryTheory.SystemLevelLeftExtension`, held by Z7. Their existing
componentwise limit, colimit and evaluation consumers keep the same maps and
properties. No other module can refer to these private names. The unchanged
public abelian instance is chosen from its now-proved unique-existence theorem.

## Status

landed 20261020T221409-L-4183604 2026-10-20 (merge of deliver/Z7/Sheaf.CategoryTheory.SystemLevelLeftExtension)
