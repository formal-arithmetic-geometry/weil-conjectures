# CategoryTheory.OrientedProduct large-site definitions

## Reason

The existence and rigidity arguments must import the explicit large triple-site data without
importing the theorem that uses them. Move the existing definitions to a data-only module,
publicly re-exported by the original module. This is a file/interface refactor, not a change
of any existing mathematical definition or statement. It introduces LargeOrientationFormula,
which abbreviates exactly the orientation conjunct already present in the original theorem.
The theorem universalWithLargeSites retains its complete signature, including universes.
No adopted WeilConjectures source module is changed.

## Old

In lean/Sheaf/CategoryTheory/Sites/OrientedProductLargeSites.lean:

```lean
/-- Associated sheaves of representables on a site with independent universes, valued in the
containing universe `Type (max v w)`; no subcanonicity is assumed.
Source: ILO XI §§1.2–1.3 (blueprint: lem-trf-oriented-product-universal). -/
noncomputable def largeAssociated {C : Type w} [Category.{v} C] (J : GrothendieckTopology C) :
    C ⥤ Sheaf J (Type (max v w)) :=
  uliftYoneda.{w} ⋙ presheafToSheaf J (Type (max v w))

variable {C₁ C₂ D : Type w} [Category.{v} C₁] [Category.{v} C₂] [Category.{v} D]
  [HasFiniteLimits C₁] [HasFiniteLimits C₂] [HasFiniteLimits D]

/-- The category of triples, using Mathlib's comma and product categories.
Source: ILO XI §1.1(i) (blueprint: lem-trf-oriented-product-universal). -/
abbrev largeTriples (F : D ⥤ C₁) (G : D ⥤ C₂) := Comma (𝟭 (C₁ × C₂)) (F.prod' G)

/-- The three generating covering types. Unchanged components are allowed to be isomorphisms;
this is the isomorphism closure of the literal generators in XI §1.1(ii)(a)–(c).
Source: ILO XI §1.1(ii) (blueprint: lem-trf-oriented-product-universal). -/
def largeGenerators (J₁ : Pretopology C₁) (J₂ : Pretopology C₂)
    (F : D ⥤ C₁) (G : D ⥤ C₂) : Precoverage (largeTriples F G) where
  coverings Z := {R |
    (∃ (I : Type (max v w)) (Zᵢ : I → largeTriples F G) (r : ∀ i, Zᵢ i ⟶ Z),
      R = Presieve.ofArrows Zᵢ r ∧
      ((Presieve.ofArrows (fun i ↦ (Zᵢ i).left.1) (fun i ↦ (r i).left.1) ∈ J₁ Z.left.1 ∧
        ∀ i, IsIso (r i).right ∧ IsIso (r i).left.2) ∨
       (Presieve.ofArrows (fun i ↦ (Zᵢ i).left.2) (fun i ↦ (r i).left.2) ∈ J₂ Z.left.2 ∧
        ∀ i, IsIso (r i).right ∧ IsIso (r i).left.1))) ∨
    (∃ (Z' : largeTriples F G) (r : Z' ⟶ Z), R = Presieve.singleton r ∧
      IsIso r.left.1 ∧ IsPullback r.left.2 Z'.hom.2 Z.hom.2 (G.map r.right))}

/-- The generated Grothendieck topology, with no unproved data.
Source: ILO XI §1.1(ii) (blueprint: lem-trf-oriented-product-universal). -/
def largeTopology (J₁ : Pretopology C₁) (J₂ : Pretopology C₂)
    (F : D ⥤ C₁) (G : D ⥤ C₂) : GrothendieckTopology (largeTriples F G) :=
  (largeGenerators J₁ J₂ F G).toGrothendieck

/-- The first site projection on objects, using final objects.
Source: ILO XI §1.3 (blueprint: lem-trf-oriented-product-universal). -/
noncomputable def largeFirstTriple (F : D ⥤ C₁) (G : D ⥤ C₂)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (U : C₁) : largeTriples F G where
  left := (U, ⊤_ C₂)
  right := ⊤_ D
  hom := (terminal.from U ≫ inv (terminalComparison F), inv (terminalComparison G))

/-- The second site projection on objects.
Source: ILO XI §1.3 (blueprint: lem-trf-oriented-product-universal). -/
noncomputable def largeSecondTriple (F : D ⥤ C₁) (G : D ⥤ C₂)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (W : C₂) : largeTriples F G where
  left := (⊤_ C₁, W)
  right := ⊤_ D
  hom := (inv (terminalComparison F), terminal.from W ≫ inv (terminalComparison G))

variable (F : D ⥤ C₁) (G : D ⥤ C₂)
  [PreservesFiniteLimits F] [PreservesFiniteLimits G]

/-- The first projection site functor. Source: ILO XI §1.3
(blueprint: lem-trf-oriented-product-universal). -/
noncomputable def largeFirst : C₁ ⥤ largeTriples F G where
  obj := largeFirstTriple F G
  map r := ⟨(r, 𝟙 _), 𝟙 _, by
    apply Prod.ext <;> simp [largeFirstTriple]⟩
  map_comp _ _ := by ext <;> simp [largeFirstTriple]

/-- The second projection site functor. Source: ILO XI §1.3
(blueprint: lem-trf-oriented-product-universal). -/
noncomputable def largeSecond : C₂ ⥤ largeTriples F G where
  obj := largeSecondTriple F G
  map r := ⟨(𝟙 _, r), 𝟙 _, by
    apply Prod.ext <;> simp [largeSecondTriple]⟩
  map_comp _ _ := by ext <;> simp [largeSecondTriple]

/-- Structural arrow to the first projection triple. Source: ILO XI Lemma 1.5
(blueprint: lem-trf-oriented-product-universal). -/
noncomputable def largeToFirst (Z : largeTriples F G) : Z ⟶ (largeFirst F G).obj Z.left.1 where
  left := (𝟙 _, terminal.from _)
  right := terminal.from _
  w := Prod.ext
    ((terminalIsTerminal.isTerminalObj F _).hom_ext _ _)
    ((terminalIsTerminal.isTerminalObj G _).hom_ext _ _)

/-- Structural arrow to the second projection triple. Source: ILO XI Lemma 1.5
(blueprint: lem-trf-oriented-product-universal). -/
noncomputable def largeToSecond (Z : largeTriples F G) : Z ⟶ (largeSecond F G).obj Z.left.2 where
  left := (terminal.from _, 𝟙 _)
  right := terminal.from _
  w := Prod.ext
    ((terminalIsTerminal.isTerminalObj F _).hom_ext _ _)
    ((terminalIsTerminal.isTerminalObj G _).hom_ext _ _)

/-- The middle triple defining the orientation. Source: ILO XI §1.3
(blueprint: lem-trf-oriented-product-universal). -/
def largeMiddle (V : D) : largeTriples F G := ⟨(F.obj V, G.obj V), V, (𝟙 _, 𝟙 _)⟩

/-- The defining pullback formula, with its actual structural maps; it is required for
all compatible lifts, hence in particular for the universal lift.
Source: ILO XI §1.6, formula (1.a) (blueprint: lem-trf-oriented-product-universal). -/
def LargeHasLiftFormula (J₁ : Pretopology C₁) (J₂ : Pretopology C₂) (K : Pretopology D)
    (f : GeometricMorphism (Sheaf J₁.toGrothendieck (Type (max v w)))
      (Sheaf K.toGrothendieck (Type (max v w))))
    (g : GeometricMorphism (Sheaf J₂.toGrothendieck (Type (max v w)))
      (Sheaf K.toGrothendieck (Type (max v w))))
    (ηF : largeAssociated K.toGrothendieck ⋙ f.inverse ≅
      F ⋙ largeAssociated J₁.toGrothendieck)
    (ηG : largeAssociated K.toGrothendieck ⋙ g.inverse ≅
      G ⋙ largeAssociated J₂.toGrothendieck)
    (p₁ : GeometricMorphism (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w)))
      (Sheaf J₁.toGrothendieck (Type (max v w))))
    (p₂ : GeometricMorphism (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w)))
      (Sheaf J₂.toGrothendieck (Type (max v w))))
    (π₁ : largeAssociated J₁.toGrothendieck ⋙ p₁.inverse ≅
      largeFirst F G ⋙ largeAssociated (largeTopology J₁ J₂ F G))
    (π₂ : largeAssociated J₂.toGrothendieck ⋙ p₂.inverse ≅
      largeSecond F G ⋙ largeAssociated (largeTopology J₁ J₂ F G))
    (τ : (p₂.comp g).direct ⟶ (p₁.comp f).direct) : Prop :=
  ∀ (E : Type e) [Category.{ve} E], IsGrothendieckTopos.{max v w} E →
    ∀ (a : GeometricMorphism E (Sheaf J₁.toGrothendieck (Type (max v w))))
      (b : GeometricMorphism E (Sheaf J₂.toGrothendieck (Type (max v w))))
      (t : (b.comp g).direct ⟶ (a.comp f).direct)
      (h : GeometricMorphism E (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w))))
      (α : (h.comp p₁).direct ≅ a.direct) (β : (h.comp p₂).direct ≅ b.direct),
      paste f g p₁ p₂ τ h a b α β = t → ∀ Z : largeTriples F G,
      IsPullback
        (h.inverse.map ((largeAssociated (largeTopology J₁ J₂ F G)).map (largeToFirst F G Z) ≫
            π₁.inv.app Z.left.1) ≫ (GeometricMorphism.inverseIso α).inv.app
              ((largeAssociated J₁.toGrothendieck).obj Z.left.1))
        (h.inverse.map ((largeAssociated (largeTopology J₁ J₂ F G)).map (largeToSecond F G Z) ≫
            π₂.inv.app Z.left.2) ≫ (GeometricMorphism.inverseIso β).inv.app
              ((largeAssociated J₂.toGrothendieck).obj Z.left.2))
        (a.inverse.map ((largeAssociated J₁.toGrothendieck).map Z.hom.1 ≫ ηF.inv.app Z.right) ≫
          (GeometricMorphism.inverseMate t).app ((largeAssociated K.toGrothendieck).obj Z.right))
        (b.inverse.map ((largeAssociated J₂.toGrothendieck).map Z.hom.2 ≫ ηG.inv.app Z.right))
```

## New

The same declarations, verbatim except their blueprint docstring attachments, now reside in
lean/Sheaf/CategoryTheory/Sites/OrientedProductLargeSiteData.lean:

```lean
/-- Associated sheaves of representables on a site with independent universes, valued in the
containing universe `Type (max v w)`; no subcanonicity is assumed.
Source: ILO XI §§1.2–1.3 (blueprint: def-trf-large-oriented-site-data). -/
noncomputable def largeAssociated {C : Type w} [Category.{v} C] (J : GrothendieckTopology C) :
    C ⥤ Sheaf J (Type (max v w)) :=
  uliftYoneda.{w} ⋙ presheafToSheaf J (Type (max v w))

variable {C₁ C₂ D : Type w} [Category.{v} C₁] [Category.{v} C₂] [Category.{v} D]
  [HasFiniteLimits C₁] [HasFiniteLimits C₂] [HasFiniteLimits D]

/-- The category of triples, using Mathlib's comma and product categories.
Source: ILO XI §1.1(i) (blueprint: def-trf-large-oriented-site-data). -/
abbrev largeTriples (F : D ⥤ C₁) (G : D ⥤ C₂) := Comma (𝟭 (C₁ × C₂)) (F.prod' G)

/-- The three generating covering types. Unchanged components are allowed to be isomorphisms;
this is the isomorphism closure of the literal generators in XI §1.1(ii)(a)–(c).
Source: ILO XI §1.1(ii) (blueprint: def-trf-large-oriented-site-data). -/
def largeGenerators (J₁ : Pretopology C₁) (J₂ : Pretopology C₂)
    (F : D ⥤ C₁) (G : D ⥤ C₂) : Precoverage (largeTriples F G) where
  coverings Z := {R |
    (∃ (I : Type (max v w)) (Zᵢ : I → largeTriples F G) (r : ∀ i, Zᵢ i ⟶ Z),
      R = Presieve.ofArrows Zᵢ r ∧
      ((Presieve.ofArrows (fun i ↦ (Zᵢ i).left.1) (fun i ↦ (r i).left.1) ∈ J₁ Z.left.1 ∧
        ∀ i, IsIso (r i).right ∧ IsIso (r i).left.2) ∨
       (Presieve.ofArrows (fun i ↦ (Zᵢ i).left.2) (fun i ↦ (r i).left.2) ∈ J₂ Z.left.2 ∧
        ∀ i, IsIso (r i).right ∧ IsIso (r i).left.1))) ∨
    (∃ (Z' : largeTriples F G) (r : Z' ⟶ Z), R = Presieve.singleton r ∧
      IsIso r.left.1 ∧ IsPullback r.left.2 Z'.hom.2 Z.hom.2 (G.map r.right))}

/-- The generated Grothendieck topology, with no unproved data.
Source: ILO XI §1.1(ii) (blueprint: def-trf-large-oriented-site-data). -/
def largeTopology (J₁ : Pretopology C₁) (J₂ : Pretopology C₂)
    (F : D ⥤ C₁) (G : D ⥤ C₂) : GrothendieckTopology (largeTriples F G) :=
  (largeGenerators J₁ J₂ F G).toGrothendieck

/-- The first site projection on objects, using final objects.
Source: ILO XI §1.3 (blueprint: def-trf-large-oriented-site-data). -/
noncomputable def largeFirstTriple (F : D ⥤ C₁) (G : D ⥤ C₂)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (U : C₁) : largeTriples F G where
  left := (U, ⊤_ C₂)
  right := ⊤_ D
  hom := (terminal.from U ≫ inv (terminalComparison F), inv (terminalComparison G))

/-- The second site projection on objects.
Source: ILO XI §1.3 (blueprint: def-trf-large-oriented-site-data). -/
noncomputable def largeSecondTriple (F : D ⥤ C₁) (G : D ⥤ C₂)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (W : C₂) : largeTriples F G where
  left := (⊤_ C₁, W)
  right := ⊤_ D
  hom := (inv (terminalComparison F), terminal.from W ≫ inv (terminalComparison G))

variable (F : D ⥤ C₁) (G : D ⥤ C₂)
  [PreservesFiniteLimits F] [PreservesFiniteLimits G]

/-- The first projection site functor. Source: ILO XI §1.3
(blueprint: def-trf-large-oriented-site-data). -/
noncomputable def largeFirst : C₁ ⥤ largeTriples F G where
  obj := largeFirstTriple F G
  map r := ⟨(r, 𝟙 _), 𝟙 _, by
    apply Prod.ext <;> simp [largeFirstTriple]⟩
  map_comp _ _ := by ext <;> simp [largeFirstTriple]

/-- The second projection site functor. Source: ILO XI §1.3
(blueprint: def-trf-large-oriented-site-data). -/
noncomputable def largeSecond : C₂ ⥤ largeTriples F G where
  obj := largeSecondTriple F G
  map r := ⟨(𝟙 _, r), 𝟙 _, by
    apply Prod.ext <;> simp [largeSecondTriple]⟩
  map_comp _ _ := by ext <;> simp [largeSecondTriple]

/-- Structural arrow to the first projection triple. Source: ILO XI Lemma 1.5
(blueprint: def-trf-large-oriented-site-data). -/
noncomputable def largeToFirst (Z : largeTriples F G) : Z ⟶ (largeFirst F G).obj Z.left.1 where
  left := (𝟙 _, terminal.from _)
  right := terminal.from _
  w := Prod.ext
    ((terminalIsTerminal.isTerminalObj F _).hom_ext _ _)
    ((terminalIsTerminal.isTerminalObj G _).hom_ext _ _)

/-- Structural arrow to the second projection triple. Source: ILO XI Lemma 1.5
(blueprint: def-trf-large-oriented-site-data). -/
noncomputable def largeToSecond (Z : largeTriples F G) : Z ⟶ (largeSecond F G).obj Z.left.2 where
  left := (terminal.from _, 𝟙 _)
  right := terminal.from _
  w := Prod.ext
    ((terminalIsTerminal.isTerminalObj F _).hom_ext _ _)
    ((terminalIsTerminal.isTerminalObj G _).hom_ext _ _)

/-- The middle triple defining the orientation. Source: ILO XI §1.3
(blueprint: def-trf-large-oriented-site-data). -/
def largeMiddle (V : D) : largeTriples F G := ⟨(F.obj V, G.obj V), V, (𝟙 _, 𝟙 _)⟩

/-- The defining pullback formula, with its actual structural maps; it is required for
all compatible lifts, hence in particular for the universal lift.
Source: ILO XI §1.6, formula (1.a) (blueprint: def-trf-large-oriented-site-data). -/
def LargeHasLiftFormula (J₁ : Pretopology C₁) (J₂ : Pretopology C₂) (K : Pretopology D)
    (f : GeometricMorphism (Sheaf J₁.toGrothendieck (Type (max v w)))
      (Sheaf K.toGrothendieck (Type (max v w))))
    (g : GeometricMorphism (Sheaf J₂.toGrothendieck (Type (max v w)))
      (Sheaf K.toGrothendieck (Type (max v w))))
    (ηF : largeAssociated K.toGrothendieck ⋙ f.inverse ≅
      F ⋙ largeAssociated J₁.toGrothendieck)
    (ηG : largeAssociated K.toGrothendieck ⋙ g.inverse ≅
      G ⋙ largeAssociated J₂.toGrothendieck)
    (p₁ : GeometricMorphism (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w)))
      (Sheaf J₁.toGrothendieck (Type (max v w))))
    (p₂ : GeometricMorphism (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w)))
      (Sheaf J₂.toGrothendieck (Type (max v w))))
    (π₁ : largeAssociated J₁.toGrothendieck ⋙ p₁.inverse ≅
      largeFirst F G ⋙ largeAssociated (largeTopology J₁ J₂ F G))
    (π₂ : largeAssociated J₂.toGrothendieck ⋙ p₂.inverse ≅
      largeSecond F G ⋙ largeAssociated (largeTopology J₁ J₂ F G))
    (τ : (p₂.comp g).direct ⟶ (p₁.comp f).direct) : Prop :=
  ∀ (E : Type e) [Category.{ve} E], IsGrothendieckTopos.{max v w} E →
    ∀ (a : GeometricMorphism E (Sheaf J₁.toGrothendieck (Type (max v w))))
      (b : GeometricMorphism E (Sheaf J₂.toGrothendieck (Type (max v w))))
      (t : (b.comp g).direct ⟶ (a.comp f).direct)
      (h : GeometricMorphism E (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w))))
      (α : (h.comp p₁).direct ≅ a.direct) (β : (h.comp p₂).direct ≅ b.direct),
      paste f g p₁ p₂ τ h a b α β = t → ∀ Z : largeTriples F G,
      IsPullback
        (h.inverse.map ((largeAssociated (largeTopology J₁ J₂ F G)).map (largeToFirst F G Z) ≫
            π₁.inv.app Z.left.1) ≫ (GeometricMorphism.inverseIso α).inv.app
              ((largeAssociated J₁.toGrothendieck).obj Z.left.1))
        (h.inverse.map ((largeAssociated (largeTopology J₁ J₂ F G)).map (largeToSecond F G Z) ≫
            π₂.inv.app Z.left.2) ≫ (GeometricMorphism.inverseIso β).inv.app
              ((largeAssociated J₂.toGrothendieck).obj Z.left.2))
        (a.inverse.map ((largeAssociated J₁.toGrothendieck).map Z.hom.1 ≫ ηF.inv.app Z.right) ≫
          (GeometricMorphism.inverseMate t).app ((largeAssociated K.toGrothendieck).obj Z.right))
        (b.inverse.map ((largeAssociated J₂.toGrothendieck).map Z.hom.2 ≫ ηG.inv.app Z.right))
```

The original module publicly imports OrientedProductLargeSiteData; its public import of
OrientedProductUniversal remains available through that module. LargeOrientationFormula is
the original final conjunct written as a predicate, with no new condition or alteration.
All original declaration names, visibility, types and computational bodies are preserved.
The equality of the old and new definition blocks (apart from blueprint tags) was checked
textually. No target interpretation changes, so this move creates no target-statement repair.

## Users

The downstream.py largeAssociated query lists the complete 41-module import closure below,
plus the item itself. Searches for every other moved name were also checked in lean/.
The direct external users are OrientedAffineNeighbourhoodLimit, OrientedConstructibleSheaf,
and QcqsOrientedTriplePresentation. They continue importing the original module.
No consumer edits are required; their original files are compiled against the moved interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteTypeTorsionUniversalStar | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberStrictLocalTorsionBound | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.CategoryTheory.Sites.LocalOrientedProjectionExact | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.CategoryTheory.Sites.OrientedAffineSliceSite | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.CategoryTheory.Sites.OrientedProductLargeSites | P8 | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.CategoryTheory.Sites.OrientedProductSliceLocalization | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.CoherentSetCriterion | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.GoodOrientedNearbyKunneth | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.NearbyClosedImage | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.NearbyCyclesDimensionBound | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.NearbyFiniteBaseDescent | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.NearbyGeometricSlice | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.NearbySpecializationSlice | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.OrientedAffineNeighbourhoodLimit | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.OrientedClosedBaseExtension | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.OrientedClosedBaseRestriction | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.OrientedConstructibleCoherent | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.OrientedConstructibleSetSheaf | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.OrientedConstructibleSheaf | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.OrientedConstructibleSheafVanishing | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.OrientedConstructibleSubquotients | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.OrientedMaximalPointFiniteness | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.OrientedNearbyStrictLocalDescription | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.OrientedProductPointsConservative | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.OrientedProperFibreExchange | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.OrientedProperImageConstructibility | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.OrientedSourceLocalization | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.OrientedTripleLimitDescent | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.PsiConstructibilityDescent | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.QcqsOrientedTriplePresentation | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.StratifiedOrientedCover | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.TraceFormula.FiniteCoverTubeComparison | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.TraceFormula.GabberNearbyCycleDimensionBound | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.TraceFormula.OrientedDerivedCohomologyContinuity | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.TraceFormula.OrientedPointCohomology | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.TraceFormula.OrientedPointNormalizedStratum | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.TraceFormula.ProperBaseChangeCoherentConservative | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | Same declarations, signatures, bodies and public visibility; no adaptation. |

## Status

landed 20261024T015523-L-2412674 2026-10-24 (merge of deliver/P8/Sheaf.CategoryTheory.Sites.OrientedProductLargeSites)
