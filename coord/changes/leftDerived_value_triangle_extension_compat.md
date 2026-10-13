# leftDerived_value_triangle_extension_compat

## Reason

The old universal implication is false. With F the identity, S the isomorphisms,
and canonical inverse-denominator cone legs, the split triangle X → 0 → X[1]
with third map identity has another distinguished completion with third map
negative identity. The required equation at identity denominators distinguishes
these maps over ℚ. Stacks 05SC constructs a compatible completion, rather than
asserting compatibility of every distinguished completion.

The corrected theorem remains an open obligation. It is equivalent, up to
conjunct order, to the existing value-triangle conclusion, so this delivery
claims no proof progress or new decomposition. No target or definition changes.

## Old

```lean
theorem leftDerived_value_triangle_extension_compat
    {C : Type u} {D : Type uD} [Category.{v} C] [Category.{vD} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [CategoryTheory.IsTriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (S : MorphismProperty C)
    (hS : S.IsSaturatedTriangulatedMultiplicativeSystem)
    (T : Triangle C) (hT : T ∈ distTriang C)
    (LX LY LZ : D)
    (hX : F.IsTriangulatedLeftDerivedValue S hS T.obj₁ LX)
    (hY : F.IsTriangulatedLeftDerivedValue S hS T.obj₂ LY)
    (hZ : F.IsTriangulatedLeftDerivedValue S hS T.obj₃ LZ)
    (uX : (Functor.const (S.Over ⊤ T.obj₁)).obj LX ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₁ ⋙ Over.forget T.obj₁ ⋙ F)
    (uY : (Functor.const (S.Over ⊤ T.obj₂)).obj LY ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₂ ⋙ Over.forget T.obj₂ ⋙ F)
    (uZ : (Functor.const (S.Over ⊤ T.obj₃)).obj LZ ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₃ ⋙ Over.forget T.obj₃ ⋙ F)
    (huX : ∃ s₀ : S.Over ⊤ T.obj₁, ∃ r : F.obj s₀.left ⟶ LX,
      uX.app s₀ ≫ r = 𝟙 LX ∧
        ∀ s : S.Over ⊤ T.obj₁, ∃ t : S.Over ⊤ T.obj₁,
          ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
            F.map b.left = F.map a.left ≫ r ≫ uX.app s)
    (huY : ∃ s₀ : S.Over ⊤ T.obj₂, ∃ r : F.obj s₀.left ⟶ LY,
      uY.app s₀ ≫ r = 𝟙 LY ∧
        ∀ s : S.Over ⊤ T.obj₂, ∃ t : S.Over ⊤ T.obj₂,
          ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
            F.map b.left = F.map a.left ≫ r ≫ uY.app s)
    (huZ : ∃ s₀ : S.Over ⊤ T.obj₃, ∃ r : F.obj s₀.left ⟶ LZ,
      uZ.app s₀ ≫ r = 𝟙 LZ ∧
        ∀ s : S.Over ⊤ T.obj₃, ∃ t : S.Over ⊤ T.obj₃,
          ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
            F.map b.left = F.map a.left ≫ r ≫ uZ.app s)
    (lf : LX ⟶ LY) (lg : LY ⟶ LZ)
    (hf : ∀ (s : S.Over ⊤ T.obj₁) (s' : S.Over ⊤ T.obj₂)
        (f' : s.left ⟶ s'.left),
        s.hom ≫ T.mor₁ = f' ≫ s'.hom →
          uX.app s ≫ F.map f' = lf ≫ uY.app s')
    (hg : ∀ (s : S.Over ⊤ T.obj₂) (s' : S.Over ⊤ T.obj₃)
        (g' : s.left ⟶ s'.left),
        s.hom ≫ T.mor₂ = g' ≫ s'.hom →
          uY.app s ≫ F.map g' = lg ≫ uZ.app s')
    (lh : LZ ⟶ (shiftFunctor D (1 : ℤ)).obj LX)
    (hdist : Triangle.mk lf lg lh ∈ distTriang D) :
      ∀ (s : S.Over ⊤ T.obj₃) (s' : S.Over ⊤ T.obj₁)
        (h' : s.left ⟶ (shiftFunctor C (1 : ℤ)).obj s'.left),
        s.hom ≫ T.mor₃ = h' ≫ (shiftFunctor C (1 : ℤ)).map s'.hom →
          uZ.app s ≫ F.map h' =
            lh ≫ (shiftFunctor D (1 : ℤ)).map (uX.app s') ≫
              (F.commShiftIso (1 : ℤ)).inv.app s'.left
```

## New

```lean
theorem leftDerived_value_triangle_extension_compat
    {C : Type u} {D : Type uD} [Category.{v} C] [Category.{vD} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [CategoryTheory.IsTriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (S : MorphismProperty C)
    (hS : S.IsSaturatedTriangulatedMultiplicativeSystem)
    (T : Triangle C) (hT : T ∈ distTriang C)
    (LX LY LZ : D)
    (hX : F.IsTriangulatedLeftDerivedValue S hS T.obj₁ LX)
    (hY : F.IsTriangulatedLeftDerivedValue S hS T.obj₂ LY)
    (hZ : F.IsTriangulatedLeftDerivedValue S hS T.obj₃ LZ)
    (uX : (Functor.const (S.Over ⊤ T.obj₁)).obj LX ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₁ ⋙ Over.forget T.obj₁ ⋙ F)
    (uY : (Functor.const (S.Over ⊤ T.obj₂)).obj LY ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₂ ⋙ Over.forget T.obj₂ ⋙ F)
    (uZ : (Functor.const (S.Over ⊤ T.obj₃)).obj LZ ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₃ ⋙ Over.forget T.obj₃ ⋙ F)
    (huX : ∃ s₀ : S.Over ⊤ T.obj₁, ∃ r : F.obj s₀.left ⟶ LX,
      uX.app s₀ ≫ r = 𝟙 LX ∧
        ∀ s : S.Over ⊤ T.obj₁, ∃ t : S.Over ⊤ T.obj₁,
          ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
            F.map b.left = F.map a.left ≫ r ≫ uX.app s)
    (huY : ∃ s₀ : S.Over ⊤ T.obj₂, ∃ r : F.obj s₀.left ⟶ LY,
      uY.app s₀ ≫ r = 𝟙 LY ∧
        ∀ s : S.Over ⊤ T.obj₂, ∃ t : S.Over ⊤ T.obj₂,
          ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
            F.map b.left = F.map a.left ≫ r ≫ uY.app s)
    (huZ : ∃ s₀ : S.Over ⊤ T.obj₃, ∃ r : F.obj s₀.left ⟶ LZ,
      uZ.app s₀ ≫ r = 𝟙 LZ ∧
        ∀ s : S.Over ⊤ T.obj₃, ∃ t : S.Over ⊤ T.obj₃,
          ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
            F.map b.left = F.map a.left ≫ r ≫ uZ.app s)
    (lf : LX ⟶ LY) (lg : LY ⟶ LZ)
    (hf : ∀ (s : S.Over ⊤ T.obj₁) (s' : S.Over ⊤ T.obj₂)
        (f' : s.left ⟶ s'.left),
        s.hom ≫ T.mor₁ = f' ≫ s'.hom →
          uX.app s ≫ F.map f' = lf ≫ uY.app s')
    (hg : ∀ (s : S.Over ⊤ T.obj₂) (s' : S.Over ⊤ T.obj₃)
        (g' : s.left ⟶ s'.left),
        s.hom ≫ T.mor₂ = g' ≫ s'.hom →
          uY.app s ≫ F.map g' = lg ≫ uZ.app s')
    : ∃ lh : LZ ⟶ (shiftFunctor D (1 : ℤ)).obj LX,
        Triangle.mk lf lg lh ∈ distTriang D ∧
        (∀ (s : S.Over ⊤ T.obj₃) (s' : S.Over ⊤ T.obj₁)
          (h' : s.left ⟶ (shiftFunctor C (1 : ℤ)).obj s'.left),
          s.hom ≫ T.mor₃ = h' ≫ (shiftFunctor C (1 : ℤ)).map s'.hom →
            uZ.app s ≫ F.map h' =
              lh ≫ (shiftFunctor D (1 : ℤ)).map (uX.app s') ≫
                (F.commShiftIso (1 : ℤ)).inv.app s'.left)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.DerivedFunctorValueTriangle | unclaimed | Unchanged signature; replace the invalid arbitrary-completion call by destructuring the compatible existential witness and reordering conjuncts. Remove imports used only by the superseded two-call proof. |

The downstream source scan finds this as the only caller. All other downstream
modules use the unchanged value-triangle theorem, so their statements and
proof calls retain the same types. DerivedFunctorValueTriangleCompletion neither
imports nor calls the compatibility theorem; it is unchanged and asserts only
distinguishedness. It cannot establish the new compatibility conclusion.

## Status

landed 20261013T024036-L-3335135 2026-10-13 (merge of deliver/J3/Sheaf.CategoryTheory.DerivedFunctorValueTriangleCompatibility)
