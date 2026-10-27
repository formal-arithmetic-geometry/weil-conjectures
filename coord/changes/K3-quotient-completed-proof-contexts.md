# QuotientCompleted proof contexts

## Reason

The nine existing theorem proofs require generic private categorical helpers and
an explicit private transport of principal local completeness to `AsSmall.{0}`.
The generic transport uses local notation, section variables and local instance
attributes, all inside a closed section before the public section. The static
stage-3 checker classifies such command changes conservatively as interface
changes and requested this record. There is no change to any existing public
signature, definition body, public import or target meaning.

The original public noncomputable section is replaced by a noncomputable section
containing these private helpers, followed by the public exposed section for all
21 original declarations. The added transparency option only enables proof
elaboration. The local instance attributes and notations end with their section.
No private helper occurs in a public type or public non-theorem body.

## Old

The original section header and elaboration options, verbatim:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
```

All existing declaration signatures and non-theorem bodies are retained verbatim.
The nine theorem bodies were `by sorry`.

## New

The new scoped proof context, verbatim:

```lean
noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section
universe c v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.NativeRestriction
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
set_option hygiene false in
local notation "F" => AsSmall.down.{v, c, 0} (C := C)
set_option hygiene false in
local notation "Jsmall" => (F).inducedTopology J
variable [(F).IsEquivalence]
variable (R : Sheaf J CommRingCat.{max c v})
set_option hygiene false in
local notation "S" => restrictedCommRing.{max c v, c, max c v, v, v} (K := Jsmall) F R
set_option hygiene false in
local notation "Rg" => NativeRings.{max c v, c, v} R
set_option hygiene false in
local notation "Rs" => NativeRings.{max c v, max c v, max c v} S
variable
  [HasSheafify J AddCommGrpCat.{max c v}] [J.WEqualsLocallyBijective AddCommGrpCat.{max c v}]
  [HasSheafify Jsmall AddCommGrpCat.{max c v}] [(Jsmall).WEqualsLocallyBijective
    AddCommGrpCat.{max c v}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max c v}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v}]
  [∀ U : AsSmall.{0} C, HasSheafify ((Jsmall).over U) AddCommGrpCat.{max c v}]
  [∀ U : AsSmall.{0} C, ((Jsmall).over U).WEqualsLocallyBijective AddCommGrpCat.{max c v}]
  [∀ U : C, HasSheafify (J.over U) CommRingCat.{max c v}]
  [∀ U : AsSmall.{0} C, HasSheafify ((Jsmall).over U) CommRingCat.{max c v}]
  [HasDerivedCategory.{w} (NativeModules.{max c v, c, v} R)]
  [HasDerivedCategory.{w} (NativeModules.{max c v, max c v, max c v} S)]
  [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{max c v} ((Rg).over U))]
  [∀ U : AsSmall.{0} C, HasDerivedCategory.{w} (SheafOfModules.{max c v} ((Rs).over U))]
attribute [local instance] sliceDense globalModulesEquivalence sliceModulesEquivalence

private theorem reflectLocalTestZero {A B : Type*} [Category* A] [Category* B]
    [HasZeroMorphisms A] [HasZeroMorphisms B] (G : A ⥤ B)
    [G.Faithful] [G.PreservesZeroMorphisms] (M : A) (h : IsZero (G.obj M)) :
    IsZero M := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  exact G.zero_of_map_zero _ (by simpa using h)

private theorem smallModelCompleteZero
    (a : (R.obj ⋙ forget CommRingCat).sections)
    (N : DerivedCategory (NativeModules.{max c v, c, v} R)) :
    letI := globalModulesEquivalence.{max c v, c, max c v, v, v}
      (K := Jsmall) F R
    principalLocallyComplete.{c, v, v, w} R a N ↔
      principalLocallyComplete.{max c v, max c v, v, w} S
        (restrictedSection.{max c v, c, max c v, v, v} (K := Jsmall) F R a)
        ((restrictModules.{max c v, c, max c v, v, v} (K := Jsmall) F
          R).mapDerivedCategory.obj N) := by
  let := globalModulesEquivalence.{max c v, c, max c v, v, v}
    (K := Jsmall) F R
  constructor
  · intro h U s hs
    let s₀ := principalSliceSection.{c, v, v} R ((F).obj U)
      (s.val (op (Over.mk (𝟙 U))))
    have he : s = restrictedSection.{max c v, max c v, max c v, v, v} (K := (Jsmall).over U)
        (Over.post F) (R.over ((F).obj U)) s₀ := by
      rw [principalSliceSection_eta.{max c v, max c v, v} S U s]
      rfl
    rw [he] at hs ⊢
    have hz := h ((F).obj U) s₀
      ((localDivisibilityRestriction.{max c v, c, max c v, v, v} (K := Jsmall) F R a U s₀).mpr
        hs)
    obtain ⟨e⟩ := localTestRestriction.{max c v, c, max c v, v, v, w} (K := Jsmall) F R U N s₀
    exact (Functor.map_isZero _ hz).of_iso e.symm
  · intro h U s hs
    let V := AsSmall.up.{v, c, 0}.obj U
    have hs' := (localDivisibilityRestriction.{max c v, c, max c v, v, v} (K := Jsmall) F R a
      V s).mp hs
    have hz := h V _ hs'
    obtain ⟨e⟩ := localTestRestriction.{max c v, c, max c v, v, v, w} (K := Jsmall) F R V N s
    exact reflectLocalTestZero _ _ (hz.of_iso e)

end CategoryTheory.NativeRestriction
end

@[expose] public section
```

Every helper is private and completely proved. The original public declarations
follow with unchanged signatures. The nine theorem bodies now contain complete
proofs from the existing dependency declarations. All original public imports
are retained; only unused private proof imports are removed.

## Users

`python3 tools/downstream.py Sheaf.Paper.QuotientCompletedCompositorUnit --names`
reported zero current Lean importers. This does not authorize withdrawal: the
node remains needed by its unfinished DAG parents. No consumer is adapted.
The public signature comparison checks all 21 existing declarations, unchanged.
The final single-file compile completed cleanly in 26.4 seconds.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.QuotientCompletedCompositorUnit | K3 | Nine holes closed; private proof contexts only; existing public signatures, imports and definition bodies unchanged. |

## Status

landed 20261023T231703-L-3633615 2026-10-23 (merge of deliver/K3/Sheaf.Paper.QuotientCompletedCompositorUnit)
