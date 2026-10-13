# AlgebraicGeometry.torsionControlled_completion_hom_lift_completion

## Reason

Repair of reviewer X-18d42, head 18d421c33, E2/E7 point 4. The universal
arbitrary-lift theorem is false. At X=Spec(k), J=0, H=F=F'=O_X,
a=a'=g=0 and θ=identity, all hypotheses hold but completion(g)≠θ.
Its original raw-lift dependency was also false without a prescribed θ (take a=id,
a'=0 and J=0). The current repository Raw declaration includes θ and hθ; this delivery does not
need that corrected raw-lift declaration. Retire the arbitrary-lift declaration and the raw-lift route.

## Old

```lean
theorem torsionControlled_completion_hom_lift_completion
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H F F' : CoherentModules X) (a : F ⟶ H) (a' : F' ⟶ H)
    (ha : (∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a.hom))))
    (ha' : (∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a'.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a'.hom))))
    (θ : (completion X J).obj F ⟶ (completion X J).obj F')
    (hθ : θ ≫ (completion X J).map a' = (completion X J).map a)
    (g : F ⟶ F') (hg : g ≫ a' = a) :
    (completion X J).map g = θ
```

## New

The finite graph is the kernel of
p₂≫q′−p₁≫q≫θ_n on the actual pullback of a and a'. Its first projection
is epi by a new surjectivity lemma, and mono by a proved categorical argument
at an Artin--Rees separating depth. The constructed g is inverse(first)
followed by second. Both equations are proved for this construction; no arbitrary
existential witness is selected. Inversion depends only on a theorem determining
a unique inverse, as permitted by the data-construction rule.

```lean
theorem torsionControlledGraphFst_mono
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    {H F F' : CoherentModules X} (a : F ⟶ H) (a' : F' ⟶ H)
    (θ : (completion X J).obj F ⟶ (completion X J).obj F') (n : ℕ)
    (hsep : Mono (kernel.ι a'.hom ≫ formalModuleQuotientπ J (n + 1) F'.obj)) :
    Mono (torsionControlledGraphFst J a a' θ n)

theorem torsionControlledGraphFst_isIso
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    {H F F' : CoherentModules X} (a : F ⟶ H) (a' : F' ⟶ H)
    (ha' : ∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a'.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a'.hom)))
    (θ : (completion X J).obj F ⟶ (completion X J).obj F')
    (hθ : θ ≫ (completion X J).map a' = (completion X J).map a)
    (n : ℕ) (hsep : Mono (kernel.ι a'.hom ≫ formalModuleQuotientπ J (n + 1) F'.obj)) :
    IsIso (torsionControlledGraphFst J a a' θ n)

noncomputable def torsionControlledCompletionHomLift
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    {H F F' : CoherentModules X} (a : F ⟶ H) (a' : F' ⟶ H)
    (ha' : ∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a'.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a'.hom)))
    (θ : (completion X J).obj F ⟶ (completion X J).obj F')
    (hθ : θ ≫ (completion X J).map a' = (completion X J).map a)
    (n : ℕ) (hsep : Mono (kernel.ι a'.hom ≫ formalModuleQuotientπ J (n + 1) F'.obj)) :
    F ⟶ F' :=
  let := torsionControlledGraphFst_isIso J a a' ha' θ hθ n hsep
  ObjectProperty.homMk
    (inv (torsionControlledGraphFst J a a' θ n) ≫ torsionControlledGraphSnd J a a' θ n)

theorem torsionControlled_completion_hom_lift_constructed
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    {H F F' : CoherentModules X} (a : F ⟶ H) (a' : F' ⟶ H)
    (ha' : ∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a'.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a'.hom)))
    (θ : (completion X J).obj F ⟶ (completion X J).obj F')
    (hθ : θ ≫ (completion X J).map a' = (completion X J).map a)
    (n : ℕ) (hsep : Mono (kernel.ι a'.hom ≫ formalModuleQuotientπ J (n + 1) F'.obj)) :
    torsionControlledCompletionHomLift J a a' ha' θ hθ n hsep ≫ a' = a ∧
      (completion X J).map
        (torsionControlledCompletionHomLift J a a' ha' θ hθ n hsep) = θ
```

## Users

`tools/downstream.py ... --uses AlgebraicGeometry.torsionControlled_completion_hom_lift_completion`
found exactly the item and its existence caller. All transitive importers
retain their signatures and meanings: the shared coherent-module and completion
definitions are unchanged, and the existing public import remains available through
the new graph module. The removed theorem was a proof dependency only.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.TorsionControlledCompletionHomLiftCompletion | S1 | Retire false arbitrary-lift theorem; define θ-dependent graph lift and prove both equations. |
| Sheaf.AlgebraicGeometry.TorsionControlledCompletionHomLiftExists | unclaimed | Forced adaptation: unchanged signature, replace raw-lift/cancellation proof with Artin--Rees depth and joint constructed lift. |

The existence module's original fails against the changed dependency with
`Unknown identifier torsionControlled_completion_hom_lift_completion` at line 42:16.
Only its proof import of Raw and the proof body are changed. The replacement import
supplies the separating depth. Destructuring ha keeps its unchanged binder explicitly
referenced for the unused-variable linter; only ha' is needed by the stronger construction.
No target signature, coherent module definition, or completion definition changes.
The direct public import of CoherentFormalModule in the item is replaced by a public
import of TorsionControlledFiniteGraphEpi, which publicly imports CoherentFormalModule.
The new public graph import is required by the constructed map's public body.

## Status

landed 20261013T054236-L-448895 2026-10-13 (merge of deliver/S1/Sheaf.AlgebraicGeometry.TorsionControlledCompletionHomLiftCompletion)
