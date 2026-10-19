## Worker report

The module `Sheaf.TraceFormula.EtaleFlatteningDescent` states the Stacks Project Tag 0814 etale-local flattening descent lemma. It introduces schemes `S`, `X`, a morphism `f`, a quasi-coherent module `F`, a quasi-compact open `U`, a finite index type `ι`, the diagrams `Xi i ⟶ Si i ⟶ S` and `Xi i ⟶ X`, and the commuting equations `g i ≫ e i = j i ≫ f`. The hypotheses render quasi-compactness and etaleness of each `e i`, etaleness of each `j i`, and joint surjectivity of the two finite families by pointwise existential cover clauses. For every index, `B i : IsAdmissible (Si i) ((e i) ⁻¹ᵁ U)` is the local admissible blowup. Its local flatness clause uses the strict transform of the canonical pullback `(Scheme.Modules.pullback (j i)).obj F`, over the canonical pullback projection `pullback.snd (g i) (B i).I.blowupMap`. The conclusion is an admissible `B' : IsAdmissible S U` and flatness of the strict transform of `F` over `pullback.snd f B'.I.blowupMap`.

The recorded dependency declarations used are: `AlgebraicGeometry.Scheme` / `Scheme.Hom` from Mathlib (`Mathlib.AlgebraicGeometry.Scheme`), `AlgebraicGeometry.RingedSpace.IsCoherent` from `WeilConjectures.AlgebraicGeometry.Coherent` for the quasi-coherent module context, `AlgebraicGeometry.Scheme.Modules.IsFlatOver` from `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`, `AlgebraicGeometry.IsAdmissible` from `WeilConjectures.Blowup.AdmissibleBlowup`, `AlgebraicGeometry.Scheme.Modules.moduleStrictTransform` from `Sheaf.AlgebraicGeometry.ModuleStrictTransform`, `AlgebraicGeometry.Etale` from `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `CategoryTheory.Limits.pullback` from `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, and `AlgebraicGeometry.Scheme.Modules.pullback` from `Mathlib.AlgebraicGeometry.Modules.Sheaf`. The module also imports the project tensor-pullback interface because it is the project’s recorded module-pullback dependency; the statement uses Mathlib’s canonical pullback functor, which is the same pullback notion characterized by the recorded interface.

Edge cases checked: empty `S` and `X` make the covering clauses vacuous and the conclusion is still meaningful; an empty finite index type is therefore allowed only when the schemes are empty. A singleton cover reduces to the ordinary local flattening statement. Taking `U = ⊤` makes admissibility the unit-centre case. The strict-transform structure map is the pullback projection `pullback.snd`; the blowup map is already the second argument used to form that pullback.

Searches made: `msearch.py leanfinder` for “Local admissible blowups flattening a quasi coherent module on finite etale covers descend to one blowup of the base” and “etale descent of Raynaud Gruson flatification” (hits only generic flatness/etale declarations; no match); `msearch.py leansearch` for “Local admissible blowups flattening a quasi coherent module on finite etale covers descend to one blowup of the base” (generic flatness/descent hits; no match); `msearch.py loogle` for `strictTransform` (0 hits); grep over Mathlib and `WeilConjectures` for `flatten.*etale|etale.*flatten` (no existing declaration). Searches over `lean/Sheaf` found the existing strict-transform module and no declaration of this theorem.

The theorem proof is intentionally `sorry` at stage 2. No statement correction or `STATEMENT-DISPUTED` applies.


## Repair notes

The returned review identified that both flatness clauses had incorrectly composed the pullback projection with the blow-up map. They now use exactly `pullback.snd (g i) (B i).I.blowupMap` in the local hypothesis and `pullback.snd f B'.I.blowupMap` in the conclusion, matching Tag 0814 and the node statement. The unused `Mathlib.AlgebraicGeometry.Modules.Tilde` import was removed. The theorem docstring now records all ten proof steps from the node proof, including affine refinement, base-change stability, product-centre domination, relative flatness descent, gluing, composition, and the empty/unit edge cases.

The corrected Lean signature is:

```lean
theorem exists_admissibleBlowup_moduleStrictTransform_isFlatOver_of_finite_etale_cover
    {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent]
    (U : S.Opens) (hU : IsCompact (U : Set S))
    {ι : Type v} [Finite ι]
    (Si : ι → Scheme.{u}) (Xi : ι → Scheme.{u})
    (g : ∀ i, Xi i ⟶ Si i) (j : ∀ i, Xi i ⟶ X) (e : ∀ i, Si i ⟶ S)
    (hcomm : ∀ i, g i ≫ e i = j i ≫ f)
    (he_qc : ∀ i, QuasiCompact (e i)) (he_etale : ∀ i, Etale (e i))
    (hj_etale : ∀ i, Etale (j i))
    (he_cover : ∀ s : S, ∃ i : ι, ∃ x : Si i, e i x = s)
    (hj_cover : ∀ x : X, ∃ i : ι, ∃ y : Xi i, j i y = x)
    (B : ∀ i, IsAdmissible (Si i) ((e i) ⁻¹ᵁ U))
    (hB_flat : ∀ i,
      letI : (B i).I.toModules.IsFiniteType :=
        (B i).I.isFiniteType_toModules_sheaf (B i).finiteType
      Scheme.Modules.IsFlatOver
        (@Scheme.Modules.moduleStrictTransform (Xi i) (Si i) (g i) (B i).I
          inferInstance ((Scheme.Modules.pullback (j i)).obj F) inferInstance)
        (pullback.snd (g i) (B i).I.blowupMap)) :
    ∃ B' : IsAdmissible S U,
      letI : B'.I.toModules.IsFiniteType :=
        B'.I.isFiniteType_toModules_sheaf B'.finiteType
      Scheme.Modules.IsFlatOver
        (@Scheme.Modules.moduleStrictTransform X S f B'.I inferInstance F inferInstance)
        (pullback.snd f B'.I.blowupMap)
```

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
