# CochainComplex.affine_perfect_hom_colimit

## Reason

Retire the duplicate Sheaf module under the human-approved retirement task in
coord/retire-items.tsv and coord/changes/retire-sheaf-twins-20261020.md.
The upstream public theorem has exactly the same signature (byte-for-byte comparison).
The three extra declarations in the Sheaf file are private, proved helpers:
scalarExtension_isKProjective, Q_map_surjective, and Q_map_eq_iff_homotopy.
The upstream proof uses proved public wrappers from DerivedCategory.ProjectiveHom instead.
No upstream declaration or target statement changes.

## Old

Location: Sheaf.AlgebraicGeometry.AffinePerfectHomColimit.

```lean
theorem affine_perfect_hom_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (i₀ : I)
    [∀ i : I, HasDerivedCategory.{w} (ModuleCat.{u} (F.obj i))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (colimit F : CommRingCat.{u}))]
    (E₀ K₀ : CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ)
    (hE : (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E₀.X n)) ∧
      ∀ n : ℤ, Module.Finite (F.obj i₀) (E₀.X n) ∧
        Module.Projective (F.obj i₀) (E₀.X n))
    (hK : (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K₀.X n)) ∧
      ∀ n : ℤ, Module.Finite (F.obj i₀) (K₀.X n) ∧
        Module.Projective (F.obj i₀) (K₀.X n))
    (H : Set.Ici i₀ ⥤ Type w) [HasColimit H]
    (ident : ∀ i : Set.Ici i₀, H.obj i ≃
      (DerivedCategory.Q.obj
        ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom) (.up ℤ)).obj E₀) ⟶
       DerivedCategory.Q.obj
        ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom) (.up ℤ)).obj K₀)))
    (htransition : ∀ (i j : Set.Ici i₀) (hij : i ≤ j)
      (f : (Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom) (.up ℤ)).obj E₀ ⟶
        (Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom) (.up ℤ)).obj K₀),
      ident j (H.map (homOfLE hij) ((ident i).symm (DerivedCategory.Q.map f))) =
        DerivedCategory.Q.map (scalarExtensionHom
          (F.map (homOfLE i.property)).hom (F.map (homOfLE hij)).hom
          (F.map (homOfLE j.property)).hom
          (congrArg CommRingCat.Hom.hom (F.map_comp
            (homOfLE i.property) (homOfLE hij))) E₀ K₀ f))
    (c : Cocone H)
    (e : c.pt ≃
      (DerivedCategory.Q.obj
        ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (colimit.ι F i₀).hom) (.up ℤ)).obj E₀) ⟶
       DerivedCategory.Q.obj
        ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (colimit.ι F i₀).hom) (.up ℤ)).obj K₀)))
    (hcanonical : ∀ (i : Set.Ici i₀)
      (f : (Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom) (.up ℤ)).obj E₀ ⟶
        (Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom) (.up ℤ)).obj K₀),
      e (c.ι.app i ((ident i).symm (DerivedCategory.Q.map f))) =
        DerivedCategory.Q.map (scalarExtensionHom
          (F.map (homOfLE i.property)).hom (colimit.ι F i.val).hom
          (colimit.ι F i₀).hom
          (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE i.property)).symm)
          E₀ K₀ f)) :
    Function.Bijective (e ∘ colimit.desc H c)
```

## New

The identical signature above lives in
WeilConjectures.AlgebraicGeometry.AffinePerfectHomColimit. The Sheaf copy is withdrawn
through deleted.txt. The DAG node lem-pc-affine-perfect-hom-colimit points to the
upstream declaration; its proof description now names the upstream localization wrappers.

## Users

tools/downstream.py Sheaf.AlgebraicGeometry.AffinePerfectHomColimit
--uses affine_perfect_hom_colimit reports zero downstream modules, and only the
retired file itself mentions the theorem in that import closure. A current search
of all Lean sources also finds no import of the retired Sheaf module.
The retirement inventory's former consumer Sheaf.AlgebraicGeometry.PerfectHomContinuityAffine
is already absent. Its upstream counterpart already imports the upstream theorem.
The DAG node is the only live attachment requiring redirection.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffinePerfectHomColimit | S2 | Withdraw duplicate, zero holes. |
| WeilConjectures.AlgebraicGeometry.PerfectHomContinuityAffine | unmodified | Already uses upstream twin; no adaptation. |

## Status

landed 20261020T132038-L-1406089 2026-10-20 (merge of deliver/S2/Sheaf.AlgebraicGeometry.AffinePerfectHomColimit)
