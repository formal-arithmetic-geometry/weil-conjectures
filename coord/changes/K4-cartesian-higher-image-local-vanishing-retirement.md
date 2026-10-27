# Cartesian higher-image affine-section local vanishing: retire the duplicate

## Reason

Complete `retire:Sheaf.AlgebraicGeometry.CartesianHigherImageAffineSectionLocalVanishing`
from `coord/retire-items.tsv`. The listed DIFFERENT twin now differs only in the
copyright header and an unused limit-proof binder in finite-cover separatedness.
The two local-vanishing theorem signatures and all proof bodies are identical.
The canonical upstream module already supplies all three public declarations.
Keeping both copies would retain competing declarations of the same names.

## Old

Module `Sheaf.AlgebraicGeometry.CartesianHigherImageAffineSectionLocalVanishing`:

```lean
theorem cartesianHigherImage_section_eq_zero_of_finite_cover
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (_hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (U : c.pt.left.Etale) (i j : I) (a : j ⟶ i)
    (x : (cartesianHigherImageStage D c f F q i).obj.obj (Opposite.op U))
    (J : Type u) [Finite J] (V : J → c.pt.left.Etale) (r : ∀ t, V t ⟶ U)
    (hcover : Sieve.ofArrows V r ∈ c.pt.left.smallEtaleTopology U)
    (hzero : ∀ t, (cartesianHigherImageTransition D c f F q a).hom.app
      (Opposite.op (V t))
      ((cartesianHigherImageStage D c f F q i).obj.map (r t).op x) = 0) :
    (cartesianHigherImageTransition D c f F q a).hom.app
      (Opposite.op U) x = 0

theorem cartesianHigherImage_affine_section_local_zero_sieve
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (U : c.pt.left.Etale) [IsAffine U.left] (i : I)
    (x : (cartesianHigherImageStage D c f F q i).obj.obj (Opposite.op U))
    (hx : (cartesianHigherImageLeg D c f F q i).hom.app (Opposite.op U) x = 0) :
    ∃ (j : I) (a : j ⟶ i) (S : Sieve U),
      S ∈ c.pt.left.smallEtaleTopology U ∧
      ∀ (V : c.pt.left.Etale) (r : V ⟶ U), S r →
        (cartesianHigherImageTransition D c f F q a).hom.app
          (Opposite.op V) ((cartesianHigherImageStage D c f F q i).obj.map r.op x) = 0

theorem exists_cartesianHigherImage_affine_section_local_zero
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (U : c.pt.left.Etale) [IsAffine U.left] (i : I)
    (x : (cartesianHigherImageStage D c f F q i).obj.obj (Opposite.op U))
    (hx : (cartesianHigherImageLeg D c f F q i).hom.app (Opposite.op U) x = 0) :
    ∃ (j : I) (a : j ⟶ i) (J : Type u) (_ : Fintype J)
      (V : J → c.pt.left.Etale) (r : ∀ t, V t ⟶ U),
      Sieve.ofArrows V r ∈ c.pt.left.smallEtaleTopology U ∧
      ∀ t, (cartesianHigherImageTransition D c f F q a).hom.app
        (Opposite.op (V t))
        ((cartesianHigherImageStage D c f F q i).obj.map (r t).op x) = 0
```

## New

Withdraw the Sheaf module using `deleted.txt`. Preserve the upstream module
`WeilConjectures.AlgebraicGeometry.CartesianHigherImageAffineSectionLocalVanishing`
verbatim, and move the existing node's Lean attachment there (`existing: true`).
Its public signatures are:

```lean
theorem cartesianHigherImage_section_eq_zero_of_finite_cover
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D)
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (U : c.pt.left.Etale) (i j : I) (a : j ⟶ i)
    (x : (cartesianHigherImageStage D c f F q i).obj.obj (Opposite.op U))
    (J : Type u) [Finite J] (V : J → c.pt.left.Etale) (r : ∀ t, V t ⟶ U)
    (hcover : Sieve.ofArrows V r ∈ c.pt.left.smallEtaleTopology U)
    (hzero : ∀ t, (cartesianHigherImageTransition D c f F q a).hom.app
      (Opposite.op (V t))
      ((cartesianHigherImageStage D c f F q i).obj.map (r t).op x) = 0) :
    (cartesianHigherImageTransition D c f F q a).hom.app
      (Opposite.op U) x = 0

theorem cartesianHigherImage_affine_section_local_zero_sieve
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (U : c.pt.left.Etale) [IsAffine U.left] (i : I)
    (x : (cartesianHigherImageStage D c f F q i).obj.obj (Opposite.op U))
    (hx : (cartesianHigherImageLeg D c f F q i).hom.app (Opposite.op U) x = 0) :
    ∃ (j : I) (a : j ⟶ i) (S : Sieve U),
      S ∈ c.pt.left.smallEtaleTopology U ∧
      ∀ (V : c.pt.left.Etale) (r : V ⟶ U), S r →
        (cartesianHigherImageTransition D c f F q a).hom.app
          (Opposite.op V) ((cartesianHigherImageStage D c f F q i).obj.map r.op x) = 0

theorem exists_cartesianHigherImage_affine_section_local_zero
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (U : c.pt.left.Etale) [IsAffine U.left] (i : I)
    (x : (cartesianHigherImageStage D c f F q i).obj.obj (Opposite.op U))
    (hx : (cartesianHigherImageLeg D c f F q i).hom.app (Opposite.op U) x = 0) :
    ∃ (j : I) (a : j ⟶ i) (J : Type u) (_ : Fintype J)
      (V : J → c.pt.left.Etale) (r : ∀ t, V t ⟶ U),
      Sieve.ofArrows V r ∈ c.pt.left.smallEtaleTopology U ∧
      ∀ t, (cartesianHigherImageTransition D c f F q a).hom.app
        (Opposite.op (V t))
        ((cartesianHigherImageStage D c f F q i).obj.map (r t).op x) = 0
```

The finite-cover theorem omits the unused `_hc` hypothesis. The replacement
therefore applies to every old use by omitting that argument. The other two
signatures agree verbatim. No target or definition changes meaning.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CartesianHigherImageAffineSectionLocalVanishing | K4 (assigned retirement) | Withdraw the duplicate; no current Lean importers. |
| WeilConjectures.AlgebraicGeometry.CartesianHigherImageAffineSectionLocalVanishing | unclaimed in shared snapshot | Canonical replacement; all declarations and imports preserved verbatim. |
| WeilConjectures.AlgebraicGeometry.CartesianHigherImageAffineSectionVanishing | unclaimed in shared snapshot | Sole DAG parent; already imports the upstream replacement and applies both local vanishing and finite-cover separatedness with the correct upstream arguments. |

`tools/downstream.py` finds zero downstream modules of the Sheaf twin. A search
of Lean and quarantine imports agrees. The retired listing's old Sheaf parent
is absent; the current parent is the upstream module named above. Checking all
`stmt_deps`, `proof_deps`, and proof-step `uses` finds exactly that one DAG parent.
Its edge stays valid because the same node now attaches to the upstream theorem.
No unit route or mathematical dependency is pruned, and no parent edit is needed.
The local-vanishing node is not removed. All its statement and proof dependencies
remain, including finite raw-class vanishing.

`scratchpad/RetirementCheck.lean` checks each old signature by applying the upstream
replacement, and imports/checks the current parent. It is validation only and is
not a library module in this delivery. Remote compilation passed (8.4 s, exit 0);
the only warning concerns the scratch file having exclusively private declarations.

## Status

landed 20261025T163819-L-857675 2026-10-25 (merge of deliver/K4/Sheaf.AlgebraicGeometry.CartesianHigherImageAffineSectionLocalVanishing)
