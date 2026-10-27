# AlgebraicGeometry.valuation_limit_qcoh_section_descent

## Reason

The proof adds `open MonoidalCategory` to use tensor and whiskering notation in
private helpers. Preflight classifies this additional scope command as a change
requiring a record. The existing public theorem signature and public imports are
unchanged. The two transparency options were already present. The new heartbeat
option is local to the theorem. No public definition or instance changes.
The proof docstring and DAG proof now describe the actual degree-zero argument.

## Old

Scope commands:

```lean
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
```

Public signature (verbatim):

```lean
theorem valuation_limit_qcoh_section_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (s : Cone D) (hs : IsLimit s)
    [∀ i : I, CompactSpace (D.obj (op i))]
    [∀ i : I, QuasiSeparatedSpace (D.obj (op i))]
    (haff : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f.op))
    (i₀ : I) (F : (D.obj (op i₀)).Modules) [F.IsQuasicoherent]
    (g : ∀ j : {j : I // i₀ ≤ j}, D.obj (op j.val) ⟶ D.obj (op i₀))
    (hg : ∀ j, g j = D.map (homOfLE j.property).op)
    (r : ∀ {j k : {j : I // i₀ ≤ j}} (f : j ⟶ k),
      (tensorPullback (g j)).obj F ⟶
        (pushforward (D.map (homOfLE (x := j.val) (y := k.val) (leOfHom f)).op)).obj
          ((tensorPullback (g k)).obj F))
    (hr : ∀ {j k : {j : I // i₀ ≤ j}} (f : j ⟶ k),
      (Classical.choose (exists_tensorPullbackAdjunction (g j))).unit.app F ≫
        (pushforward (g j)).map (r f) ≫
        (pushforwardComp
          (D.map (homOfLE (x := j.val) (y := k.val) (leOfHom f)).op) (g j)).hom.app
          ((tensorPullback (g k)).obj F) ≫
        (pushforwardCongr (f := D.map (homOfLE (x := j.val) (y := k.val)
          (leOfHom f)).op ≫ g j) (g := g k)
          (by rw [hg j, hg k, ← D.map_comp]; rfl)).hom.app
          ((tensorPullback (g k)).obj F) =
      (Classical.choose (exists_tensorPullbackAdjunction (g k))).unit.app F)
    (t : ∀ j : {j : I // i₀ ≤ j}, (tensorPullback (g j)).obj F ⟶
      (pushforward (s.π.app (op j.val))).obj
        ((tensorPullback (s.π.app (op i₀))).obj F))
    (ht : ∀ j,
      (Classical.choose (exists_tensorPullbackAdjunction (g j))).unit.app F ≫
        (pushforward (g j)).map (t j) ≫
        (pushforwardComp (s.π.app (op j.val)) (g j)).hom.app
          ((tensorPullback (s.π.app (op i₀))).obj F) ≫
        (pushforwardCongr (f := s.π.app (op j.val) ≫ g j)
          (g := s.π.app (op i₀))
          (by rw [hg j]; exact s.w (homOfLE j.property).op)).hom.app
          ((tensorPullback (s.π.app (op i₀))).obj F) =
      (Classical.choose (exists_tensorPullbackAdjunction (s.π.app (op i₀)))).unit.app F)
    (M : {j : I // i₀ ≤ j} ⥤ AddCommGrpCat.{u})
    (e : ∀ j : {j : I // i₀ ≤ j}, M.obj j ≅
      AddCommGrpCat.of (Γ((tensorPullback (g j)).obj F, ⊤)))
    (hM : ∀ {j k : {j : I // i₀ ≤ j}} (f : j ⟶ k) (x : M.obj j),
      (e k).hom (M.map f x) =
        ((tensorPullback (g k)).obj F).presheaf.map (eqToHom (by simp)).op
          ((r f).app ⊤ ((e j).hom x)))
    (q : colimit M ⟶ AddCommGrpCat.of
      (Γ((tensorPullback (s.π.app (op i₀))).obj F, ⊤)))
    (hq : ∀ (j : {j : I // i₀ ≤ j}) (x : M.obj j), q (colimit.ι M j x) =
      ((tensorPullback (s.π.app (op i₀))).obj F).presheaf.map (eqToHom (by simp)).op
        ((t j).app ⊤ ((e j).hom x))) :
    IsIso q ∧
      ∀ (j : {j : I // i₀ ≤ j}) (x : M.obj j), q (colimit.ι M j x) = 0 →
        ∃ k : {j : I // i₀ ≤ j}, ∃ (f : j ⟶ k), M.map f x = 0
```

## New

Scope commands:

```lean
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open MonoidalCategory
```

The public signature is identical to the old signature above, byte for byte.
The namespace opening resolves notation locally; it introduces no declaration,
notation, attribute or instance. Proof helpers have private visibility, and all
new proof imports are non-public. Every existing consumer can therefore retain
its original statement and proof without adaptation. Target meanings do not change.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ValuationLimitQcohSectionDescent
--uses valuation_limit_qcoh_section_descent` reported zero downstream modules
and only the defining module as a declaration-name match. There are no consumer
modules to adapt. Pending DAG users remain attached to the unchanged statement.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ValuationLimitQcohSectionDescent | U4 | Proof completed; signature unchanged. |

## Status

landed 20261024T191354-L-318816 2026-10-24 (merge of deliver/U4/Sheaf.AlgebraicGeometry.ValuationLimitQcohSectionDescent)
