# AlgebraicGeometry.coherentFormalModule_kernel_quotient_aux

## Reason

The fixed-bound statement is false, as its existing STATEMENT-DISPUTED comment correctly
explains. On Spec Z with I=(2), F_n=Z/2^(n+1), H_n=Z/2, and reduction alpha, c=0 satisfies
image stabilization. Its stabilized kernel S_n=2Z/2^(n+1) has S_0=0 and S_1=Z/2; the prescribed
quotient sequence is not adic. Stacks 087X chooses a bound for both the kernel and image
Artin--Rees calculations. The repaired auxiliary permits enlargement d>=c. The library's
construction statement already existentially chooses its bound and stays identical.

## Old

```lean
theorem coherentFormalModule_kernel_quotient_aux {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) (F H : CoherentFormalModule X I) (α : F ⟶ H) (c : ℕ) (S : ℕᵒᵖ ⥤ X.Modules) (j : S ⟶ F.obj) (hc : ∀ (l m : ℕ) (h : m + c ≤ l), Subobject.mk (Abelian.image.ι (kernel.ι (α.hom.app (op l)) ≫ F.obj.map (homOfLE (Nat.le_trans (Nat.le_add_right m c) h)).op)) = Subobject.mk (Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫ F.obj.map (homOfLE (Nat.le_add_right m c)).op))) (hS : ∀ m : ℕ, ∃ e : S.obj (op m) ≅ Abelian.image (kernel.ι (α.hom.app (op (m + c))) ≫ F.obj.map (homOfLE (Nat.le_add_right m c)).op), e.hom ≫ Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫ F.obj.map (homOfLE (Nat.le_add_right m c)).op) = j.app (op m)) : ∃ (K : CoherentFormalModule X I) (ι : K ⟶ F) (e : ∀ n : ℕ, formalModuleQuotient I (n + 1) (S.obj (op (n + c))) ≅ K.obj.obj (op n)), (∀ n : ℕ, formalModuleQuotientπ I (n + 2) (S.obj (op (n + 1 + c))) ≫ (e (n + 1)).hom ≫ K.obj.map (homOfLE (Nat.le_succ n)).op = S.map (homOfLE (Nat.add_le_add_right (Nat.le_succ n) c)).op ≫ formalModuleQuotientπ I (n + 1) (S.obj (op (n + c))) ≫ (e n).hom) ∧ (∀ n : ℕ, formalModuleQuotientπ I (n + 1) (S.obj (op (n + c))) ≫ (e n).hom ≫ ι.hom.app (op n) = j.app (op (n + c)) ≫ F.obj.map (homOfLE (Nat.le_add_right n c)).op) ∧ (∀ n : ℕ, kernel.ι (ι.hom.app (op (n + c))) ≫ K.obj.map (homOfLE (Nat.le_add_right n c)).op = 0)
```

## New

```lean
theorem coherentFormalModule_kernel_quotient_aux {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) (F H : CoherentFormalModule X I) (α : F ⟶ H) (c : ℕ) (S : ℕᵒᵖ ⥤ X.Modules) (j : S ⟶ F.obj) (hc : ∀ (l m : ℕ) (h : m + c ≤ l), Subobject.mk (Abelian.image.ι (kernel.ι (α.hom.app (op l)) ≫ F.obj.map (homOfLE (Nat.le_trans (Nat.le_add_right m c) h)).op)) = Subobject.mk (Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫ F.obj.map (homOfLE (Nat.le_add_right m c)).op))) (hS : ∀ m : ℕ, ∃ e : S.obj (op m) ≅ Abelian.image (kernel.ι (α.hom.app (op (m + c))) ≫ F.obj.map (homOfLE (Nat.le_add_right m c)).op), e.hom ≫ Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫ F.obj.map (homOfLE (Nat.le_add_right m c)).op) = j.app (op m)) : ∃ d : ℕ, c ≤ d ∧ ∃ (K : CoherentFormalModule X I) (ι : K ⟶ F) (e : ∀ n : ℕ, formalModuleQuotient I (n + 1) (S.obj (op (n + d))) ≅ K.obj.obj (op n)), (∀ n : ℕ, formalModuleQuotientπ I (n + 2) (S.obj (op (n + 1 + d))) ≫ (e (n + 1)).hom ≫ K.obj.map (homOfLE (Nat.le_succ n)).op = S.map (homOfLE (Nat.add_le_add_right (Nat.le_succ n) d)).op ≫ formalModuleQuotientπ I (n + 1) (S.obj (op (n + d))) ≫ (e n).hom) ∧ (∀ n : ℕ, formalModuleQuotientπ I (n + 1) (S.obj (op (n + d))) ≫ (e n).hom ≫ ι.hom.app (op n) = j.app (op (n + d)) ≫ F.obj.map (homOfLE (Nat.le_add_right n d)).op) ∧ (∀ n : ℕ, kernel.ι (ι.hom.app (op (n + d))) ≫ K.obj.map (homOfLE (Nat.le_add_right n d)).op = 0)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelConstruction | unclaimed | Sole external declaration user. Original proof expects K as the first witness; new first witness is d. Its signature and visibility stay identical; the proof transports stabilization and image representatives to d. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelQuotient | V2 | Assigned auxiliary corrected and proved from a strictly smaller quotient-comparison theorem. |

All other downstream modules consume the unchanged construction statement. The new definitions
are explicit functors and cokernel descents; they do not change any existing target-used definition.
No target statement or universe is edited and no target semantic review is reopened by a definition
change. The mathematical route through stabilized images and Artin--Rees remains the same.

The only forced caller edits are the witness pattern after applying the auxiliary, the proofs hd
and hSd needed for the newly selected d, and the final witness assembly. Other caller imports and
its existing docstring are untouched. The original against the changed auxiliary fails at the
witness destructuring; deliver3.py repeats the counterfactual and records the exact compiler error.

## Status

landed 20261013T045611-L-139346 2026-10-13 (merge of deliver/V2/Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelQuotient)
