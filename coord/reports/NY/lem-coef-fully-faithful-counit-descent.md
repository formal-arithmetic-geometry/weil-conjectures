## Worker report

The delivery repairs the owning module `Sheaf.CategoryTheory.FullyFaithfulCounitDescent`
and states `CategoryTheory.fully_faithful_counit_descent`, with its whole proof `sorry`.
The DAG statement, statement dependencies, and proof are unchanged. The existing module
and the current published source were both read. Their Lean statement omitted the two
counit compatibility assumptions that the node explicitly includes. The repair restores
these as `hCounitA` and `hCounitB`; an existing:true binding would retain the defect.
It also replaces the redundant separately supplied inverse and its two equations by
Mathlib's canonical `inv (c' Q_A)`, using exactly the assumed invertibility at `Q_A`.
No new definition or dependency module is needed.

Source checked: the full node, its eight-step diagram chase, and the retained blueprint
`sec-six-functors/sk-prop-sf-biduality-general/lem-coef-finite-dualizing.md`, Proof,
closed-immersion paragraph: the local map equals the global adjoint map because its
transpose is the composite counit. The theorem docstring contains all eight proof steps.
The module uses the public module system and explicitly disables auto-bound implicits.

Every hypothesis and conclusion clause is represented as follows. All compositions in
Lean use `≫`, so the factors are written in application order.

| Node clause | Lean rendering |
| --- | --- |
| Eight categories, each with associative unital composition | `C_A`, `C_B`, `D_A`, `D_B`, `Cp_A`, `Cp_B`, `Dp_A`, `Dp_B`, each with its own explicit object and Hom universes and `Category` instance |
| `F_R`, `I_R`, and their adjunctions | `F_A`, `I_A`, `F_B`, `I_B`, `adj_A : F_A ⊣ I_A`, `adj_B : F_B ⊣ I_B` |
| The counits `e_R` | `adj_A.counit.app` and `adj_B.counit.app` |
| Four comparison functors and two primed left functors | `S_C_A`, `S_C_B`, `S_D_A`, `S_D_B`, `F'p_A`, `F'p_B` |
| Four coefficient functors | `T_C`, `T_D`, `T'C`, `T'D` |
| Natural comparison isomorphisms | `t_C : T_C ⋙ S_C_B ≅ S_C_A ⋙ T'C`, `t_D : T_D ⋙ S_D_B ≅ S_D_A ⋙ T'D` |
| Fixed `M`, `N = I_A M`, and `M_B = T_D M` | `M : D_A`; the latter two objects are always written `I_A.obj M` and `T_D.obj M` |
| Single `δ_A,N` | `δ_A`, whose precise domain and codomain use `I_A.obj M` |
| Full `C_B^0` containing `T_C N` and `I_B M_B` | `C0 : ObjectProperty C_B`, its `FullSubcategory`, and `hX`, `hY` |
| The family `δ_B,X`, natural only on that full subcategory | `δ_B`, and `hδ_B` for all `X Y : C0.FullSubcategory` and every morphism `f : X ⟶ Y` |
| The chosen primed object | `Q_A : Cp_A` |
| Full `V_B` containing the two displayed primed objects | `V : ObjectProperty Dp_B`, `hW`, `hZ`; `ObjectProperty.isoMk (t_D.app M)` lifts the specified isomorphism |
| A functor defined only on `V_B` | `J_B : V.FullSubcategory ⥤ Cp_B` |
| The two isomorphisms `α_A`, `α_B` | `α_A`, `α_B`, with the exact domains and codomains from the node |
| Family `E_B,Q`, natural for `t_D,M` | `E_B` and the single naturality equation `hE`, using `ObjectProperty.homMk` |
| The morphism `E_A` | `E_A : F'p_A.obj Q_A ⟶ S_D_A.obj M` |
| The A-counit compatibility equation | `hCounitA : δ_A ≫ F'p_A.map α_A.hom ≫ E_A = S_D_A.map (adj_A.counit.app M)` |
| The B-counit compatibility equation | `hCounitB : δ_B ⟨I_B.obj (T_D.obj M), hY⟩ ≫ F'p_B.map α_B.hom ≫ E_B ⟨S_D_B.obj (T_D.obj M), hW⟩ = S_D_B.map (adj_B.counit.app (T_D.obj M))` |
| Isomorphism `c` | `c : T_D.obj (F_A.obj (I_A.obj M)) ≅ F_B.obj (T_C.obj (I_A.obj M))` |
| Family `c'_Q` natural for `α_A` | `c'` and `hc'`; no naturality at any other morphism is required |
| Invertible components at the two objects | `hc'U : IsIso (c' (S_C_A.obj (I_A.obj M)))`, `[hc'Q : IsIso (c' Q_A)]` |
| Coefficient square | `hcoef`, with `t_D`, `δ_A`, `c'` on one side and `S_D_B.map c.hom`, `δ_B`, `F'p_B.map t_C` on the other |
| Primed isomorphism and its counit equation | `b'` and `hb'`; the inverse is `inv (c' Q_A)` |
| Full faithfulness on a possibly different full subcategory containing the two objects | `P`, `hPX`, `hPY`, `hFF : (P.ι ⋙ S_C_B).FullyFaithful` |
| Faithfulness only on the specified Hom set | `hSD : Function.Injective (fun f : F_B.obj (T_C.obj (I_A.obj M)) ⟶ T_D.obj M ↦ S_D_B.map f)` |
| Three invertible delta components | `hδA`, `hδBX`, `hδBY`; these are retained even though the diagram chase does not need them |
| Existence of an isomorphism `b` | `∃ b : T_C.obj (I_A.obj M) ⟶ I_B.obj (T_D.obj M), IsIso b ∧ ...` |
| Prescribed image of `b` | First equality in the conclusion: `(t_C ≪≫ T'C.mapIso α_A).hom ≫ b'.hom ≫ (α_B ≪≫ J_B.mapIso (ObjectProperty.isoMk (t_D.app M))).symm.hom` |
| Original counit identity | `F_B.map b ≫ adj_B.counit.app (T_D.obj M) = c.inv ≫ T_D.map (adj_A.counit.app M)` |
| Uniqueness of an isomorphism with the prescribed image | Final universal clause, requiring only `IsIso b''` and the image equality to conclude `b'' = b` |

The single dependency `lem-weil-pbc-adjunction-of-natural-bijection` is a Mathlib leaf:
`CategoryTheory.Adjunction.mkOfHomEquiv` in `Mathlib.CategoryTheory.Adjunction.Basic`.
Its full declaration and `Adjunction.CoreHomEquiv` were read: the bijections and both
naturality laws yield the standard `Adjunction` with the stated unit and counit.
The item assumes those adjunctions, so it directly uses their standard type and counits.
Other reused Mathlib interfaces are `ObjectProperty.FullSubcategory`, `ι`, `homMk`,
and `isoMk` from `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`, and
`Functor.FullyFaithful` from `Mathlib.CategoryTheory.Functor.FullyFaithful`.
Their signatures and docstrings were read. There is no private copy of any notion.

Edge cases checked: all identity data in the terminal category satisfy the conclusion;
empty full subcategories cannot satisfy the explicit membership hypotheses; `C0` and
`P` can differ, because each is full and both contain the needed objects. No closure
under coefficient functors, no global primed adjunction, and no global faithfulness
are assumed. All eight object and all eight morphism universes are independent.
Composition order was checked on noncommutative one-object groupoids using the
formulas `u ≫ b' ≫ v⁻¹` and `c⁻¹ ≫ T_D(e_A)`.

The omission in the old Lean statement is substantive: take every category to be the
one-object groupoid with automorphism group C₂, every functor to be identity, both
adjunctions to be identity adjunctions, and all comparison isomorphisms and delta
components to be identities. Set `E_A` to the nonidentity automorphism `s`, `E_B` to
identity, and `b' = s`. Every old hypothesis holds, including `hb'`, but its image
condition forces `b = s` whereas its counit conclusion forces `b = 1`. The restored
A-counit hypothesis excludes this example. Interchanging `E_A` and `E_B` similarly
tests the restored B-counit hypothesis. This is an interface repair, not a correction
to the already correct natural-language node; no `statement_change` is needed.

Searches performed with `msearch.py`:

- LeanFinder: "Descend a coefficient change isomorphism through fully faithful functors
  and verify the original adjunction counit identity". Eight hits, led by
  `Adjunction.map_restrictFullyFaithful_counit_app` and its reassociated version.
- Loogle: `CategoryTheory.Functor.FullyFaithful.preimageIso`. Seven hits, including the
  unique isomorphism lift and its hom/inverse formulas.
- Mathlib grep: `fullyFaithful.*counit|counit.*fullyFaithful|fully_faithful_counit_descent`
  in `CategoryTheory`. Eleven hits, principally adjunction restriction and reflection.
- LeanSearch: "Descent of isomorphism and counit compatibility through fully faithful
  functors". Eight hits, about invertibility or restriction of adjunction counits.
- Direct `rg` of the source project's `WeilConjectures/` and the shared `lean/Sheaf/`
  for `fully_faithful_counit_descent|FullyFaithfulCounitDescent|fullyFaithful.*counit`
  found only the defective owning side module. Direct `grep -rn` for the blueprint id
  in the upstream source found no result. The upstream-name index had no result.

The full types of `map_restrictFullyFaithful_counit_app` and `preimageIso` were read.
Neither is the node's statement: the first requires a global primed adjunction and
full faithfulness of both embeddings, and the second gives only the isomorphism lift.
The current owning module was also read through `scompile.py --source`; it has the same
missing hypotheses as the local source. No exact reusable declaration was found.

Validation: the prescribed `scompile.py` compiled the repaired module in isolation.
The only initial warning was an overlong source-reference line, which was shortened.
Final clean compilation and delivery preflight are run before pushing.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
