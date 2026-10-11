## Worker report

(Restated by reviewer R-cre; P1's delivered report described the reverted statement.)

The delivered statement correction was reverted (`--revert-statement`): it named a fault of
the earlier Lean theorem, not of the node, and the corrected node was weaker than the source
(acyclicity only for positive-degree terms, dropping D^0; a degreewise cohomology isomorphism
instead of `Rf_* F ≅ f_* D` in D(O_S); no augmentation map). The node stays as on sheaf-dag.

The Lean is restated against that node. `AlgebraicGeometry.cech_resolution_derived_direct_image`
takes `f : X ⟶ Spec A` with `[IsSeparated f] [QuasiCompact f]`, a finite affine open cover
`U : ι → X.Opens` (`[Finite ι]`, `iSup U = ⊤`, `∀ i, IsAffineOpen (U i)`) and a quasi-coherent
`F`, and asserts a complex `D` of O_X-modules with augmentation `ε : single₀ F ⟶ D` such that
- `D` is the Čech complex of sheaves: its presheaf of sections (as Γ(X,⊤)-modules) is, term by
  term and compatibly with the differentials, upstream `cechComplexFunctor U` applied to the
  presheaf `W ↦ (V ↦ F(W ⨯ V))`, i.e. `V ↦ Č(U ∩ V, F)`; `ε` is the restriction
  `F(V) → F(U_i ⨯ V)`; each term is isomorphic as O_X-module to `∏_y j_{U_y,*}(F|_{U_y})`;
- `QuasiIso ε` (the augmented complex is exact);
- every term `D.X p` is f_*-acyclic (`R^q f_* D^p = 0`, q > 0);
- `Rf_* F ≅ Q(f_* D)` in D(O_S), f_* = `RingedSpace.moduleDirectImage`, D extended to ℤ along
  `embeddingUpNat`.
The Čech complex is the ordered one of upstream `cechComplexFunctor` (STATE line ČECH
COMPARISON), homotopy equivalent to the alternating one of the node.

## Second reading by P1

P1's second reading matched its corrected node (positive-degree acyclicity, degreewise
cohomology isomorphism, untied complexes `D` and `C`); that reading is superseded by the
reviewer's restatement above against the node as on sheaf-dag, read clause by clause by R-cre.
