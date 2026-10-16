# AlgebraicGeometry.ProEtale.integralLatticeSheaf_locallyConstant

## Reason

Separate the already proved foundational lattice API from its final local-constancy proof,
so the new proof lemmas can import the foundations without an import cycle.
`LatticeSheafLocallyConstant` publicly imports `LatticeSheafBasic`; importers therefore
see the same original declarations. This separation is for the dependency direction,
not to divide an over-time compilation. The final Basic file compiles as one file
in 55.6 seconds in the second reading.
The second reading encountered a timeout and repaired elaboration in that same file:
its proof sections now respect type transparency, and the private local-basis
coordinate equivalence receives an explicit expected type at construction. Neither
change affects any public signature or definition body.

All 26 original public signatures were compared and are unchanged. Every original
public definition has the same body. No hypothesis, universe, conclusion or target
meaning changes. The new coefficient-matrix definitions are explicit constructions.
The only choice of lattice data uses the previously proved
`exists_matrixIntegralLatticePair`, not an unproved existence assertion.

Two existing private ring homomorphisms become public so the matrix proof can evaluate
coefficient sections and form constant sections. Their bodies are unchanged. The private
coset-detection calculation is generalized from the identity object to an arbitrary
nonempty object of the same slice; all old public theorems keep their signatures.
New proved public consequences are `integralMatrixSubgroup_mem_iff` and
`matrixLatticeImage_coset_eq_of_eq_at`.

## Old

The original file contains the foundational declarations followed by the main theorem.
The two relevant private signatures were:

```lean
private noncomputable def latticeConstantRingHom (X : Scheme.{u}) (K : Type u)
    [TopologicalSpace K] [CommRing K] [IsTopologicalRing K] (V : X.ProEt) :
    K →+* (latticeCoefficientSheaf X K).obj.obj (op V) where
  toFun := latticeConstantCoefficient X K V
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private noncomputable def latticeEvaluationRingHom (V : X.ProEt) (x : V.left) :
    (latticeCoefficientSheaf X K).obj.obj (op V) →+* K where
  toFun c := c.down x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
```

## New

The original module now starts with:

```lean
module
public import Sheaf.Paper.LatticeSheafBasic
import Sheaf.Paper.LatticeClassDescent
import Sheaf.Paper.LatticeCosetLocalSurjectivity
```

The publicly imported Basic module contains the original foundational declarations,
with the same original signatures and bodies, and these now public signatures:

```lean
noncomputable def latticeConstantRingHom (X : Scheme.{u}) (K : Type u)
    [TopologicalSpace K] [CommRing K] [IsTopologicalRing K] (V : X.ProEt) :
    K →+* (latticeCoefficientSheaf X K).obj.obj (op V) where
  toFun := latticeConstantCoefficient X K V
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

noncomputable def latticeEvaluationRingHom (V : X.ProEt) (x : V.left) :
    (latticeCoefficientSheaf X K).obj.obj (op V) →+* K where
  toFun c := c.down x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem integralMatrixSubgroup_mem_iff (g : Matrix.GeneralLinearGroup (Fin n) K) :
    g ∈ integralMatrixSubgroup A n ↔
      (∀ i j, g.val i j ∈ A) ∧ (∀ i j, (g⁻¹).val i j ∈ A)

theorem matrixLatticeImage_coset_eq_of_eq_at
    (g h : Matrix.GeneralLinearGroup (Fin n) K) (T : (Over U)ᵒᵖ)
    (hT : Nonempty T.unop.left.left)
    (heq : matrixLatticeImage X K A U n g T = matrixLatticeImage X K A U n h T) :
    (Quotient.mk _ g : integralMatrixCosets A n) = Quotient.mk _ h
```

The theorem `integralLatticeSheaf_locallyConstant` retains its exact original signature.
Its proof combines exact class descent with local surjectivity of the explicitly
constructed coset map, and uses its sheafification and normalization lemmas.

## Users

`tools/downstream.py Sheaf.Paper.LatticeSheafLocallyConstant --uses
integralLatticeSheaf_locallyConstant` was run after the downstream E3 landing.
The full downstream list follows. The only direct external textual use of the theorem
is now in `LisseLatticeClassSheaf`. No existing consumer is changed in this delivery.
All seven current lattice coefficients, normalization, coefficient transport,
presentation transport, slice transport, class sheaf and etale-local modules compiled
unchanged against the overlay. The remaining importers have the same reexported API;
no statement or definition that they use changes meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.IntegralLatticeCoefficientTransport | unclaimed | unchanged signature and reexported definitions; no adaptation |
| Sheaf.AlgebraicGeometry.LisseLatticeClassSheaf | unclaimed | unchanged signature and reexported definitions; no adaptation |
| Sheaf.AlgebraicGeometry.LisseLatticeCoefficientNormalization | unclaimed | unchanged signature and reexported definitions; no adaptation |
| Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal | unclaimed | unchanged signature and reexported definitions; no adaptation |
| Sheaf.AlgebraicGeometry.LisseLatticePresentationTransport | unclaimed | unchanged signature and reexported definitions; no adaptation |
| Sheaf.AlgebraicGeometry.LisseLatticeSliceTransport | unclaimed | unchanged signature and reexported definitions; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | unchanged signature and reexported definitions; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | unchanged signature and reexported definitions; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | unchanged signature and reexported definitions; no adaptation |
| Sheaf.Paper.ContinuousEtaleLocalLattices | B2 | unchanged signature and reexported definitions; no adaptation |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | unchanged signature and reexported definitions; no adaptation |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | unchanged signature and reexported definitions; no adaptation |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | unchanged signature and reexported definitions; no adaptation |
| TargetsCheck | unclaimed | unchanged signature and reexported definitions; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | unchanged signature and reexported definitions; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | unchanged signature and reexported definitions; no adaptation |

No module held by another group is adapted. No forced adaptation or target statement
review is required: no original definition body or public signature changes.

## Status

landed 20261016T085349-L-1757920 2026-10-16 (merge of deliver/B3/Sheaf.Paper.LatticeSheafLocallyConstant)
