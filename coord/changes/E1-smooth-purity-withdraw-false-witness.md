# AlgebraicGeometry.ProEtale.CondensedRing.exists_normalizedSmoothPurityMaps

## Reason

Withdraw a false, unused intermediate witness after replacing its sole active parent by
an application of the existing source-library purity isomorphism. The witness explicitly
omits smoothness and contains no finite-reduction or counit-normalization equation.
For f the identity of a nonempty point and d = 1 it would identify a degree-zero unit
with a Tate line shifted to degree -2. Even its intended smooth specialization does not
specify normalized maps, so its arbitrary pair cannot construct smoothTrace.

The active-parent scan of stmt_deps, proof_deps and proof-step uses found only
nt-target-smooth-purity-qbar. No unit record cites this node. Its Lean attachment is
set to null; the DAG node is preserved. The parent now depends on the existing
source-library smoothPurityIso, whose finite/integral/condensed unit route is preserved.

## Old

```lean
omit [SmoothOfRelativeDimension d f.left] in
/--
The normalized diagonal/DNC construction of smooth purity provides mutually inverse maps
between the exceptional inverse image of the coefficient unit and the shifted Tate twist.
The finite coefficient maps are compatible with coefficient extension, so their coherent
reconstruction gives the displayed maps in the condensed bounded constructible category.
This is the geometric reconstruction step: the source is SGA 4, Exposé XVIII, Théorème 3.2.5,
and the condensed coefficient passage is the reconstruction argument of the smooth-purity
blueprint (finite diagonal class, deformation to the normal bundle, and the coherent
finite-extension tower).

(blueprint: lem-pur-condensed-normalized-witness)
-/
theorem exists_normalizedSmoothPurityMaps :
    Nonempty {p :
      (((boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))).obj ⟶
        (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d)) ×
      (((shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d)) ⟶
        ((boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
          (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))).obj)
      // p.1 ≫ p.2 = 𝟙 _ ∧ p.2 ≫ p.1 = 𝟙 _} := by
  sorry

```

## New

The module is withdrawn using deleted.txt and will be replaced by an empty module.
There is no replacement public declaration. Sheaf.Targets.SmoothPurityQbar keeps its
statement verbatim and proves its Nonempty conclusion by:

```lean
by
  exact ⟨smoothPurityIso ℓ f d⟩
```

No source-library declaration, signature, attribute, public import or non-theorem body
is removed or changed. A proved private adjunction identity and a dispute comment are
added to the assigned source module.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | False witness withdrawn. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Sole importer; remove private witness import, use the source isomorphism instead. |
| WeilConjectures.SmoothPurity.Defs | E1 | Public interface unchanged; private trace/adjunct identity and statement-dispute comment only. |

The read-only downstream.py --uses scan found no use of the witness outside its own
declaration. Its sole importer is nevertheless adapted and compiled in this packet.
No other interface changes, so no forced adaptations are needed.

## Status

landed 20261026T235848-L-1461864 2026-10-26 (merge of deliver/E1/WeilConjectures.SmoothPurity.Defs)
