# AlgebraicGeometry.bertiniUniversalSection and universal-family helpers

## Reason

Move the four concrete universal-family definitions into a support module so that the local
first-order theorem and fibre-chart theorem can use them without importing the global
dimension theorem. This prevents an import cycle. There is no mathematical definition or
statement change. The original module publicly imports the support module, preserving access
for its consumers. New helpers construct the reduced singular scheme and its projection;
no object is chosen from a mere existence assertion.

## Old

In `Sheaf.AlgebraicGeometry.BertiniSingularLocusDimension`:

```lean
/-- The universal section `∑ xᵢ pr₂* sᵢ` on coefficient affine space times `Y`.
The coordinates are the polynomial variables under the canonical global-sections isomorphism.
Source: Stacks Project, Situation 0FD3 (blueprint: lem-zl-bertini-singular-locus-dimension). -/
def bertiniUniversalSection {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) :
    Γ((Scheme.Modules.tensorPullback
      (pullback.snd (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k)))
        f)).obj L, ⊤) :=
  ∑ i, (pullback.fst
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))) f).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial I k))).inv (MvPolynomial.X i)) •
    Scheme.Modules.tensorSectionsUnit
      (pullback.snd (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k)))
        f) L (s i)

/-- The ideal sheaf of the universal zero scheme, constructed using the recorded zero scheme.
Source: Stacks Project, Situation 0FD3 (blueprint: lem-zl-bertini-singular-locus-dimension). -/
def bertiniUniversalIdeal {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) :
    (pullback
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))) f).IdealSheafData :=
  (Scheme.Modules.homOfGlobalSection _ (bertiniUniversalSection f L s)).zeroLocus

/-- The projection `q : H_univ ⟶ A^I_k` from the universal zero scheme.
Source: Stacks Project, Tag 0FD6 (blueprint: lem-zl-bertini-singular-locus-dimension). -/
def bertiniUniversalProjection {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) :
    (bertiniUniversalIdeal f L s).subscheme ⟶ Spec (CommRingCat.of (MvPolynomial I k)) :=
  (bertiniUniversalIdeal f L s).subschemeι ≫
    pullback.fst
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))) f

/-- The non-smooth locus of the universal projection: points with no smooth open neighbourhood.
Source: Stacks Project, Tag 0FD6 (blueprint: lem-zl-bertini-singular-locus-dimension). -/
def bertiniUniversalSingularLocus {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) :
    Set (bertiniUniversalIdeal f L s).subscheme :=
  {h | ¬ ∃ W : (bertiniUniversalIdeal f L s).subscheme.Opens,
    h ∈ W ∧ Smooth (W.ι ≫ bertiniUniversalProjection f L s)}
```

## New

The same four signatures and bodies, verbatim, in
`Sheaf.AlgebraicGeometry.BertiniUniversalFamily`, publicly imported by the old module.
Only the blueprint tag in their docstrings points to their new definition node.
The global theorem has exactly its original signature.

## Users

`tools/downstream.py` was run for each of the four names. Each reports only the original
module as a textual user. The current downstream import closure contains 26 modules; its only
direct importer is BertiniSmoothMember, whose original source does not use any of these four
names. Its public declaration signatures do not change. No consumer adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.BertiniSingularLocusDimension | Q7 | Publicly imports support module; exact theorem signature retained. |
| Sheaf.AlgebraicGeometry.BertiniSmoothMember | unchanged consumer | Existing direct import resolves the same theorem; source untouched. |

All 26 transitive import consumers have no textual uses of the moved definitions.
No target declaration or mathematical definition in a target signature is changed. The target
meaning review remains valid because the moved expressions are identical.

## Status

landed 20261020T132029-L-1404056 2026-10-20 (merge of deliver/Q7/Sheaf.AlgebraicGeometry.BertiniSingularLocusDimension)
