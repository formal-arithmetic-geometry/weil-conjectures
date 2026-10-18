# IsLocalRing depth helper visibility

## Reason

The returned AuslanderBuchsbaum delivery duplicated three existing proved private
helpers in CohenMacaulayDepthFirstTerm. Expose the original helpers in that module
and use them through a proof-only import. No proof or type of these helpers changes.
CohenMacaulayDepthFirstTerm is unclaimed (checked 2026-10-18). No target statement
or definition changes. The three added docstrings describe the existing results.

## Old

```lean
private theorem depth_equiv_local {R : Type u} [CommRing R] [IsLocalRing R]
    {A : Type*} [AddCommGroup A] [Module R A] [Module.Finite R A]
    {B : Type*} [AddCommGroup B] [Module R B] [Module.Finite R B]
    (e : A ≃ₗ[R] B) : depth (R := R) A = depth (R := R) B

private theorem depth_subsingleton {R : Type u} [CommRing R] [IsLocalRing R]
    (A : Type*) [AddCommGroup A] [Module R A] [Module.Finite R A] [Subsingleton A] :
    depth (R := R) A = ⊤

private theorem depth_free_ge {R : Type u} [CommRing R] [IsLocalRing R]
    (A : Type*) [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Free R A] :
    depth (R := R) R ≤ depth (R := R) A
```

## New

```lean
theorem depth_equiv_local {R : Type u} [CommRing R] [IsLocalRing R]
    {A : Type*} [AddCommGroup A] [Module R A] [Module.Finite R A]
    {B : Type*} [AddCommGroup B] [Module R B] [Module.Finite R B]
    (e : A ≃ₗ[R] B) : depth (R := R) A = depth (R := R) B

theorem depth_subsingleton {R : Type u} [CommRing R] [IsLocalRing R]
    (A : Type*) [AddCommGroup A] [Module R A] [Module.Finite R A] [Subsingleton A] :
    depth (R := R) A = ⊤

theorem depth_free_ge {R : Type u} [CommRing R] [IsLocalRing R]
    (A : Type*) [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Free R A] :
    depth (R := R) R ≤ depth (R := R) A
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.CohenMacaulayDepthFirstTerm | unclaimed | Only three visibility modifiers and explanatory docstrings change; proofs and types are identical. |
| Sheaf.RingTheory.CohenMacaulayFreeResolutionMCM | unclaimed | The sole existing direct importer. Its first_term_depth_ge application is unchanged; compiled against the exposed helpers. |
| Sheaf.RingTheory.AuslanderBuchsbaum | Q2 | Remove all three duplicate private helpers and import the existing ones for proofs. |

`tools/downstream.py --direct --uses depth_equiv_local depth_free_ge
 depth_subsingleton` lists the sole direct importer above and finds no existing
external textual users of these previously private names. This additive visibility
change preserves every existing public signature and every import. There is no
forced adaptation of another group's module.

## Status

landed 20261018T091410-L-3257941 2026-10-18 (merge of deliver/Q2/Sheaf.RingTheory.AuslanderBuchsbaum)
