# IsLocalRing.depth_eq_projectiveDimension_add_depth

## Reason

Restore the assigned quarantined module and its sole consumer against the synchronized
upstream API. The rework row records missing public depth helpers: the Sheaf helper module
was retired and the upstream counterpart keeps its helpers private. The canonical
GlobalDimension module also replaced the old minimum-resolution definition of finite
projective dimension with Mathlib's Ext-bound predicate and removed the natural-number
ModuleCat.projectiveDimension wrapper.

Use the canonical upstream imports and express the same Auslander–Buchsbaum equality
using CategoryTheory.projectiveDimension in WithBot ℕ∞. For a nonzero module of finite
projective dimension this is the cast of the least natural Ext bound, as the proved
private projectiveDimension_eq_nat shows. The bounded-resolution bridge identifies
this minimum with the former minimum resolution length. Depth embeds injectively into
WithBot ℕ∞ and addition of embedded values agrees with addition in ℕ∞, so this changes
neither the mathematical statement nor its hypotheses. The zero module remains excluded;
the case of projective dimension zero is handled explicitly by nontriviality.

The three unavailable helper results are proved privately inside the restored Sheaf
module, using the same regular-sequence arguments as upstream. The source-library
boundary forbids changing upstream visibility; no upstream source is edited and no
new definition, public helper, axiom, or hole is introduced.

## Old

The quarantined module publicly imported Sheaf.RingTheory.GlobalDimension and privately
imported Sheaf.RingTheory.BoundedProjectiveResolutionDimension and
Sheaf.RingTheory.CohenMacaulayDepthFirstTerm. Its public theorem signature was:

```lean
theorem depth_eq_projectiveDimension_add_depth
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type (max u v)) [AddCommGroup M] [Module R M] [Nontrivial M] [Module.Finite R M]
    (h : ModuleCat.HasFiniteProjectiveDimension (ModuleCat.of R M)) :
    depth (R := R) R =
      (ModuleCat.projectiveDimension (ModuleCat.of R M) h : ℕ∞) + depth (R := R) M
```

The consumer used an explicit resolution witness as finite projective dimension, then
extracted the retired natural-number projective dimension and converted it back to
HasProjectiveDimensionLE through the bounded-resolution bridge.

## New

The restored module publicly imports WeilConjectures.RingTheory.GlobalDimension and
privately imports WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension.
The retired helper import is replaced with proved private lemmas and the finite-free
and flat regular-sequence Mathlib imports their proofs need. Its public signature is:

```lean
theorem depth_eq_projectiveDimension_add_depth
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type (max u v)) [AddCommGroup M] [Module R M] [Nontrivial M] [Module.Finite R M]
    (h : ModuleCat.HasFiniteProjectiveDimension (ModuleCat.of R M)) :
    (depth (R := R) R : WithBot ℕ∞) =
      CategoryTheory.projectiveDimension (ModuleCat.of R M) +
        (depth (R := R) M : WithBot ℕ∞)
```

UniformPerfectQuotientBound is restored from its quarantine archive. Its only proof
adaptation replaces the old finite-resolution/natural-dimension block with
HasFiniteProjectiveDimension N := ⟨d, hdloc⟩ and the direct categorical inequality
projectiveDimension N ≤ depth R ≤ r. The public signatures and public imports are
byte-identical to the archive. Its now-unused proof import of
Sheaf.RingTheory.BoundedProjectiveResolutionDimension is removed.
Both nodes retain their statements, attachments, unit, and parent dependencies;
their proof descriptions follow the restored code. Only the consumer's direct
proof edge to the bounded-resolution comparison is removed; AuslanderBuchsbaum
continues to require that comparison.

## Users

The live downstream command reports the item unknown because it is quarantined.
Text searches of lean/Sheaf, lean/WeilConjectures, and quarantine/Sheaf locate exactly
one direct importer and application of the changed theorem. Claim records contain
no UniformPerfectQuotientBound claim at the time of adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.AuslanderBuchsbaum | G2 | Restore zero-hole proof with canonical imports, categorical equality, and private depth helpers. |
| Sheaf.RingTheory.UniformPerfectQuotientBound | unclaimed; quarantined | Restore and adapt the sole call; preserve both signatures and public imports. |
| Sheaf.Paper.AmplificationProper | quarantined | Imports UniformPerfectQuotientBound; its public interface is identical, so no adaptation. |
| Sheaf.Paper.CompletedConstructibleReductionControl | quarantined | Imports UniformPerfectQuotientBound; its public interface is identical, so no adaptation. |

The original UniformPerfectQuotientBound was compiled against the restored item:
it failed at line 153 because a HasProjectiveResolutionLE witness was supplied where
HasProjectiveDimensionLE was required, and at lines 155–168 because the retired
ModuleCat.projectiveDimension constant was unknown. The adapted consumer compiles
cleanly. Both consumer declaration signatures were compared verbatim with the archive.
No other module changes its meaning, and no target statement or target definition changes.
The mathematical DAG citer lem-weil-pbc-uniform-perfect-quotient-bound remains true
and uses the same Auslander–Buchsbaum formula. All archives are preserved.

## Status

landed 20261020T163314-L-3728444 2026-10-20 (merge of deliver/G2/Sheaf.RingTheory.AuslanderBuchsbaum)
