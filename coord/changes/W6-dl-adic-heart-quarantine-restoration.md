# DlLocallyConstructibleAdicHeart quarantine restoration and proof repair

## Reason

Returned delivery `830d61ae2fd` could not land because the global build moved this
importer to quarantine after the delivery base. The return explicitly required
claiming its rework item and restoring the archived source. W6 claimed the rework
item and preserved the complete archived source. Root repairs have now restored
this importer and its prerequisites on main; the packet follows that restoration.
The quarantine archive is retained.

## Old

The original compiler error was a deterministic `whnf` timeout at
`dlAdicLocalCompatible_zero`, followed by an unknown-constant error at its consumer.
The earlier scoped heartbeat increase still reached the compile-time limit on the
current base, so it is removed.

The public theorem signature is preserved verbatim:

```lean
theorem dlAdicLocalCompatible_zero (F G : DlAdicLocalRaw D c T) :
    dlAdicLocalCompatible D c T (InducedCategory.homMk (fun U ↦ (0 : F.value U ⟶ G.value U)))
```

## New

Elaboration now respects transparency. The multiplicativity proof explicitly uses
category identity and composition laws. A private proof import of
`GeneralAlgebraicallyClosedCoefficients` exposes its proved private `mkHom_zero`.
Proved private categorical helpers rewrite the stage formula and transport the zero
arrow across the specified object equalities. Local irreducibility protects large
comparison definitions during this calculation.

All existing declarations, signatures, attributes, public imports, non-theorem
bodies, and mathematical dependencies are preserved. No heartbeat limit is raised.
The node remains `def-dl-a1-locally-constructible-adic-heart`; its proof description
records the existing lemma and categorical transport. No proof holes are added.
A clean single-file check completes in about 20 seconds.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.DlLocallyConstructibleAdicHeart` | unclaimed after restoration; W6 rework claim held during quarantine | Restore complete source and repair proof elaboration. |
| `Sheaf.Paper.NormalizedDVRFlatCokernel` | W6 | Include the importer adaptation required by the returned delivery. |

The public interface is unchanged, so consumers need no source adaptation.

## Status

landed 20261026T121136-L-2760628 2026-10-26 (merge of deliver/W6/Sheaf.Paper.NormalizedDVRFlatCokernel)
