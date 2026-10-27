# O2 stage-2 compile maintenance, 2026-10-26

`lem-sfb-action-topos-coefficient-coherence` repeatedly failed before its packet
was checked. The failing library declaration was the private
`wordProjection_graph` in `SfGraphSecondProjectionSquare.lean`.

Landing `1bdfa420dba` changed `sfGraphWordProjection` from an inline composite to
a wrapper around `sfGraphProjectionWord`. The square proofs landed alongside it
still expanded only the wrapper. In particular, the second square left the
entire `sfGraphProjectionWord` application as an unsolved goal. This is a
mechanical proof compatibility issue; no statement correction or re-plan of the
action-topos item is warranted.

Explicitly unfold the new helper at the expansion steps in the first and middle
graph-square modules and remove obsolete simp arguments. The same repair of the
second square was independently committed during this investigation as
`9779daa4de1`; retain it. Preserve all definitions, signatures, docstrings and
proof strategies, and introduce no `sorry`.

The action-topos packet reaches these squares transitively through
`ProfiniteActionCoherentPresentation`, `Sites.CoherentToposRepair`, the Weil
coefficient category modules, finite-coefficient derived stability and
`SfGraphWordProjectionSquare`. The failing snapshot's source-override manifest
was `[]`; the worker reports' description of a mandatory override was not the
actual selection mechanism.

Validation: server `scompile.py` compiles each supplied file separately with its
60-second acceptance limit, against the current source overlay. Detailed
commands and results are retained in the maintenance workspace's `REPORT.md`.

Before writing the live files, preserve each original as
`<file>.maint-O2-action-topos-1792998847.bak`. Commit this repair under
`coord/.merge.lock` as `SHEAF_LEAD=L-only`.

The local compile-attachment cache also retains dependency failures while only
tracking the published-build stamp. After this repair, the O2 packet's two old
failed-result entries must be invalidated with backups so normal retries see
the current server sources. The launcher tool itself is outside this repair's
editable scope; its cache should eventually track the server source snapshot.
