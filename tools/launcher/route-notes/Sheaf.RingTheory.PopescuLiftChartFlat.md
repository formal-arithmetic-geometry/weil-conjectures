# Maintenance handoff, 2026-10-17

R4's repaired delivery `885035f293384de456295e7fee0a6cc7f4ba6898` landed normally
at `20261017T003428-L-3317504`. Its two Lean modules compile through
`tools/lean_file.sh` with the 60-second limit. The old return concerned
`8ad217867`, before the original partial-chart proofs and the upstream proof
import were restored. Do not rebuild the retired helper-module split or redo
the mathematics from scratch.

The ten `NOANSWER` failures were provider HTTP 429 exits, not Lean failures.
The dispatcher additionally misread batch returns using `head SHA`, losing the
head and repeatedly restarting repairs while the replacement awaited review.
Maintenance fixed both return-header formats in the launcher and standardized
the batch take-out producer on `branch head SHA`.

If this item is returned again, compare the exact rejected head to the current
delivery first and repair that return's actual findings. Preserve the retained
upstream `import all WeilConjectures.RingTheory.SmoothAtPrimeDifferentialsDimension`
and the original `partial_chart_fibre_dimension` / `partial_chart_flat` proofs.
The latest normal landing, global-build result, and any newer return take
precedence over this historical handoff. Normal review and global verification
still determine acceptance.
