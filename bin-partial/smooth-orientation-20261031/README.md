Handover to Houyi (Zulip #1325), 2026-10-31: our partial work on smoothOrientation / smoothOrientation_baseChange.
Source: Weil sheaf-dag at d3532dc6ecf (lean/ paths as in that repo). MANIFEST.tsv: module, sorry count of its own text
(0 = no sorry in the file; imports may still carry sorries, closure not re-verified for this package), DAG nodes.
nodes/: DAG node JSON (statement, NL proof steps, deps, blueprint source). route-notes/: our worker route notes
(the orientation/Defs notes now start with the handover banner; the plan below it is the earlier route record).
Construction plan (node def-route-smooth-orientation): finite diagonal orientations phi_n
(lem-pur-finite-smooth-adjunction-general-base) -> strict integral tower (lem-pur-condensed-tate-integral-tower) ->
c_0 (lem-pur-condensed-exceptional-reconstruction, case b, r=-2d) -> Tate realization a, unit u
(lem-pur-condensed-tate-realization); smoothOrientation = G(u) o c_0 o a~^{-1}.
