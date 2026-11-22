/- MPRWE round 3 C control.
   The local `have` exposes the selected CategoryStruct.comp/LinearMap.comp
   descendant while the outer transport equality and its M0 pair are kept.
   The full source snapshot is replayed by the round-3 runner. -/
-- Selected descendant: right-square map, argument[6]/argument[5].
-- Intervention form used in the source snapshot:
--   have hSelected := e.pull_pin.right.hom.app M
--   show _ ≫ (restrict ...).map hSelected ≫ _ = _
-- The restoration snapshot removes only this local alignment.
