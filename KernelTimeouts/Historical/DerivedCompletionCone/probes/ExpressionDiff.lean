/- Structural-diff record for inferred versus declared types. -/

-- The historical diff descends through equal application heads and records the minimal
-- differing pairs. It reports 36 leaves, all proof expressions. Representative leaves:
--   derivedCompletionDiagram._proof_1  vs  instIsGrothendieckAbelianModuleCat
--   derivedCompletionDiagram._proof_3  vs  CategoryTheory.Sheaf.monoidalPreadditive
--   derivedCompletionDiagram._proof_8  vs  DerivedCategory.hasDerivedMonoidalCategory

-- A proof comparison is only cheap after its proposition types are reconciled. Those types
-- contain the concrete derived MonoidalCategory instance printed in REPORT.md.
