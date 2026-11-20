/- Historical probe shape from 195ac97d078. The declaration names are intentionally left
   as comments so this file is a readable, non-invasive record rather than a new library API. -/

-- set_option debug.skipKernelTC true in
-- lemma test_tensorObj_kernelProbe ... := by rfl

-- For a declaration `d`, the historical command probe performed:
--   Kernel.check env default (info.value! true)
--   Kernel.isDefEq env default inferredType info.type
--   Kernel.isDefEq env default info.type inferredType
-- and printed wall milliseconds for each call.

-- The reproducer's exact checked pair was:
--   @CategoryTheory.MonoidalCategoryStruct.tensorObj
--     (DerivedCategory (Sheaf X.smallEtaleTopology A)) _ inferInstance K L
--   @CategoryTheory.MonoidalCategoryStruct.tensorObj
--     (DerivedMonoidal DerivedCategory.Qh
--       (HomotopyCategory.quasiIso
--         (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ)))
--     _ inferInstance K L

-- Recorded output:
--   Kernel.check(value): 1 ms
--   isDefEq forward: 49867 ms, reverse: 50279 ms
